//! Deterministic source-retention fixed point over the owned compiler graph.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, TyCtxt, TypeSuperVisitable, TypeVisitable, TypeVisitor};

use crate::definitions::CollectedDefinitions;
use crate::dependency_graph::{
    DependencyGraph, DependencyKind, ExpansionNode, GraphNode, MacroImplementationKind,
    expansion_source_survival, valid_roots,
};
use crate::graph::{
    DefinitionGraph, DefinitionId, DefinitionKind, DefinitionOrigin, DefinitionTarget,
};
use crate::source::{
    CfgState, MacroRuleSourceFacts, SourceInventory, SourceUnitId, WrittenUnit, WrittenUnitKind,
    validate_macro_rule_facts, validate_ownerless_attribute_invocations,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SourceRequirement {
    pub trigger: SourceUnitId,
    pub required: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CompilerSourceRequirement {
    trigger: GraphNode,
    required: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRuleSelectionRequirement {
    pub expansion: crate::dependency_graph::ExpansionId,
    pub rule: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ConditionalSourceRequirement {
    pub left: SourceUnitId,
    pub right: SourceUnitId,
    pub required: SourceUnitId,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SourceDisjunction {
    pub trigger: SourceUnitId,
    pub choices: Vec<SourceUnitId>,
}

fn source_macro_rule_requirements(
    source: &SourceInventory,
) -> impl Iterator<Item = SourceRequirement> + '_ {
    source
        .macro_rules
        .iter()
        .filter_map(|facts| match facts {
            MacroRuleSourceFacts::Whole { .. } => None,
            MacroRuleSourceFacts::Refined {
                definition,
                rules,
                observed_selections,
                ..
            } if observed_selections.is_empty() => Some((*definition, rules.as_slice())),
            MacroRuleSourceFacts::Refined { .. } => None,
        })
        .flat_map(|(trigger, rules)| {
            rules
                .iter()
                .copied()
                .map(move |required| SourceRequirement { trigger, required })
        })
}

/// Owned source-domain constraints collected before leaving the compiler
/// session.
///
/// Compiler-to-source facts remain producer-specific here so each producer
/// can prove its own coverage before validation projects them into the shared
/// retention fixed point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourceConstraints {
    pub atomic_groups: Vec<Vec<SourceUnitId>>,
    pub macro_rule_selection_requirements: Vec<MacroRuleSelectionRequirement>,
    pub ancestor_requirements: Vec<SourceRequirement>,
    pub shell_requirements: Vec<SourceRequirement>,
    pub macro_rule_requirements: Vec<SourceRequirement>,
    pub member_requirements: Vec<SourceRequirement>,
    pub conditional_member_requirements: Vec<ConditionalSourceRequirement>,
    pub disjunctions: Vec<SourceDisjunction>,
    pub member_containers: Vec<SourceUnitId>,
    pub classified_members: Vec<SourceUnitId>,
}

impl SourceConstraints {
    /// Builds the constraints that are intrinsic to the unexpanded source.
    /// Trait/impl constraints and their coverage witnesses are added by the
    /// compiler adapter.
    pub(crate) fn from_source(source: &SourceInventory) -> Self {
        let mut groups = BTreeMap::new();
        for unit in &source.units {
            groups
                .entry(unit.atomic_group)
                .or_insert_with(Vec::new)
                .push(unit.id);
        }
        Self {
            atomic_groups: groups.into_values().collect(),
            macro_rule_selection_requirements: Vec::new(),
            ancestor_requirements: source
                .units
                .iter()
                .filter_map(|unit| {
                    unit.parent.map(|required| SourceRequirement {
                        trigger: unit.id,
                        required,
                    })
                })
                .collect(),
            shell_requirements: Vec::new(),
            macro_rule_requirements: source_macro_rule_requirements(source).collect(),
            member_requirements: Vec::new(),
            conditional_member_requirements: Vec::new(),
            disjunctions: Vec::new(),
            member_containers: Vec::new(),
            classified_members: Vec::new(),
        }
    }
}

/// Converts rustc's trait/impl completeness rules into an owned source model.
/// No compiler-lifetime value crosses this boundary.
pub(crate) fn collect_source_constraints(
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
) -> Result<SourceConstraints, RetentionError> {
    validate_source(source)?;
    let local_definitions = reverse_local_definitions(tcx, definitions)?;
    let definition_units = definition_source_units_from_graph(source, &definitions.graph)?;
    let mut constraints = SourceConstraints::from_source(source);

    let mut containers = BTreeMap::new();
    for definition in &definitions.graph.definitions {
        if !matches!(
            definition.kind,
            DefinitionKind::Trait | DefinitionKind::Impl
        ) {
            continue;
        }
        let DefinitionOrigin::Written { unit, .. } = &definition.origin else {
            continue;
        };
        let unit = *unit;
        let local = local_definitions[definition.id.0 as usize];
        let expected = match definition.kind {
            DefinitionKind::Trait => DefKind::Trait,
            DefinitionKind::Impl => tcx.def_kind(local),
            _ => unreachable!(),
        };
        if tcx.def_kind(local) != expected
            || !matches!(tcx.def_kind(local), DefKind::Trait | DefKind::Impl { .. })
            || source.units.get(unit.0 as usize).is_none_or(|source_unit| {
                source_unit.id != unit || source_unit.cfg_state != CfgState::Active
            })
            || containers.insert(unit, definition.id).is_some()
        {
            return Err(RetentionError::IncompleteMemberConstraints);
        }
    }
    constraints.member_containers = containers.keys().copied().collect();

    let mut member_requirements = BTreeSet::new();
    for member in source.units.iter().filter(|unit| {
        unit.cfg_state == CfgState::Active
            && matches!(
                unit.kind,
                WrittenUnitKind::TraitMember | WrittenUnitKind::ImplMember
            )
    }) {
        let candidates = definitions
            .graph
            .definitions
            .iter()
            .filter(|definition| {
                matches!(
                    definition.kind,
                    DefinitionKind::AssociatedType
                        | DefinitionKind::AssociatedFunction
                        | DefinitionKind::AssociatedConst
                ) && matches!(definition.origin, DefinitionOrigin::Written { unit, .. } if unit == member.id)
            })
            .collect::<Vec<_>>();
        let [definition] = candidates.as_slice() else {
            return Err(RetentionError::IncompleteMemberConstraints);
        };
        let parent = definition
            .parent
            .ok_or(RetentionError::IncompleteMemberConstraints)?;
        let expected_parent_kind = match member.kind {
            WrittenUnitKind::TraitMember => DefinitionKind::Trait,
            WrittenUnitKind::ImplMember => DefinitionKind::Impl,
            _ => unreachable!(),
        };
        if definitions.graph.definitions[parent.0 as usize].kind != expected_parent_kind
            || member.parent != Some(definition_units[parent.0 as usize])
            || !containers.contains_key(&definition_units[parent.0 as usize])
            || !tcx
                .def_kind(local_definitions[definition.id.0 as usize])
                .is_assoc()
        {
            return Err(RetentionError::IncompleteMemberConstraints);
        }
        constraints.classified_members.push(member.id);
        constraints.shell_requirements.push(SourceRequirement {
            trigger: member.id,
            required: member.parent.expect("member parent was checked"),
        });
    }

    for definition in definitions.graph.definitions.iter().filter(|definition| {
        matches!(
            definition.kind,
            DefinitionKind::AssociatedType
                | DefinitionKind::AssociatedFunction
                | DefinitionKind::AssociatedConst
        ) && matches!(
            definition.origin,
            DefinitionOrigin::Written { .. } | DefinitionOrigin::Expanded { .. }
        )
    }) {
        collect_semantic_member_requirements(
            tcx,
            definitions,
            &definition_units,
            local_definitions[definition.id.0 as usize],
            definition_units[definition.id.0 as usize],
            &mut member_requirements,
        )?;
    }

    let mut conditional_requirements = BTreeSet::new();
    let mut disjunctions = BTreeSet::new();
    for definition in definitions
        .graph
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::Impl)
    {
        collect_impl_constraints(
            tcx,
            source,
            definitions,
            &local_definitions,
            &definition_units,
            definition.id,
            &mut member_requirements,
            &mut conditional_requirements,
            &mut disjunctions,
        )?;
    }
    collect_body_impl_requirements(
        tcx,
        definitions,
        &definition_units,
        &mut member_requirements,
    )?;
    constraints.member_requirements = member_requirements.into_iter().collect();
    constraints.conditional_member_requirements = conditional_requirements.into_iter().collect();
    constraints.disjunctions = disjunctions.into_iter().collect();
    constraints.shell_requirements.sort();
    constraints.shell_requirements.dedup();
    constraints.member_containers.sort();
    constraints.classified_members.sort();
    Ok(constraints)
}

#[cfg(rust_item_dependencies_patched)]
fn collect_body_impl_requirements(
    tcx: TyCtxt<'_>,
    definitions: &CollectedDefinitions,
    definition_units: &[SourceUnitId],
    requirements: &mut BTreeSet<SourceRequirement>,
) -> Result<(), RetentionError> {
    let cold = tcx.typeck_impl_dependencies(());
    let warm = tcx.typeck_impl_dependencies(());
    let (Ok(cold), Ok(warm)) = (cold, warm) else {
        return Err(RetentionError::IncompleteMemberConstraints);
    };
    if !std::ptr::eq(cold, warm) {
        return Err(RetentionError::IncompleteMemberConstraints);
    }

    for dependency in cold {
        let trigger = compiler_definition_unit(
            definitions,
            definition_units,
            dependency.source_owner.to_def_id(),
        )?;
        let impl_unit = compiler_definition_unit(
            definitions,
            definition_units,
            dependency.impl_def_id.to_def_id(),
        )?;
        if trigger != impl_unit {
            requirements.insert(SourceRequirement {
                trigger,
                required: impl_unit,
            });
        }
        if let Some(item) = dependency.associated_item
            && let Some(item_unit) =
                optional_compiler_definition_unit(definitions, definition_units, item)?
            && trigger != item_unit
        {
            requirements.insert(SourceRequirement {
                trigger,
                required: item_unit,
            });
        }
    }
    Ok(())
}

#[cfg(not(rust_item_dependencies_patched))]
fn collect_body_impl_requirements(
    _tcx: TyCtxt<'_>,
    _definitions: &CollectedDefinitions,
    _definition_units: &[SourceUnitId],
    _requirements: &mut BTreeSet<SourceRequirement>,
) -> Result<(), RetentionError> {
    Ok(())
}

fn collect_semantic_member_requirements(
    tcx: TyCtxt<'_>,
    definitions: &CollectedDefinitions,
    definition_units: &[SourceUnitId],
    member: LocalDefId,
    member_unit: SourceUnitId,
    requirements: &mut BTreeSet<SourceRequirement>,
) -> Result<(), RetentionError> {
    let mut aliases = LocalMemberAliasCollector::default();
    match tcx.def_kind(member) {
        DefKind::AssocFn => tcx
            .fn_sig(member)
            .instantiate_identity()
            .skip_norm_wip()
            .visit_with(&mut aliases),
        DefKind::AssocConst { .. } => tcx
            .type_of(member)
            .instantiate_identity()
            .skip_norm_wip()
            .visit_with(&mut aliases),
        DefKind::AssocTy if tcx.defaultness(member).has_value() => tcx
            .type_of(member)
            .instantiate_identity()
            .skip_norm_wip()
            .visit_with(&mut aliases),
        DefKind::AssocTy => {}
        _ => return Err(RetentionError::IncompleteMemberConstraints),
    }
    for (clause, _) in tcx.explicit_clauses_of(member).instantiate_identity(tcx) {
        clause.skip_normalization().visit_with(&mut aliases);
    }
    aliases
        .targets
        .sort_by_key(|target| tcx.def_path_hash(*target));
    aliases.targets.dedup();
    for target in aliases.targets {
        if let Some(target_unit) =
            optional_compiler_definition_unit(definitions, definition_units, target)?
            && target_unit != member_unit
        {
            requirements.insert(SourceRequirement {
                trigger: member_unit,
                required: target_unit,
            });
        }
    }
    Ok(())
}

#[derive(Default)]
struct LocalMemberAliasCollector {
    targets: Vec<DefId>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for LocalMemberAliasCollector {
    fn visit_ty(&mut self, value: ty::Ty<'tcx>) {
        if let ty::Alias(_, alias) = *value.kind() {
            let target = match alias.kind {
                ty::AliasTyKind::Projection { def_id } | ty::AliasTyKind::Inherent { def_id } => {
                    Some(def_id)
                }
                ty::AliasTyKind::Opaque { .. } | ty::AliasTyKind::Free { .. } => None,
            };
            if let Some(target) = target {
                self.targets.push(target);
            }
        }
        value.super_visit_with(self);
    }
}

fn reverse_local_definitions(
    tcx: TyCtxt<'_>,
    definitions: &CollectedDefinitions,
) -> Result<Vec<LocalDefId>, RetentionError> {
    let mut reverse = vec![None; definitions.graph.definitions.len()];
    for local in tcx.iter_local_def_id() {
        let id = definitions
            .definition_id(local)
            .ok_or(RetentionError::IncompleteMemberConstraints)?;
        let slot = reverse
            .get_mut(id.0 as usize)
            .ok_or(RetentionError::IncompleteMemberConstraints)?;
        if slot.replace(local).is_some() {
            return Err(RetentionError::IncompleteMemberConstraints);
        }
    }
    reverse
        .into_iter()
        .map(|local| local.ok_or(RetentionError::IncompleteMemberConstraints))
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn collect_impl_constraints(
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
    local_definitions: &[LocalDefId],
    definition_units: &[SourceUnitId],
    impl_definition: DefinitionId,
    member_requirements: &mut BTreeSet<SourceRequirement>,
    conditional_requirements: &mut BTreeSet<ConditionalSourceRequirement>,
    disjunctions: &mut BTreeSet<SourceDisjunction>,
) -> Result<(), RetentionError> {
    let impl_local = local_definitions[impl_definition.0 as usize];
    if !matches!(tcx.def_kind(impl_local), DefKind::Impl { .. }) {
        return Err(RetentionError::IncompleteMemberConstraints);
    }
    let impl_id = impl_local.to_def_id();
    let impl_unit = definition_units[impl_definition.0 as usize];
    let Some(trait_ref) = tcx.impl_opt_trait_ref(impl_id) else {
        return Ok(());
    };
    let associated_items = tcx.associated_items(impl_id);
    match tcx.impl_polarity(impl_id) {
        ty::ImplPolarity::Negative => {
            return (associated_items.len() == 0)
                .then_some(())
                .ok_or(RetentionError::IncompleteMemberConstraints);
        }
        ty::ImplPolarity::Reservation => {
            return Err(RetentionError::IncompleteMemberConstraints);
        }
        ty::ImplPolarity::Positive => {}
    }
    if !tcx.defaultness(impl_id).is_final() {
        return Err(RetentionError::IncompleteMemberConstraints);
    }

    let trait_id = trait_ref.skip_binder().def_id;
    let trait_definition = tcx.trait_def(trait_id);
    let ancestors = trait_definition
        .ancestors(tcx, impl_id)
        .map_err(|_| RetentionError::IncompleteMemberConstraints)?;
    if ancestors.count() != 2 {
        return Err(RetentionError::IncompleteMemberConstraints);
    }
    let implementors = tcx.impl_item_implementor_ids(impl_id);

    for impl_item in associated_items.in_definition_order() {
        let impl_item_unit =
            compiler_definition_unit(definitions, definition_units, impl_item.def_id)?;
        let trait_item = impl_item
            .trait_item_def_id()
            .ok_or(RetentionError::IncompleteMemberConstraints)?;
        if let Some(trait_item_unit) =
            optional_compiler_definition_unit(definitions, definition_units, trait_item)?
            && impl_item_unit != trait_item_unit
        {
            member_requirements.insert(SourceRequirement {
                trigger: impl_item_unit,
                required: trait_item_unit,
            });
        }
    }

    let unsized_self = tcx.impl_self_is_guaranteed_unsized(impl_id);
    for trait_item in tcx.associated_items(trait_id).in_definition_order() {
        if unsized_self && tcx.generics_require_sized_self(trait_item.def_id) {
            continue;
        }
        let Some(&impl_item) = implementors.get(&trait_item.def_id) else {
            if trait_item.defaultness(tcx).has_value() {
                continue;
            }
            return Err(RetentionError::IncompleteMemberConstraints);
        };
        let impl_item_unit = compiler_definition_unit(definitions, definition_units, impl_item)?;
        if impl_item_unit == impl_unit {
            continue;
        }
        if let Some(trait_item_unit) =
            optional_compiler_definition_unit(definitions, definition_units, trait_item.def_id)?
        {
            if trait_item_unit != impl_unit && trait_item_unit != impl_item_unit {
                conditional_requirements.insert(ConditionalSourceRequirement {
                    left: impl_unit,
                    right: trait_item_unit,
                    required: impl_item_unit,
                });
            }
        } else if !trait_item.defaultness(tcx).has_value() {
            member_requirements.insert(SourceRequirement {
                trigger: impl_unit,
                required: impl_item_unit,
            });
        }
    }

    if let Some(required_names) = trait_definition.must_implement_one_of.as_deref() {
        if trait_id.is_local() {
            return Err(RetentionError::IncompleteMemberConstraints);
        }
        let trait_items = tcx.associated_items(trait_id);
        let mut choices = BTreeSet::new();
        let mut fulfilled_by_impl_unit = false;
        for required_name in required_names {
            let matching = trait_items
                .in_definition_order()
                .filter(|item| item.opt_name() == Some(required_name.name))
                .collect::<Vec<_>>();
            let [trait_item] = matching.as_slice() else {
                return Err(RetentionError::IncompleteMemberConstraints);
            };
            let Some(&impl_item) = implementors.get(&trait_item.def_id) else {
                continue;
            };
            let choice = compiler_definition_unit(definitions, definition_units, impl_item)?;
            if choice == impl_unit {
                fulfilled_by_impl_unit = true;
            } else {
                choices.insert(choice);
            }
        }
        if !fulfilled_by_impl_unit {
            if choices.is_empty() {
                return Err(RetentionError::IncompleteMemberConstraints);
            }
            disjunctions.insert(SourceDisjunction {
                trigger: impl_unit,
                choices: choices.into_iter().collect(),
            });
        }
    }

    if source
        .units
        .get(impl_unit.0 as usize)
        .is_none_or(|unit| unit.cfg_state != CfgState::Active)
    {
        return Err(RetentionError::IncompleteMemberConstraints);
    }
    Ok(())
}

fn compiler_definition_unit(
    definitions: &CollectedDefinitions,
    definition_units: &[SourceUnitId],
    definition: DefId,
) -> Result<SourceUnitId, RetentionError> {
    optional_compiler_definition_unit(definitions, definition_units, definition)?
        .ok_or(RetentionError::IncompleteMemberConstraints)
}

fn optional_compiler_definition_unit(
    definitions: &CollectedDefinitions,
    definition_units: &[SourceUnitId],
    definition: DefId,
) -> Result<Option<SourceUnitId>, RetentionError> {
    let Some(local) = definition.as_local() else {
        return Ok(None);
    };
    let id = definitions
        .definition_id(local)
        .ok_or(RetentionError::IncompleteMemberConstraints)?;
    definition_units
        .get(id.0 as usize)
        .copied()
        .map(Some)
        .ok_or(RetentionError::IncompleteMemberConstraints)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Retention {
    pub semantic_required: BTreeSet<GraphNode>,
    pub compile_required: BTreeSet<GraphNode>,
    pub retained_units: BTreeSet<SourceUnitId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RetentionError {
    InvalidSource,
    InvalidGraph,
    InvalidConstraint,
    IncompleteMemberConstraints,
}

pub(crate) fn compute_retention(
    source: &SourceInventory,
    graph: &DependencyGraph,
    constraints: &SourceConstraints,
) -> Result<Retention, RetentionError> {
    validate_source(source)?;
    validate_graph(graph)?;
    let definition_units = definition_source_units(source, graph)?;
    let validated = validate_constraints(source, graph, constraints)?;

    let semantic_roots = graph
        .roots
        .iter()
        .filter(|root| root.reason.is_semantic())
        .map(|root| root.node)
        .collect();
    let semantic_required =
        semantic_closure_for_source(graph, source, &definition_units, &validated, semantic_roots)?;

    let compile_roots = graph
        .roots
        .iter()
        .map(|root| root.node)
        .collect::<BTreeSet<_>>();
    let mut compile_required = compile_roots;
    let mut retained_units = BTreeSet::new();

    loop {
        close_deterministic_constraints(
            source,
            graph,
            &definition_units,
            &validated,
            &mut compile_required,
            &mut retained_units,
        )?;

        let mut selected = false;
        for disjunction in &validated.disjunctions {
            if retained_units.contains(&disjunction.trigger)
                && !disjunction
                    .choices
                    .iter()
                    .any(|choice| retained_units.contains(choice))
            {
                let choice = disjunction
                    .choices
                    .iter()
                    .min_by_key(|choice| {
                        let unit = &source.units[choice.0 as usize];
                        (unit.full_range.len(), unit.full_range, unit.id)
                    })
                    .expect("validated disjunctions have a choice");
                selected |= retained_units.insert(*choice);
            }
        }
        if !selected {
            break;
        }
    }

    let root = source
        .units
        .iter()
        .find(|unit| unit.parent.is_none())
        .expect("validated source has one root");
    if !retained_units.contains(&root.id) {
        return Err(RetentionError::InvalidGraph);
    }
    validate_retained_macro_definitions(source, &validated, &compile_required, &retained_units)?;

    Ok(Retention {
        semantic_required,
        compile_required,
        retained_units,
    })
}

fn close_deterministic_constraints(
    source: &SourceInventory,
    graph: &DependencyGraph,
    definition_units: &[SourceUnitId],
    constraints: &ValidatedConstraints,
    compile_required: &mut BTreeSet<GraphNode>,
    retained_units: &mut BTreeSet<SourceUnitId>,
) -> Result<(), RetentionError> {
    loop {
        let compile_before = compile_required.len();
        let source_before = retained_units.len();

        *compile_required = compiler_closure_for_source(
            graph,
            source,
            retained_units,
            std::mem::take(compile_required),
        )?;
        for node in compile_required.iter().copied().collect::<Vec<_>>() {
            if let GraphNode::Definition(definition) = node {
                retained_units.insert(definition_units[definition.0 as usize]);
            }
        }
        for requirement in constraints.compiler_source_requirements() {
            if compile_required.contains(&requirement.trigger) {
                retained_units.insert(requirement.required);
            }
        }
        close_source_requirements(constraints, retained_units);

        for (index, unit) in definition_units.iter().enumerate() {
            if retained_units.contains(unit) {
                compile_required.insert(GraphNode::Definition(DefinitionId(index as u32)));
            }
        }
        if compile_required.len() == compile_before && retained_units.len() == source_before {
            break;
        }
    }
    Ok(())
}

fn close_source_requirements(
    constraints: &ValidatedConstraints,
    retained: &mut BTreeSet<SourceUnitId>,
) {
    loop {
        let before = retained.len();
        close_atomic_groups(&constraints.atomic_groups, retained);
        for requirement in constraints
            .ancestor_requirements
            .iter()
            .chain(&constraints.shell_requirements)
            .chain(&constraints.macro_rule_requirements)
            .chain(&constraints.member_requirements)
        {
            if retained.contains(&requirement.trigger) {
                retained.insert(requirement.required);
            }
        }
        for requirement in &constraints.conditional_member_requirements {
            if retained.contains(&requirement.left) && retained.contains(&requirement.right) {
                retained.insert(requirement.required);
            }
        }
        if retained.len() == before {
            break;
        }
    }
}

fn close_atomic_groups(groups: &[Vec<SourceUnitId>], retained: &mut BTreeSet<SourceUnitId>) {
    for group in groups {
        if group.iter().any(|unit| retained.contains(unit)) {
            retained.extend(group.iter().copied());
        }
    }
}

fn semantic_closure_for_source(
    graph: &DependencyGraph,
    source: &SourceInventory,
    definition_units: &[SourceUnitId],
    constraints: &ValidatedConstraints,
    roots: BTreeSet<GraphNode>,
) -> Result<BTreeSet<GraphNode>, RetentionError> {
    let mut reachable = roots;
    let mut source_units = BTreeSet::new();
    loop {
        let node_count = reachable.len();
        let unit_count = source_units.len();
        for node in reachable.iter().copied() {
            if let GraphNode::Definition(definition) = node {
                source_units.insert(definition_units[definition.0 as usize]);
            }
        }
        close_atomic_groups(&constraints.atomic_groups, &mut source_units);
        reachable = compiler_closure_for_source(graph, source, &source_units, reachable)?;
        if reachable.len() == node_count && source_units.len() == unit_count {
            return Ok(reachable);
        }
    }
}

fn compiler_closure_for_source(
    graph: &DependencyGraph,
    source: &SourceInventory,
    retained_units: &BTreeSet<SourceUnitId>,
    reachable: BTreeSet<GraphNode>,
) -> Result<BTreeSet<GraphNode>, RetentionError> {
    let surviving_expansions = expansion_source_survival(&graph.expansions, |unit| {
        source
            .units
            .get(unit.0 as usize)
            .filter(|written| {
                written.id == unit
                    && written.kind == WrittenUnitKind::MacroInvocation
                    && written.cfg_state == CfgState::Active
            })
            .map(|written| retained_units.contains(&written.id))
    })
    .ok_or(RetentionError::InvalidGraph)?;
    let mut reachable = reachable;
    let mut work = reachable.iter().copied().collect::<Vec<_>>();
    while let Some(from) = work.pop() {
        for edge in graph
            .edges
            .iter()
            .filter(|edge| edge.from == from && is_compiler_dependency(&edge.kind))
        {
            let active = if edge.sites.is_empty() {
                true
            } else {
                match from {
                    GraphNode::Definition(_) => {
                        edge.sites.iter().try_fold(false, |active, site| {
                            if active {
                                Ok(true)
                            } else if let crate::dependency_graph::ObservationSite::Source(range) =
                                site
                            {
                                source_site_is_retained(source, retained_units, *range)
                            } else {
                                Ok(true)
                            }
                        })?
                    }
                    _ => true,
                }
            };
            let active = active
                && match (&edge.kind, edge.to) {
                    (DependencyKind::ExpansionUse, GraphNode::Expansion(expansion)) => {
                        surviving_expansions
                            .get(expansion.0 as usize)
                            .copied()
                            .ok_or(RetentionError::InvalidGraph)?
                    }
                    _ => true,
                };
            if active && reachable.insert(edge.to) {
                work.push(edge.to);
            }
        }
    }
    Ok(reachable)
}

pub(crate) fn source_site_is_retained(
    source: &SourceInventory,
    retained_units: &BTreeSet<SourceUnitId>,
    site: crate::source::ByteRange,
) -> Result<bool, RetentionError> {
    let candidates = source
        .units
        .iter()
        .filter(|unit| unit.cfg_state == CfgState::Active && unit.full_range.contains(site))
        .collect::<Vec<_>>();
    let smallest = candidates
        .iter()
        .map(|unit| unit.full_range.len())
        .min()
        .ok_or(RetentionError::InvalidGraph)?;
    let candidates = candidates
        .iter()
        .filter(|unit| unit.full_range.len() == smallest)
        .map(|unit| Ok((*unit, source_unit_depth(source, unit.id)?)))
        .collect::<Result<Vec<_>, _>>()?;
    let deepest = candidates
        .iter()
        .map(|(_, depth)| *depth)
        .max()
        .ok_or(RetentionError::InvalidGraph)?;
    let owner_states = candidates
        .into_iter()
        .filter(|(_, depth)| *depth == deepest)
        .map(|(unit, _)| unit)
        .map(|unit| retained_units.contains(&unit.id))
        .collect::<BTreeSet<_>>();
    if owner_states.len() != 1 {
        return Err(RetentionError::InvalidGraph);
    }
    Ok(*owner_states.first().expect("one owner state was checked"))
}

fn source_unit_depth(
    source: &SourceInventory,
    mut unit: SourceUnitId,
) -> Result<usize, RetentionError> {
    let mut depth = 0;
    while let Some(parent) = source
        .units
        .get(unit.0 as usize)
        .ok_or(RetentionError::InvalidGraph)?
        .parent
    {
        depth += 1;
        unit = parent;
    }
    Ok(depth)
}

fn is_compiler_dependency(kind: &DependencyKind) -> bool {
    match kind {
        DependencyKind::Definition(_)
        | DependencyKind::ExpansionDiscoveredIn
        | DependencyKind::ExpansionSemanticParent
        | DependencyKind::ExpansionSourceCallParent
        | DependencyKind::MacroDefinition
        | DependencyKind::GeneratedBy
        | DependencyKind::SelectionProof { .. }
        | DependencyKind::ProofRelation { .. }
        | DependencyKind::MaterializesDefinition
        | DependencyKind::Mono { .. }
        | DependencyKind::ExpansionUse => true,
    }
}

#[derive(Clone)]
struct ValidatedConstraints {
    atomic_groups: Vec<Vec<SourceUnitId>>,
    macro_rule_selection_requirements: Vec<MacroRuleSelectionRequirement>,
    ancestor_requirements: Vec<SourceRequirement>,
    shell_requirements: Vec<SourceRequirement>,
    macro_rule_requirements: Vec<SourceRequirement>,
    member_requirements: Vec<SourceRequirement>,
    conditional_member_requirements: Vec<ConditionalSourceRequirement>,
    disjunctions: Vec<SourceDisjunction>,
}

impl ValidatedConstraints {
    fn compiler_source_requirements(&self) -> impl Iterator<Item = CompilerSourceRequirement> + '_ {
        self.macro_rule_selection_requirements
            .iter()
            .map(|requirement| CompilerSourceRequirement {
                trigger: GraphNode::Expansion(requirement.expansion),
                required: requirement.rule,
            })
    }
}

fn validate_constraints(
    source: &SourceInventory,
    graph: &DependencyGraph,
    constraints: &SourceConstraints,
) -> Result<ValidatedConstraints, RetentionError> {
    let unit_count = source.units.len();
    let valid_unit = |id: SourceUnitId| (id.0 as usize) < unit_count;

    let expected_groups = source
        .units
        .iter()
        .fold(BTreeMap::new(), |mut groups, unit| {
            groups
                .entry(unit.atomic_group)
                .or_insert_with(BTreeSet::new)
                .insert(unit.id);
            groups
        })
        .into_values()
        .collect::<BTreeSet<_>>();
    let mut seen_units = BTreeSet::new();
    let mut actual_groups = BTreeSet::new();
    for group in &constraints.atomic_groups {
        let members = group.iter().copied().collect::<BTreeSet<_>>();
        if group.is_empty()
            || members.len() != group.len()
            || members.iter().any(|member| !valid_unit(*member))
            || members.iter().any(|member| !seen_units.insert(*member))
            || !actual_groups.insert(members)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    if actual_groups != expected_groups || seen_units.len() != unit_count {
        return Err(RetentionError::InvalidConstraint);
    }

    let expected_ancestors = source
        .units
        .iter()
        .filter_map(|unit| {
            unit.parent.map(|required| SourceRequirement {
                trigger: unit.id,
                required,
            })
        })
        .collect::<BTreeSet<_>>();
    let ancestors = validate_requirements(
        source,
        &constraints.ancestor_requirements,
        RequirementClass::Structural,
    )?;
    if ancestors.iter().copied().collect::<BTreeSet<_>>() != expected_ancestors {
        return Err(RetentionError::InvalidConstraint);
    }
    let shells = validate_requirements(
        source,
        &constraints.shell_requirements,
        RequirementClass::Semantic,
    )?;
    let macro_rules = validate_requirements(
        source,
        &constraints.macro_rule_requirements,
        RequirementClass::Semantic,
    )?;
    let expected_macro_rules = source_macro_rule_requirements(source).collect::<BTreeSet<_>>();
    if macro_rules.iter().copied().collect::<BTreeSet<_>>() != expected_macro_rules {
        return Err(RetentionError::InvalidConstraint);
    }
    let macro_rule_selection_requirements = validate_macro_rule_selection_requirements(
        source,
        graph,
        &constraints.macro_rule_selection_requirements,
    )?;
    let members = validate_requirements(
        source,
        &constraints.member_requirements,
        RequirementClass::Semantic,
    )?;
    let conditional_members =
        validate_conditional_requirements(source, &constraints.conditional_member_requirements)?;

    let member_containers = unique_active_units(source, &constraints.member_containers)?;
    let expected_containers = graph
        .definitions
        .definitions
        .iter()
        .filter_map(|definition| {
            if !matches!(
                definition.kind,
                DefinitionKind::Trait | DefinitionKind::Impl
            ) {
                return None;
            }
            match &definition.origin {
                DefinitionOrigin::Written { unit, .. } => Some(*unit),
                DefinitionOrigin::Expanded { .. }
                | DefinitionOrigin::CompilerGenerated { .. }
                | DefinitionOrigin::Injected { .. } => None,
            }
        })
        .collect::<BTreeSet<_>>();
    if member_containers != expected_containers {
        return Err(RetentionError::IncompleteMemberConstraints);
    }

    let classified_members = unique_active_units(source, &constraints.classified_members)?;
    let expected_members = source
        .units
        .iter()
        .filter(|unit| {
            unit.cfg_state == CfgState::Active
                && matches!(
                    unit.kind,
                    WrittenUnitKind::TraitMember | WrittenUnitKind::ImplMember
                )
        })
        .map(|unit| unit.id)
        .collect::<BTreeSet<_>>();
    if classified_members != expected_members
        || expected_members.iter().any(|member| {
            source.units[member.0 as usize]
                .parent
                .is_none_or(|parent| !member_containers.contains(&parent))
        })
    {
        return Err(RetentionError::IncompleteMemberConstraints);
    }

    let mut disjunction_keys = BTreeSet::new();
    let mut disjunctions = Vec::new();
    for disjunction in &constraints.disjunctions {
        if !valid_unit(disjunction.trigger)
            || source.units[disjunction.trigger.0 as usize].cfg_state != CfgState::Active
            || disjunction.choices.is_empty()
        {
            return Err(RetentionError::InvalidConstraint);
        }
        let choices = disjunction.choices.iter().copied().collect::<BTreeSet<_>>();
        if choices.len() != disjunction.choices.len()
            || choices.contains(&disjunction.trigger)
            || choices.iter().any(|choice| {
                !valid_unit(*choice)
                    || source.units[choice.0 as usize].cfg_state != CfgState::Active
                    || source.units[choice.0 as usize].parent != Some(disjunction.trigger)
                    || !matches!(
                        source.units[choice.0 as usize].kind,
                        WrittenUnitKind::ImplMember | WrittenUnitKind::MacroInvocation
                    )
            })
            || !disjunction_keys.insert((disjunction.trigger, choices.clone()))
        {
            return Err(RetentionError::InvalidConstraint);
        }
        disjunctions.push(SourceDisjunction {
            trigger: disjunction.trigger,
            choices: choices.into_iter().collect(),
        });
    }
    disjunctions.sort();

    Ok(ValidatedConstraints {
        atomic_groups: actual_groups
            .into_iter()
            .map(|group| group.into_iter().collect())
            .collect(),
        macro_rule_selection_requirements,
        ancestor_requirements: ancestors,
        shell_requirements: shells,
        macro_rule_requirements: macro_rules,
        member_requirements: members,
        conditional_member_requirements: conditional_members,
        disjunctions,
    })
}

pub(crate) fn collect_macro_rule_expansion_constraints(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    expansions: &[ExpansionNode],
    constraints: &mut SourceConstraints,
) -> Result<(), RetentionError> {
    if !constraints.macro_rule_selection_requirements.is_empty() {
        return Err(RetentionError::InvalidConstraint);
    }
    let mut requirements = BTreeSet::new();
    for expansion in expansions {
        let Some(selected_range) = expansion
            .key
            .0
            .last()
            .and_then(|part| part.selected_macro_rule)
        else {
            continue;
        };
        let Some(rule) = selected_macro_rule_unit(source, selected_range)? else {
            continue;
        };
        let requirement = MacroRuleSelectionRequirement {
            expansion: expansion.id,
            rule: rule.id,
        };
        if !macro_rule_requirement_matches(source, definitions, expansion, requirement.rule)
            || !requirements.insert(requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }

    if macro_rule_selection_counts(requirements.iter().map(|requirement| requirement.rule))
        != observed_macro_rule_selection_counts(source)
    {
        return Err(RetentionError::InvalidConstraint);
    }
    constraints
        .macro_rule_selection_requirements
        .extend(requirements);
    Ok(())
}

fn selected_macro_rule_unit(
    source: &SourceInventory,
    selected_range: crate::source::ByteRange,
) -> Result<Option<&WrittenUnit>, RetentionError> {
    let matching_rules = source
        .units
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroRule
                && unit.cfg_state == CfgState::Active
                && unit.full_range == selected_range
        })
        .collect::<Vec<_>>();
    if let [rule] = matching_rules.as_slice() {
        return Ok(Some(rule));
    }
    if !matching_rules.is_empty() {
        return Err(RetentionError::InvalidConstraint);
    }

    let enclosing_whole_definitions = source
        .macro_rules
        .iter()
        .filter_map(|facts| match facts {
            MacroRuleSourceFacts::Whole { definition } => source.units.get(definition.0 as usize),
            MacroRuleSourceFacts::Refined { .. } => None,
        })
        .filter(|definition| definition.full_range.contains(selected_range))
        .count();
    match enclosing_whole_definitions {
        1 => Ok(None),
        _ => Err(RetentionError::InvalidConstraint),
    }
}

fn validate_macro_rule_selection_requirements(
    source: &SourceInventory,
    graph: &DependencyGraph,
    requirements: &[MacroRuleSelectionRequirement],
) -> Result<Vec<MacroRuleSelectionRequirement>, RetentionError> {
    let requirement_count = requirements.len();
    let requirements = requirements.iter().copied().collect::<BTreeSet<_>>();
    let expansion_count = requirements
        .iter()
        .map(|requirement| requirement.expansion)
        .collect::<BTreeSet<_>>()
        .len();
    if requirements.len() != requirement_count
        || expansion_count != requirements.len()
        || requirements.iter().any(|requirement| {
            graph
                .expansions
                .get(requirement.expansion.0 as usize)
                .filter(|expansion| expansion.id == requirement.expansion)
                .is_none_or(|expansion| {
                    !macro_rule_requirement_matches(
                        source,
                        &graph.definitions,
                        expansion,
                        requirement.rule,
                    )
                })
        })
    {
        return Err(RetentionError::InvalidConstraint);
    }
    if macro_rule_selection_counts(requirements.iter().map(|requirement| requirement.rule))
        != observed_macro_rule_selection_counts(source)
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(requirements.into_iter().collect())
}

fn macro_rule_selection_definition(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    expansion: &ExpansionNode,
) -> Option<SourceUnitId> {
    if expansion.implementation != Some(MacroImplementationKind::Declarative) {
        return None;
    }
    let DefinitionTarget::Local(definition) = expansion.macro_definition? else {
        return None;
    };
    let definition = definitions.definitions.get(definition.0 as usize)?;
    let DefinitionOrigin::Written { unit, .. } = &definition.origin else {
        return None;
    };
    (definition.kind == DefinitionKind::Macro
        && source.macro_rules.iter().any(|facts| {
            matches!(facts, MacroRuleSourceFacts::Refined { definition, .. } if definition == unit)
        }))
    .then_some(*unit)
}

fn macro_rule_requirement_matches(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    expansion: &ExpansionNode,
    required: SourceUnitId,
) -> bool {
    let Some(rule) = source.units.get(required.0 as usize).filter(|rule| {
        rule.id == required
            && rule.kind == WrittenUnitKind::MacroRule
            && rule.cfg_state == CfgState::Active
    }) else {
        return false;
    };
    macro_rule_selection_definition(source, definitions, expansion)
        .is_some_and(|definition_unit| rule.parent == Some(definition_unit))
}

fn macro_rule_selection_counts(
    selections: impl Iterator<Item = SourceUnitId>,
) -> BTreeMap<SourceUnitId, usize> {
    let mut counts = BTreeMap::new();
    for selection in selections {
        *counts.entry(selection).or_insert(0) += 1;
    }
    counts
}

fn observed_macro_rule_selection_counts(source: &SourceInventory) -> BTreeMap<SourceUnitId, usize> {
    macro_rule_selection_counts(
        source
            .macro_rules
            .iter()
            .flat_map(|facts| match facts {
                MacroRuleSourceFacts::Whole { .. } => &[][..],
                MacroRuleSourceFacts::Refined {
                    observed_selections,
                    ..
                } => observed_selections.as_slice(),
            })
            .copied(),
    )
}

fn validate_retained_macro_definitions(
    source: &SourceInventory,
    constraints: &ValidatedConstraints,
    compile_required: &BTreeSet<GraphNode>,
    retained_units: &BTreeSet<SourceUnitId>,
) -> Result<(), RetentionError> {
    let definitions_with_reachable_selection = constraints
        .macro_rule_selection_requirements
        .iter()
        .filter(|requirement| {
            compile_required.contains(&GraphNode::Expansion(requirement.expansion))
        })
        .filter_map(|requirement| source.units[requirement.rule.0 as usize].parent)
        .collect::<BTreeSet<_>>();
    if source.macro_rules.iter().any(|facts| match facts {
        MacroRuleSourceFacts::Whole { .. } => false,
        MacroRuleSourceFacts::Refined {
            definition,
            observed_selections,
            ..
        } => {
            !observed_selections.is_empty()
                && retained_units.contains(definition)
                && !definitions_with_reachable_selection.contains(definition)
        }
    }) {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(())
}

fn validate_conditional_requirements(
    source: &SourceInventory,
    requirements: &[ConditionalSourceRequirement],
) -> Result<Vec<ConditionalSourceRequirement>, RetentionError> {
    let mut unique = BTreeSet::new();
    for requirement in requirements {
        let units = [requirement.left, requirement.right, requirement.required]
            .map(|id| source.units.get(id.0 as usize));
        if units
            .iter()
            .any(|unit| unit.is_none_or(|unit| unit.cfg_state != CfgState::Active))
            || requirement.left == requirement.right
            || requirement.required == requirement.left
            || requirement.required == requirement.right
            || !unique.insert(*requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    Ok(unique.into_iter().collect())
}

#[derive(Clone, Copy)]
enum RequirementClass {
    Structural,
    Semantic,
}

fn validate_requirements(
    source: &SourceInventory,
    requirements: &[SourceRequirement],
    class: RequirementClass,
) -> Result<Vec<SourceRequirement>, RetentionError> {
    let mut unique = BTreeSet::new();
    for requirement in requirements {
        let Some(trigger) = source.units.get(requirement.trigger.0 as usize) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let Some(required) = source.units.get(requirement.required.0 as usize) else {
            return Err(RetentionError::InvalidConstraint);
        };
        if requirement.trigger == requirement.required
            || matches!(class, RequirementClass::Semantic)
                && (trigger.cfg_state != CfgState::Active || required.cfg_state != CfgState::Active)
            || !unique.insert(*requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    Ok(unique.into_iter().collect())
}

fn unique_active_units(
    source: &SourceInventory,
    units: &[SourceUnitId],
) -> Result<BTreeSet<SourceUnitId>, RetentionError> {
    let unique = units.iter().copied().collect::<BTreeSet<_>>();
    if unique.len() != units.len()
        || unique.iter().any(|unit| {
            source
                .units
                .get(unit.0 as usize)
                .is_none_or(|unit| unit.cfg_state != CfgState::Active)
        })
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(unique)
}

fn definition_source_units(
    source: &SourceInventory,
    graph: &DependencyGraph,
) -> Result<Vec<SourceUnitId>, RetentionError> {
    definition_source_units_from_graph(source, &graph.definitions)
}

fn definition_source_units_from_graph(
    source: &SourceInventory,
    graph: &DefinitionGraph,
) -> Result<Vec<SourceUnitId>, RetentionError> {
    let mut states = vec![0_u8; graph.definitions.len()];
    let mut units = vec![None; graph.definitions.len()];
    for index in 0..graph.definitions.len() {
        resolve_definition_unit(source, graph, index, &mut states, &mut units)?;
    }
    units
        .into_iter()
        .map(|unit| unit.ok_or(RetentionError::InvalidGraph))
        .collect()
}

fn resolve_definition_unit(
    source: &SourceInventory,
    graph: &DefinitionGraph,
    index: usize,
    states: &mut [u8],
    units: &mut [Option<SourceUnitId>],
) -> Result<SourceUnitId, RetentionError> {
    match states[index] {
        1 => return Err(RetentionError::InvalidGraph),
        2 => return units[index].ok_or(RetentionError::InvalidGraph),
        _ => {}
    }
    states[index] = 1;
    let definition = &graph.definitions[index];
    let unit = match &definition.origin {
        DefinitionOrigin::Written {
            unit,
            unit_range,
            anchor,
            unit_kind,
            unit_ordinal,
        } => {
            let written = source
                .units
                .get(unit.0 as usize)
                .ok_or(RetentionError::InvalidGraph)?;
            if written.id != *unit
                || written.full_range != *unit_range
                || written.kind != *unit_kind
                || written.same_role_ordinal != *unit_ordinal
                || written.cfg_state != CfgState::Active
                || !unit_range.contains(*anchor)
            {
                return Err(RetentionError::InvalidGraph);
            }
            *unit
        }
        DefinitionOrigin::Expanded {
            invocation,
            invocation_range,
            ..
        } => {
            let written = source
                .units
                .get(invocation.0 as usize)
                .ok_or(RetentionError::InvalidGraph)?;
            if written.id != *invocation
                || written.full_range != *invocation_range
                || written.kind != WrittenUnitKind::MacroInvocation
                || written.cfg_state != CfgState::Active
            {
                return Err(RetentionError::InvalidGraph);
            }
            *invocation
        }
        DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => {
            let parent = definition.parent.ok_or(RetentionError::InvalidGraph)?;
            resolve_definition_unit(source, graph, parent.0 as usize, states, units)?
        }
    };
    states[index] = 2;
    units[index] = Some(unit);
    Ok(unit)
}

fn validate_source(source: &SourceInventory) -> Result<(), RetentionError> {
    let source_len =
        u32::try_from(source.original.len()).map_err(|_| RetentionError::InvalidSource)?;
    let roots = source
        .units
        .iter()
        .filter(|unit| unit.parent.is_none())
        .collect::<Vec<_>>();
    if roots.len() != 1
        || roots[0].kind != WrittenUnitKind::CrateRoot
        || roots[0].full_range.start != 0
        || roots[0].full_range.end != source_len
    {
        return Err(RetentionError::InvalidSource);
    }
    for (index, unit) in source.units.iter().enumerate() {
        if unit.id.0 as usize != index
            || unit.full_range.start > unit.full_range.end
            || unit.full_range.end > source_len
            || !source
                .original
                .is_char_boundary(unit.full_range.start as usize)
            || !source
                .original
                .is_char_boundary(unit.full_range.end as usize)
        {
            return Err(RetentionError::InvalidSource);
        }
        if let Some(parent) = unit.parent {
            let parent = source
                .units
                .get(parent.0 as usize)
                .ok_or(RetentionError::InvalidSource)?;
            if parent.id == unit.id
                || !parent.full_range.contains(unit.full_range)
                || parent.cfg_state == CfgState::Inactive && unit.cfg_state == CfgState::Active
            {
                return Err(RetentionError::InvalidSource);
            }
        }
        let mut cursor = unit.parent;
        let mut steps = 0;
        while let Some(parent) = cursor {
            cursor = source
                .units
                .get(parent.0 as usize)
                .ok_or(RetentionError::InvalidSource)?
                .parent;
            steps += 1;
            if steps > source.units.len() {
                return Err(RetentionError::InvalidSource);
            }
        }
    }
    validate_macro_rule_facts(&source.units, &source.macro_rules)
        .map_err(|_| RetentionError::InvalidSource)?;
    validate_ownerless_attribute_invocations(
        &source.units,
        &source.ownerless_attribute_invocations,
    )
    .map_err(|_| RetentionError::InvalidSource)?;
    Ok(())
}

fn validate_graph(graph: &DependencyGraph) -> Result<(), RetentionError> {
    if !valid_roots(&graph.roots, &graph.definitions, &graph.mono_nodes)
        || graph
            .definitions
            .definitions
            .iter()
            .enumerate()
            .any(|(index, definition)| {
                definition.id.0 as usize != index
                    || definition.parent.is_some_and(|parent| {
                        parent.0 as usize >= graph.definitions.definitions.len()
                    })
            })
        || graph
            .definitions
            .external_definitions
            .iter()
            .enumerate()
            .any(|(index, definition)| definition.id.0 as usize != index)
        || graph
            .expansions
            .iter()
            .enumerate()
            .any(|(index, node)| node.id.0 as usize != index)
        || graph
            .proofs
            .iter()
            .enumerate()
            .any(|(index, node)| node.id.0 as usize != index)
        || graph
            .mono_nodes
            .iter()
            .enumerate()
            .any(|(index, node)| node.id.0 as usize != index)
        || graph
            .edges
            .iter()
            .any(|edge| !valid_graph_node(graph, edge.from) || !valid_graph_node(graph, edge.to))
    {
        return Err(RetentionError::InvalidGraph);
    }
    Ok(())
}

fn valid_graph_node(graph: &DependencyGraph, node: GraphNode) -> bool {
    match node {
        GraphNode::Definition(id) => (id.0 as usize) < graph.definitions.definitions.len(),
        GraphNode::ExternalDefinition(id) => {
            (id.0 as usize) < graph.definitions.external_definitions.len()
        }
        GraphNode::Expansion(id) => (id.0 as usize) < graph.expansions.len(),
        GraphNode::Proof(id) => (id.0 as usize) < graph.proofs.len(),
        GraphNode::Mono(id) => (id.0 as usize) < graph.mono_nodes.len(),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::compiler_terms::CanonicalCompilerTerm;
    use crate::dependency_graph::{
        DefinitionReferenceKey, DependencyEdge, EvidenceOrigin, ExpansionFragmentKind, ExpansionId,
        ExpansionKey, ExpansionKeyPart, ExpansionKind, ExpansionNode, MacroStyle, MonoInstanceKey,
        MonoInstanceRole, MonoKey, MonoNode, ObservationSite, RootReason, RootRecord,
    };
    use crate::graph::{
        Definition, DefinitionGraph, DefinitionKey, DefinitionKeyPart,
        DependencyKind as DefinitionDependencyKind, GeneratedRole, InjectedRole,
    };
    use crate::source::{
        AtomicGroupId, ByteRange, MacroRuleSourceFacts, OriginalOffsetMap, SourceInventory,
        WrittenUnit,
    };

    use super::*;
    use crate::dependency_graph::MonoId;

    fn unit(
        id: u32,
        kind: WrittenUnitKind,
        range: (u32, u32),
        parent: Option<u32>,
        group: u32,
    ) -> WrittenUnit {
        WrittenUnit {
            id: SourceUnitId(id),
            kind,
            full_range: ByteRange {
                start: range.0,
                end: range.1,
            },
            parent: parent.map(SourceUnitId),
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(group),
            same_role_ordinal: id.saturating_sub(1),
        }
    }

    fn inventory(source: &str, units: Vec<WrittenUnit>) -> SourceInventory {
        let (normalized, offsets) = OriginalOffsetMap::from_source(source).unwrap();
        SourceInventory {
            original: Arc::from(source),
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces: Vec::new(),
            macro_rules: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn written_definition(
        id: u32,
        kind: DefinitionKind,
        unit: &WrittenUnit,
        parent: Option<u32>,
        name: &str,
    ) -> Definition {
        let origin = DefinitionOrigin::Written {
            unit: unit.id,
            unit_range: unit.full_range,
            anchor: ByteRange {
                start: unit.full_range.start,
                end: unit.full_range.start,
            },
            unit_kind: unit.kind,
            unit_ordinal: unit.same_role_ordinal,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![DefinitionKeyPart {
                kind,
                origin: origin.key(),
                name: Some(name.to_owned()),
                same_role_ordinal: 0,
            }]),
            kind,
            parent: parent.map(DefinitionId),
            origin,
        }
    }

    fn expanded_definition(
        id: u32,
        kind: DefinitionKind,
        invocation: &WrittenUnit,
        parent: Option<u32>,
        name: &str,
    ) -> Definition {
        let origin = DefinitionOrigin::Expanded {
            invocation: invocation.id,
            invocation_range: invocation.full_range,
            generated_role: None,
            ordinal: id,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![DefinitionKeyPart {
                kind,
                origin: origin.key(),
                name: Some(name.to_owned()),
                same_role_ordinal: id,
            }]),
            kind,
            parent: parent.map(DefinitionId),
            origin,
        }
    }

    fn compiler_generated_definition(id: u32, parent: u32) -> Definition {
        let origin = DefinitionOrigin::CompilerGenerated {
            role: GeneratedRole::OpaqueType,
            ordinal: id,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![DefinitionKeyPart {
                kind: DefinitionKind::OpaqueType,
                origin: origin.key(),
                name: None,
                same_role_ordinal: id,
            }]),
            kind: DefinitionKind::OpaqueType,
            parent: Some(DefinitionId(parent)),
            origin,
        }
    }

    fn injected_definition(id: u32, parent: u32) -> Definition {
        let origin = DefinitionOrigin::Injected {
            role: InjectedRole::PreludeImport,
            ordinal: 0,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![DefinitionKeyPart {
                kind: DefinitionKind::Use,
                origin: origin.key(),
                name: None,
                same_role_ordinal: 0,
            }]),
            kind: DefinitionKind::Use,
            parent: Some(DefinitionId(parent)),
            origin,
        }
    }

    fn edge(from: GraphNode, to: GraphNode) -> DependencyEdge {
        let materialization = matches!(from, GraphNode::Mono(_))
            && matches!(
                to,
                GraphNode::Definition(_) | GraphNode::ExternalDefinition(_)
            );
        DependencyEdge {
            from,
            to,
            kind: if materialization {
                DependencyKind::MaterializesDefinition
            } else {
                DependencyKind::Definition(DefinitionDependencyKind::ValuePath)
            },
            sites: (!materialization)
                .then_some(ObservationSite::CompilerGenerated)
                .into_iter()
                .collect(),
            evidence: EvidenceOrigin::Compiler,
        }
    }

    fn graph(definitions: Vec<Definition>, mut edges: Vec<DependencyEdge>) -> DependencyGraph {
        let main = definitions
            .iter()
            .find(|definition| {
                definition
                    .key
                    .0
                    .last()
                    .and_then(|part| part.name.as_deref())
                    == Some("main")
            })
            .unwrap();
        let main_id = main.id;
        let main_key = main.key.clone();
        let term = CanonicalCompilerTerm {
            schema_version: 1,
            bytes: vec![1],
        };
        let main_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(main_key),
            arguments: term.clone(),
            kind: term.clone(),
        };
        let start_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(definitions[0].key.clone()),
            arguments: term.clone(),
            kind: term,
        };
        let mono_nodes = vec![
            MonoNode {
                id: MonoId(0),
                key: MonoKey::Instance {
                    instance: main_instance,
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(crate::graph::DefinitionTarget::Local(main_id)),
                allocation_observation: None,
            },
            MonoNode {
                id: MonoId(1),
                key: MonoKey::Instance {
                    instance: start_instance,
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: None,
                allocation_observation: None,
            },
        ];
        edges.push(edge(
            GraphNode::Mono(MonoId(0)),
            GraphNode::Definition(main_id),
        ));
        DependencyGraph {
            definitions: DefinitionGraph {
                definitions,
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions: Vec::new(),
            proofs: Vec::new(),
            mono_nodes,
            edges,
            roots: vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
            ],
        }
    }

    fn complete_constraints(
        source: &SourceInventory,
        graph: &DependencyGraph,
    ) -> SourceConstraints {
        let mut constraints = SourceConstraints::from_source(source);
        constraints.member_containers = graph
            .definitions
            .definitions
            .iter()
            .filter_map(|definition| {
                matches!(
                    definition.kind,
                    DefinitionKind::Trait | DefinitionKind::Impl
                )
                .then(|| match &definition.origin {
                    DefinitionOrigin::Written { unit, .. } => Some(*unit),
                    _ => None,
                })
                .flatten()
            })
            .collect();
        constraints.classified_members = source
            .units
            .iter()
            .filter(|unit| {
                matches!(
                    unit.kind,
                    WrittenUnitKind::TraitMember | WrittenUnitKind::ImplMember
                ) && unit.cfg_state == CfgState::Active
            })
            .map(|unit| unit.id)
            .collect();
        collect_macro_rule_expansion_constraints(
            source,
            &graph.definitions,
            &graph.expansions,
            &mut constraints,
        )
        .unwrap();
        constraints
    }

    #[test]
    fn retained_macro_products_reenter_the_compiler_closure() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
            unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "first"),
            expanded_definition(3, DefinitionKind::Function, &units[2], Some(0), "sibling"),
            written_definition(4, DefinitionKind::Struct, &units[3], Some(0), "dependency"),
            compiler_generated_definition(5, 4),
        ];
        let graph = graph(
            definitions,
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(2)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(3)),
                    GraphNode::Definition(DefinitionId(5)),
                ),
            ],
        );
        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert_eq!(
            retention.retained_units,
            BTreeSet::from([
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ])
        );
        assert_eq!(
            retention.compile_required,
            BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
                GraphNode::Definition(DefinitionId(3)),
                GraphNode::Definition(DefinitionId(4)),
                GraphNode::Definition(DefinitionId(5)),
                GraphNode::Mono(MonoId(0)),
                GraphNode::Mono(MonoId(1)),
            ])
        );
    }

    #[test]
    fn source_site_uses_the_deepest_equal_range_owner() {
        let source = "fn main(){}";
        let inventory = inventory(
            source,
            vec![
                unit(0, WrittenUnitKind::CrateRoot, (0, 11), None, 0),
                unit(1, WrittenUnitKind::Item, (0, 11), Some(0), 1),
            ],
        );
        let site = crate::source::ByteRange { start: 3, end: 7 };

        assert_eq!(
            source_site_is_retained(&inventory, &BTreeSet::from([SourceUnitId(1)]), site),
            Ok(true)
        );
        assert_eq!(
            source_site_is_retained(&inventory, &BTreeSet::from([SourceUnitId(0)]), site),
            Ok(false)
        );
    }

    #[test]
    fn compiler_roots_do_not_pollute_semantic_requirements() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
            unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(
                2,
                DefinitionKind::Static,
                &units[2],
                Some(0),
                "compiler_root",
            ),
            written_definition(3, DefinitionKind::Function, &units[3], Some(0), "entry"),
        ];
        let mut graph = graph(
            definitions,
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        let compiler_root = MonoId(graph.mono_nodes.len() as u32);
        graph.mono_nodes.push(MonoNode {
            id: compiler_root,
            key: MonoKey::Static {
                definition: graph.definitions.definitions[2].key.clone(),
            },
            materialized_definition: Some(crate::graph::DefinitionTarget::Local(DefinitionId(2))),
            allocation_observation: None,
        });
        graph.roots.push(RootRecord {
            node: GraphNode::Mono(compiler_root),
            reason: RootReason::UsedAttribute,
        });
        graph.roots.push(RootRecord {
            node: GraphNode::Definition(DefinitionId(3)),
            reason: RootReason::ExplicitEntry,
        });
        graph.edges.push(edge(
            GraphNode::Mono(compiler_root),
            GraphNode::Definition(DefinitionId(2)),
        ));
        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert_eq!(
            retention.semantic_required,
            BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(3)),
                GraphNode::Mono(MonoId(0)),
            ])
        );
        assert!(
            retention
                .compile_required
                .contains(&GraphNode::Definition(DefinitionId(2)))
        );
    }

    #[test]
    fn a_reexport_definition_root_retains_a_generic_function_without_a_mono_node() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 40), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
            unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "generic"),
            written_definition(2, DefinitionKind::Use, &units[2], Some(0), "export"),
            written_definition(3, DefinitionKind::Function, &units[3], Some(0), "unused"),
        ];
        let graph = DependencyGraph::new(
            DefinitionGraph {
                definitions,
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(2)),
                    GraphNode::Definition(DefinitionId(1)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(2)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
            ],
            vec![RootRecord {
                node: GraphNode::Definition(DefinitionId(2)),
                reason: RootReason::ExplicitEntry,
            }],
        )
        .unwrap();
        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert!(graph.mono_nodes.is_empty());
        assert_eq!(
            retention.semantic_required,
            BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ])
        );
        assert_eq!(
            retention.retained_units,
            BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
        );
    }

    #[test]
    fn native_link_definition_roots_are_compile_only() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(
                2,
                DefinitionKind::ForeignModule,
                &units[2],
                Some(0),
                "linked",
            ),
        ];
        let mut graph = graph(
            definitions,
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        graph.roots.push(RootRecord {
            node: GraphNode::Definition(DefinitionId(2)),
            reason: RootReason::NativeLink,
        });

        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert_eq!(
            retention.semantic_required,
            BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Mono(MonoId(0)),
            ])
        );
        assert!(
            retention
                .compile_required
                .contains(&GraphNode::Definition(DefinitionId(2)))
        );
        assert!(retention.retained_units.contains(&SourceUnitId(2)));
    }

    #[test]
    fn disjunction_uses_shortest_member_then_source_order() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 5), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (6, 60), Some(0), 2),
            unit(3, WrittenUnitKind::ImplMember, (10, 20), Some(2), 3),
            unit(4, WrittenUnitKind::ImplMember, (21, 26), Some(2), 4),
            unit(5, WrittenUnitKind::ImplMember, (30, 35), Some(2), 5),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Impl, &units[2], Some(0), "impl"),
            written_definition(
                3,
                DefinitionKind::AssociatedFunction,
                &units[3],
                Some(2),
                "long",
            ),
            written_definition(
                4,
                DefinitionKind::AssociatedFunction,
                &units[4],
                Some(2),
                "first_short",
            ),
            written_definition(
                5,
                DefinitionKind::AssociatedFunction,
                &units[5],
                Some(2),
                "second_short",
            ),
        ];
        let graph = graph(
            definitions,
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(2)),
                ),
            ],
        );
        let mut constraints = complete_constraints(&inventory, &graph);
        constraints.disjunctions.push(SourceDisjunction {
            trigger: SourceUnitId(2),
            choices: vec![SourceUnitId(5), SourceUnitId(3), SourceUnitId(4)],
        });
        let retention = compute_retention(&inventory, &graph, &constraints).unwrap();

        assert_eq!(
            retention.retained_units,
            BTreeSet::from([
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(4),
            ])
        );
    }

    #[test]
    fn conditional_member_requirement_needs_both_inputs() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 5), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (6, 30), Some(0), 2),
            unit(3, WrittenUnitKind::TraitMember, (10, 15), Some(2), 3),
            unit(4, WrittenUnitKind::Item, (31, 60), Some(0), 4),
            unit(5, WrittenUnitKind::ImplMember, (40, 50), Some(4), 5),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Trait, &units[2], Some(0), "trait"),
            written_definition(
                3,
                DefinitionKind::AssociatedType,
                &units[3],
                Some(2),
                "required",
            ),
            written_definition(4, DefinitionKind::Impl, &units[4], Some(0), "impl"),
            written_definition(
                5,
                DefinitionKind::AssociatedType,
                &units[5],
                Some(4),
                "implementation",
            ),
        ];
        let conditional = ConditionalSourceRequirement {
            left: SourceUnitId(4),
            right: SourceUnitId(3),
            required: SourceUnitId(5),
        };

        for (edges, expected_member) in [
            (
                vec![edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(4)),
                )],
                false,
            ),
            (
                vec![edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(3)),
                )],
                false,
            ),
            (
                vec![
                    edge(
                        GraphNode::Definition(DefinitionId(1)),
                        GraphNode::Definition(DefinitionId(3)),
                    ),
                    edge(
                        GraphNode::Definition(DefinitionId(1)),
                        GraphNode::Definition(DefinitionId(4)),
                    ),
                ],
                true,
            ),
        ] {
            let graph = graph(definitions.clone(), edges);
            let mut constraints = complete_constraints(&inventory, &graph);
            constraints
                .conditional_member_requirements
                .push(conditional);
            let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
            assert_eq!(
                retention.retained_units.contains(&SourceUnitId(5)),
                expected_member
            );
        }
    }

    #[test]
    fn atomicity_and_an_empty_impl_shell_are_retained() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, (2, 4), Some(1), 1),
            unit(3, WrittenUnitKind::Item, (11, 20), Some(0), 2),
        ];
        let inventory = inventory(source, units.clone());
        let definitions = vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Impl, &units[3], Some(0), "empty_impl"),
        ];
        let graph = graph(
            definitions,
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(2)),
                ),
            ],
        );
        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert_eq!(
            retention.retained_units,
            BTreeSet::from([
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ])
        );
    }

    #[test]
    fn invalid_constraints_and_missing_member_coverage_fail_closed() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (11, 30), Some(0), 2),
            unit(3, WrittenUnitKind::TraitMember, (15, 20), Some(2), 3),
        ];
        let inventory = inventory(source, units.clone());
        let graph = graph(
            vec![
                written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
                written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
                written_definition(2, DefinitionKind::Trait, &units[2], Some(0), "trait"),
                written_definition(
                    3,
                    DefinitionKind::AssociatedFunction,
                    &units[3],
                    Some(2),
                    "member",
                ),
            ],
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(2)),
                ),
            ],
        );

        let missing = SourceConstraints::from_source(&inventory);
        assert_eq!(
            compute_retention(&inventory, &graph, &missing),
            Err(RetentionError::IncompleteMemberConstraints)
        );

        let mut invalid = complete_constraints(&inventory, &graph);
        invalid.member_requirements.push(SourceRequirement {
            trigger: SourceUnitId(3),
            required: SourceUnitId(99),
        });
        assert_eq!(
            compute_retention(&inventory, &graph, &invalid),
            Err(RetentionError::InvalidConstraint)
        );
    }

    #[test]
    fn reachable_macro_expansion_requires_only_its_selected_rule() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (24, 32), Some(0), 1),
            unit(2, WrittenUnitKind::MacroDefinition, (0, 23), Some(0), 2),
            unit(3, WrittenUnitKind::MacroRule, (5, 12), Some(2), 3),
            unit(4, WrittenUnitKind::MacroRule, (13, 22), Some(2), 4),
        ];
        let mut inventory = inventory(source, units.clone());
        inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(2),
            rules: vec![SourceUnitId(3), SourceUnitId(4)],
            observed_selections: vec![SourceUnitId(3), SourceUnitId(3)],
        }];
        let mut graph = graph(
            vec![
                written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
                written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
                written_definition(2, DefinitionKind::Macro, &units[2], Some(0), "m"),
            ],
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        let expansion_kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "m".into(),
        };
        graph.expansions.push(ExpansionNode {
            id: ExpansionId(0),
            key: ExpansionKey(vec![ExpansionKeyPart {
                kind: expansion_kind.clone(),
                fragment: Some(ExpansionFragmentKind::Expression),
                implementation: Some(MacroImplementationKind::Declarative),
                invocation_range: Some(ByteRange { start: 24, end: 25 }),
                node_range: Some(ByteRange { start: 24, end: 25 }),
                target_range: None,
                macro_definition: Some(DefinitionReferenceKey::Local(
                    graph.definitions.definitions[2].key.clone(),
                )),
                selected_macro_rule: Some(units[3].full_range),
                same_role_ordinal: 0,
            }]),
            kind: expansion_kind,
            fragment: Some(ExpansionFragmentKind::Expression),
            implementation: Some(MacroImplementationKind::Declarative),
            discovered_in: None,
            semantic_parent: None,
            source_call_parent: None,
            written_invocation: None,
            source_owner: Some(DefinitionId(1)),
            macro_definition: Some(DefinitionTarget::Local(DefinitionId(2))),
        });
        let mut repeated_expansion = graph.expansions[0].clone();
        repeated_expansion.id = ExpansionId(1);
        repeated_expansion.key.0[0].invocation_range = Some(ByteRange { start: 25, end: 26 });
        repeated_expansion.key.0[0].node_range = Some(ByteRange { start: 25, end: 26 });
        repeated_expansion.key.0[0].same_role_ordinal = 1;
        graph.expansions.push(repeated_expansion);
        graph.edges.extend([
            DependencyEdge {
                from: GraphNode::Definition(DefinitionId(1)),
                to: GraphNode::Expansion(ExpansionId(0)),
                kind: DependencyKind::ExpansionUse,
                sites: vec![ObservationSite::CompilerGenerated],
                evidence: EvidenceOrigin::Compiler,
            },
            DependencyEdge {
                from: GraphNode::Expansion(ExpansionId(0)),
                to: GraphNode::Definition(DefinitionId(2)),
                kind: DependencyKind::MacroDefinition,
                sites: Vec::new(),
                evidence: EvidenceOrigin::Compiler,
            },
            DependencyEdge {
                from: GraphNode::Definition(DefinitionId(1)),
                to: GraphNode::Expansion(ExpansionId(1)),
                kind: DependencyKind::ExpansionUse,
                sites: vec![ObservationSite::CompilerGenerated],
                evidence: EvidenceOrigin::Compiler,
            },
            DependencyEdge {
                from: GraphNode::Expansion(ExpansionId(1)),
                to: GraphNode::Definition(DefinitionId(2)),
                kind: DependencyKind::MacroDefinition,
                sites: Vec::new(),
                evidence: EvidenceOrigin::Compiler,
            },
        ]);

        let mut missing_selection_graph = graph.clone();
        missing_selection_graph.expansions[0].key.0[0].selected_macro_rule = None;
        let mut incomplete_constraints = SourceConstraints::from_source(&inventory);
        assert_eq!(
            collect_macro_rule_expansion_constraints(
                &inventory,
                &missing_selection_graph.definitions,
                &missing_selection_graph.expansions,
                &mut incomplete_constraints,
            ),
            Err(RetentionError::InvalidConstraint),
            "every in-scope expansion needs a collected rule selection"
        );

        let mut missing_definition_graph = graph.clone();
        missing_definition_graph.expansions[1].macro_definition = None;
        missing_definition_graph.expansions[1].key.0[0].macro_definition = None;
        let mut incomplete_constraints = SourceConstraints::from_source(&inventory);
        assert_eq!(
            collect_macro_rule_expansion_constraints(
                &inventory,
                &missing_definition_graph.definitions,
                &missing_definition_graph.expansions,
                &mut incomplete_constraints,
            ),
            Err(RetentionError::InvalidConstraint),
            "coverage must not depend on the macro-definition relation being present"
        );

        let constraints = complete_constraints(&inventory, &graph);
        assert_eq!(
            constraints.macro_rule_selection_requirements,
            vec![
                MacroRuleSelectionRequirement {
                    expansion: ExpansionId(0),
                    rule: SourceUnitId(3),
                },
                MacroRuleSelectionRequirement {
                    expansion: ExpansionId(1),
                    rule: SourceUnitId(3),
                },
            ]
        );
        let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
        assert!(retention.retained_units.contains(&SourceUnitId(2)));
        assert!(retention.retained_units.contains(&SourceUnitId(3)));
        assert!(!retention.retained_units.contains(&SourceUnitId(4)));

        let mut missing_repeated_selection = constraints.clone();
        missing_repeated_selection
            .macro_rule_selection_requirements
            .pop();
        assert_eq!(
            compute_retention(&inventory, &graph, &missing_repeated_selection),
            Err(RetentionError::InvalidConstraint),
            "every expansion must keep its own selection even when the rule is shared"
        );

        let mut normalized_graph = graph.clone();
        for expansion in &mut normalized_graph.expansions {
            expansion.key.0[0].selected_macro_rule = Some(ByteRange { start: 6, end: 13 });
        }
        let normalized_retention =
            compute_retention(&inventory, &normalized_graph, &constraints).unwrap();
        assert_eq!(normalized_retention, retention);

        let mut orphaned_graph = graph.clone();
        orphaned_graph.edges.retain(|edge| {
            !(edge.from == GraphNode::Definition(DefinitionId(1))
                && matches!(edge.to, GraphNode::Expansion(_)))
        });
        orphaned_graph.edges.push(edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ));
        assert_eq!(
            compute_retention(&inventory, &orphaned_graph, &constraints),
            Err(RetentionError::InvalidConstraint),
            "an observed definition cannot survive without a reachable selecting expansion"
        );
    }

    #[test]
    fn retained_unobserved_macro_definition_keeps_every_rule() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
            unit(1, WrittenUnitKind::Item, (24, 32), Some(0), 1),
            unit(2, WrittenUnitKind::MacroDefinition, (0, 23), Some(0), 2),
            unit(3, WrittenUnitKind::MacroRule, (5, 12), Some(2), 3),
            unit(4, WrittenUnitKind::MacroRule, (13, 22), Some(2), 4),
        ];
        let mut inventory = inventory(source, units.clone());
        inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(2),
            rules: vec![SourceUnitId(3), SourceUnitId(4)],
            observed_selections: Vec::new(),
        }];
        let graph = graph(
            vec![
                written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
                written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
                written_definition(2, DefinitionKind::Macro, &units[2], Some(0), "m"),
            ],
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(0)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(2)),
                ),
            ],
        );

        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();
        assert!(retention.retained_units.contains(&SourceUnitId(2)));
        assert!(retention.retained_units.contains(&SourceUnitId(3)));
        assert!(retention.retained_units.contains(&SourceUnitId(4)));

        let mut missing = complete_constraints(&inventory, &graph);
        missing.macro_rule_requirements.pop();
        assert_eq!(
            compute_retention(&inventory, &graph, &missing),
            Err(RetentionError::InvalidConstraint)
        );
    }

    #[test]
    fn source_free_definitions_inherit_their_parent_unit() {
        let source = "xxxxxxxxxxxxxxxxxxxxxxxx";
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 24), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 12), Some(0), 1),
        ];
        let inventory = inventory(source, units.clone());
        let graph = graph(
            vec![
                written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
                written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
                injected_definition(2, 1),
            ],
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert!(
            retention
                .compile_required
                .contains(&GraphNode::Definition(DefinitionId(2)))
        );
    }
}
