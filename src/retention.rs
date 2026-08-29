//! Deterministic source-retention fixed point over the owned compiler graph.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{self, TyCtxt, TypeSuperVisitable, TypeVisitable, TypeVisitor};

use crate::definitions::CollectedDefinitions;
use crate::dependency_graph::{
    DependencyGraph, DependencyKind, ExpansionId, ExpansionNode, GraphNode,
    MacroImplementationKind, valid_roots,
};
#[cfg(test)]
use crate::expansions::{
    MacroCompleteOutputMeaning, MacroContributorDag, MacroContributorSetId,
    MacroOutputMaterializationGroup, MacroOutputRange, MacroOwnerEffect, MacroProducerCoverage,
};
use crate::expansions::{
    MacroCompleteOutputMeaningInventory, MacroProducerCoverageInventory,
    validated_outputless_macro_expansions,
};
use crate::graph::{
    DefinitionGraph, DefinitionId, DefinitionKind, DefinitionOrigin, DefinitionTarget,
};
use crate::source::{
    CfgState, DeclarativeSourceUnitKind, DeriveTargetSourceFacts, MacroRuleSelectionIndex,
    MacroRuleSourceFacts, SourceInventory, SourceUnitId, WrittenUnit, WrittenUnitKind,
    validate_declarative_macro_source_facts, validate_derive_target_facts,
    validate_ownerless_attribute_invocations,
};

mod disjunctions;
mod external;
mod macro_products;
mod reachability;
mod source_closure;
mod source_sites;

use disjunctions::{DisjunctionClosure, DisjunctionDemandLanes};
use macro_products::{
    DefinitionMacroProducerIndex, MacroProducerClassification, RetentionClosure,
    ValidatedMacroProducts, outputless_complete_macro_outputs,
    outputless_macro_expansions_after_rewrite, validate_complete_macro_output_meaning,
    validate_macro_product_constraints, validate_macro_source_refinement_coverage,
    validate_refined_macro_producers,
};
use reachability::{CompilerReachabilityClosure, CompilerReachabilityIndex};
use source_closure::{SourceRequirementClosure, SourceRequirementIndex, SourceRequirementMode};
pub(crate) use source_sites::SourceSiteOwnerIndex;

#[cfg(test)]
use macro_products::{
    MacroContributorProvenanceNode, MacroDefinitionParent, MacroMaterialization,
    MacroOwnerRequirement, MacroSourceContributorIndex, PendingMacroMaterializationGroup,
    immediate_macro_parent, lower_macro_materialization_groups,
    macro_contributor_provenance_parent, outputless_complete_macro_outputs_with_stats,
    outputless_macro_expansions_after_rewrite_with_stats, resolve_macro_contributor_provenance,
    validate_macro_contributor_provenance_with_stats, validate_macro_definition_product_class,
    validate_macro_owner_effect_members,
};

pub(crate) use external::{
    ExternalCompilerExpectation, ExternalCompilerObservation, external_compiler_expectation,
    external_compiler_observation, external_compiler_outcome_difference,
};

#[cfg(test)]
use external::{
    CompilerGeneratedCrateActivation, ExternalCompilerMetadataFact,
    ExternalCompilerOutcomeDifference, ExternalCrateActivation, ExternalCrateBinding,
    ExternalCrateBindingTarget, ExternalCrateDependency, ExternalCrateLoad, ExternalDependencyKind,
    ExternalMetadataProvider, ExternalMetadataProviderKind, ExternalMetadataRequirement,
    ExternalMetadataRequirementKind, LocalMetadataRequirement,
};

#[cfg(test)]
pub(crate) fn with_one_omitted_external_compiler_metadata_fact<T>(f: impl FnOnce() -> T) -> T {
    external::with_one_omitted_external_compiler_metadata_fact(f)
}
use external::{
    CompilerCrateLoadCarrier, CompilerCrateLoadDisjunction, ExternalCrateFacts,
    collect_external_crate_facts, validate_external_crate_facts,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SourceRequirement {
    pub trigger: SourceUnitId,
    pub required: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRuleSelectionRequirement {
    pub expansion: crate::dependency_graph::ExpansionId,
    pub rule: SourceUnitId,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SourceDisjunction {
    pub trigger: SourceUnitId,
    pub choices: Vec<SourceUnitId>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DefinitionRequirement {
    trigger: DefinitionId,
    required: DefinitionId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ConditionalDefinitionRequirement {
    left: DefinitionId,
    right: DefinitionId,
    required: DefinitionId,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DefinitionDisjunction {
    trigger: DefinitionId,
    choices: Vec<DefinitionId>,
}

/// Compiler-owned semantic relations between trait and implementation
/// definitions.  These facts deliberately stay in the definition domain:
/// multiple expanded products may share one written macro invocation unit.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct CompilerMemberConstraints {
    classified_members: Vec<DefinitionId>,
    classified_implementations: Vec<DefinitionId>,
    requirements: Vec<DefinitionRequirement>,
    conditional_requirements: Vec<ConditionalDefinitionRequirement>,
    disjunctions: Vec<DefinitionDisjunction>,
}

#[derive(Clone)]
struct ValidatedCompilerMemberConstraints {
    requirements_by_trigger: BTreeMap<DefinitionId, Vec<DefinitionId>>,
    conditional_requirements: Vec<ConditionalDefinitionRequirement>,
    conditional_by_trigger: BTreeMap<DefinitionId, Vec<(usize, u8)>>,
    disjunctions: Vec<DefinitionDisjunction>,
}

fn source_macro_rule_disjunctions(
    source: &SourceInventory,
) -> impl Iterator<Item = SourceDisjunction> + '_ {
    source.macro_rules.iter().filter_map(|facts| match facts {
        MacroRuleSourceFacts::Whole { .. } => None,
        MacroRuleSourceFacts::Refined {
            definition, rules, ..
        } => Some(SourceDisjunction {
            trigger: *definition,
            choices: rules.clone(),
        }),
    })
}

fn source_derive_requirements(
    source: &SourceInventory,
) -> impl Iterator<Item = SourceRequirement> + '_ {
    source.derive_targets.iter().flat_map(|facts| {
        let (influences, helpers) = match facts {
            DeriveTargetSourceFacts::Complete {
                influences,
                helpers,
                ..
            } => (influences.as_slice(), helpers.as_slice()),
            DeriveTargetSourceFacts::Opaque { .. } => (&[][..], &[][..]),
        };
        influences
            .iter()
            .map(|requirement| SourceRequirement {
                trigger: requirement.trigger,
                required: requirement.required,
            })
            .chain(helpers.iter().flat_map(|helper| {
                [
                    SourceRequirement {
                        trigger: helper.attribute,
                        required: helper.provider,
                    },
                    SourceRequirement {
                        trigger: helper.provider,
                        required: helper.attribute,
                    },
                ]
            }))
    })
}

fn source_macro_repetition_disjunctions(
    source: &SourceInventory,
) -> impl Iterator<Item = SourceDisjunction> + '_ {
    source
        .macro_repetitions
        .iter()
        .filter(|repetition| repetition.minimum == 1)
        .map(|repetition| SourceDisjunction {
            trigger: repetition.parent,
            choices: repetition
                .elements
                .iter()
                .map(|element| element.unit)
                .collect(),
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
    declarative_macros: Option<DeclarativeMacroConstraints>,
    pub ancestor_requirements: Vec<SourceRequirement>,
    pub shell_requirements: Vec<SourceRequirement>,
    pub derive_requirements: Vec<SourceRequirement>,
    pub macro_rule_requirements: Vec<SourceRequirement>,
    pub disjunctions: Vec<SourceDisjunction>,
    pub member_containers: Vec<SourceUnitId>,
    pub classified_members: Vec<SourceUnitId>,
    compiler_members: CompilerMemberConstraints,
    external_crates: ExternalCrateFacts,
}

/// One exhaustive declarative-macro observer snapshot. Rule selections,
/// output materializations, and outputless producers come from one compiler
/// observation and therefore enter `SourceConstraints` atomically.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarativeMacroConstraints {
    rule_selections: Vec<MacroRuleSelectionRequirement>,
    producer_coverage: MacroProducerCoverageInventory,
    complete_output_meaning: MacroCompleteOutputMeaningInventory,
    outputless_expansions: Vec<ExpansionId>,
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
            declarative_macros: None,
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
            derive_requirements: source_derive_requirements(source).collect(),
            macro_rule_requirements: Vec::new(),
            disjunctions: source_macro_rule_disjunctions(source)
                .chain(source_macro_repetition_disjunctions(source))
                .collect(),
            member_containers: Vec::new(),
            classified_members: Vec::new(),
            compiler_members: CompilerMemberConstraints::default(),
            external_crates: ExternalCrateFacts::default(),
        }
    }

    pub(crate) fn set_declarative_macro_constraints(
        &mut self,
        constraints: DeclarativeMacroConstraints,
    ) -> Result<(), RetentionError> {
        if self.declarative_macros.is_some() {
            return Err(RetentionError::InvalidConstraint);
        }
        self.declarative_macros = Some(constraints);
        Ok(())
    }

    fn declarative_macros(&self) -> Result<&DeclarativeMacroConstraints, RetentionError> {
        self.declarative_macros
            .as_ref()
            .ok_or(RetentionError::IncompleteMacroProductConstraints)
    }

    pub(crate) fn macro_rule_selections(
        &self,
    ) -> Result<&[MacroRuleSelectionRequirement], RetentionError> {
        Ok(&self.declarative_macros()?.rule_selections)
    }
}

/// Converts rustc's trait/impl completeness rules into owned definition-domain
/// semantics plus written-source structural shells. No compiler-lifetime value
/// crosses this boundary.
pub(crate) fn collect_source_constraints(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
    external_artifact_directory: Option<&Path>,
) -> Result<SourceConstraints, RetentionError> {
    validate_source(source)?;
    let local_definitions = reverse_local_definitions(tcx, definitions)?;
    let definition_units = definition_source_units_from_graph(source, &definitions.graph)?;
    let mut constraints = SourceConstraints::from_source(source);
    constraints.external_crates = collect_external_crate_facts(
        compiler,
        tcx,
        source,
        definitions,
        &local_definitions,
        &definition_units,
        external_artifact_directory,
    )
    .map_err(|_| RetentionError::IncompleteExternalCrateConstraints)?;

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
            local_definitions[definition.id.0 as usize],
            definition.id,
            &mut constraints.compiler_members.requirements,
        )?;
        constraints
            .compiler_members
            .classified_members
            .push(definition.id);
    }

    for definition in definitions
        .graph
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::Impl)
    {
        collect_impl_constraints(
            tcx,
            definitions,
            &local_definitions,
            definition.id,
            &mut constraints.compiler_members.requirements,
            &mut constraints.compiler_members.conditional_requirements,
            &mut constraints.compiler_members.disjunctions,
        )?;
        constraints
            .compiler_members
            .classified_implementations
            .push(definition.id);
    }
    collect_body_impl_requirements(
        tcx,
        definitions,
        &mut constraints.compiler_members.requirements,
    )?;
    constraints.compiler_members.classified_members.sort();
    constraints
        .compiler_members
        .classified_implementations
        .sort();
    constraints.compiler_members.requirements.sort();
    constraints.compiler_members.requirements.dedup();
    constraints.compiler_members.conditional_requirements.sort();
    constraints
        .compiler_members
        .conditional_requirements
        .dedup();
    constraints.compiler_members.disjunctions.sort();
    constraints.compiler_members.disjunctions.dedup();
    constraints.disjunctions.sort();
    constraints.disjunctions.dedup();
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
    requirements: &mut Vec<DefinitionRequirement>,
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
        let trigger = compiler_definition_id(definitions, dependency.source_owner.to_def_id())?;
        let implementation =
            compiler_definition_id(definitions, dependency.impl_def_id.to_def_id())?;
        if trigger != implementation {
            requirements.push(DefinitionRequirement {
                trigger,
                required: implementation,
            });
        }
        if let Some(item) = dependency.associated_item
            && let Some(item) = optional_compiler_definition_id(definitions, item)?
            && trigger != item
        {
            requirements.push(DefinitionRequirement {
                trigger,
                required: item,
            });
        }
    }
    Ok(())
}

#[cfg(not(rust_item_dependencies_patched))]
fn collect_body_impl_requirements(
    _tcx: TyCtxt<'_>,
    _definitions: &CollectedDefinitions,
    _requirements: &mut Vec<DefinitionRequirement>,
) -> Result<(), RetentionError> {
    Ok(())
}

fn collect_semantic_member_requirements(
    tcx: TyCtxt<'_>,
    definitions: &CollectedDefinitions,
    member: LocalDefId,
    member_definition: DefinitionId,
    requirements: &mut Vec<DefinitionRequirement>,
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
        if let Some(target_definition) = optional_compiler_definition_id(definitions, target)?
            && target_definition != member_definition
        {
            requirements.push(DefinitionRequirement {
                trigger: member_definition,
                required: target_definition,
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
    definitions: &CollectedDefinitions,
    local_definitions: &[LocalDefId],
    impl_definition: DefinitionId,
    member_requirements: &mut Vec<DefinitionRequirement>,
    conditional_requirements: &mut Vec<ConditionalDefinitionRequirement>,
    disjunctions: &mut Vec<DefinitionDisjunction>,
) -> Result<(), RetentionError> {
    let impl_local = local_definitions[impl_definition.0 as usize];
    if !matches!(tcx.def_kind(impl_local), DefKind::Impl { .. }) {
        return Err(RetentionError::IncompleteMemberConstraints);
    }
    let impl_id = impl_local.to_def_id();
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
        let impl_item_definition = compiler_definition_id(definitions, impl_item.def_id)?;
        let trait_item = impl_item
            .trait_item_def_id()
            .ok_or(RetentionError::IncompleteMemberConstraints)?;
        if let Some(trait_item_definition) =
            optional_compiler_definition_id(definitions, trait_item)?
            && impl_item_definition != trait_item_definition
        {
            member_requirements.push(DefinitionRequirement {
                trigger: impl_item_definition,
                required: trait_item_definition,
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
        let impl_item_definition = compiler_definition_id(definitions, impl_item)?;
        if impl_item_definition == impl_definition {
            continue;
        }
        if let Some(trait_item_definition) =
            optional_compiler_definition_id(definitions, trait_item.def_id)?
        {
            // Completeness requires an implementation only when the trait has
            // no default. A used override is reached independently through
            // the compiler dependency graph.
            if !trait_item.defaultness(tcx).has_value()
                && trait_item_definition != impl_definition
                && trait_item_definition != impl_item_definition
            {
                conditional_requirements.push(ConditionalDefinitionRequirement {
                    left: impl_definition,
                    right: trait_item_definition,
                    required: impl_item_definition,
                });
            }
        } else if !trait_item.defaultness(tcx).has_value() {
            member_requirements.push(DefinitionRequirement {
                trigger: impl_definition,
                required: impl_item_definition,
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
            let choice = compiler_definition_id(definitions, impl_item)?;
            if choice == impl_definition {
                fulfilled_by_impl_unit = true;
            } else {
                choices.insert(choice);
            }
        }
        if !fulfilled_by_impl_unit {
            if choices.is_empty() {
                return Err(RetentionError::IncompleteMemberConstraints);
            }
            disjunctions.push(DefinitionDisjunction {
                trigger: impl_definition,
                choices: choices.into_iter().collect(),
            });
        }
    }
    Ok(())
}

fn compiler_definition_id(
    definitions: &CollectedDefinitions,
    definition: DefId,
) -> Result<DefinitionId, RetentionError> {
    optional_compiler_definition_id(definitions, definition)?
        .ok_or(RetentionError::IncompleteMemberConstraints)
}

fn optional_compiler_definition_id(
    definitions: &CollectedDefinitions,
    definition: DefId,
) -> Result<Option<DefinitionId>, RetentionError> {
    let Some(local) = definition.as_local() else {
        return Ok(None);
    };
    definitions
        .definition_id(local)
        .map(Some)
        .ok_or(RetentionError::IncompleteMemberConstraints)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Retention {
    pub semantic_required: BTreeSet<GraphNode>,
    pub compile_required: BTreeSet<GraphNode>,
    pub retained_units: BTreeSet<SourceUnitId>,
    pub outputless_macro_expansions: BTreeSet<ExpansionId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RetentionError {
    InvalidSource,
    InvalidGraph,
    InvalidConstraint,
    IncompleteMemberConstraints,
    IncompleteExternalCrateConstraints,
    IncompleteOpaqueSourceConstraints,
    IncompleteMacroProductConstraints,
    UnsupportedExternalNativeLink,
}

pub(crate) fn compute_retention(
    source: &SourceInventory,
    graph: &DependencyGraph,
    constraints: &SourceConstraints,
) -> Result<Retention, RetentionError> {
    validate_source(source)?;
    validate_graph(graph)?;
    let definition_units = definition_source_units(source, graph)?;
    let validated = validate_constraints(source, graph, &definition_units, constraints)?;
    let source_requirements = SourceRequirementIndex::new(
        source.units.len(),
        &validated.atomic_groups,
        &validated.ancestor_requirements,
        &validated.shell_requirements,
        &validated.derive_requirements,
        &validated.macro_rule_requirements,
    )?;
    let source_sites = SourceSiteOwnerIndex::new(source)?;
    let compiler_reachability = CompilerReachabilityIndex::new(
        source,
        &source_sites,
        graph,
        &validated.macro_products.delegated_macro_expansions,
    )?;
    let mut macro_repetition_tokens = crate::rewrite::MacroRepetitionTokenRequirements::new(source)
        .map_err(|_| RetentionError::InvalidConstraint)?;
    let semantic_roots = graph
        .roots
        .iter()
        .filter(|root| root.reason.is_semantic())
        .map(|root| root.node)
        .collect();
    let semantic_required = semantic_closure_for_source(
        &validated,
        &source_requirements,
        &compiler_reachability,
        semantic_roots,
    )?;

    let compile_roots = graph
        .roots
        .iter()
        .map(|root| root.node)
        .collect::<BTreeSet<_>>();
    let mut compile_required = compile_roots;
    let mut actual_required = compile_required.clone();
    let mut retained_units = BTreeSet::new();
    let mut token_retained_deltas = Vec::new();
    let mut pending_compile = compile_required.iter().copied().collect::<Vec<_>>();
    let mut pending_actual = actual_required.iter().copied().collect::<Vec<_>>();
    let mut pending_source = Vec::new();
    let mut macro_closure =
        RetentionClosure::new(&validated.macro_products, Some(&validated.compiler_members));
    macro_closure.seed(&compile_required, &actual_required, &retained_units)?;
    let mut reachability_closure = CompilerReachabilityClosure::new(&compiler_reachability);
    reachability_closure.seed(&compile_required, &retained_units)?;
    let mut actual_reachability_closure = CompilerReachabilityClosure::new(&compiler_reachability);
    actual_reachability_closure.seed(&actual_required, &retained_units)?;
    let mut source_closure =
        SourceRequirementClosure::new(&source_requirements, SourceRequirementMode::Compile);
    source_closure.seed(&retained_units)?;
    let mut disjunction_closure = DisjunctionClosure::new(
        source,
        graph,
        &validated.singleton_definition_units,
        &validated.macro_products,
        &validated.disjunctions,
        &validated.compiler_disjunctions,
        &validated.compiler_members.disjunctions,
    )?;
    disjunction_closure.seed(&compile_required, &actual_required, &retained_units)?;
    let mut preserve_active_source_opened = false;

    loop {
        close_deterministic_constraints(
            &validated,
            DeterministicRetentionState {
                compile_required: &mut compile_required,
                actual_required: &mut actual_required,
                retained_units: &mut retained_units,
                pending_compile: &mut pending_compile,
                pending_actual: &mut pending_actual,
                pending_source: &mut pending_source,
                token_retained_deltas: &mut token_retained_deltas,
            },
            DeterministicClosures {
                macro_products: &mut macro_closure,
                reachability: &mut reachability_closure,
                actual_reachability: &mut actual_reachability_closure,
                source_requirements: &mut source_closure,
                disjunctions: &mut disjunction_closure,
                preserve_active_source_opened: &mut preserve_active_source_opened,
            },
        )?;

        let mut selected = disjunction_closure.select(
            DisjunctionDemandLanes {
                compile: &mut compile_required,
                actual: &mut actual_required,
                newly_compile: &mut pending_compile,
                newly_actual: &mut pending_actual,
            },
            &mut retained_units,
            &mut pending_source,
            &mut token_retained_deltas,
        )?;
        if !selected {
            selected = macro_repetition_tokens
                .close(
                    &mut retained_units,
                    &std::mem::take(&mut token_retained_deltas),
                )
                .map_err(|_| RetentionError::InvalidConstraint)?;
            if selected {
                let forced = macro_repetition_tokens.take_newly_forced_units();
                pending_source.extend_from_slice(&forced);
                token_retained_deltas.extend(forced);
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
    validate_retained_macro_definitions(source, &retained_units)?;
    let mut outputless_macro_expansions = validated.outputless_macro_expansions;
    outputless_macro_expansions.extend(outputless_macro_expansions_after_rewrite(
        &validated.macro_products,
        &retained_units,
    )?);
    Ok(Retention {
        semantic_required,
        compile_required,
        retained_units,
        outputless_macro_expansions,
    })
}

/// Computes the outputless declarative expansions represented by an already
/// rewritten source without selecting another reduction.
///
/// Every source unit in this inventory exists in the rewritten text. Running
/// the same macro-output least fixed point over that complete set gives the
/// exclusions used to canonicalize the reduced compiler snapshot, including
/// control-only parents of directly empty expansions.
pub(crate) fn outputless_macro_expansions_in_complete_source(
    graph: &DependencyGraph,
    constraints: &SourceConstraints,
) -> Result<BTreeSet<ExpansionId>, RetentionError> {
    let declarative_macros = constraints.declarative_macros()?;
    let directly_outputless = validate_outputless_macro_expansions(graph, declarative_macros)?;
    let complete_output_meaning = validate_complete_macro_output_meaning(
        graph,
        &declarative_macros.complete_output_meaning,
        &directly_outputless,
    )?;
    outputless_complete_macro_outputs(&complete_output_meaning)
}

struct DeterministicClosures<'state, 'constraints> {
    macro_products: &'state mut RetentionClosure<'constraints>,
    reachability: &'state mut CompilerReachabilityClosure<'constraints>,
    actual_reachability: &'state mut CompilerReachabilityClosure<'constraints>,
    source_requirements: &'state mut SourceRequirementClosure<'constraints>,
    disjunctions: &'state mut DisjunctionClosure,
    preserve_active_source_opened: &'state mut bool,
}

struct DeterministicRetentionState<'state> {
    compile_required: &'state mut BTreeSet<GraphNode>,
    actual_required: &'state mut BTreeSet<GraphNode>,
    retained_units: &'state mut BTreeSet<SourceUnitId>,
    pending_compile: &'state mut Vec<GraphNode>,
    pending_actual: &'state mut Vec<GraphNode>,
    pending_source: &'state mut Vec<SourceUnitId>,
    token_retained_deltas: &'state mut Vec<SourceUnitId>,
}

fn close_deterministic_constraints(
    constraints: &ValidatedConstraints,
    state: DeterministicRetentionState<'_>,
    closures: DeterministicClosures<'_, '_>,
) -> Result<(), RetentionError> {
    let DeterministicRetentionState {
        compile_required,
        actual_required,
        retained_units,
        pending_compile,
        pending_actual,
        pending_source,
        token_retained_deltas,
    } = state;
    let DeterministicClosures {
        macro_products: macro_closure,
        reachability: reachability_closure,
        actual_reachability: actual_reachability_closure,
        source_requirements: source_closure,
        disjunctions: disjunction_closure,
        preserve_active_source_opened,
    } = closures;
    let token_notification_start = pending_source.len();
    let mut macro_presence_cursor = 0;
    let mut macro_actual_cursor = 0;
    let mut macro_source_cursor = 0;
    let mut side_effect_compile_cursor = 0;
    let mut source_definition_cursor = 0;
    let mut source_closure_cursor = 0;
    let mut disjunction_actual_cursor = 0;
    let mut disjunction_compile_cursor = 0;
    let mut disjunction_source_cursor = 0;
    let mut reachability_compile_cursor = 0;
    let mut reachability_source_cursor = 0;
    let mut actual_reachability_cursor = 0;
    let mut actual_reachability_source_cursor = 0;
    let mut actual_to_compile_cursor = 0;

    loop {
        while macro_presence_cursor < pending_compile.len()
            || macro_actual_cursor < pending_actual.len()
            || macro_source_cursor < pending_source.len()
            || side_effect_compile_cursor < pending_compile.len()
            || source_definition_cursor < pending_source.len()
            || source_closure_cursor < pending_source.len()
            || disjunction_actual_cursor < pending_actual.len()
            || disjunction_compile_cursor < pending_compile.len()
            || disjunction_source_cursor < pending_source.len()
        {
            if macro_presence_cursor < pending_compile.len() {
                let deltas = pending_compile[macro_presence_cursor..].to_vec();
                macro_presence_cursor = pending_compile.len();
                macro_closure.add_presence(deltas);
            }
            if macro_actual_cursor < pending_actual.len() {
                let deltas = pending_actual[macro_actual_cursor..].to_vec();
                macro_actual_cursor = pending_actual.len();
                macro_closure.add_actual(deltas);
            }
            if macro_source_cursor < pending_source.len() {
                let deltas = pending_source[macro_source_cursor..].to_vec();
                macro_source_cursor = pending_source.len();
                macro_closure.add_source(deltas);
            }
            if disjunction_compile_cursor < pending_compile.len() {
                let deltas = pending_compile[disjunction_compile_cursor..].to_vec();
                disjunction_compile_cursor = pending_compile.len();
                disjunction_closure.add_compile(deltas);
            }
            if disjunction_actual_cursor < pending_actual.len() {
                let deltas = pending_actual[disjunction_actual_cursor..].to_vec();
                disjunction_actual_cursor = pending_actual.len();
                disjunction_closure.add_actual(deltas);
            }
            if disjunction_source_cursor < pending_source.len() {
                let deltas = pending_source[disjunction_source_cursor..].to_vec();
                disjunction_source_cursor = pending_source.len();
                disjunction_closure.add_source(deltas)?;
            }

            let compile_deltas = pending_compile[side_effect_compile_cursor..].to_vec();
            side_effect_compile_cursor = pending_compile.len();
            for node in compile_deltas {
                if let GraphNode::Definition(definition) = node
                    && let Some(unit) =
                        constraints.singleton_definition_units[definition.0 as usize]
                {
                    retain_source_unit(retained_units, pending_source, unit);
                }
                if let Some(required) = constraints.compiler_sources_by_trigger.get(&node) {
                    retain_source_units(retained_units, pending_source, required.iter().copied());
                }
                if !*preserve_active_source_opened
                    && constraints.preserve_active_source_triggers.contains(&node)
                {
                    *preserve_active_source_opened = true;
                    retain_source_units(
                        retained_units,
                        pending_source,
                        constraints.active_source_units.iter().copied(),
                    );
                }
            }

            if source_closure_cursor < pending_source.len() {
                let deltas = pending_source[source_closure_cursor..].to_vec();
                source_closure_cursor = pending_source.len();
                source_closure.add(deltas)?;
                source_closure.close(retained_units, pending_source)?;
            }

            let source_deltas = pending_source[source_definition_cursor..].to_vec();
            source_definition_cursor = pending_source.len();
            for unit in source_deltas {
                let Some(definitions) = constraints
                    .singleton_definitions_by_source
                    .get(unit.0 as usize)
                else {
                    return Err(RetentionError::InvalidConstraint);
                };
                for &definition in definitions {
                    require_compiler_node(
                        compile_required,
                        pending_compile,
                        GraphNode::Definition(definition),
                    );
                }
            }

            macro_closure.close(
                compile_required,
                pending_compile,
                actual_required,
                pending_actual,
                retained_units,
                pending_source,
            );
        }

        if reachability_compile_cursor < pending_compile.len() {
            let deltas = pending_compile[reachability_compile_cursor..].to_vec();
            reachability_compile_cursor = pending_compile.len();
            reachability_closure.add_reachable(deltas);
        }
        if reachability_source_cursor < pending_source.len() {
            let deltas = pending_source[reachability_source_cursor..].to_vec();
            reachability_source_cursor = pending_source.len();
            reachability_closure.add_sources(deltas)?;
        }
        let compile_before = pending_compile.len();
        reachability_closure.close(compile_required, pending_compile)?;

        if actual_reachability_cursor < pending_actual.len() {
            let deltas = pending_actual[actual_reachability_cursor..].to_vec();
            actual_reachability_cursor = pending_actual.len();
            actual_reachability_closure.add_reachable(deltas);
        }
        if actual_reachability_source_cursor < pending_source.len() {
            let deltas = pending_source[actual_reachability_source_cursor..].to_vec();
            actual_reachability_source_cursor = pending_source.len();
            actual_reachability_closure.add_sources(deltas)?;
        }
        let actual_before = pending_actual.len();
        actual_reachability_closure.close(actual_required, pending_actual)?;
        if actual_to_compile_cursor < pending_actual.len() {
            mirror_actual_nodes_into_compile(
                &pending_actual[actual_to_compile_cursor..],
                compile_required,
                pending_compile,
            );
            actual_to_compile_cursor = pending_actual.len();
        }
        if pending_compile.len() == compile_before && pending_actual.len() == actual_before {
            break;
        }
    }

    token_retained_deltas.extend_from_slice(&pending_source[token_notification_start..]);
    pending_compile.clear();
    pending_actual.clear();
    pending_source.clear();
    Ok(())
}

#[derive(Default)]
struct MacroProductRankCache {
    contributor_classes: Vec<Option<MacroProductGroupRank>>,
    #[cfg(test)]
    rank_queries: usize,
    #[cfg(test)]
    contributor_class_misses: usize,
    #[cfg(test)]
    dag_node_visits: usize,
}

struct MacroProductGroupRank {
    size: u64,
    ranges: Arc<[crate::source::ByteRange]>,
}

type DefinitionChoiceRank = (
    u64,
    Arc<[crate::source::ByteRange]>,
    crate::graph::DefinitionKey,
);

type CompilerCrateLoadCarrierRank = (
    u64,
    Arc<[crate::source::ByteRange]>,
    Option<crate::graph::DefinitionKey>,
    CompilerCrateLoadCarrier,
);

fn definition_choice_rank(
    source: &SourceInventory,
    graph: &DependencyGraph,
    singleton_definition_units: &[Option<SourceUnitId>],
    macro_products: &ValidatedMacroProducts,
    macro_rank_cache: &mut MacroProductRankCache,
    choice: DefinitionId,
) -> Result<DefinitionChoiceRank, RetentionError> {
    let definition = graph
        .definitions
        .definitions
        .get(choice.0 as usize)
        .filter(|definition| definition.id == choice)
        .ok_or(RetentionError::InvalidConstraint)?;
    #[cfg(test)]
    {
        macro_rank_cache.rank_queries += 1;
    }
    let group = macro_products.group_for_product(GraphNode::Definition(choice));
    let singleton = singleton_definition_units
        .get(choice.0 as usize)
        .copied()
        .flatten();
    let (size, ranges) = match (group, singleton) {
        (Some(group), None) => {
            let contributor_class = macro_products
                .contributor_class_for_group(group)
                .ok_or(RetentionError::InvalidConstraint)?;
            let (size, ranges) = if let Some(rank) = macro_rank_cache
                .contributor_classes
                .get(contributor_class)
                .and_then(Option::as_ref)
            {
                (rank.size, Arc::clone(&rank.ranges))
            } else {
                let (contributor_sources, _dag_node_visits) =
                    macro_products.contributor_sources_for_class_with_visits(contributor_class)?;
                #[cfg(test)]
                {
                    macro_rank_cache.contributor_class_misses += 1;
                    macro_rank_cache.dag_node_visits += _dag_node_visits;
                }
                let mut ranges = contributor_sources
                    .into_iter()
                    .map(|unit| {
                        source
                            .units
                            .get(unit.0 as usize)
                            .filter(|source_unit| source_unit.id == unit)
                            .map(|source_unit| source_unit.full_range)
                            .ok_or(RetentionError::InvalidConstraint)
                    })
                    .collect::<Result<Vec<_>, RetentionError>>()?;
                ranges.sort();
                let size = ranges.iter().try_fold(0u64, |size, range| {
                    size.checked_add(u64::from(range.len()))
                        .ok_or(RetentionError::InvalidConstraint)
                })?;
                let ranges = Arc::from(ranges);
                if macro_rank_cache.contributor_classes.len() <= contributor_class {
                    macro_rank_cache
                        .contributor_classes
                        .resize_with(contributor_class + 1, || None);
                }
                macro_rank_cache.contributor_classes[contributor_class] =
                    Some(MacroProductGroupRank {
                        size,
                        ranges: Arc::clone(&ranges),
                    });
                (size, ranges)
            };
            (size, ranges)
        }
        (None, Some(unit)) => {
            let range = source
                .units
                .get(unit.0 as usize)
                .filter(|source_unit| source_unit.id == unit)
                .map(|source_unit| source_unit.full_range)
                .ok_or(RetentionError::InvalidConstraint)?;
            (u64::from(range.len()), Arc::from(vec![range]))
        }
        (Some(_), Some(_)) | (None, None) => return Err(RetentionError::InvalidConstraint),
    };
    Ok((size, ranges, definition.key.clone()))
}

fn require_compiler_node(
    required: &mut BTreeSet<GraphNode>,
    newly_required: &mut Vec<GraphNode>,
    node: GraphNode,
) -> bool {
    let inserted = required.insert(node);
    if inserted {
        newly_required.push(node);
    }
    inserted
}

fn mirror_actual_nodes_into_compile(
    actual_deltas: &[GraphNode],
    compile_required: &mut BTreeSet<GraphNode>,
    newly_compile_required: &mut Vec<GraphNode>,
) {
    for &node in actual_deltas {
        require_compiler_node(compile_required, newly_compile_required, node);
    }
}

fn retain_source_unit(
    retained: &mut BTreeSet<SourceUnitId>,
    newly_retained: &mut Vec<SourceUnitId>,
    unit: SourceUnitId,
) -> bool {
    let inserted = retained.insert(unit);
    if inserted {
        newly_retained.push(unit);
    }
    inserted
}

fn retain_source_units(
    retained: &mut BTreeSet<SourceUnitId>,
    newly_retained: &mut Vec<SourceUnitId>,
    units: impl IntoIterator<Item = SourceUnitId>,
) {
    for unit in units {
        retain_source_unit(retained, newly_retained, unit);
    }
}

fn compiler_crate_load_carrier_rank(
    source: &SourceInventory,
    graph: &DependencyGraph,
    singleton_definition_units: &[Option<SourceUnitId>],
    macro_products: &ValidatedMacroProducts,
    macro_rank_cache: &mut MacroProductRankCache,
    carrier: CompilerCrateLoadCarrier,
) -> Result<CompilerCrateLoadCarrierRank, RetentionError> {
    match carrier {
        CompilerCrateLoadCarrier::Definition(definition) => {
            let (size, ranges, key) = definition_choice_rank(
                source,
                graph,
                singleton_definition_units,
                macro_products,
                macro_rank_cache,
                definition,
            )?;
            Ok((size, ranges, Some(key), carrier))
        }
        CompilerCrateLoadCarrier::Source(unit) => {
            let unit = source
                .units
                .get(unit.0 as usize)
                .filter(|source_unit| source_unit.id == unit)
                .ok_or(RetentionError::InvalidConstraint)?;
            Ok((
                u64::from(unit.full_range.len()),
                Arc::from(vec![unit.full_range]),
                None,
                carrier,
            ))
        }
    }
}

fn semantic_closure_for_source(
    constraints: &ValidatedConstraints,
    source_requirements: &SourceRequirementIndex,
    compiler_reachability: &CompilerReachabilityIndex,
    roots: BTreeSet<GraphNode>,
) -> Result<BTreeSet<GraphNode>, RetentionError> {
    let mut reachable = roots;
    let mut actual_required = reachable.clone();
    let mut source_units = BTreeSet::new();
    let mut pending_compile = reachable.iter().copied().collect::<Vec<_>>();
    let mut pending_actual = actual_required.iter().copied().collect::<Vec<_>>();
    let mut pending_source = Vec::new();
    let mut macro_closure = RetentionClosure::new(&constraints.macro_products, None);
    macro_closure.seed(&reachable, &actual_required, &source_units)?;
    let mut reachability_closure = CompilerReachabilityClosure::new(compiler_reachability);
    reachability_closure.seed(&reachable, &source_units)?;
    let mut actual_reachability_closure = CompilerReachabilityClosure::new(compiler_reachability);
    actual_reachability_closure.seed(&actual_required, &source_units)?;
    let mut source_closure =
        SourceRequirementClosure::new(source_requirements, SourceRequirementMode::Semantic);
    source_closure.seed(&source_units)?;
    let mut macro_presence_cursor = 0;
    let mut macro_actual_cursor = 0;
    let mut macro_source_cursor = 0;
    let mut definition_source_cursor = 0;
    let mut source_closure_cursor = 0;
    let mut reachability_compile_cursor = 0;
    let mut reachability_source_cursor = 0;
    let mut actual_reachability_cursor = 0;
    let mut actual_reachability_source_cursor = 0;
    let mut actual_to_compile_cursor = 0;

    loop {
        while macro_presence_cursor < pending_compile.len()
            || macro_actual_cursor < pending_actual.len()
            || macro_source_cursor < pending_source.len()
            || definition_source_cursor < pending_compile.len()
            || source_closure_cursor < pending_source.len()
        {
            if macro_presence_cursor < pending_compile.len() {
                let deltas = pending_compile[macro_presence_cursor..].to_vec();
                macro_presence_cursor = pending_compile.len();
                macro_closure.add_presence(deltas);
            }
            if macro_actual_cursor < pending_actual.len() {
                let deltas = pending_actual[macro_actual_cursor..].to_vec();
                macro_actual_cursor = pending_actual.len();
                macro_closure.add_actual(deltas);
            }
            if macro_source_cursor < pending_source.len() {
                let deltas = pending_source[macro_source_cursor..].to_vec();
                macro_source_cursor = pending_source.len();
                macro_closure.add_source(deltas);
            }

            let compile_deltas = pending_compile[definition_source_cursor..].to_vec();
            definition_source_cursor = pending_compile.len();
            for node in compile_deltas {
                if let GraphNode::Definition(definition) = node
                    && let Some(unit) =
                        constraints.singleton_definition_units[definition.0 as usize]
                {
                    retain_source_unit(&mut source_units, &mut pending_source, unit);
                }
            }

            if source_closure_cursor < pending_source.len() {
                let deltas = pending_source[source_closure_cursor..].to_vec();
                source_closure_cursor = pending_source.len();
                source_closure.add(deltas)?;
                source_closure.close(&mut source_units, &mut pending_source)?;
            }

            macro_closure.close(
                &mut reachable,
                &mut pending_compile,
                &mut actual_required,
                &mut pending_actual,
                &mut source_units,
                &mut pending_source,
            );
        }

        if reachability_compile_cursor < pending_compile.len() {
            let deltas = pending_compile[reachability_compile_cursor..].to_vec();
            reachability_compile_cursor = pending_compile.len();
            reachability_closure.add_reachable(deltas);
        }
        if reachability_source_cursor < pending_source.len() {
            let deltas = pending_source[reachability_source_cursor..].to_vec();
            reachability_source_cursor = pending_source.len();
            reachability_closure.add_sources(deltas)?;
        }
        let compile_before = pending_compile.len();
        reachability_closure.close(&mut reachable, &mut pending_compile)?;

        if actual_reachability_cursor < pending_actual.len() {
            let deltas = pending_actual[actual_reachability_cursor..].to_vec();
            actual_reachability_cursor = pending_actual.len();
            actual_reachability_closure.add_reachable(deltas);
        }
        if actual_reachability_source_cursor < pending_source.len() {
            let deltas = pending_source[actual_reachability_source_cursor..].to_vec();
            actual_reachability_source_cursor = pending_source.len();
            actual_reachability_closure.add_sources(deltas)?;
        }
        let actual_before = pending_actual.len();
        actual_reachability_closure.close(&mut actual_required, &mut pending_actual)?;
        if actual_to_compile_cursor < pending_actual.len() {
            mirror_actual_nodes_into_compile(
                &pending_actual[actual_to_compile_cursor..],
                &mut reachable,
                &mut pending_compile,
            );
            actual_to_compile_cursor = pending_actual.len();
        }
        if pending_compile.len() == compile_before && pending_actual.len() == actual_before {
            return Ok(reachable);
        }
    }
}

pub(crate) fn source_site_is_retained(
    source_sites: &SourceSiteOwnerIndex,
    retained_units: &BTreeSet<SourceUnitId>,
    site: crate::source::ByteRange,
) -> Result<bool, RetentionError> {
    let owner_states = source_sites
        .owners(site)?
        .into_iter()
        .map(|unit| retained_units.contains(&unit))
        .collect::<BTreeSet<_>>();
    if owner_states.len() != 1 {
        return Err(RetentionError::InvalidGraph);
    }
    Ok(*owner_states.first().expect("one owner state was checked"))
}

fn source_site_owner(
    source_sites: &SourceSiteOwnerIndex,
    site: crate::source::ByteRange,
) -> Result<SourceUnitId, RetentionError> {
    let owners = source_sites.owners(site)?;
    let [owner] = owners.as_slice() else {
        return Err(RetentionError::IncompleteMemberConstraints);
    };
    Ok(*owner)
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
    singleton_definition_units: Vec<Option<SourceUnitId>>,
    singleton_definitions_by_source: Vec<Vec<DefinitionId>>,
    atomic_groups: Vec<Vec<SourceUnitId>>,
    macro_rule_selection_requirements: Vec<MacroRuleSelectionRequirement>,
    macro_products: ValidatedMacroProducts,
    outputless_macro_expansions: BTreeSet<ExpansionId>,
    ancestor_requirements: Vec<SourceRequirement>,
    shell_requirements: Vec<SourceRequirement>,
    derive_requirements: Vec<SourceRequirement>,
    macro_rule_requirements: Vec<SourceRequirement>,
    compiler_members: ValidatedCompilerMemberConstraints,
    disjunctions: Vec<SourceDisjunction>,
    compiler_disjunctions: Vec<CompilerCrateLoadDisjunction>,
    compiler_sources_by_trigger: BTreeMap<GraphNode, Vec<SourceUnitId>>,
    preserve_active_source_triggers: BTreeSet<GraphNode>,
    active_source_units: Vec<SourceUnitId>,
}

fn validate_outputless_macro_expansions(
    graph: &DependencyGraph,
    declarative_macros: &DeclarativeMacroConstraints,
) -> Result<BTreeSet<ExpansionId>, RetentionError> {
    let outputless = validated_outputless_macro_expansions(
        &graph.expansions,
        &graph.edges,
        &declarative_macros.outputless_expansions,
    )
    .ok_or(RetentionError::InvalidConstraint)?;
    if declarative_macros
        .producer_coverage
        .producers()
        .iter()
        .any(|coverage| {
            coverage.output_token_count() == 0 || outputless.contains(&coverage.producer())
        })
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(outputless)
}

struct ValidatedDeclarativeMacroConstraints {
    singleton_definition_units: Vec<Option<SourceUnitId>>,
    macro_rule_selection_requirements: Vec<MacroRuleSelectionRequirement>,
    macro_products: ValidatedMacroProducts,
    outputless_macro_expansions: BTreeSet<ExpansionId>,
}

fn validate_declarative_macro_constraints(
    source: &SourceInventory,
    graph: &DependencyGraph,
    definition_units: &[SourceUnitId],
    declarative_macros: &DeclarativeMacroConstraints,
) -> Result<ValidatedDeclarativeMacroConstraints, RetentionError> {
    let refined_macro_definitions = refined_macro_definition_units(source);
    let macro_rule_selection_requirements = validate_macro_rule_selection_requirements(
        source,
        graph,
        &refined_macro_definitions,
        &declarative_macros.rule_selections,
    )?;
    let outputless_macro_expansions =
        validate_outputless_macro_expansions(graph, declarative_macros)?;
    let refined_macro_producers = validate_refined_macro_producers(
        source,
        graph,
        &refined_macro_definitions,
        &macro_rule_selection_requirements,
        declarative_macros.producer_coverage.producers(),
    )?;
    validate_macro_source_refinement_coverage(
        source,
        graph,
        &macro_rule_selection_requirements,
        &refined_macro_producers,
        &outputless_macro_expansions,
    )?;
    let complete_output_meaning = validate_complete_macro_output_meaning(
        graph,
        &declarative_macros.complete_output_meaning,
        &outputless_macro_expansions,
    )?;
    let macro_producers = DefinitionMacroProducerIndex::new(graph);
    let singleton_definition_units = definition_singleton_source_units(
        &graph.definitions,
        &macro_producers,
        definition_units,
        &refined_macro_producers,
    )?;
    let macro_products = validate_macro_product_constraints(
        source,
        graph,
        &macro_producers,
        &singleton_definition_units,
        &MacroProducerClassification::new(&refined_macro_producers, &complete_output_meaning),
        &macro_rule_selection_requirements,
        &declarative_macros.producer_coverage,
    )?;
    Ok(ValidatedDeclarativeMacroConstraints {
        singleton_definition_units,
        macro_rule_selection_requirements,
        macro_products,
        outputless_macro_expansions,
    })
}

fn validate_constraints(
    source: &SourceInventory,
    graph: &DependencyGraph,
    definition_units: &[SourceUnitId],
    constraints: &SourceConstraints,
) -> Result<ValidatedConstraints, RetentionError> {
    let declarative_macros = constraints.declarative_macros()?;
    let macro_graph = graph;
    let unit_count = source.units.len();
    let valid_unit = |id: SourceUnitId| (id.0 as usize) < unit_count;
    let declarative_unit_kinds = source
        .declarative_unit_kinds()
        .map_err(|_| RetentionError::InvalidConstraint)?;

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
    let derives = validate_requirements(
        source,
        &constraints.derive_requirements,
        RequirementClass::Semantic,
    )?;
    let expected_derives = source_derive_requirements(source).collect::<BTreeSet<_>>();
    if derives.iter().copied().collect::<BTreeSet<_>>() != expected_derives {
        return Err(RetentionError::InvalidConstraint);
    }
    let macro_rules = validate_requirements(
        source,
        &constraints.macro_rule_requirements,
        RequirementClass::Semantic,
    )?;
    if !macro_rules.is_empty() {
        return Err(RetentionError::InvalidConstraint);
    }
    let ValidatedDeclarativeMacroConstraints {
        singleton_definition_units,
        macro_rule_selection_requirements,
        macro_products,
        outputless_macro_expansions,
    } = validate_declarative_macro_constraints(
        source,
        macro_graph,
        definition_units,
        declarative_macros,
    )?;
    let mut singleton_definitions_by_source = vec![Vec::new(); unit_count];
    for (index, unit) in singleton_definition_units.iter().copied().enumerate() {
        if let Some(unit) = unit {
            singleton_definitions_by_source[unit.0 as usize].push(DefinitionId(index as u32));
        }
    }
    let compiler_members =
        validate_compiler_member_constraints(graph, &constraints.compiler_members)?;

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
    let expected_macro_rule_disjunctions = source_macro_rule_disjunctions(source)
        .map(|disjunction| {
            (
                disjunction.trigger,
                disjunction.choices.into_iter().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeSet<_>>();
    let expected_macro_repetition_disjunctions = source_macro_repetition_disjunctions(source)
        .map(|disjunction| {
            (
                disjunction.trigger,
                disjunction.choices.into_iter().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeSet<_>>();
    let mut actual_macro_rule_disjunctions = BTreeSet::new();
    let mut actual_macro_repetition_disjunctions = BTreeSet::new();
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
                        WrittenUnitKind::ImplMember
                            | WrittenUnitKind::MacroInvocation
                            | WrittenUnitKind::MacroRule
                    ) && declarative_unit_kinds[choice.0 as usize]
                        != Some(DeclarativeSourceUnitKind::MatcherElement)
            })
            || !disjunction_keys.insert((disjunction.trigger, choices.clone()))
        {
            return Err(RetentionError::InvalidConstraint);
        }
        let contains_macro_rules = choices
            .iter()
            .any(|choice| source.units[choice.0 as usize].kind == WrittenUnitKind::MacroRule);
        let contains_macro_repetition_elements = choices.iter().any(|choice| {
            declarative_unit_kinds[choice.0 as usize]
                == Some(DeclarativeSourceUnitKind::MatcherElement)
        });
        if contains_macro_rules {
            if choices
                .iter()
                .any(|choice| source.units[choice.0 as usize].kind != WrittenUnitKind::MacroRule)
            {
                return Err(RetentionError::InvalidConstraint);
            }
            actual_macro_rule_disjunctions.insert((disjunction.trigger, choices.clone()));
        } else if contains_macro_repetition_elements {
            if choices.iter().any(|choice| {
                declarative_unit_kinds[choice.0 as usize]
                    != Some(DeclarativeSourceUnitKind::MatcherElement)
            }) {
                return Err(RetentionError::InvalidConstraint);
            }
            actual_macro_repetition_disjunctions.insert((disjunction.trigger, choices.clone()));
        }
        disjunctions.push(SourceDisjunction {
            trigger: disjunction.trigger,
            choices: choices.into_iter().collect(),
        });
    }
    if actual_macro_rule_disjunctions != expected_macro_rule_disjunctions
        || actual_macro_repetition_disjunctions != expected_macro_repetition_disjunctions
    {
        return Err(RetentionError::InvalidConstraint);
    }
    disjunctions.sort();
    let compiler_disjunctions = validate_external_crate_facts(
        source,
        graph,
        definition_units,
        &constraints.external_crates,
    )?;
    let preserve_active_source_triggers =
        validate_preserve_active_source_requirements(source, graph, definition_units)?
            .into_iter()
            .collect();
    let mut compiler_sources_by_trigger = BTreeMap::<GraphNode, Vec<SourceUnitId>>::new();
    for requirement in &macro_rule_selection_requirements {
        compiler_sources_by_trigger
            .entry(GraphNode::Expansion(requirement.expansion))
            .or_default()
            .push(requirement.rule);
    }
    let active_source_units = source
        .units
        .iter()
        .filter(|unit| unit.cfg_state == CfgState::Active)
        .map(|unit| unit.id)
        .collect();

    Ok(ValidatedConstraints {
        singleton_definition_units,
        singleton_definitions_by_source,
        atomic_groups: actual_groups
            .into_iter()
            .map(|group| group.into_iter().collect())
            .collect(),
        macro_rule_selection_requirements,
        macro_products,
        outputless_macro_expansions,
        ancestor_requirements: ancestors,
        shell_requirements: shells,
        derive_requirements: derives,
        macro_rule_requirements: macro_rules,
        compiler_members,
        disjunctions,
        compiler_disjunctions,
        compiler_sources_by_trigger,
        preserve_active_source_triggers,
        active_source_units,
    })
}

fn validate_preserve_active_source_requirements(
    source: &SourceInventory,
    graph: &DependencyGraph,
    definition_units: &[SourceUnitId],
) -> Result<Vec<GraphNode>, RetentionError> {
    let crate_definition = graph
        .definitions
        .definitions
        .iter()
        .find(|definition| definition.parent.is_none())
        .map(|definition| definition.id)
        .ok_or(RetentionError::IncompleteOpaqueSourceConstraints)?;
    let opaque_edges = graph
        .definitions
        .edges
        .iter()
        .filter(|edge| edge.kind == crate::graph::DependencyKind::OpaqueSource)
        .collect::<Vec<_>>();
    let triggers = opaque_edges
        .iter()
        .map(|edge| edge.from)
        .collect::<BTreeSet<_>>();
    if opaque_edges.iter().any(|edge| {
        let index = edge.from.0 as usize;
        let owner = definition_units
            .get(index)
            .and_then(|unit| source.units.get(unit.0 as usize));
        edge.to != DefinitionTarget::Local(crate_definition)
            || edge.sites.is_empty()
            || graph.definitions.definitions.get(index).is_none()
            || owner.is_none_or(|owner| {
                owner.cfg_state != CfgState::Active
                    || edge
                        .sites
                        .iter()
                        .any(|site| !owner.full_range.contains(*site))
            })
    }) {
        return Err(RetentionError::IncompleteOpaqueSourceConstraints);
    }
    Ok(triggers.into_iter().map(GraphNode::Definition).collect())
}

fn collect_macro_rule_selection_requirements(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    expansions: &[ExpansionNode],
) -> Result<Vec<MacroRuleSelectionRequirement>, RetentionError> {
    let rule_index = source
        .macro_rule_selection_index()
        .map_err(|_| RetentionError::InvalidConstraint)?;
    let refined_macro_definitions = refined_macro_definition_units(source);
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
        let Some(rule) = selected_macro_rule_unit(source, &rule_index, selected_range)? else {
            continue;
        };
        let requirement = MacroRuleSelectionRequirement {
            expansion: expansion.id,
            rule: rule.id,
        };
        if !macro_rule_requirement_matches(
            source,
            definitions,
            &refined_macro_definitions,
            expansion,
            requirement.rule,
        ) || !requirements.insert(requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }

    if macro_rule_selection_counts(requirements.iter().map(|requirement| requirement.rule))
        != observed_macro_rule_selection_counts(source)
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(requirements.into_iter().collect())
}

pub(crate) fn collect_declarative_macro_constraints(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    expansions: &[ExpansionNode],
    producer_coverage: MacroProducerCoverageInventory,
    complete_output_meaning: MacroCompleteOutputMeaningInventory,
    outputless_expansions: Vec<ExpansionId>,
) -> Result<DeclarativeMacroConstraints, RetentionError> {
    Ok(DeclarativeMacroConstraints {
        rule_selections: collect_macro_rule_selection_requirements(
            source,
            definitions,
            expansions,
        )?,
        producer_coverage,
        complete_output_meaning,
        outputless_expansions,
    })
}

fn selected_macro_rule_unit<'a>(
    source: &'a SourceInventory,
    rule_index: &MacroRuleSelectionIndex,
    selected_range: crate::source::ByteRange,
) -> Result<Option<&'a WrittenUnit>, RetentionError> {
    let Some(rule) = rule_index
        .selected_rule(selected_range)
        .map_err(|_| RetentionError::InvalidConstraint)?
    else {
        return Ok(None);
    };
    source
        .units
        .get(rule.0 as usize)
        .filter(|unit| {
            unit.id == rule
                && unit.kind == WrittenUnitKind::MacroRule
                && unit.cfg_state == CfgState::Active
                && unit.full_range == selected_range
        })
        .map(Some)
        .ok_or(RetentionError::InvalidConstraint)
}

fn refined_macro_definition_units(source: &SourceInventory) -> BTreeSet<SourceUnitId> {
    source
        .macro_rules
        .iter()
        .filter_map(|facts| match facts {
            MacroRuleSourceFacts::Whole { .. } => None,
            MacroRuleSourceFacts::Refined { definition, .. } => Some(*definition),
        })
        .collect()
}

fn validate_macro_rule_selection_requirements(
    source: &SourceInventory,
    graph: &DependencyGraph,
    refined_macro_definitions: &BTreeSet<SourceUnitId>,
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
                        refined_macro_definitions,
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
    definitions: &DefinitionGraph,
    refined_macro_definitions: &BTreeSet<SourceUnitId>,
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
    (definition.kind == DefinitionKind::Macro && refined_macro_definitions.contains(unit))
        .then_some(*unit)
}

fn macro_rule_requirement_matches(
    source: &SourceInventory,
    definitions: &DefinitionGraph,
    refined_macro_definitions: &BTreeSet<SourceUnitId>,
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
    macro_rule_selection_definition(definitions, refined_macro_definitions, expansion)
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
    retained_units: &BTreeSet<SourceUnitId>,
) -> Result<(), RetentionError> {
    if source.macro_rules.iter().any(|facts| match facts {
        MacroRuleSourceFacts::Whole { .. } => false,
        MacroRuleSourceFacts::Refined {
            definition, rules, ..
        } => {
            retained_units.contains(definition)
                && rules.iter().all(|rule| !retained_units.contains(rule))
        }
    }) {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(())
}

fn validate_compiler_member_constraints(
    graph: &DependencyGraph,
    constraints: &CompilerMemberConstraints,
) -> Result<ValidatedCompilerMemberConstraints, RetentionError> {
    let definition = |id: DefinitionId| {
        graph
            .definitions
            .definitions
            .get(id.0 as usize)
            .filter(|definition| definition.id == id)
    };
    let is_member = |kind: DefinitionKind| {
        matches!(
            kind,
            DefinitionKind::AssociatedType
                | DefinitionKind::AssociatedFunction
                | DefinitionKind::AssociatedConst
        )
    };

    let expected_members = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| {
            is_member(definition.kind)
                && matches!(
                    definition.origin,
                    DefinitionOrigin::Written { .. } | DefinitionOrigin::Expanded { .. }
                )
        })
        .map(|definition| definition.id)
        .collect::<BTreeSet<_>>();
    let actual_members = constraints
        .classified_members
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let expected_implementations = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::Impl)
        .map(|definition| definition.id)
        .collect::<BTreeSet<_>>();
    let actual_implementations = constraints
        .classified_implementations
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if actual_members != expected_members
        || actual_members.len() != constraints.classified_members.len()
        || actual_implementations != expected_implementations
        || actual_implementations.len() != constraints.classified_implementations.len()
    {
        return Err(RetentionError::IncompleteMemberConstraints);
    }

    let mut requirements = BTreeSet::new();
    for requirement in &constraints.requirements {
        let Some(trigger) = definition(requirement.trigger) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let Some(required) = definition(requirement.required) else {
            return Err(RetentionError::InvalidConstraint);
        };
        if trigger.id == required.id
            || !matches!(
                required.kind,
                DefinitionKind::Impl
                    | DefinitionKind::AssociatedType
                    | DefinitionKind::AssociatedFunction
                    | DefinitionKind::AssociatedConst
            )
            || !requirements.insert(*requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }

    let mut conditional_requirements = BTreeSet::new();
    for requirement in &constraints.conditional_requirements {
        let Some(left) = definition(requirement.left) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let Some(right) = definition(requirement.right) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let Some(required) = definition(requirement.required) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let right_parent = right.parent.and_then(definition);
        if left.kind != DefinitionKind::Impl
            || !is_member(right.kind)
            || right_parent.is_none_or(|parent| parent.kind != DefinitionKind::Trait)
            || !is_member(required.kind)
            || required.parent != Some(left.id)
            || requirement.left == requirement.right
            || requirement.required == requirement.left
            || requirement.required == requirement.right
            || !conditional_requirements.insert(*requirement)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }

    let mut disjunctions = BTreeSet::new();
    let mut triggers = BTreeSet::new();
    for disjunction in &constraints.disjunctions {
        let Some(trigger) = definition(disjunction.trigger) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let choices = disjunction.choices.iter().copied().collect::<BTreeSet<_>>();
        if trigger.kind != DefinitionKind::Impl
            || choices.is_empty()
            || choices.len() != disjunction.choices.len()
            || !triggers.insert(disjunction.trigger)
            || choices.iter().any(|choice| {
                definition(*choice).is_none_or(|choice| {
                    !is_member(choice.kind) || choice.parent != Some(disjunction.trigger)
                })
            })
        {
            return Err(RetentionError::InvalidConstraint);
        }
        disjunctions.insert(DefinitionDisjunction {
            trigger: disjunction.trigger,
            choices: choices.into_iter().collect(),
        });
    }

    let requirements = requirements.into_iter().collect::<Vec<_>>();
    let conditional_requirements = conditional_requirements.into_iter().collect::<Vec<_>>();
    let mut requirements_by_trigger = BTreeMap::<DefinitionId, Vec<DefinitionId>>::new();
    for requirement in &requirements {
        requirements_by_trigger
            .entry(requirement.trigger)
            .or_default()
            .push(requirement.required);
    }
    let mut conditional_by_trigger = BTreeMap::<DefinitionId, Vec<(usize, u8)>>::new();
    for (index, requirement) in conditional_requirements.iter().enumerate() {
        conditional_by_trigger
            .entry(requirement.left)
            .or_default()
            .push((index, 1));
        conditional_by_trigger
            .entry(requirement.right)
            .or_default()
            .push((index, 2));
    }
    Ok(ValidatedCompilerMemberConstraints {
        requirements_by_trigger,
        conditional_requirements,
        conditional_by_trigger,
        disjunctions: disjunctions.into_iter().collect(),
    })
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

/// Returns the source units which materialize definitions without a macro
/// product conjunction.  Expanded definitions, and compiler definitions
/// nested below them, deliberately have no singleton binding.
fn definition_singleton_source_units(
    graph: &DefinitionGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    definition_units: &[SourceUnitId],
    refined_macro_producers: &BTreeSet<ExpansionId>,
) -> Result<Vec<Option<SourceUnitId>>, RetentionError> {
    if graph.definitions.len() != definition_units.len() {
        return Err(RetentionError::InvalidGraph);
    }
    let mut states = vec![0_u8; graph.definitions.len()];
    let mut bindings = vec![None; graph.definitions.len()];
    for start in 0..graph.definitions.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        let binding = loop {
            match states.get(current).copied() {
                Some(2) => break bindings[current],
                Some(1) | None => return Err(RetentionError::InvalidGraph),
                Some(0) => {}
                _ => unreachable!(),
            }
            states[current] = 1;
            path.push(current);
            let definition = &graph.definitions[current];
            match definition.origin {
                DefinitionOrigin::Written { .. } => break Some(definition_units[current]),
                DefinitionOrigin::Expanded { .. } => {
                    let refined = macro_producers
                        .producer(definition.id)
                        .is_ok_and(|producer| refined_macro_producers.contains(&producer));
                    break (!refined).then_some(definition_units[current]);
                }
                DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => {
                    current = definition.parent.ok_or(RetentionError::InvalidGraph)?.0 as usize;
                }
            }
        };
        for index in path.into_iter().rev() {
            states[index] = 2;
            bindings[index] = binding;
        }
    }
    Ok(bindings)
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
                || invocation_range.is_empty()
                || !written.full_range.contains(*invocation_range)
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
                || unit.kind == WrittenUnitKind::InactiveCfgComponent
                    && (unit.cfg_state != CfgState::Inactive
                        || parent.cfg_state != CfgState::Active)
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
    validate_declarative_macro_source_facts(
        &source.original,
        &source.units,
        &source.macro_rules,
        &source.macro_templates,
        &source.macro_repetitions,
    )
    .map_err(|_| RetentionError::InvalidSource)?;
    validate_derive_target_facts(&source.units, &source.derive_targets)
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
mod tests;
