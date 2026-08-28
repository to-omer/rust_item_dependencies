use std::collections::{BTreeMap, BTreeSet};

use super::syntax::{Delimiter, SourceSyntaxError, comma_list_segments, tokenize_balanced_range};
#[cfg(rust_item_dependencies_patched)]
use super::{
    AttributeSource, collect_procedural_macro_observations, original_span_range,
    procedural_macro_observes_unit, resolve_procedural_macro_anchors,
    resolve_written_builtin_derive_outer,
};
use super::{
    ByteRange, CfgState, PendingUnit, SourceError, SourceInventory, SourceUnitId, WrittenUnit,
    WrittenUnitKind, derive_helper_owner, finish_pending_units, own_lexical_pieces, pending_units,
    valid_source_range, validate_inventory, validate_ownerless_attribute_invocations,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::FxHashMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::unord::UnordMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
use rustc_lexer::TokenKind;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{MacroImplementationKind, MacroInvocationOrigin, TyCtxt};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::{ExpnId, ExpnKind, MacroKind};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeriveAttributeSourceFacts {
    pub attribute: SourceUnitId,
    pub elements: Vec<SourceUnitId>,
    pub directly_written: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct DeriveSourceRequirement {
    pub trigger: SourceUnitId,
    pub required: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct DeriveHelperSourceFacts {
    pub attribute: SourceUnitId,
    pub provider: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ObservedDeriveHelper {
    pub range: ByteRange,
    pub provider: SourceUnitId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeriveTargetSourceFacts {
    Opaque {
        target: SourceUnitId,
        attributes: Vec<DeriveAttributeSourceFacts>,
        helper_candidates: Vec<ByteRange>,
    },
    Complete {
        target: SourceUnitId,
        attributes: Vec<DeriveAttributeSourceFacts>,
        helper_candidates: Vec<ByteRange>,
        influences: Vec<DeriveSourceRequirement>,
        helpers: Vec<DeriveHelperSourceFacts>,
    },
}

impl DeriveTargetSourceFacts {
    pub(crate) fn target(&self) -> SourceUnitId {
        match self {
            Self::Opaque { target, .. } | Self::Complete { target, .. } => *target,
        }
    }

    pub(crate) fn attributes(&self) -> &[DeriveAttributeSourceFacts] {
        match self {
            Self::Opaque { attributes, .. } | Self::Complete { attributes, .. } => attributes,
        }
    }

    pub(crate) fn helper_candidates(&self) -> &[ByteRange] {
        match self {
            Self::Opaque {
                helper_candidates, ..
            }
            | Self::Complete {
                helper_candidates, ..
            } => helper_candidates,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum DeriveTargetObservation {
    Opaque(SourceUnitId),
    Complete {
        target: SourceUnitId,
        influences: Vec<DeriveSourceRequirement>,
        helpers: Vec<ObservedDeriveHelper>,
    },
}

impl DeriveTargetObservation {
    fn target(&self) -> SourceUnitId {
        match self {
            Self::Opaque(target) | Self::Complete { target, .. } => *target,
        }
    }
}

pub(crate) fn refine_derive_targets(
    inventory: &mut SourceInventory,
    mut observations: Vec<DeriveTargetObservation>,
) -> Result<(), SourceError> {
    if !inventory.macro_rules.is_empty()
        || inventory
            .units
            .iter()
            .any(|unit| unit.kind == WrittenUnitKind::MacroRule)
        || inventory
            .derive_targets
            .iter()
            .any(|facts| matches!(facts, DeriveTargetSourceFacts::Complete { .. }))
    {
        return Err(SourceError::InvalidInventory);
    }
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;
    validate_derive_target_facts(&inventory.units, &inventory.derive_targets)?;
    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )?;

    observations.sort_by_key(|observation| observation.target());
    if observations
        .windows(2)
        .any(|pair| pair[0].target() == pair[1].target())
    {
        return Err(SourceError::IncompleteDeriveObservation);
    }
    let expected = inventory
        .derive_targets
        .iter()
        .map(DeriveTargetSourceFacts::target)
        .collect::<Vec<_>>();
    let observed = observations
        .iter()
        .map(|observation| observation.target())
        .collect::<Vec<_>>();
    if observed != expected {
        return Err(SourceError::IncompleteDeriveObservation);
    }

    for (facts, observation) in inventory.derive_targets.iter().zip(&observations) {
        let DeriveTargetObservation::Complete {
            influences,
            helpers,
            ..
        } = observation
        else {
            continue;
        };
        let target = &inventory.units[facts.target().0 as usize];
        if target.cfg_state != CfgState::Active
            || facts
                .attributes()
                .iter()
                .any(|attribute| !attribute.directly_written)
            || facts
                .helper_candidates()
                .iter()
                .any(|range| !valid_source_range(&inventory.original, *range))
        {
            return Err(SourceError::IncompleteDeriveObservation);
        }
        for attribute in facts.attributes() {
            let attribute_unit = &inventory.units[attribute.attribute.0 as usize];
            let element_ranges = attribute
                .elements
                .iter()
                .map(|element| inventory.units[element.0 as usize].full_range)
                .collect::<Vec<_>>();
            derive_attribute_layout(
                &inventory.original,
                attribute_unit.full_range,
                &element_ranges,
            )?;
        }

        let elements = facts
            .attributes()
            .iter()
            .flat_map(|attribute| attribute.elements.iter().copied())
            .collect::<BTreeSet<_>>();
        let helper_ranges = helpers
            .iter()
            .map(|helper| helper.range)
            .collect::<BTreeSet<_>>();
        if influences.windows(2).any(|pair| pair[0] >= pair[1])
            || influences.iter().any(|requirement| {
                !elements.contains(&requirement.trigger)
                    || !elements.contains(&requirement.required)
            })
            || helpers.windows(2).any(|pair| pair[0] >= pair[1])
            || helper_ranges.len() != helpers.len()
            || helpers.iter().any(|helper| {
                !elements.contains(&helper.provider)
                    || facts
                        .helper_candidates()
                        .binary_search(&helper.range)
                        .is_err()
                    || !target.full_range.contains(helper.range)
                    || !valid_source_range(&inventory.original, helper.range)
                    || helper.range.is_empty()
            })
        {
            return Err(SourceError::IncompleteDeriveObservation);
        }
    }

    let (mut pending, _) = pending_units(&inventory.units);
    let mut next_temporary =
        u32::try_from(pending.len()).map_err(|_| SourceError::SourceTooLarge)?;
    let mut pending_dependencies = BTreeMap::new();
    for (facts, observation) in inventory.derive_targets.iter().zip(&observations) {
        let DeriveTargetObservation::Complete {
            influences,
            helpers,
            ..
        } = observation
        else {
            continue;
        };
        for attribute in facts.attributes() {
            let attribute_unit = pending
                .get_mut(attribute.attribute.0 as usize)
                .ok_or(SourceError::InvalidInventory)?;
            if attribute_unit.temporary_id != attribute.attribute.0 {
                return Err(SourceError::InvalidInventory);
            }
            attribute_unit.atomic_representative = attribute_unit.temporary_id;
            for element in &attribute.elements {
                let element_unit = pending
                    .get_mut(element.0 as usize)
                    .ok_or(SourceError::InvalidInventory)?;
                if element_unit.temporary_id != element.0 {
                    return Err(SourceError::InvalidInventory);
                }
                element_unit.atomic_representative = element_unit.temporary_id;
            }
        }
        let mut pending_helpers = Vec::new();
        for helper in helpers {
            let owner = derive_helper_owner(&inventory.units, facts.target(), helper.range, None)?;
            let attribute = next_temporary;
            next_temporary = next_temporary
                .checked_add(1)
                .ok_or(SourceError::SourceTooLarge)?;
            pending.push(PendingUnit {
                temporary_id: attribute,
                kind: WrittenUnitKind::MacroInvocation,
                full_range: helper.range,
                parent: Some(owner.0),
                cfg_state: CfgState::Active,
                atomic_representative: attribute,
                syntax_ordinal: attribute,
            });
            pending_helpers.push((attribute, helper.provider.0));
        }
        if pending_dependencies
            .insert(facts.target().0, (influences.clone(), pending_helpers))
            .is_some()
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    let (units, id_map) = finish_pending_units(pending)?;
    let mut derive_targets = remap_derive_target_facts(&inventory.derive_targets, &id_map)?;
    let mut complete_dependencies = BTreeMap::new();
    for (target, (influences, helpers)) in pending_dependencies {
        let target = *id_map.get(&target).ok_or(SourceError::InvalidInventory)?;
        let mut influences = influences
            .into_iter()
            .map(|requirement| {
                Ok(DeriveSourceRequirement {
                    trigger: *id_map
                        .get(&requirement.trigger.0)
                        .ok_or(SourceError::InvalidInventory)?,
                    required: *id_map
                        .get(&requirement.required.0)
                        .ok_or(SourceError::InvalidInventory)?,
                })
            })
            .collect::<Result<Vec<_>, SourceError>>()?;
        influences.sort();
        influences.dedup();
        let mut helpers = helpers
            .into_iter()
            .map(|(attribute, provider)| {
                Ok(DeriveHelperSourceFacts {
                    attribute: *id_map
                        .get(&attribute)
                        .ok_or(SourceError::InvalidInventory)?,
                    provider: *id_map.get(&provider).ok_or(SourceError::InvalidInventory)?,
                })
            })
            .collect::<Result<Vec<_>, SourceError>>()?;
        helpers.sort();
        if complete_dependencies
            .insert(target, (influences, helpers))
            .is_some()
        {
            return Err(SourceError::InvalidInventory);
        }
    }
    for facts in &mut derive_targets {
        let Some((influences, helpers)) = complete_dependencies.remove(&facts.target()) else {
            continue;
        };
        let DeriveTargetSourceFacts::Opaque {
            target,
            attributes,
            helper_candidates,
        } = facts
        else {
            return Err(SourceError::InvalidInventory);
        };
        *facts = DeriveTargetSourceFacts::Complete {
            target: *target,
            attributes: std::mem::take(attributes),
            helper_candidates: std::mem::take(helper_candidates),
            influences,
            helpers,
        };
    }
    if !complete_dependencies.is_empty() {
        return Err(SourceError::InvalidInventory);
    }
    let mut ownerless_attribute_invocations = inventory
        .ownerless_attribute_invocations
        .iter()
        .map(|invocation| id_map[&invocation.0])
        .collect::<Vec<_>>();
    ownerless_attribute_invocations.sort();
    let pieces = own_lexical_pieces(&inventory.original, &units)?;
    validate_inventory(&inventory.original, &units, &pieces)?;
    validate_derive_target_facts(&units, &derive_targets)?;
    validate_ownerless_attribute_invocations(&units, &ownerless_attribute_invocations)?;
    inventory.units = units;
    inventory.pieces = pieces;
    inventory.derive_targets = derive_targets;
    inventory.ownerless_attribute_invocations = ownerless_attribute_invocations;
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
struct DirectDeriveCompilerIndex {
    outer_sources: FxHashMap<ExpnId, AttributeSource>,
    outers_by_target: BTreeMap<SourceUnitId, Vec<ExpnId>>,
    outers_by_attribute: BTreeMap<SourceUnitId, Vec<ExpnId>>,
    children_by_outer: FxHashMap<ExpnId, Vec<ExpnId>>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeriveObservationCounts {
    children: usize,
    output_influences: usize,
    helper_uses: usize,
}

#[cfg(rust_item_dependencies_patched)]
fn derive_observation_is_complete(
    witness: Option<(bool, DeriveObservationCounts)>,
    observed: DeriveObservationCounts,
) -> bool {
    witness.is_some_and(|(complete, expected)| complete && expected == observed)
}

#[cfg(rust_item_dependencies_patched)]
fn derive_target_census_is_complete(
    globally_complete: bool,
    inventory_targets: &BTreeSet<SourceUnitId>,
    compiler_targets: &BTreeSet<SourceUnitId>,
) -> bool {
    globally_complete && compiler_targets.is_subset(inventory_targets)
}

#[cfg(rust_item_dependencies_patched)]
fn observed_derive_requirement(
    target: Option<SourceUnitId>,
    dependent: Option<(SourceUnitId, SourceUnitId)>,
    provider: Option<(SourceUnitId, SourceUnitId)>,
) -> Result<(SourceUnitId, DeriveSourceRequirement), BTreeSet<SourceUnitId>> {
    match (target, dependent, provider) {
        (Some(target), Some((dependent_target, dependent)), Some((provider_target, provider)))
            if target == dependent_target && target == provider_target =>
        {
            Ok((
                target,
                DeriveSourceRequirement {
                    trigger: dependent,
                    required: provider,
                },
            ))
        }
        (target, dependent, provider) => Err(target
            .into_iter()
            .chain(dependent.map(|(target, _)| target))
            .chain(provider.map(|(target, _)| target))
            .collect()),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn observed_derive_helper(
    target: Option<SourceUnitId>,
    range: Option<ByteRange>,
    provider: Option<(SourceUnitId, SourceUnitId)>,
    candidates: Option<&[ByteRange]>,
) -> Result<(SourceUnitId, ObservedDeriveHelper), BTreeSet<SourceUnitId>> {
    match (target, range, provider) {
        (Some(target), Some(range), Some((provider_target, provider)))
            if target == provider_target
                && candidates
                    .is_some_and(|candidates| candidates.binary_search(&range).is_ok()) =>
        {
            Ok((target, ObservedDeriveHelper { range, provider }))
        }
        (target, _, provider) => Err(target
            .into_iter()
            .chain(provider.map(|(target, _)| target))
            .collect()),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn direct_derive_compiler_index(
    compiler: &Compiler,
    inventory: &SourceInventory,
    origins: &UnordMap<ExpnId, MacroInvocationOrigin>,
) -> Result<DirectDeriveCompilerIndex, SourceError> {
    let mut index = DirectDeriveCompilerIndex {
        outer_sources: FxHashMap::default(),
        outers_by_target: BTreeMap::new(),
        outers_by_attribute: BTreeMap::new(),
        children_by_outer: FxHashMap::default(),
    };
    let sorted_origins = origins
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    for (_, expansion, origin) in sorted_origins {
        if matches!(
            expansion.expn_data().kind,
            ExpnKind::Macro(MacroKind::Derive, _)
        ) {
            index
                .children_by_outer
                .entry(origin.discovered_in_expansion)
                .or_default()
                .push(expansion);
        }
        if !matches!(
            expansion.expn_data().kind,
            ExpnKind::Macro(MacroKind::Attr, _)
        ) {
            continue;
        }
        let Some(resolved) =
            resolve_written_builtin_derive_outer(compiler, inventory, origins, expansion)?
        else {
            continue;
        };
        let source = resolved.source;
        if index.outer_sources.insert(expansion, source).is_some() {
            return Err(SourceError::IncompleteDeriveObservation);
        }
        index
            .outers_by_target
            .entry(source.target)
            .or_default()
            .push(expansion);
        if let Some(attribute) = source.invocation {
            index
                .outers_by_attribute
                .entry(attribute)
                .or_default()
                .push(expansion);
        }
    }

    Ok(index)
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn refine_derive_targets_from_compiler(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &mut SourceInventory,
) -> Result<(), SourceError> {
    let procedural = collect_procedural_macro_observations(compiler, tcx, inventory)?;
    let procedural_anchors = resolve_procedural_macro_anchors(inventory, procedural)?;
    let resolutions = tcx.resolutions(());
    let origins = &resolutions.macro_invocation_origins;
    let index = direct_derive_compiler_index(compiler, inventory, origins)?;
    let inventory_targets = inventory
        .derive_targets
        .iter()
        .map(DeriveTargetSourceFacts::target)
        .collect::<BTreeSet<_>>();
    let compiler_targets = index
        .outers_by_target
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    if !derive_target_census_is_complete(
        resolutions.derive_observations_complete,
        &inventory_targets,
        &compiler_targets,
    ) {
        return Err(SourceError::IncompleteDeriveObservation);
    }
    let output_influences = resolutions
        .derive_output_influences
        .items()
        .map(|influence| {
            (
                (
                    influence.target_expansion.expn_hash().local_hash().as_u64(),
                    influence
                        .dependent_expansion
                        .expn_hash()
                        .local_hash()
                        .as_u64(),
                    influence
                        .provider_expansion
                        .expn_hash()
                        .local_hash()
                        .as_u64(),
                ),
                *influence,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    let mut output_influences_by_outer = FxHashMap::default();
    for (_, influence) in &output_influences {
        output_influences_by_outer
            .entry(influence.target_expansion)
            .or_insert_with(Vec::new)
            .push(*influence);
    }
    let helper_uses = resolutions
        .derive_helper_uses
        .items()
        .map(|helper| {
            let provider = helper
                .provider_expansion
                .map(|expansion| expansion.expn_hash().local_hash().as_u64());
            (
                (
                    helper.target_expansion.expn_hash().local_hash().as_u64(),
                    u8::from(provider.is_some()),
                    provider.unwrap_or_default(),
                    (helper.use_span.lo().0, helper.use_span.hi().0),
                ),
                *helper,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    let mut helper_uses_by_outer = FxHashMap::default();
    for (_, helper) in &helper_uses {
        helper_uses_by_outer
            .entry(helper.target_expansion)
            .or_insert_with(Vec::new)
            .push(*helper);
    }
    let mut opaque_targets = BTreeSet::new();
    let mut complete_children = BTreeMap::<SourceUnitId, FxHashMap<ExpnId, SourceUnitId>>::new();

    for facts in &inventory.derive_targets {
        let target = inventory
            .units
            .get(facts.target().0 as usize)
            .ok_or(SourceError::InvalidInventory)?;
        let opaque = target.cfg_state != CfgState::Active
            || facts
                .attributes()
                .iter()
                .any(|attribute| !attribute.directly_written)
            || procedural_anchors.iter().any(|anchor| {
                anchor.range.contains(target.full_range)
                    && procedural_macro_observes_unit(*anchor, target)
            });
        if opaque {
            opaque_targets.insert(target.id);
            continue;
        }

        let child_elements = (|| -> Option<FxHashMap<ExpnId, SourceUnitId>> {
            let expected_attributes = facts
                .attributes()
                .iter()
                .map(|attribute| attribute.attribute)
                .collect::<BTreeSet<_>>();
            let target_outers = index.outers_by_target.get(&target.id)?;
            let observed_attributes = target_outers
                .iter()
                .map(|outer| index.outer_sources.get(outer)?.invocation)
                .collect::<Option<BTreeSet<_>>>()?;
            if target_outers.len() != expected_attributes.len()
                || observed_attributes != expected_attributes
            {
                return None;
            }

            let mut child_elements = FxHashMap::default();
            for attribute in facts.attributes() {
                let outers = index.outers_by_attribute.get(&attribute.attribute)?;
                let [outer] = outers.as_slice() else {
                    return None;
                };
                if index.outer_sources.get(outer)?.target != target.id {
                    return None;
                }
                let children = index
                    .children_by_outer
                    .get(outer)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                let witness = resolutions
                    .derive_observation_witnesses
                    .get(outer)
                    .map(|witness| {
                        (
                            witness.complete,
                            DeriveObservationCounts {
                                children: witness.child_count,
                                output_influences: witness.output_influence_count,
                                helper_uses: witness.helper_use_count,
                            },
                        )
                    });
                let observed = DeriveObservationCounts {
                    children: children.len(),
                    output_influences: output_influences_by_outer.get(outer).map_or(0, Vec::len),
                    helper_uses: helper_uses_by_outer.get(outer).map_or(0, Vec::len),
                };
                if !derive_observation_is_complete(witness, observed)
                    || children.len() != attribute.elements.len()
                {
                    return None;
                }

                let mut observed_indices = BTreeSet::new();
                for child in children {
                    let origin = origins.get(child)?;
                    if origin.implementation_kind != MacroImplementationKind::Builtin {
                        return None;
                    }
                    let source_index = origin.derive_source_index?;
                    let element = attribute.elements.get(source_index).copied()?;
                    let call_range = original_span_range(
                        compiler,
                        &inventory.offsets,
                        child.expn_data().call_site,
                    )
                    .ok()?;
                    if call_range != inventory.units[element.0 as usize].full_range
                        || !observed_indices.insert(source_index)
                        || child_elements.insert(*child, element).is_some()
                    {
                        return None;
                    }
                }
                if observed_indices.len() != attribute.elements.len() {
                    return None;
                }
            }
            Some(child_elements)
        })();
        let Some(child_elements) = child_elements else {
            opaque_targets.insert(target.id);
            continue;
        };
        complete_children.insert(target.id, child_elements);
    }

    let mut child_sources = FxHashMap::default();
    for (&target, children) in &complete_children {
        for (&expansion, &element) in children {
            if child_sources.insert(expansion, (target, element)).is_some() {
                return Err(SourceError::IncompleteDeriveObservation);
            }
        }
    }
    let mut influences = BTreeMap::<SourceUnitId, BTreeSet<DeriveSourceRequirement>>::new();
    for (_, influence) in output_influences {
        let target = index
            .outer_sources
            .get(&influence.target_expansion)
            .map(|source| source.target);
        let dependent = child_sources.get(&influence.dependent_expansion).copied();
        let provider = child_sources.get(&influence.provider_expansion).copied();
        match observed_derive_requirement(target, dependent, provider) {
            Ok((target, requirement)) => {
                influences.entry(target).or_default().insert(requirement);
            }
            Err(targets) => opaque_targets.extend(targets),
        }
    }

    let helper_candidates_by_target = inventory
        .derive_targets
        .iter()
        .map(|facts| (facts.target(), facts.helper_candidates()))
        .collect::<BTreeMap<_, _>>();
    let mut helpers = BTreeMap::<SourceUnitId, BTreeSet<ObservedDeriveHelper>>::new();
    let mut helper_ranges = BTreeMap::<SourceUnitId, BTreeSet<ByteRange>>::new();
    for (_, helper) in helper_uses {
        let target = index
            .outer_sources
            .get(&helper.target_expansion)
            .map(|source| source.target);
        let range = original_span_range(compiler, &inventory.offsets, helper.use_span).ok();
        let provider = helper
            .provider_expansion
            .and_then(|expansion| child_sources.get(&expansion).copied());
        let candidates =
            target.and_then(|target| helper_candidates_by_target.get(&target).copied());
        match observed_derive_helper(target, range, provider, candidates) {
            Ok((target, helper)) => {
                if helper_ranges
                    .entry(target)
                    .or_default()
                    .insert(helper.range)
                {
                    helpers.entry(target).or_default().insert(helper);
                } else {
                    opaque_targets.insert(target);
                }
            }
            Err(targets) => opaque_targets.extend(targets),
        }
    }

    let observations = inventory
        .derive_targets
        .iter()
        .map(|facts| {
            let target = facts.target();
            if opaque_targets.contains(&target) {
                Ok(DeriveTargetObservation::Opaque(target))
            } else {
                if !complete_children.contains_key(&target) {
                    return Err(SourceError::IncompleteDeriveObservation);
                }
                Ok(DeriveTargetObservation::Complete {
                    target,
                    influences: influences
                        .remove(&target)
                        .unwrap_or_default()
                        .into_iter()
                        .collect(),
                    helpers: helpers
                        .remove(&target)
                        .unwrap_or_default()
                        .into_iter()
                        .collect(),
                })
            }
        })
        .collect::<Result<Vec<_>, SourceError>>()?;

    refine_derive_targets(inventory, observations)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DeriveListEntryLayout {
    pub element: ByteRange,
    pub segment: ByteRange,
    pub previous_comma: Option<ByteRange>,
    pub following_comma: Option<ByteRange>,
}

pub(crate) fn derive_attribute_layout(
    source: &str,
    attribute: ByteRange,
    elements: &[ByteRange],
) -> Result<Vec<DeriveListEntryLayout>, SourceError> {
    if !valid_source_range(source, attribute)
        || attribute.is_empty()
        || elements.iter().any(|element| {
            element.is_empty()
                || !attribute.contains(*element)
                || !valid_source_range(source, *element)
        })
        || elements.windows(2).any(|pair| pair[0].end > pair[1].start)
    {
        return Err(SourceError::IncompleteDeriveObservation);
    }
    let (tokens, pairs) =
        tokenize_balanced_range(source, attribute).map_err(|error| match error {
            SourceSyntaxError::SourceTooLarge => SourceError::SourceTooLarge,
            SourceSyntaxError::InvalidRange | SourceSyntaxError::InvalidSyntax => {
                SourceError::IncompleteDeriveObservation
            }
        })?;

    let mut containers = pairs
        .iter()
        .filter_map(|pair| {
            if pair.delimiter != Delimiter::Parenthesis {
                return None;
            }
            let interior = ByteRange {
                start: tokens[pair.open].range.end,
                end: tokens[pair.close].range.start,
            };
            elements
                .iter()
                .all(|element| interior.contains(*element))
                .then_some((interior.len(), *pair))
        })
        .collect::<Vec<_>>();
    containers.sort_by_key(|(size, pair)| (*size, pair.open, pair.close));
    let Some(&(smallest, pair)) = containers.first() else {
        return Err(SourceError::IncompleteDeriveObservation);
    };
    if containers
        .get(1)
        .is_some_and(|candidate| candidate.0 == smallest)
    {
        return Err(SourceError::IncompleteDeriveObservation);
    }

    let segments =
        comma_list_segments(&tokens, pair).map_err(|_| SourceError::IncompleteDeriveObservation)?;
    let comma_count = segments
        .len()
        .checked_sub(1)
        .ok_or(SourceError::IncompleteDeriveObservation)?;
    if !matches!(comma_count, count if count == elements.len().saturating_sub(1) || count == elements.len())
    {
        return Err(SourceError::IncompleteDeriveObservation);
    }

    let mut assigned = BTreeSet::new();
    let mut layout = Vec::with_capacity(elements.len());
    for (segment_index, list_segment) in segments.into_iter().enumerate() {
        let segment = list_segment.range;
        let in_segment = elements
            .iter()
            .copied()
            .filter(|element| segment.contains(*element))
            .collect::<Vec<_>>();
        let element = match in_segment.as_slice() {
            [] if segment_index == elements.len() && comma_count == elements.len() => None,
            [element] => Some(*element),
            _ => return Err(SourceError::IncompleteDeriveObservation),
        };
        if let Some(element) = element
            && !assigned.insert(element)
        {
            return Err(SourceError::IncompleteDeriveObservation);
        }
        if tokens.iter().any(|token| {
            segment.contains(token.range)
                && !matches!(
                    token.kind,
                    TokenKind::Whitespace
                        | TokenKind::LineComment { .. }
                        | TokenKind::BlockComment { .. }
                )
                && element.is_none_or(|element| !element.contains(token.range))
        }) {
            return Err(SourceError::IncompleteDeriveObservation);
        }
        if let Some(element) = element {
            layout.push(DeriveListEntryLayout {
                element,
                segment,
                previous_comma: list_segment.previous_comma,
                following_comma: list_segment.following_comma,
            });
        }
    }
    if assigned.len() != elements.len() {
        return Err(SourceError::IncompleteDeriveObservation);
    }
    layout.sort_by_key(|entry| entry.element);
    Ok(layout)
}

pub(crate) fn validate_derive_target_facts(
    units: &[WrittenUnit],
    derive_targets: &[DeriveTargetSourceFacts],
) -> Result<(), SourceError> {
    if derive_targets
        .windows(2)
        .any(|pair| pair[0].target() >= pair[1].target())
    {
        return Err(SourceError::InvalidInventory);
    }

    let mut attributes_seen = BTreeSet::new();
    let mut elements_seen = BTreeSet::new();
    let mut helper_attributes = BTreeSet::new();
    for facts in derive_targets {
        let target = units
            .get(facts.target().0 as usize)
            .filter(|unit| unit.id == facts.target())
            .ok_or(SourceError::InvalidInventory)?;
        if !matches!(
            target.kind,
            WrittenUnitKind::Item
                | WrittenUnitKind::NestedItem
                | WrittenUnitKind::InlineModule
                | WrittenUnitKind::MacroInvocation
        ) || facts.attributes().is_empty()
            || facts
                .helper_candidates()
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || facts
                .helper_candidates()
                .iter()
                .any(|candidate| candidate.is_empty() || !target.full_range.contains(*candidate))
        {
            return Err(SourceError::InvalidInventory);
        }

        let mut previous_attribute = None;
        let mut refined_groups = BTreeSet::from([target.atomic_group]);
        let mut target_elements = BTreeSet::new();
        for attribute_facts in facts.attributes() {
            let attribute = units
                .get(attribute_facts.attribute.0 as usize)
                .ok_or(SourceError::InvalidInventory)?;
            if attribute.kind != WrittenUnitKind::MacroInvocation
                || attribute.parent != Some(target.id)
                || attribute.cfg_state != target.cfg_state
                || !attributes_seen.insert(attribute.id)
                || previous_attribute
                    .is_some_and(|previous: ByteRange| previous.end > attribute.full_range.start)
                || (!attribute_facts.directly_written && !attribute_facts.elements.is_empty())
            {
                return Err(SourceError::InvalidInventory);
            }
            previous_attribute = Some(attribute.full_range);
            if facts.helper_candidates().iter().any(|candidate| {
                candidate.start < attribute.full_range.end
                    && attribute.full_range.start < candidate.end
            }) {
                return Err(SourceError::InvalidInventory);
            }

            let mut previous_element = None;
            for &element_id in &attribute_facts.elements {
                let element = units
                    .get(element_id.0 as usize)
                    .ok_or(SourceError::InvalidInventory)?;
                if element.kind != WrittenUnitKind::MacroInvocation
                    || element.parent != Some(attribute.id)
                    || element.cfg_state != target.cfg_state
                    || element.full_range.is_empty()
                    || !elements_seen.insert(element.id)
                    || !target_elements.insert(element.id)
                    || previous_element
                        .is_some_and(|previous: ByteRange| previous.end > element.full_range.start)
                {
                    return Err(SourceError::InvalidInventory);
                }
                previous_element = Some(element.full_range);
            }

            match facts {
                DeriveTargetSourceFacts::Opaque { .. } => {
                    if attribute.atomic_group != target.atomic_group
                        || attribute_facts.elements.iter().any(|element| {
                            units[element.0 as usize].atomic_group != target.atomic_group
                        })
                    {
                        return Err(SourceError::InvalidInventory);
                    }
                }
                DeriveTargetSourceFacts::Complete { .. } => {
                    if target.cfg_state != CfgState::Active
                        || !attribute_facts.directly_written
                        || !refined_groups.insert(attribute.atomic_group)
                        || attribute_facts.elements.iter().any(|element| {
                            !refined_groups.insert(units[element.0 as usize].atomic_group)
                        })
                    {
                        return Err(SourceError::InvalidInventory);
                    }
                }
            }
        }
        let DeriveTargetSourceFacts::Complete {
            influences,
            helpers,
            ..
        } = facts
        else {
            continue;
        };
        if influences.windows(2).any(|pair| pair[0] >= pair[1])
            || helpers.windows(2).any(|pair| pair[0] >= pair[1])
            || influences.iter().any(|requirement| {
                !target_elements.contains(&requirement.trigger)
                    || !target_elements.contains(&requirement.required)
            })
        {
            return Err(SourceError::InvalidInventory);
        }

        for helper in helpers {
            let attribute = units
                .get(helper.attribute.0 as usize)
                .filter(|unit| unit.id == helper.attribute)
                .ok_or(SourceError::InvalidInventory)?;
            let owner =
                derive_helper_owner(units, target.id, attribute.full_range, Some(attribute.id))
                    .map_err(|_| SourceError::InvalidInventory)?;
            if !target_elements.contains(&helper.provider)
                || attribute.kind != WrittenUnitKind::MacroInvocation
                || attribute.parent != Some(owner)
                || attribute.cfg_state != CfgState::Active
                || attribute.atomic_group == units[owner.0 as usize].atomic_group
                || !target.full_range.contains(attribute.full_range)
                || facts
                    .helper_candidates()
                    .binary_search(&attribute.full_range)
                    .is_err()
                || !helper_attributes.insert(attribute.id)
            {
                return Err(SourceError::InvalidInventory);
            }
        }
    }
    Ok(())
}

pub(super) fn remap_derive_target_facts(
    derive_targets: &[DeriveTargetSourceFacts],
    id_map: &BTreeMap<u32, SourceUnitId>,
) -> Result<Vec<DeriveTargetSourceFacts>, SourceError> {
    let mut remapped = Vec::with_capacity(derive_targets.len());
    for facts in derive_targets {
        let Some(&target) = id_map.get(&facts.target().0) else {
            if matches!(facts, DeriveTargetSourceFacts::Complete { .. }) {
                return Err(SourceError::InvalidInventory);
            }
            continue;
        };
        if facts.attributes().iter().any(|attribute| {
            !id_map.contains_key(&attribute.attribute.0)
                || attribute
                    .elements
                    .iter()
                    .any(|element| !id_map.contains_key(&element.0))
        }) {
            if matches!(facts, DeriveTargetSourceFacts::Complete { .. }) {
                return Err(SourceError::InvalidInventory);
            }
            continue;
        }
        let attributes = facts
            .attributes()
            .iter()
            .map(|attribute| DeriveAttributeSourceFacts {
                attribute: id_map[&attribute.attribute.0],
                elements: attribute
                    .elements
                    .iter()
                    .map(|element| id_map[&element.0])
                    .collect(),
                directly_written: attribute.directly_written,
            })
            .collect();
        let helper_candidates = facts.helper_candidates().to_vec();
        remapped.push(match facts {
            DeriveTargetSourceFacts::Opaque { .. } => DeriveTargetSourceFacts::Opaque {
                target,
                attributes,
                helper_candidates,
            },
            DeriveTargetSourceFacts::Complete {
                influences,
                helpers,
                ..
            } => {
                let mut influences = influences
                    .iter()
                    .map(|requirement| {
                        Ok(DeriveSourceRequirement {
                            trigger: *id_map
                                .get(&requirement.trigger.0)
                                .ok_or(SourceError::InvalidInventory)?,
                            required: *id_map
                                .get(&requirement.required.0)
                                .ok_or(SourceError::InvalidInventory)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SourceError>>()?;
                influences.sort();
                influences.dedup();
                let mut helpers = helpers
                    .iter()
                    .map(|helper| {
                        Ok(DeriveHelperSourceFacts {
                            attribute: *id_map
                                .get(&helper.attribute.0)
                                .ok_or(SourceError::InvalidInventory)?,
                            provider: *id_map
                                .get(&helper.provider.0)
                                .ok_or(SourceError::InvalidInventory)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SourceError>>()?;
                helpers.sort();
                if helpers.windows(2).any(|pair| pair[0] == pair[1]) {
                    return Err(SourceError::InvalidInventory);
                }
                DeriveTargetSourceFacts::Complete {
                    target,
                    attributes,
                    helper_candidates,
                    influences,
                    helpers,
                }
            }
        });
    }
    remapped.sort_by_key(DeriveTargetSourceFacts::target);
    Ok(remapped)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use super::super::{
        AtomicGroupId, ByteRange, CfgState, OriginalOffsetMap, SourceError, SourceInventory,
        SourceUnitId, WrittenUnit, WrittenUnitKind, own_lexical_pieces,
    };
    use super::{
        DeriveAttributeSourceFacts, DeriveSourceRequirement, DeriveTargetObservation,
        DeriveTargetSourceFacts, ObservedDeriveHelper, refine_derive_targets,
    };
    #[cfg(rust_item_dependencies_patched)]
    use super::{
        DeriveObservationCounts, derive_observation_is_complete, derive_target_census_is_complete,
        observed_derive_helper, observed_derive_requirement,
    };

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn compiler_derive_observation_matcher_fails_closed() {
        let observed = DeriveObservationCounts {
            children: 2,
            output_influences: 1,
            helper_uses: 1,
        };
        assert!(derive_observation_is_complete(
            Some((true, observed)),
            observed
        ));
        assert!(!derive_observation_is_complete(None, observed));
        assert!(!derive_observation_is_complete(
            Some((false, observed)),
            observed
        ));
        for incomplete in [
            DeriveObservationCounts {
                children: 1,
                ..observed
            },
            DeriveObservationCounts {
                output_influences: 0,
                ..observed
            },
            DeriveObservationCounts {
                helper_uses: 0,
                ..observed
            },
        ] {
            assert!(!derive_observation_is_complete(
                Some((true, incomplete)),
                observed
            ));
        }

        assert!(derive_target_census_is_complete(
            true,
            &BTreeSet::from([SourceUnitId(1), SourceUnitId(2)]),
            &BTreeSet::from([SourceUnitId(1)])
        ));
        assert!(!derive_target_census_is_complete(
            false,
            &BTreeSet::from([SourceUnitId(1)]),
            &BTreeSet::from([SourceUnitId(1)])
        ));
        assert!(!derive_target_census_is_complete(
            true,
            &BTreeSet::from([SourceUnitId(1)]),
            &BTreeSet::from([SourceUnitId(1), SourceUnitId(2)])
        ));

        assert_eq!(
            observed_derive_requirement(
                Some(SourceUnitId(1)),
                Some((SourceUnitId(1), SourceUnitId(10))),
                Some((SourceUnitId(1), SourceUnitId(11))),
            ),
            Ok((
                SourceUnitId(1),
                DeriveSourceRequirement {
                    trigger: SourceUnitId(10),
                    required: SourceUnitId(11),
                }
            ))
        );
        assert_eq!(
            observed_derive_requirement(
                Some(SourceUnitId(1)),
                Some((SourceUnitId(1), SourceUnitId(10))),
                Some((SourceUnitId(2), SourceUnitId(11))),
            ),
            Err(BTreeSet::from([SourceUnitId(1), SourceUnitId(2)]))
        );

        let helper_range = ByteRange { start: 20, end: 30 };
        assert_eq!(
            observed_derive_helper(
                Some(SourceUnitId(1)),
                Some(helper_range),
                Some((SourceUnitId(1), SourceUnitId(11))),
                Some(&[helper_range]),
            ),
            Ok((
                SourceUnitId(1),
                ObservedDeriveHelper {
                    range: helper_range,
                    provider: SourceUnitId(11),
                }
            ))
        );
        assert_eq!(
            observed_derive_helper(
                Some(SourceUnitId(1)),
                Some(helper_range),
                Some((SourceUnitId(1), SourceUnitId(11))),
                Some(&[]),
            ),
            Err(BTreeSet::from([SourceUnitId(1)]))
        );
    }

    #[test]
    fn derive_targets_split_only_after_a_complete_target_census() {
        let source = Arc::<str>::from(
            "#[derive(Clone, Debug)]\nstruct A;\n#[cfg_attr(all(), derive(Default))]\nstruct B;\n",
        );
        let first_target = marker(&source, "#[derive(Clone, Debug)]\nstruct A;");
        let first_attribute = marker(&source, "#[derive(Clone, Debug)]");
        let clone = marker(&source, "Clone");
        let debug = marker(&source, "Debug");
        let second_target = marker(&source, "#[cfg_attr(all(), derive(Default))]\nstruct B;");
        let second_attribute = marker(&source, "#[cfg_attr(all(), derive(Default))]");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::Item, first_target, Some(0), 1),
            unit(
                2,
                WrittenUnitKind::MacroInvocation,
                first_attribute,
                Some(1),
                1,
            ),
            unit(3, WrittenUnitKind::MacroInvocation, clone, Some(2), 1),
            unit(4, WrittenUnitKind::MacroInvocation, debug, Some(2), 1),
            unit(5, WrittenUnitKind::Item, second_target, Some(0), 2),
            unit(
                6,
                WrittenUnitKind::MacroInvocation,
                second_attribute,
                Some(5),
                2,
            ),
        ];
        let mut inventory = test_inventory(source, units);
        inventory.derive_targets = vec![
            DeriveTargetSourceFacts::Opaque {
                target: SourceUnitId(1),
                attributes: vec![DeriveAttributeSourceFacts {
                    attribute: SourceUnitId(2),
                    elements: vec![SourceUnitId(3), SourceUnitId(4)],
                    directly_written: true,
                }],
                helper_candidates: Vec::new(),
            },
            DeriveTargetSourceFacts::Opaque {
                target: SourceUnitId(5),
                attributes: vec![DeriveAttributeSourceFacts {
                    attribute: SourceUnitId(6),
                    elements: Vec::new(),
                    directly_written: false,
                }],
                helper_candidates: Vec::new(),
            },
        ];

        let mut missing = inventory.clone();
        assert_eq!(
            refine_derive_targets(
                &mut missing,
                vec![DeriveTargetObservation::Complete {
                    target: SourceUnitId(1),
                    influences: Vec::new(),
                    helpers: Vec::new(),
                }]
            ),
            Err(SourceError::IncompleteDeriveObservation)
        );

        refine_derive_targets(
            &mut inventory,
            vec![
                DeriveTargetObservation::Complete {
                    target: SourceUnitId(1),
                    influences: Vec::new(),
                    helpers: Vec::new(),
                },
                DeriveTargetObservation::Opaque(SourceUnitId(5)),
            ],
        )
        .unwrap();
        assert!(matches!(
            inventory.derive_targets[0],
            DeriveTargetSourceFacts::Complete { .. }
        ));
        assert!(matches!(
            inventory.derive_targets[1],
            DeriveTargetSourceFacts::Opaque { .. }
        ));
        let groups = [1_u32, 2, 3, 4]
            .map(|unit| inventory.units[unit as usize].atomic_group)
            .into_iter()
            .collect::<BTreeSet<_>>();
        assert_eq!(groups.len(), 4);
        assert_eq!(
            inventory.units[5].atomic_group,
            inventory.units[6].atomic_group
        );
    }

    #[test]
    fn derive_refinement_rejects_an_omitted_list_element() {
        let source = Arc::<str>::from("#[derive(Clone, Debug)]\nstruct A;\n");
        let target = marker(&source, "#[derive(Clone, Debug)]\nstruct A;");
        let attribute = marker(&source, "#[derive(Clone, Debug)]");
        let clone = marker(&source, "Clone");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::Item, target, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, attribute, Some(1), 1),
            unit(3, WrittenUnitKind::MacroInvocation, clone, Some(2), 1),
        ];
        let mut inventory = test_inventory(source, units);
        inventory.derive_targets = vec![DeriveTargetSourceFacts::Opaque {
            target: SourceUnitId(1),
            attributes: vec![DeriveAttributeSourceFacts {
                attribute: SourceUnitId(2),
                elements: vec![SourceUnitId(3)],
                directly_written: true,
            }],
            helper_candidates: Vec::new(),
        }];

        assert_eq!(
            refine_derive_targets(
                &mut inventory,
                vec![DeriveTargetObservation::Complete {
                    target: SourceUnitId(1),
                    influences: Vec::new(),
                    helpers: Vec::new(),
                }]
            ),
            Err(SourceError::IncompleteDeriveObservation)
        );
    }

    #[test]
    fn derive_refinement_owns_helper_attributes_and_preserves_typed_requirements() {
        let source =
            Arc::<str>::from("# [derive(Clone, Default)]\nenum Choice { # [default] First }\n");
        let target = marker(
            &source,
            "# [derive(Clone, Default)]\nenum Choice { # [default] First }",
        );
        let attribute = marker(&source, "# [derive(Clone, Default)]");
        let clone = marker(&source, "Clone");
        let default = marker(&source, "Default");
        let helper = marker(&source, "# [default]");
        let helper_owner = marker(&source, "# [default] First");
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                None,
                0,
            ),
            unit(1, WrittenUnitKind::Item, target, Some(0), 1),
            unit(2, WrittenUnitKind::MacroInvocation, attribute, Some(1), 1),
            unit(3, WrittenUnitKind::MacroInvocation, clone, Some(2), 1),
            unit(4, WrittenUnitKind::MacroInvocation, default, Some(2), 1),
            unit(5, WrittenUnitKind::NestedItem, helper_owner, Some(1), 1),
        ];
        let mut inventory = test_inventory(source, units);
        inventory.derive_targets = vec![DeriveTargetSourceFacts::Opaque {
            target: SourceUnitId(1),
            attributes: vec![DeriveAttributeSourceFacts {
                attribute: SourceUnitId(2),
                elements: vec![SourceUnitId(3), SourceUnitId(4)],
                directly_written: true,
            }],
            helper_candidates: vec![helper],
        }];

        refine_derive_targets(
            &mut inventory,
            vec![DeriveTargetObservation::Complete {
                target: SourceUnitId(1),
                influences: vec![DeriveSourceRequirement {
                    trigger: SourceUnitId(3),
                    required: SourceUnitId(4),
                }],
                helpers: vec![ObservedDeriveHelper {
                    range: helper,
                    provider: SourceUnitId(4),
                }],
            }],
        )
        .unwrap();

        let helper_unit = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == helper)
            .unwrap();
        let helper_owner = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == helper_owner)
            .unwrap();
        assert_eq!(helper_unit.parent, Some(helper_owner.id));
        assert_ne!(helper_unit.atomic_group, helper_owner.atomic_group);
        let DeriveTargetSourceFacts::Complete {
            influences,
            helpers,
            ..
        } = &inventory.derive_targets[0]
        else {
            panic!("derive target should be refined");
        };
        assert_eq!(influences.len(), 1);
        assert_eq!(helpers.len(), 1);
        assert_eq!(helpers[0].attribute, helper_unit.id);
        assert_eq!(helpers[0].provider, influences[0].required);
    }

    fn unit(
        id: u32,
        kind: WrittenUnitKind,
        full_range: ByteRange,
        parent: Option<u32>,
        atomic_group: u32,
    ) -> WrittenUnit {
        WrittenUnit {
            id: SourceUnitId(id),
            kind,
            full_range,
            parent: parent.map(SourceUnitId),
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(atomic_group),
            same_role_ordinal: 0,
        }
    }

    fn test_inventory(source: Arc<str>, units: Vec<WrittenUnit>) -> SourceInventory {
        let (normalized, offsets) = OriginalOffsetMap::from_source(&source).unwrap();
        let pieces = own_lexical_pieces(&source, &units).unwrap();
        SourceInventory {
            original: source,
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces,
            derive_targets: Vec::new(),
            macro_rules: Vec::new(),
            macro_templates: Vec::new(),
            macro_repetitions: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn marker(source: &str, text: &str) -> ByteRange {
        let start = source.find(text).unwrap();
        ByteRange {
            start: start as u32,
            end: (start + text.len()) as u32,
        }
    }
}
