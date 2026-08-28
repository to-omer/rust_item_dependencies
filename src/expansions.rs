//! Ownership-preserving conversion of compiler expansion provenance.

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::FxHashMap;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
#[cfg(rust_item_dependencies_patched)]
use rustc_span::ExpnId;
#[cfg(rust_item_dependencies_patched)]
use std::collections::{BTreeMap, BTreeSet};

use crate::definitions::{CollectedDefinitions, DefinitionError};
use crate::dependency_graph::{DependencyEdge, ExpansionId, ExpansionNode};
#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{DependencyKind, ExpansionKind, GraphNode, MacroImplementationKind};
#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{
    EvidenceOrigin, ExpansionFragmentKind, ExpansionKey, ExpansionKeyPart, ObservationSite,
};
#[cfg(rust_item_dependencies_patched)]
use crate::graph::{DefinitionId, DefinitionOrigin, DefinitionTarget};
#[cfg(all(test, rust_item_dependencies_patched))]
use crate::source::ByteRange;
#[cfg(rust_item_dependencies_patched)]
use crate::source::EditableMacroSourceRole;
use crate::source::SourceInventory;
#[cfg(all(test, rust_item_dependencies_patched))]
use crate::source::SourceUnitId;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpansionError {
    IncompleteOrigin,
    InvalidSpan,
    Definition(DefinitionError),
}

impl From<DefinitionError> for ExpansionError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

mod output;
mod provenance;

#[cfg(test)]
pub(crate) use output::{
    MacroCompleteOutputMeaning, MacroOutputMaterializationGroup, MacroOutputSlice,
};
pub(crate) use output::{
    MacroCompleteOutputMeaningInventory, MacroDefinitionProductRole, MacroOutputRange,
    MacroOwnerEffect, MacroProducerCoverage, MacroProducerCoverageInventory,
    macro_definition_product_role, validated_outputless_macro_expansions,
};
pub(crate) use provenance::{
    MacroContributorDag, MacroContributorSetId, MacroProvenance, collect_macro_provenance,
};

#[cfg(rust_item_dependencies_patched)]
use output::lower_macro_output_inventories;
#[cfg(all(test, rust_item_dependencies_patched))]
use output::{MacroOutputClass, coalesce_definition_identity_cohorts};
#[cfg(rust_item_dependencies_patched)]
use provenance::PreparedExpansionOrigin;

pub(crate) struct CollectedExpansions {
    pub nodes: Vec<ExpansionNode>,
    pub edges: Vec<DependencyEdge>,
    macro_producer_coverage: MacroProducerCoverageInventory,
    macro_complete_output_meaning: MacroCompleteOutputMeaningInventory,
    outputless_macro_expansions: Vec<ExpansionId>,
}

impl CollectedExpansions {
    pub(crate) fn into_parts(
        self,
    ) -> (
        Vec<ExpansionNode>,
        Vec<DependencyEdge>,
        MacroProducerCoverageInventory,
        MacroCompleteOutputMeaningInventory,
        Vec<ExpansionId>,
    ) {
        (
            self.nodes,
            self.edges,
            self.macro_producer_coverage,
            self.macro_complete_output_meaning,
            self.outputless_macro_expansions,
        )
    }
}

#[cfg(not(rust_item_dependencies_patched))]
pub(crate) fn collect_expansions(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _definitions: &mut CollectedDefinitions,
    _provenance: &MacroProvenance,
) -> Result<CollectedExpansions, ExpansionError> {
    Err(ExpansionError::IncompleteOrigin)
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn collect_expansions(
    _compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &mut CollectedDefinitions,
    provenance: &MacroProvenance,
) -> Result<CollectedExpansions, ExpansionError> {
    let mut raw = Vec::with_capacity(provenance.origins.ordered.len());
    for prepared in &provenance.origins.ordered {
        let macro_definition = prepared
            .macro_definition
            .map(|definition| definitions.target(tcx, definition))
            .transpose()?;
        let macro_definition_key = prepared
            .macro_definition
            .map(|definition| definitions.target_key(tcx, definition))
            .transpose()?;
        let source_owner = prepared
            .parent_definition
            .map(|_| expansion_source_owner(source, definitions, prepared))
            .transpose()?
            .flatten();
        raw.push(RawExpansion {
            compiler_id: prepared.compiler_id,
            identity_parent: prepared.parents.identity(),
            kind: prepared.kind.clone(),
            part: ExpansionKeyPart {
                kind: prepared.kind.clone(),
                fragment: prepared.fragment,
                implementation: prepared.implementation,
                invocation_range: prepared.invocation_range,
                node_range: prepared.node_range,
                target_range: prepared.target_range,
                macro_definition: macro_definition_key,
                selected_macro_rule: prepared.selected_rule.map(|selected| selected.range),
                same_role_ordinal: 0,
            },
            fragment: prepared.fragment,
            implementation: prepared.implementation,
            discovered_in: prepared.parents.discovered_in,
            semantic_parent: prepared.parents.semantic,
            source_call_parent: prepared.parents.source_call,
            written_invocation: prepared.written_invocation(),
            source_owner,
            macro_definition,
            key: ExpansionKey(Vec::new()),
        });
    }

    assign_expansion_keys(&mut raw)?;
    raw.sort_by(|left, right| left.key.cmp(&right.key));
    let expansion_ids = raw
        .iter()
        .enumerate()
        .map(|(index, expansion)| (expansion.compiler_id, ExpansionId(index as u32)))
        .collect::<FxHashMap<_, _>>();
    if expansion_ids.len() != raw.len() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let expansion_id = |compiler_id: ExpnId| expansion_ids.get(&compiler_id).copied();

    let mut nodes = Vec::with_capacity(raw.len());
    let mut edges = Vec::new();
    for (index, expansion) in raw.iter().enumerate() {
        let id = ExpansionId(index as u32);
        let site = expansion_site(expansion);
        let discovered_in = map_relation(expansion.discovered_in, &expansion_id)?;
        let semantic_parent = map_relation(expansion.semantic_parent, &expansion_id)?;
        let source_call_parent = map_relation(expansion.source_call_parent, &expansion_id)?;
        nodes.push(ExpansionNode {
            id,
            key: expansion.key.clone(),
            kind: expansion.kind.clone(),
            fragment: expansion.fragment,
            implementation: expansion.implementation,
            discovered_in,
            semantic_parent,
            source_call_parent,
            written_invocation: expansion.written_invocation,
            source_owner: expansion.source_owner,
            macro_definition: expansion.macro_definition,
        });
        for (parent, kind) in [
            (discovered_in, DependencyKind::ExpansionDiscoveredIn),
            (semantic_parent, DependencyKind::ExpansionSemanticParent),
            (
                source_call_parent,
                DependencyKind::ExpansionSourceCallParent,
            ),
        ] {
            if let Some(parent) = parent {
                edges.push(structural_edge(
                    GraphNode::Expansion(id),
                    GraphNode::Expansion(parent),
                    kind,
                ));
            }
        }
        if let Some(target) = expansion.macro_definition {
            edges.push(structural_edge(
                GraphNode::Expansion(id),
                definition_node(target),
                DependencyKind::MacroDefinition,
            ));
        }
        if let Some(owner) = expansion.source_owner {
            edges.push(edge(
                GraphNode::Definition(owner),
                GraphNode::Expansion(id),
                DependencyKind::ExpansionUse,
                site,
            ));
        }
    }

    let mut generated_by = Vec::new();
    for definition in tcx.iter_local_def_id() {
        let Some(id) = definitions.definition_id(definition) else {
            return Err(ExpansionError::IncompleteOrigin);
        };
        let compiler_expansion = match definitions.graph.definitions[id.0 as usize].origin {
            DefinitionOrigin::Expanded { .. } => definition_expansion(tcx, definition)?,
            DefinitionOrigin::CompilerGenerated { .. } => {
                let expansion = tcx.expn_that_defined(definition.to_def_id());
                if expansion == ExpnId::root() {
                    continue;
                }
                expansion
            }
            DefinitionOrigin::Written { .. } | DefinitionOrigin::Injected { .. } => continue,
        };
        generated_by.push((id, compiler_expansion));
    }
    let generated_expansions = provenance.nearest_collected_expansions(
        generated_by.iter().map(|(_, expansion)| *expansion),
        &expansion_ids,
    )?;
    for (id, compiler_expansion) in generated_by {
        let expansion = generated_expansions
            .get(&compiler_expansion)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        edges.push(structural_edge(
            GraphNode::Definition(id),
            GraphNode::Expansion(expansion),
            DependencyKind::GeneratedBy,
        ));
    }

    let mut outputless_macro_expansions = provenance
        .outputless_producers
        .iter()
        .map(|compiler_id| expansion_id(*compiler_id).ok_or(ExpansionError::IncompleteOrigin))
        .collect::<Result<Vec<_>, _>>()?;
    outputless_macro_expansions.sort();
    let outputless_macro_expansions =
        validated_outputless_macro_expansions(&nodes, &edges, &outputless_macro_expansions)
            .ok_or(ExpansionError::IncompleteOrigin)?
            .into_iter()
            .collect();

    let (macro_producer_coverage, macro_complete_output_meaning) =
        lower_macro_output_inventories(definitions, provenance, &raw, expansion_ids, &edges)?;

    Ok(CollectedExpansions {
        nodes,
        edges,
        macro_producer_coverage,
        macro_complete_output_meaning,
        outputless_macro_expansions,
    })
}

#[cfg(rust_item_dependencies_patched)]
struct RawExpansion {
    compiler_id: ExpnId,
    identity_parent: Option<ExpnId>,
    kind: ExpansionKind,
    part: ExpansionKeyPart,
    key: ExpansionKey,
    fragment: Option<ExpansionFragmentKind>,
    implementation: Option<MacroImplementationKind>,
    discovered_in: Option<ExpnId>,
    semantic_parent: Option<ExpnId>,
    source_call_parent: Option<ExpnId>,
    written_invocation: Option<crate::source::SourceUnitId>,
    source_owner: Option<DefinitionId>,
    macro_definition: Option<DefinitionTarget>,
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_source_owner(
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
    origin: &PreparedExpansionOrigin,
) -> Result<Option<DefinitionId>, ExpansionError> {
    if origin
        .editable_source
        .is_some_and(|editable| editable.role == EditableMacroSourceRole::TransparentAttribute)
    {
        return Ok(None);
    }
    let written_invocation = origin.written_invocation();
    if let Some(target_range) = origin.target_range {
        let mut candidates = definitions
            .graph
            .definitions
            .iter()
            .filter_map(|definition| match definition.origin {
                DefinitionOrigin::Written { anchor, .. }
                    if target_range.contains(anchor)
                        && !matches!(definition.kind, crate::graph::DefinitionKind::Crate) =>
                {
                    Some((definition.key.0.len(), definition.id))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        candidates.sort();
        if let Some(&(depth, owner)) = candidates.first()
            && candidates
                .get(1)
                .is_none_or(|candidate| candidate.0 != depth)
        {
            return Ok(Some(owner));
        }
        if candidates.is_empty()
            && origin.attribute_like
            && (origin.parents.discovered_in.is_some()
                || written_invocation.is_some_and(|invocation| {
                    source
                        .ownerless_attribute_target(invocation)
                        .and_then(|target| source.units.get(target.0 as usize))
                        .is_some_and(|target| target.full_range.contains(target_range))
                        || definitions.graph.definitions.iter().any(|definition| {
                            matches!(
                                definition.origin,
                                DefinitionOrigin::Expanded {
                                    invocation: definition_invocation,
                                    ..
                                } if definition_invocation == invocation
                            )
                        })
                }))
        {
            return Ok(None);
        }
        return Err(ExpansionError::IncompleteOrigin);
    }
    definitions
        .definition_id(
            origin
                .parent_definition
                .ok_or(ExpansionError::IncompleteOrigin)?,
        )
        .map(Some)
        .ok_or(ExpansionError::IncompleteOrigin)
}

#[cfg(rust_item_dependencies_patched)]
fn assign_expansion_keys(raw: &mut [RawExpansion]) -> Result<(), ExpansionError> {
    let mut remaining = (0..raw.len()).collect::<BTreeSet<_>>();
    let mut keys = BTreeMap::<usize, ExpansionKey>::new();
    while !remaining.is_empty() {
        let ready = remaining
            .iter()
            .copied()
            .filter(|&index| {
                raw[index].identity_parent.is_none_or(|parent| {
                    raw.iter()
                        .position(|candidate| candidate.compiler_id == parent)
                        .is_some_and(|parent_index| keys.contains_key(&parent_index))
                })
            })
            .collect::<Vec<_>>();
        if ready.is_empty() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut groups = BTreeMap::<(Option<ExpansionKey>, ExpansionKeyPart), Vec<usize>>::new();
        for index in ready {
            let parent = raw[index].identity_parent.and_then(|parent| {
                raw.iter()
                    .position(|candidate| candidate.compiler_id == parent)
                    .and_then(|parent_index| keys.get(&parent_index).cloned())
            });
            groups
                .entry((parent, raw[index].part.clone()))
                .or_default()
                .push(index);
        }
        for ((parent, _), mut members) in groups {
            members.sort_by_key(|&index| raw[index].compiler_id.expn_hash().local_hash().as_u64());
            let hashes = members
                .iter()
                .map(|&index| raw[index].compiler_id.expn_hash().local_hash().as_u64())
                .collect::<BTreeSet<_>>();
            if hashes.len() != members.len() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            for (ordinal, index) in members.into_iter().enumerate() {
                raw[index].part.same_role_ordinal = ordinal as u32;
                let mut parts = parent.as_ref().map_or_else(Vec::new, |key| key.0.clone());
                parts.push(raw[index].part.clone());
                let key = ExpansionKey(parts);
                keys.insert(index, key.clone());
                raw[index].key = key;
                remaining.remove(&index);
            }
        }
    }
    if keys.values().collect::<BTreeSet<_>>().len() != raw.len() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn definition_expansion(
    tcx: TyCtxt<'_>,
    mut definition: rustc_hir::def_id::LocalDefId,
) -> Result<ExpnId, ExpansionError> {
    let mut visited = Vec::new();
    loop {
        if visited.contains(&definition) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        visited.push(definition);
        let expansion = tcx.expn_that_defined(definition.to_def_id());
        if expansion != ExpnId::root() {
            return Ok(expansion);
        }
        definition = tcx
            .opt_local_parent(definition)
            .ok_or(ExpansionError::IncompleteOrigin)?;
    }
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_site(expansion: &RawExpansion) -> Vec<ObservationSite> {
    if expansion.written_invocation.is_none() {
        // A generated invocation can reuse a transcriber or call-site span,
        // but that range is provenance rather than a written use site. Its
        // source requirements are carried by the producer materialization;
        // gating the use edge on that same source creates a circular reason
        // to discard a semantically required child expansion.
        return vec![ObservationSite::CompilerGenerated];
    }
    expansion
        .part
        .invocation_range
        .or(expansion.part.node_range)
        .map_or_else(
            || vec![ObservationSite::CompilerGenerated],
            |range| vec![ObservationSite::Source(range)],
        )
}

#[cfg(rust_item_dependencies_patched)]
fn structural_edge(from: GraphNode, to: GraphNode, kind: DependencyKind) -> DependencyEdge {
    DependencyEdge {
        from,
        to,
        kind,
        sites: Vec::new(),
        evidence: EvidenceOrigin::PatchedObserver,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn edge(
    from: GraphNode,
    to: GraphNode,
    kind: DependencyKind,
    sites: Vec<ObservationSite>,
) -> DependencyEdge {
    DependencyEdge {
        from,
        to,
        kind,
        sites,
        evidence: EvidenceOrigin::PatchedObserver,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn definition_node(target: DefinitionTarget) -> GraphNode {
    match target {
        DefinitionTarget::Local(id) => GraphNode::Definition(id),
        DefinitionTarget::External(id) => GraphNode::ExternalDefinition(id),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn map_relation(
    relation: Option<ExpnId>,
    lookup: &impl Fn(ExpnId) -> Option<ExpansionId>,
) -> Result<Option<ExpansionId>, ExpansionError> {
    relation
        .map(|relation| lookup(relation).ok_or(ExpansionError::IncompleteOrigin))
        .transpose()
}

#[cfg(all(test, rust_item_dependencies_patched))]
#[path = "expansions/tests.rs"]
mod tests;
