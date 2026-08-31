//! Canonical compiler-decision snapshots used by reduced-source verification.
//!
//! Dense inventory IDs are deliberately resolved to owned semantic keys before
//! comparison.  The snapshot also excludes session observations which are not
//! part of the verification contract: evidence provenance, allocation bytes,
//! numeric allocation offsets, and diagnostic locations.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use crate::compiler_terms::CanonicalCompilerTerm;
use crate::dependency_graph::{
    BuiltinTraitTarget, DefinitionReferenceKey, DependencyGraph, DependencyKind, ExpansionId,
    ExpansionKey, ExpansionKeyPart, ExpansionKind, GraphNode, MacroImplementationKind,
    MonoCollection, MonoId, MonoInstanceKey, MonoKey, ObservationSite, ProjectionOutcome,
    ProjectionSourceKind, ProofId, ProofKey, ProofNodeKind, ProofRelationKind, RootReason,
    SelectionSource, SelectionSourceKind, SolverTracePayload, SpecializationNode,
    SpecializationNodeKind,
};
use crate::graph::{
    DefinitionId, DefinitionKey, DefinitionTarget, ExternalDefinitionId, ExternalDefinitionKey,
};
use crate::retention::{Retention, SourceSiteOwnerIndex, source_site_is_retained};
use crate::rewrite::SourceRewrite;
use crate::source::{ByteRange, SourceInventory};

type SourceFilter<'a> = (
    &'a SourceSiteOwnerIndex,
    &'a BTreeSet<crate::source::SourceUnitId>,
);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SnapshotNodeKey {
    Definition(DefinitionKey),
    ExternalDefinition(ExternalDefinitionKey),
    Expansion(ExpansionKey),
    Proof(ProofKey),
    Mono(MonoKey),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum SnapshotNodeDecision {
    Definition,
    ExternalDefinition,
    Expansion(SnapshotExpansionDecision),
    Proof(SnapshotProofDecision),
    Mono {
        materialized_definition: Option<DefinitionReferenceKey>,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotExpansionDecision {
    kind: ExpansionKind,
    fragment: Option<crate::dependency_graph::ExpansionFragmentKind>,
    implementation: Option<MacroImplementationKind>,
    discovered_in: Option<ExpansionKey>,
    semantic_parent: Option<ExpansionKey>,
    source_call_parent: Option<ExpansionKey>,
    source_owner: Option<DefinitionKey>,
    macro_definition: Option<DefinitionReferenceKey>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotSelectionSource {
    kind: SelectionSourceKind,
    term: CanonicalCompilerTerm,
    implementation: Option<DefinitionReferenceKey>,
    builtin_trait: Option<SnapshotBuiltinTraitTarget>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotBuiltinTraitTarget {
    kind: crate::dependency_graph::BuiltinTraitTargetKind,
    target: DefinitionReferenceKey,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotSolverTrace {
    root: ProofKey,
    obligations: Vec<ProofKey>,
    trait_selections: Vec<ProofKey>,
    projections: Vec<ProofKey>,
    fulfillments: Vec<ProofKey>,
    cycles: Vec<ProofKey>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotSpecializationNode {
    kind: SpecializationNodeKind,
    target: DefinitionReferenceKey,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum SnapshotProofDecision {
    Obligation {
        environment: CanonicalCompilerTerm,
        predicate: CanonicalCompilerTerm,
        source: Option<SnapshotSelectionSource>,
        selection_nested: Option<Vec<ProofKey>>,
        fulfillment_nested: Option<Vec<ProofKey>>,
        query_trace: Option<SnapshotSolverTrace>,
    },
    Projection {
        environment: CanonicalCompilerTerm,
        alias: CanonicalCompilerTerm,
        source_kind: ProjectionSourceKind,
        source: CanonicalCompilerTerm,
        outcome: ProjectionOutcome,
        selected_trait: Option<ProofKey>,
        selected_impl: Option<DefinitionReferenceKey>,
        selected_item: Option<DefinitionReferenceKey>,
        owners: Vec<ProofKey>,
        nested: Vec<ProofKey>,
        query_trace: Option<SnapshotSolverTrace>,
        normalized_result: Option<CanonicalCompilerTerm>,
    },
    AssociatedItem {
        request: CanonicalCompilerTerm,
        raw_instance: MonoInstanceKey,
        codegen_instance: MonoInstanceKey,
        selection: ProofKey,
        source_kind: SelectionSourceKind,
        leaf: Option<DefinitionReferenceKey>,
        defining_node: Option<SnapshotSpecializationNode>,
        finalizing_node: Option<SnapshotSpecializationNode>,
        ancestor_path: Vec<SnapshotSpecializationNode>,
    },
    Cycle {
        members: Vec<ProofKey>,
        coinductive: bool,
    },
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SnapshotObservationSite {
    Source(ByteRange),
    ExternalSource,
    AllocationReference,
    VTableSlot(u64),
    CompilerGenerated,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum SnapshotEdgeFrom {
    Node(SnapshotNodeKey),
    SourceAssociatedItem,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotEdge {
    pub from: SnapshotEdgeFrom,
    pub to: SnapshotNodeKey,
    pub kind: DependencyKind,
    pub sites: Vec<SnapshotObservationSite>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SnapshotCollectionEdgeKey {
    from: SnapshotEdgeFrom,
    to: SnapshotNodeKey,
    used_kind: DependencyKind,
}

#[derive(Default)]
struct SnapshotCollectionObservations {
    source_free: bool,
    sites: BTreeSet<SnapshotObservationSite>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotRoot {
    pub node: SnapshotNodeKey,
    pub reason: RootReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompilerDecisionSnapshot {
    roots: BTreeSet<SnapshotRoot>,
    nodes: BTreeMap<SnapshotNodeKey, SnapshotNodeDecision>,
    edges: BTreeSet<SnapshotEdge>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum SnapshotError {
    InvalidNode,
    InvalidEdge,
    InvalidRoot,
    InvalidSourceSite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum SnapshotDiff {
    Root {
        original: Option<SnapshotRoot>,
        reduced: Option<SnapshotRoot>,
    },
    Node {
        key: SnapshotNodeKey,
        original: Option<SnapshotNodeDecision>,
        reduced: Option<SnapshotNodeDecision>,
    },
    Edge {
        original: Option<SnapshotEdge>,
        reduced: Option<SnapshotEdge>,
    },
}

impl CompilerDecisionSnapshot {
    /// Builds the expected decision set from the original analysis.  Only the
    /// retention fixed point and observations owned by retained source units
    /// participate in verification.
    pub(crate) fn original(
        graph: &DependencyGraph,
        source: &SourceInventory,
        retention: &Retention,
        rewrite: &SourceRewrite,
    ) -> Result<Self, SnapshotError> {
        let surviving_expansions = surviving_expansions(graph, source, &retention.retained_units)?;
        let permitted = retention
            .compile_required
            .iter()
            .copied()
            .map(|node| {
                if matches!(node, GraphNode::Expansion(expansion) if retention
                    .outputless_macro_expansions
                    .contains(&expansion))
                {
                    return Ok(None);
                }
                selected_node_survives_rewrite(graph, &rewrite.pieces, &surviving_expansions, node)
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<BTreeSet<_>>();
        let mut selected = permitted
            .iter()
            .copied()
            .filter(|node| matches!(node, GraphNode::Definition(_)))
            .collect::<BTreeSet<_>>();
        selected.extend(graph.roots.iter().map(|root| root.node));
        if !selected.is_subset(&permitted) {
            return Err(SnapshotError::InvalidRoot);
        }

        let source_sites =
            SourceSiteOwnerIndex::new(source).map_err(|_| SnapshotError::InvalidSourceSite)?;
        let source_filter = Some((&source_sites, &retention.retained_units));
        let mut work = selected.iter().copied().collect::<Vec<_>>();
        while let Some(from) = work.pop() {
            for edge in graph
                .edges
                .iter()
                .filter(|edge| edge.from == from && permitted.contains(&edge.to))
            {
                if snapshot_observation_sites(&edge.sites, source_filter)?.is_some()
                    && selected.insert(edge.to)
                {
                    work.push(edge.to);
                }
            }
        }
        Self::build(
            graph,
            &selected,
            source_filter,
            &retention.outputless_macro_expansions,
        )
    }

    /// Builds the observed decision set from the reduced analysis.  Every
    /// local definition is a root so a newly introduced retained definition
    /// cannot hide merely because it is not reachable from an entry root.
    pub(crate) fn reduced(graph: &DependencyGraph) -> Result<Self, SnapshotError> {
        Self::reduced_excluding(graph, &BTreeSet::new())
    }

    /// Builds a reduced snapshot after excluding macro expansions whose
    /// validated surviving output has no semantic product. This includes
    /// directly empty expansions and transparent control-only parents whose
    /// children are all outputless.
    pub(crate) fn reduced_excluding_outputless_macros(
        graph: &DependencyGraph,
        outputless_macro_expansions: &BTreeSet<ExpansionId>,
    ) -> Result<Self, SnapshotError> {
        Self::reduced_excluding(graph, outputless_macro_expansions)
    }

    fn reduced_excluding(
        graph: &DependencyGraph,
        outputless_macro_expansions: &BTreeSet<ExpansionId>,
    ) -> Result<Self, SnapshotError> {
        let mut selected = graph
            .definitions
            .definitions
            .iter()
            .map(|definition| GraphNode::Definition(definition.id))
            .collect::<BTreeSet<_>>();
        selected.extend(graph.roots.iter().map(|root| root.node));

        let mut work = selected.iter().copied().collect::<Vec<_>>();
        while let Some(from) = work.pop() {
            for edge in graph.edges.iter().filter(|edge| edge.from == from) {
                if matches!(edge.to, GraphNode::Expansion(expansion) if outputless_macro_expansions
                    .contains(&expansion))
                {
                    continue;
                }
                if selected.insert(edge.to) {
                    work.push(edge.to);
                }
            }
        }
        Self::build(graph, &selected, None, outputless_macro_expansions)
    }

    pub(crate) fn first_difference(&self, reduced: &Self) -> Option<SnapshotDiff> {
        if let Some((original, reduced)) = first_set_difference(&self.roots, &reduced.roots) {
            return Some(SnapshotDiff::Root { original, reduced });
        }
        if let Some((key, original, reduced)) = first_map_difference(&self.nodes, &reduced.nodes) {
            return Some(SnapshotDiff::Node {
                key,
                original,
                reduced,
            });
        }
        first_set_difference(&self.edges, &reduced.edges)
            .map(|(original, reduced)| SnapshotDiff::Edge { original, reduced })
    }

    fn build(
        graph: &DependencyGraph,
        selected: &BTreeSet<GraphNode>,
        source_filter: Option<SourceFilter<'_>>,
        outputless_macro_expansions: &BTreeSet<ExpansionId>,
    ) -> Result<Self, SnapshotError> {
        let expansion_keys =
            snapshot_expansion_keys(graph, selected, source_filter, outputless_macro_expansions)?;
        let mut roots = BTreeSet::new();
        for root in &graph.roots {
            if !selected.contains(&root.node)
                || !roots.insert(SnapshotRoot {
                    node: node_key(graph, &expansion_keys, root.node)?,
                    reason: root.reason,
                })
            {
                return Err(SnapshotError::InvalidRoot);
            }
        }

        let mut nodes = BTreeMap::new();
        for &node in selected {
            let (key, decision) = snapshot_node(graph, &expansion_keys, node)?;
            if nodes.insert(key, decision).is_some() {
                return Err(SnapshotError::InvalidNode);
            }
        }

        let mut edges = BTreeSet::new();
        for edge in graph
            .edges
            .iter()
            .filter(|edge| selected.contains(&edge.from) && selected.contains(&edge.to))
        {
            let Some(sites) = snapshot_observation_sites(&edge.sites, source_filter)? else {
                continue;
            };
            let snapshot = SnapshotEdge {
                from: SnapshotEdgeFrom::Node(node_key(graph, &expansion_keys, edge.from)?),
                to: node_key(graph, &expansion_keys, edge.to)?,
                kind: snapshot_dependency_kind(&edge.kind),
                sites,
            };
            edges.extend(project_source_associated_item(snapshot));
        }

        Ok(Self {
            roots,
            nodes,
            edges: canonicalize_collection_edges(edges),
        })
    }
}

/// Projects a trait-associated item selected from pre-optimization source onto
/// its source site. The observer propagates this proof through MIR inlining, so
/// the optimized owner is placement rather than part of the selection itself.
fn project_source_associated_item(mut edge: SnapshotEdge) -> Vec<SnapshotEdge> {
    if !matches!(
        edge.kind,
        DependencyKind::SelectionProof {
            relation: crate::dependency_graph::MonoDependencyKind::SourceAssociatedItem,
            collection: MonoCollection::Mentioned,
        }
    ) {
        return vec![edge];
    }

    let mut source_sites = Vec::new();
    edge.sites.retain(|site| {
        if matches!(
            site,
            SnapshotObservationSite::Source(_) | SnapshotObservationSite::ExternalSource
        ) {
            source_sites.push(*site);
            false
        } else {
            true
        }
    });
    if source_sites.is_empty() {
        return vec![edge];
    }

    let mut projected =
        Vec::with_capacity(source_sites.len() + usize::from(!edge.sites.is_empty()));
    let target = edge.to.clone();
    let kind = edge.kind.clone();
    if !edge.sites.is_empty() {
        projected.push(edge);
    }
    projected.extend(source_sites.into_iter().map(|site| SnapshotEdge {
        from: SnapshotEdgeFrom::SourceAssociatedItem,
        to: target.clone(),
        kind: kind.clone(),
        sites: vec![site],
    }));
    projected
}

/// Projects raw monomorphization observations onto compiler obligations.
///
/// `Mentioned` keeps an optimization-independent item available for compiler
/// checks. An otherwise identical `Used` observation already requires that
/// item for code generation and subsumes the same check. Distinct sites,
/// relations, endpoints, and edge categories remain separate decisions.
fn canonicalize_collection_edges(edges: BTreeSet<SnapshotEdge>) -> BTreeSet<SnapshotEdge> {
    let mut used = BTreeMap::<SnapshotCollectionEdgeKey, SnapshotCollectionObservations>::new();
    for edge in &edges {
        let Some((MonoCollection::Used, key)) = snapshot_collection_edge_key(edge) else {
            continue;
        };
        let observations = used.entry(key).or_default();
        if edge.sites.is_empty() {
            observations.source_free = true;
        } else {
            observations.sites.extend(edge.sites.iter().copied());
        }
    }

    edges
        .into_iter()
        .filter_map(|mut edge| {
            let Some((MonoCollection::Mentioned, key)) = snapshot_collection_edge_key(&edge) else {
                return Some(edge);
            };
            let Some(used) = used.get(&key) else {
                return Some(edge);
            };
            if edge.sites.is_empty() {
                return (!used.source_free).then_some(edge);
            }
            edge.sites.retain(|site| !used.sites.contains(site));
            (!edge.sites.is_empty()).then_some(edge)
        })
        .collect()
}

fn snapshot_collection_edge_key(
    edge: &SnapshotEdge,
) -> Option<(MonoCollection, SnapshotCollectionEdgeKey)> {
    let (collection, used_kind) = match &edge.kind {
        DependencyKind::Mono {
            relation,
            collection,
        } => (
            *collection,
            DependencyKind::Mono {
                relation: *relation,
                collection: MonoCollection::Used,
            },
        ),
        DependencyKind::SelectionProof {
            relation,
            collection,
        } => (
            *collection,
            DependencyKind::SelectionProof {
                relation: *relation,
                collection: MonoCollection::Used,
            },
        ),
        _ => return None,
    };
    Some((
        collection,
        SnapshotCollectionEdgeKey {
            from: edge.from.clone(),
            to: edge.to.clone(),
            used_kind,
        },
    ))
}

fn snapshot_expansion_keys(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    source_filter: Option<SourceFilter<'_>>,
    outputless_macro_expansions: &BTreeSet<ExpansionId>,
) -> Result<Vec<ExpansionKey>, SnapshotError> {
    let mut keys = graph
        .expansions
        .iter()
        .enumerate()
        .map(|(index, node)| {
            (node.id.0 as usize == index && !node.key.0.is_empty())
                .then(|| node.key.clone())
                .ok_or(SnapshotError::InvalidNode)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let raw_ids = graph
        .expansions
        .iter()
        .map(|node| (node.key.clone(), node.id))
        .collect::<BTreeMap<_, _>>();
    if raw_ids.len() != graph.expansions.len() {
        return Err(SnapshotError::InvalidNode);
    }
    let filtered_raw_ordinals = if outputless_macro_expansions.is_empty() {
        None
    } else {
        Some(outputless_filtered_expansion_ordinals(graph, outputless_macro_expansions)?.0)
    };

    let mut by_depth = graph
        .expansions
        .iter()
        .filter(|node| selected.contains(&GraphNode::Expansion(node.id)))
        .map(|node| (node.key.0.len(), node.id))
        .collect::<Vec<_>>();
    by_depth.sort();
    let subtree_ranks = expansion_subtree_ranks(graph, selected, &raw_ids, &by_depth)?;
    let mut start = 0;
    while start < by_depth.len() {
        let depth = by_depth[start].0;
        let end = by_depth[start..]
            .iter()
            .position(|&(candidate, _)| candidate != depth)
            .map_or(by_depth.len(), |offset| start + offset);
        let mut groups =
            BTreeMap::<(Option<ExpansionKey>, ExpansionKeyPart), Vec<ExpansionId>>::new();
        for &(_, id) in &by_depth[start..end] {
            let raw = expansion_key(graph, id)?;
            let parent = if depth == 1 {
                None
            } else {
                let raw_parent = ExpansionKey(raw.0[..depth - 1].to_vec());
                let parent = raw_ids
                    .get(&raw_parent)
                    .copied()
                    .filter(|parent| selected.contains(&GraphNode::Expansion(*parent)))
                    .ok_or(SnapshotError::InvalidNode)?;
                Some(snapshot_expansion_key(&keys, parent)?.clone())
            };
            let mut leaf = raw.0[depth - 1].clone();
            leaf.same_role_ordinal = 0;
            groups.entry((parent, leaf)).or_default().push(id);
        }

        for ((parent, _), members) in groups {
            let mut witnessed = members
                .iter()
                .copied()
                .map(|id| {
                    Ok((
                        generated_by_witness(graph, selected, id)?,
                        expansion_key(graph, id)?.0[depth - 1].same_role_ordinal,
                        id,
                    ))
                })
                .collect::<Result<Vec<_>, SnapshotError>>()?;
            let mut witnesses_are_canonical = witnessed.len() == 1
                || (witnessed.iter().all(|(witness, _, _)| !witness.is_empty())
                    && witnessed
                        .iter()
                        .map(|(witness, _, _)| witness)
                        .collect::<BTreeSet<_>>()
                        .len()
                        == witnessed.len());
            let mut subtree_shape_is_admissible = false;
            if !witnesses_are_canonical
                && witnessed.iter().all(|(witness, _, _)| witness.is_empty())
            {
                for (witness, _, id) in &mut witnessed {
                    *witness = generated_by_subtree_witness(graph, selected, *id)?;
                }
                witnesses_are_canonical =
                    witnessed.iter().all(|(witness, _, _)| !witness.is_empty())
                        && witnessed
                            .iter()
                            .map(|(witness, _, _)| witness)
                            .collect::<BTreeSet<_>>()
                            .len()
                            == witnessed.len();
            }
            if !witnesses_are_canonical
                && witnessed.iter().all(|(witness, _, _)| witness.is_empty())
            {
                for (witness, _, id) in &mut witnessed {
                    *witness = expansion_use_witness(graph, selected, *id, source_filter)?;
                }
                subtree_shape_is_admissible =
                    witnessed.iter().all(|(witness, _, _)| witness.is_empty())
                        || witnessed.iter().all(|(witness, _, _)| !witness.is_empty());
                witnesses_are_canonical =
                    witnessed.iter().all(|(witness, _, _)| !witness.is_empty())
                        && witnessed
                            .iter()
                            .map(|(witness, _, _)| witness)
                            .collect::<BTreeSet<_>>()
                            .len()
                            == witnessed.len();
            }
            let subtree_is_canonical = subtree_shape_is_admissible
                && !witnesses_are_canonical
                && witnessed
                    .iter()
                    .map(|&(_, _, id)| {
                        subtree_ranks
                            .get(id.0 as usize)
                            .copied()
                            .flatten()
                            .ok_or(SnapshotError::InvalidNode)
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?
                    .len()
                    == witnessed.len();
            if witnesses_are_canonical {
                witnessed.sort();
            } else if subtree_is_canonical {
                witnessed.sort_by_key(|&(_, _, id)| subtree_ranks[id.0 as usize]);
            } else {
                witnessed.sort_by_key(|&(_, raw_ordinal, _)| raw_ordinal);
            }
            for (ordinal, (_, _, id)) in witnessed.into_iter().enumerate() {
                let mut leaf = expansion_key(graph, id)?.0[depth - 1].clone();
                if witnesses_are_canonical || subtree_is_canonical {
                    leaf.same_role_ordinal =
                        u32::try_from(ordinal).map_err(|_| SnapshotError::InvalidNode)?;
                } else if let Some(filtered_raw_ordinals) = &filtered_raw_ordinals {
                    leaf.same_role_ordinal = filtered_raw_ordinals
                        .get(id.0 as usize)
                        .copied()
                        .flatten()
                        .ok_or(SnapshotError::InvalidNode)?;
                }
                let mut parts = parent.as_ref().map_or_else(Vec::new, |key| key.0.clone());
                parts.push(leaf);
                keys[id.0 as usize] = ExpansionKey(parts);
            }
        }
        start = end;
    }

    let selected_keys = by_depth
        .iter()
        .map(|&(_, id)| snapshot_expansion_key(&keys, id))
        .collect::<Result<BTreeSet<_>, _>>()?;
    if selected_keys.len() != by_depth.len() {
        return Err(SnapshotError::InvalidNode);
    }
    Ok(keys)
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct OutputlessOrdinalWork {
    #[cfg(test)]
    expansion_visits: usize,
    #[cfg(test)]
    grouped_expansions: usize,
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct ExpansionSiblingRole<'a> {
    parent: Option<ExpansionId>,
    kind: &'a ExpansionKind,
    fragment: Option<crate::dependency_graph::ExpansionFragmentKind>,
    implementation: Option<MacroImplementationKind>,
    invocation_range: Option<ByteRange>,
    node_range: Option<ByteRange>,
    target_range: Option<ByteRange>,
    macro_definition: Option<&'a DefinitionReferenceKey>,
    selected_macro_rule: Option<ByteRange>,
}

fn expansion_sibling_role(
    node: &crate::dependency_graph::ExpansionNode,
) -> Result<ExpansionSiblingRole<'_>, SnapshotError> {
    let leaf = node.key.0.last().ok_or(SnapshotError::InvalidNode)?;
    Ok(ExpansionSiblingRole {
        // This is the same identity-parent precedence validated by
        // DependencyGraph::new when it checks the stored key prefix.
        parent: node
            .discovered_in
            .or(node.source_call_parent)
            .or(node.semantic_parent),
        kind: &leaf.kind,
        fragment: leaf.fragment,
        implementation: leaf.implementation,
        invocation_range: leaf.invocation_range,
        node_range: leaf.node_range,
        target_range: leaf.target_range,
        macro_definition: leaf.macro_definition.as_ref(),
        selected_macro_rule: leaf.selected_macro_rule,
    })
}

fn outputless_filtered_expansion_ordinals(
    graph: &DependencyGraph,
    outputless_macro_expansions: &BTreeSet<ExpansionId>,
) -> Result<(Vec<Option<u32>>, OutputlessOrdinalWork), SnapshotError> {
    debug_assert!(!outputless_macro_expansions.is_empty());
    let mut affected_roles = BTreeSet::new();
    for id in outputless_macro_expansions {
        let expansion = graph
            .expansions
            .get(id.0 as usize)
            .filter(|expansion| expansion.id == *id)
            .ok_or(SnapshotError::InvalidNode)?;
        affected_roles.insert(expansion_sibling_role(expansion)?);
    }

    #[cfg(test)]
    let mut work = OutputlessOrdinalWork::default();
    #[cfg(not(test))]
    let work = OutputlessOrdinalWork::default();
    let mut ordinals = vec![None; graph.expansions.len()];
    let mut groups = BTreeMap::<ExpansionSiblingRole<'_>, Vec<(u32, ExpansionId)>>::new();
    for expansion in &graph.expansions {
        #[cfg(test)]
        {
            work.expansion_visits += 1;
        }
        let leaf = expansion.key.0.last().ok_or(SnapshotError::InvalidNode)?;
        let raw_ordinal = leaf.same_role_ordinal;
        *ordinals
            .get_mut(expansion.id.0 as usize)
            .ok_or(SnapshotError::InvalidNode)? = Some(raw_ordinal);
        let role = expansion_sibling_role(expansion)?;
        if affected_roles.contains(&role) {
            #[cfg(test)]
            {
                work.grouped_expansions += 1;
            }
            groups
                .entry(role)
                .or_default()
                .push((raw_ordinal, expansion.id));
        }
    }

    for members in groups.values_mut() {
        members.sort_unstable();
        let mut excluded_before = 0_u32;
        let mut previous = None;
        for &(raw_ordinal, id) in members.iter() {
            if previous == Some(raw_ordinal)
                || graph
                    .expansions
                    .get(id.0 as usize)
                    .is_none_or(|candidate| candidate.id != id)
            {
                return Err(SnapshotError::InvalidNode);
            }
            previous = Some(raw_ordinal);
            if outputless_macro_expansions.contains(&id) {
                *ordinals
                    .get_mut(id.0 as usize)
                    .ok_or(SnapshotError::InvalidNode)? = None;
                excluded_before = excluded_before
                    .checked_add(1)
                    .ok_or(SnapshotError::InvalidNode)?;
                continue;
            }
            *ordinals
                .get_mut(id.0 as usize)
                .ok_or(SnapshotError::InvalidNode)? = Some(
                raw_ordinal
                    .checked_sub(excluded_before)
                    .ok_or(SnapshotError::InvalidNode)?,
            );
        }
    }
    Ok((ordinals, work))
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct ExpansionSubtreeShape {
    leaf: ExpansionKeyPart,
    children: Vec<u32>,
}

fn expansion_subtree_ranks(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    raw_ids: &BTreeMap<ExpansionKey, ExpansionId>,
    by_depth: &[(usize, ExpansionId)],
) -> Result<Vec<Option<u32>>, SnapshotError> {
    let mut children = vec![Vec::new(); graph.expansions.len()];
    let mut ids_by_depth = BTreeMap::<usize, Vec<ExpansionId>>::new();
    for &(depth, id) in by_depth {
        ids_by_depth.entry(depth).or_default().push(id);
        if depth == 1 {
            continue;
        }
        let raw = expansion_key(graph, id)?;
        let parent = raw_ids
            .get(&ExpansionKey(raw.0[..depth - 1].to_vec()))
            .copied()
            .filter(|parent| selected.contains(&GraphNode::Expansion(*parent)))
            .ok_or(SnapshotError::InvalidNode)?;
        children[parent.0 as usize].push(id);
    }

    let mut ranks = vec![None; graph.expansions.len()];
    for (&depth, ids) in ids_by_depth.iter().rev() {
        let mut shapes = Vec::with_capacity(ids.len());
        for &id in ids {
            let mut leaf = expansion_key(graph, id)?.0[depth - 1].clone();
            leaf.same_role_ordinal = 0;
            let mut child_ranks = children[id.0 as usize]
                .iter()
                .map(|child| {
                    ranks
                        .get(child.0 as usize)
                        .copied()
                        .flatten()
                        .ok_or(SnapshotError::InvalidNode)
                })
                .collect::<Result<Vec<_>, _>>()?;
            child_ranks.sort_unstable();
            shapes.push((
                id,
                ExpansionSubtreeShape {
                    leaf,
                    children: child_ranks,
                },
            ));
        }
        let rank_by_shape = shapes
            .iter()
            .map(|(_, shape)| shape.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(rank, shape)| {
                u32::try_from(rank)
                    .map(|rank| (shape, rank))
                    .map_err(|_| SnapshotError::InvalidNode)
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        for (id, shape) in shapes {
            ranks[id.0 as usize] = rank_by_shape.get(&shape).copied();
        }
    }
    Ok(ranks)
}

fn generated_by_witness(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    expansion: ExpansionId,
) -> Result<BTreeSet<DefinitionKey>, SnapshotError> {
    graph
        .edges
        .iter()
        .filter(|edge| {
            edge.to == GraphNode::Expansion(expansion)
                && edge.kind == DependencyKind::GeneratedBy
                && selected.contains(&edge.from)
        })
        .map(|edge| match edge.from {
            GraphNode::Definition(id) => definition_key(graph, id).cloned(),
            _ => Err(SnapshotError::InvalidEdge),
        })
        .collect()
}

fn generated_by_subtree_witness(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    expansion: ExpansionId,
) -> Result<BTreeSet<DefinitionKey>, SnapshotError> {
    let prefix = &expansion_key(graph, expansion)?.0;
    let mut witness = BTreeSet::new();
    for edge in graph
        .edges
        .iter()
        .filter(|edge| edge.kind == DependencyKind::GeneratedBy)
    {
        let GraphNode::Expansion(target) = edge.to else {
            return Err(SnapshotError::InvalidEdge);
        };
        if !selected.contains(&edge.to) || !expansion_key(graph, target)?.0.starts_with(prefix) {
            continue;
        }
        let GraphNode::Definition(id) = edge.from else {
            return Err(SnapshotError::InvalidEdge);
        };
        if selected.contains(&edge.from) {
            witness.insert(definition_key(graph, id)?.clone());
        }
    }
    Ok(witness)
}

fn expansion_use_witness(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    expansion: ExpansionId,
    source_filter: Option<SourceFilter<'_>>,
) -> Result<BTreeSet<DefinitionKey>, SnapshotError> {
    let mut witness = BTreeSet::new();
    for edge in graph.edges.iter().filter(|edge| {
        edge.to == GraphNode::Expansion(expansion)
            && edge.kind == DependencyKind::ExpansionUse
            && selected.contains(&edge.from)
    }) {
        if snapshot_observation_sites(&edge.sites, source_filter)?.is_none() {
            continue;
        }
        let GraphNode::Definition(id) = edge.from else {
            return Err(SnapshotError::InvalidEdge);
        };
        witness.insert(definition_key(graph, id)?.clone());
    }
    Ok(witness)
}

fn snapshot_observation_sites(
    observations: &[ObservationSite],
    source_filter: Option<SourceFilter<'_>>,
) -> Result<Option<Vec<SnapshotObservationSite>>, SnapshotError> {
    let mut sites = BTreeSet::new();
    for site in observations {
        if let ObservationSite::Source(range) = site
            && let Some((source_sites, retained_units)) = source_filter
            && !source_site_is_retained(source_sites, retained_units, *range)
                .map_err(|_| SnapshotError::InvalidSourceSite)?
        {
            continue;
        }
        sites.insert(snapshot_observation_site(site));
    }
    Ok((observations.is_empty() || !sites.is_empty()).then(|| sites.into_iter().collect()))
}

fn selected_node_survives_rewrite(
    graph: &DependencyGraph,
    pieces: &[crate::rewrite::SourcePiece],
    surviving_expansions: &[bool],
    node: GraphNode,
) -> Result<Option<GraphNode>, SnapshotError> {
    let id = match node {
        GraphNode::Definition(id) => id,
        GraphNode::Expansion(id) => {
            return surviving_expansions
                .get(id.0 as usize)
                .copied()
                .map(|survives| survives.then_some(node))
                .ok_or(SnapshotError::InvalidNode);
        }
        GraphNode::ExternalDefinition(_) | GraphNode::Proof(_) | GraphNode::Mono(_) => {
            return Ok(Some(node));
        }
    };
    let definition = graph
        .definitions
        .definitions
        .get(id.0 as usize)
        .filter(|definition| definition.id == id)
        .ok_or(SnapshotError::InvalidNode)?;
    let crate::graph::DefinitionOrigin::Written {
        anchor,
        unit_kind: crate::source::WrittenUnitKind::UseItem,
        ..
    } = definition.origin
    else {
        return Ok(Some(node));
    };
    if definition.kind != crate::graph::DefinitionKind::Use || anchor.start == anchor.end {
        return Err(SnapshotError::InvalidNode);
    }
    let last_byte = anchor.end - 1;
    Ok(pieces
        .iter()
        .any(|piece| {
            piece.original_range.start <= last_byte && last_byte < piece.original_range.end
        })
        .then_some(node))
}

fn surviving_expansions(
    graph: &DependencyGraph,
    source: &SourceInventory,
    retained_units: &BTreeSet<crate::source::SourceUnitId>,
) -> Result<Vec<bool>, SnapshotError> {
    crate::dependency_graph::expansion_source_survival(&graph.expansions, |unit| {
        let written = source.units.get(unit.0 as usize).filter(|written| {
            written.id == unit
                && written.kind == crate::source::WrittenUnitKind::MacroInvocation
                && written.cfg_state == crate::source::CfgState::Active
        })?;
        Some(retained_units.contains(&written.id))
    })
    .ok_or(SnapshotError::InvalidNode)
}

fn snapshot_observation_site(site: &ObservationSite) -> SnapshotObservationSite {
    match site {
        ObservationSite::Source(range) => SnapshotObservationSite::Source(*range),
        ObservationSite::ExternalSource => SnapshotObservationSite::ExternalSource,
        ObservationSite::AllocationOffset(_) => SnapshotObservationSite::AllocationReference,
        ObservationSite::VTableSlot(slot) => SnapshotObservationSite::VTableSlot(*slot),
        ObservationSite::CompilerGenerated => SnapshotObservationSite::CompilerGenerated,
    }
}

fn snapshot_dependency_kind(kind: &DependencyKind) -> DependencyKind {
    let mut kind = kind.clone();
    if let DependencyKind::ProofRelation { relation, ordinal } = &mut kind
        && matches!(
            *relation,
            ProofRelationKind::TraceObligation
                | ProofRelationKind::TraceTraitSelection
                | ProofRelationKind::TraceProjection
                | ProofRelationKind::TraceFulfillment
                | ProofRelationKind::TraceCycle
        )
    {
        // These ordinals index query-local trace collections. The target
        // ProofKey, retained by SnapshotEdge::to, is the semantic identity.
        *ordinal = 0;
    }
    kind
}

fn snapshot_node(
    graph: &DependencyGraph,
    expansion_keys: &[ExpansionKey],
    node: GraphNode,
) -> Result<(SnapshotNodeKey, SnapshotNodeDecision), SnapshotError> {
    match node {
        GraphNode::Definition(id) => Ok((
            SnapshotNodeKey::Definition(definition_key(graph, id)?.clone()),
            SnapshotNodeDecision::Definition,
        )),
        GraphNode::ExternalDefinition(id) => Ok((
            SnapshotNodeKey::ExternalDefinition(external_definition_key(graph, id)?.clone()),
            SnapshotNodeDecision::ExternalDefinition,
        )),
        GraphNode::Expansion(id) => {
            let node = graph
                .expansions
                .get(id.0 as usize)
                .filter(|node| node.id == id)
                .ok_or(SnapshotError::InvalidNode)?;
            Ok((
                SnapshotNodeKey::Expansion(snapshot_expansion_key(expansion_keys, id)?.clone()),
                SnapshotNodeDecision::Expansion(SnapshotExpansionDecision {
                    kind: node.kind.clone(),
                    fragment: node.fragment,
                    implementation: node.implementation,
                    discovered_in: optional_expansion_key(expansion_keys, node.discovered_in)?,
                    semantic_parent: optional_expansion_key(expansion_keys, node.semantic_parent)?,
                    source_call_parent: optional_expansion_key(
                        expansion_keys,
                        node.source_call_parent,
                    )?,
                    source_owner: node
                        .source_owner
                        .map(|owner| definition_key(graph, owner).cloned())
                        .transpose()?,
                    macro_definition: node
                        .macro_definition
                        .map(|target| definition_target_key(graph, target))
                        .transpose()?,
                }),
            ))
        }
        GraphNode::Proof(id) => {
            let node = graph
                .proofs
                .get(id.0 as usize)
                .filter(|node| node.id == id)
                .ok_or(SnapshotError::InvalidNode)?;
            Ok((
                SnapshotNodeKey::Proof(node.key.clone()),
                SnapshotNodeDecision::Proof(snapshot_proof_decision(graph, &node.kind)?),
            ))
        }
        GraphNode::Mono(id) => {
            let node = graph
                .mono_nodes
                .get(id.0 as usize)
                .filter(|node| node.id == id)
                .ok_or(SnapshotError::InvalidNode)?;
            Ok((
                SnapshotNodeKey::Mono(node.key.clone()),
                SnapshotNodeDecision::Mono {
                    materialized_definition: node
                        .materialized_definition
                        .map(|target| definition_target_key(graph, target))
                        .transpose()?,
                },
            ))
        }
    }
}

fn snapshot_proof_decision(
    graph: &DependencyGraph,
    kind: &ProofNodeKind,
) -> Result<SnapshotProofDecision, SnapshotError> {
    Ok(match kind {
        ProofNodeKind::Obligation {
            environment,
            predicate,
            source,
            selection_nested,
            fulfillment_nested,
            query_trace,
        } => SnapshotProofDecision::Obligation {
            environment: environment.clone(),
            predicate: predicate.clone(),
            source: source
                .as_ref()
                .map(|source| snapshot_selection_source(graph, source))
                .transpose()?,
            selection_nested: optional_proof_keys(graph, selection_nested.as_deref())?,
            fulfillment_nested: optional_proof_keys(graph, fulfillment_nested.as_deref())?,
            query_trace: query_trace
                .as_ref()
                .map(|trace| snapshot_solver_trace(graph, trace))
                .transpose()?,
        },
        ProofNodeKind::Projection {
            environment,
            alias,
            source_kind,
            source,
            outcome,
            selected_trait,
            selected_impl,
            selected_item,
            owners,
            nested,
            query_trace,
            normalized_result,
        } => SnapshotProofDecision::Projection {
            environment: environment.clone(),
            alias: alias.clone(),
            source_kind: *source_kind,
            source: source.clone(),
            outcome: outcome.clone(),
            selected_trait: selected_trait
                .map(|id| proof_key(graph, id).cloned())
                .transpose()?,
            selected_impl: selected_impl
                .map(|target| definition_target_key(graph, target))
                .transpose()?,
            selected_item: selected_item
                .map(|target| definition_target_key(graph, target))
                .transpose()?,
            owners: proof_keys(graph, owners)?,
            nested: proof_keys(graph, nested)?,
            query_trace: query_trace
                .as_ref()
                .map(|trace| snapshot_solver_trace(graph, trace))
                .transpose()?,
            normalized_result: normalized_result.clone(),
        },
        ProofNodeKind::AssociatedItem {
            request,
            raw_instance,
            codegen_instance,
            selection,
            source_kind,
            leaf,
            defining_node,
            finalizing_node,
            ancestor_path,
        } => SnapshotProofDecision::AssociatedItem {
            request: request.clone(),
            raw_instance: raw_instance.clone(),
            codegen_instance: codegen_instance.clone(),
            selection: proof_key(graph, *selection)?.clone(),
            source_kind: *source_kind,
            leaf: leaf
                .map(|target| definition_target_key(graph, target))
                .transpose()?,
            defining_node: defining_node
                .map(|node| snapshot_specialization_node(graph, node))
                .transpose()?,
            finalizing_node: finalizing_node
                .map(|node| snapshot_specialization_node(graph, node))
                .transpose()?,
            ancestor_path: ancestor_path
                .iter()
                .copied()
                .map(|node| snapshot_specialization_node(graph, node))
                .collect::<Result<_, _>>()?,
        },
        ProofNodeKind::Cycle {
            members,
            coinductive,
        } => SnapshotProofDecision::Cycle {
            members: proof_keys(graph, members)?,
            coinductive: *coinductive,
        },
    })
}

fn snapshot_selection_source(
    graph: &DependencyGraph,
    source: &SelectionSource,
) -> Result<SnapshotSelectionSource, SnapshotError> {
    Ok(SnapshotSelectionSource {
        kind: source.kind,
        term: source.term.clone(),
        implementation: source
            .implementation
            .map(|target| definition_target_key(graph, target))
            .transpose()?,
        builtin_trait: source
            .builtin_trait
            .map(|target| snapshot_builtin_trait_target(graph, target))
            .transpose()?,
    })
}

fn snapshot_builtin_trait_target(
    graph: &DependencyGraph,
    target: BuiltinTraitTarget,
) -> Result<SnapshotBuiltinTraitTarget, SnapshotError> {
    Ok(SnapshotBuiltinTraitTarget {
        kind: target.kind,
        target: definition_target_key(graph, target.target)?,
    })
}

fn snapshot_solver_trace(
    graph: &DependencyGraph,
    trace: &SolverTracePayload,
) -> Result<SnapshotSolverTrace, SnapshotError> {
    Ok(SnapshotSolverTrace {
        root: proof_key(graph, trace.root)?.clone(),
        obligations: sorted_unique_proof_keys(graph, &trace.obligations)?,
        trait_selections: sorted_unique_proof_keys(graph, &trace.trait_selections)?,
        projections: sorted_unique_proof_keys(graph, &trace.projections)?,
        fulfillments: sorted_unique_proof_keys(graph, &trace.fulfillments)?,
        cycles: sorted_unique_proof_keys(graph, &trace.cycles)?,
    })
}

fn sorted_unique_proof_keys(
    graph: &DependencyGraph,
    ids: &[ProofId],
) -> Result<Vec<ProofKey>, SnapshotError> {
    let mut keys = proof_keys(graph, ids)?;
    keys.sort();
    keys.dedup();
    Ok(keys)
}

fn snapshot_specialization_node(
    graph: &DependencyGraph,
    node: SpecializationNode,
) -> Result<SnapshotSpecializationNode, SnapshotError> {
    Ok(SnapshotSpecializationNode {
        kind: node.kind,
        target: definition_target_key(graph, node.target)?,
    })
}

fn optional_proof_keys(
    graph: &DependencyGraph,
    ids: Option<&[ProofId]>,
) -> Result<Option<Vec<ProofKey>>, SnapshotError> {
    ids.map(|ids| proof_keys(graph, ids)).transpose()
}

fn proof_keys(graph: &DependencyGraph, ids: &[ProofId]) -> Result<Vec<ProofKey>, SnapshotError> {
    ids.iter()
        .map(|&id| proof_key(graph, id).cloned())
        .collect()
}

fn node_key(
    graph: &DependencyGraph,
    expansion_keys: &[ExpansionKey],
    node: GraphNode,
) -> Result<SnapshotNodeKey, SnapshotError> {
    match node {
        GraphNode::Definition(id) => Ok(SnapshotNodeKey::Definition(
            definition_key(graph, id)?.clone(),
        )),
        GraphNode::ExternalDefinition(id) => Ok(SnapshotNodeKey::ExternalDefinition(
            external_definition_key(graph, id)?.clone(),
        )),
        GraphNode::Expansion(id) => Ok(SnapshotNodeKey::Expansion(
            snapshot_expansion_key(expansion_keys, id)?.clone(),
        )),
        GraphNode::Proof(id) => Ok(SnapshotNodeKey::Proof(proof_key(graph, id)?.clone())),
        GraphNode::Mono(id) => Ok(SnapshotNodeKey::Mono(mono_key(graph, id)?.clone())),
    }
}

fn definition_target_key(
    graph: &DependencyGraph,
    target: DefinitionTarget,
) -> Result<DefinitionReferenceKey, SnapshotError> {
    match target {
        DefinitionTarget::Local(id) => Ok(DefinitionReferenceKey::Local(
            definition_key(graph, id)?.clone(),
        )),
        DefinitionTarget::External(id) => Ok(DefinitionReferenceKey::External(
            external_definition_key(graph, id)?.clone(),
        )),
    }
}

fn definition_key(
    graph: &DependencyGraph,
    id: DefinitionId,
) -> Result<&DefinitionKey, SnapshotError> {
    graph
        .definitions
        .definitions
        .get(id.0 as usize)
        .filter(|definition| definition.id == id)
        .map(|definition| &definition.key)
        .ok_or(SnapshotError::InvalidNode)
}

fn external_definition_key(
    graph: &DependencyGraph,
    id: ExternalDefinitionId,
) -> Result<&ExternalDefinitionKey, SnapshotError> {
    graph
        .definitions
        .external_definitions
        .get(id.0 as usize)
        .filter(|definition| definition.id == id)
        .map(|definition| &definition.key)
        .ok_or(SnapshotError::InvalidNode)
}

fn optional_expansion_key(
    expansion_keys: &[ExpansionKey],
    id: Option<ExpansionId>,
) -> Result<Option<ExpansionKey>, SnapshotError> {
    id.map(|id| snapshot_expansion_key(expansion_keys, id).cloned())
        .transpose()
}

fn snapshot_expansion_key(
    expansion_keys: &[ExpansionKey],
    id: ExpansionId,
) -> Result<&ExpansionKey, SnapshotError> {
    expansion_keys
        .get(id.0 as usize)
        .ok_or(SnapshotError::InvalidNode)
}

fn expansion_key(graph: &DependencyGraph, id: ExpansionId) -> Result<&ExpansionKey, SnapshotError> {
    graph
        .expansions
        .get(id.0 as usize)
        .filter(|node| node.id == id)
        .map(|node| &node.key)
        .ok_or(SnapshotError::InvalidNode)
}

fn proof_key(graph: &DependencyGraph, id: ProofId) -> Result<&ProofKey, SnapshotError> {
    graph
        .proofs
        .get(id.0 as usize)
        .filter(|node| node.id == id)
        .map(|node| &node.key)
        .ok_or(SnapshotError::InvalidNode)
}

fn mono_key(graph: &DependencyGraph, id: MonoId) -> Result<&MonoKey, SnapshotError> {
    graph
        .mono_nodes
        .get(id.0 as usize)
        .filter(|node| node.id == id)
        .map(|node| &node.key)
        .ok_or(SnapshotError::InvalidNode)
}

fn first_set_difference<T: Clone + Ord>(
    original: &BTreeSet<T>,
    reduced: &BTreeSet<T>,
) -> Option<(Option<T>, Option<T>)> {
    let mut original = original.iter();
    let mut reduced = reduced.iter();
    let mut left = original.next();
    let mut right = reduced.next();
    loop {
        match (left, right) {
            (None, None) => return None,
            (Some(value), None) => return Some((Some(value.clone()), None)),
            (None, Some(value)) => return Some((None, Some(value.clone()))),
            (Some(left_value), Some(right_value)) => match left_value.cmp(right_value) {
                Ordering::Less => return Some((Some(left_value.clone()), None)),
                Ordering::Greater => return Some((None, Some(right_value.clone()))),
                Ordering::Equal => {
                    left = original.next();
                    right = reduced.next();
                }
            },
        }
    }
}

fn first_map_difference<K: Clone + Ord, V: Clone + Eq>(
    original: &BTreeMap<K, V>,
    reduced: &BTreeMap<K, V>,
) -> Option<(K, Option<V>, Option<V>)> {
    let mut original = original.iter();
    let mut reduced = reduced.iter();
    let mut left = original.next();
    let mut right = reduced.next();
    loop {
        match (left, right) {
            (None, None) => return None,
            (Some((key, value)), None) => {
                return Some((key.clone(), Some(value.clone()), None));
            }
            (None, Some((key, value))) => {
                return Some((key.clone(), None, Some(value.clone())));
            }
            (Some((left_key, left_value)), Some((right_key, right_value))) => {
                match left_key.cmp(right_key) {
                    Ordering::Less => {
                        return Some((left_key.clone(), Some(left_value.clone()), None));
                    }
                    Ordering::Greater => {
                        return Some((right_key.clone(), None, Some(right_value.clone())));
                    }
                    Ordering::Equal if left_value != right_value => {
                        return Some((
                            left_key.clone(),
                            Some(left_value.clone()),
                            Some(right_value.clone()),
                        ));
                    }
                    Ordering::Equal => {
                        left = original.next();
                        right = reduced.next();
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::dependency_graph::{
        DependencyEdge, EvidenceOrigin, ExpansionFragmentKind, ExpansionKeyPart, ExpansionNode,
        MacroStyle, MonoNode, ProofNode, RootRecord,
    };
    use crate::graph::{
        Definition, DefinitionGraph, DefinitionKeyPart, DefinitionKind, DefinitionOrigin,
        DefinitionOriginKey, ExternalDefinition,
    };
    use crate::source::{
        AtomicGroupId, CfgState, OriginalOffsetMap, OwnedPiece, PieceKind, SourceUnitId,
        WrittenUnit, WrittenUnitKind,
    };

    fn definition_key(name: &str, start: u32) -> DefinitionKey {
        DefinitionKey(vec![DefinitionKeyPart {
            kind: DefinitionKind::Function,
            origin: DefinitionOriginKey::Written {
                anchor: ByteRange {
                    start,
                    end: start + 1,
                },
                unit_kind: WrittenUnitKind::Item,
            },
            name: Some(name.into()),
            same_role_ordinal: 0,
        }])
    }

    fn written_definition(
        id: u32,
        kind: DefinitionKind,
        unit_kind: WrittenUnitKind,
        start: u32,
        end: u32,
    ) -> Definition {
        let anchor = ByteRange { start, end };
        let origin = DefinitionOrigin::Written {
            unit: SourceUnitId(id),
            unit_range: anchor,
            anchor,
            unit_kind,
            unit_ordinal: 0,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![DefinitionKeyPart {
                kind,
                origin: origin.key(),
                name: None,
                same_role_ordinal: 0,
            }]),
            kind,
            parent: None,
            origin,
        }
    }

    fn snapshot() -> CompilerDecisionSnapshot {
        let entry_definition = definition_key("entry", 0);
        let entry_instance = MonoKey::Static {
            definition: entry_definition.clone(),
        };
        CompilerDecisionSnapshot {
            roots: BTreeSet::from([SnapshotRoot {
                node: SnapshotNodeKey::Mono(entry_instance.clone()),
                reason: RootReason::ExplicitEntry,
            }]),
            nodes: BTreeMap::from([
                (
                    SnapshotNodeKey::Definition(entry_definition),
                    SnapshotNodeDecision::Definition,
                ),
                (
                    SnapshotNodeKey::Mono(entry_instance),
                    SnapshotNodeDecision::Mono {
                        materialized_definition: None,
                    },
                ),
            ]),
            edges: BTreeSet::new(),
        }
    }

    fn snapshot_entry_instance(snapshot: &CompilerDecisionSnapshot) -> &MonoKey {
        let SnapshotNodeKey::Mono(instance) = &snapshot
            .roots
            .first()
            .expect("the fixture snapshot has one entry root")
            .node
        else {
            panic!("the fixture entry root must be a mono node")
        };
        instance
    }

    fn snapshot_entry_definition(snapshot: &CompilerDecisionSnapshot) -> &DefinitionKey {
        let MonoKey::Static { definition } = snapshot_entry_instance(snapshot) else {
            panic!("the fixture entry root must be a static mono node")
        };
        definition
    }

    fn term(value: u8) -> CanonicalCompilerTerm {
        CanonicalCompilerTerm {
            schema_version: 1,
            bytes: vec![value],
        }
    }

    fn graph_with_proof_ids(cycle: ProofId, obligation: ProofId) -> DependencyGraph {
        let definition_key = definition_key("main", 0);
        let origin = DefinitionOrigin::Written {
            unit: SourceUnitId(0),
            unit_range: ByteRange { start: 0, end: 1 },
            anchor: ByteRange { start: 0, end: 1 },
            unit_kind: WrittenUnitKind::Item,
            unit_ordinal: 0,
        };
        let obligation_key = ProofKey::Obligation {
            environment: term(1),
            predicate: term(2),
        };
        let cycle_key = ProofKey::Cycle {
            members: vec![obligation_key.clone()],
            coinductive: true,
        };
        let mut proofs = vec![
            ProofNode {
                id: cycle,
                key: cycle_key,
                kind: ProofNodeKind::Cycle {
                    members: vec![obligation],
                    coinductive: true,
                },
            },
            ProofNode {
                id: obligation,
                key: obligation_key,
                kind: ProofNodeKind::Obligation {
                    environment: term(1),
                    predicate: term(2),
                    source: None,
                    selection_nested: None,
                    fulfillment_nested: None,
                    query_trace: None,
                },
            },
        ];
        proofs.sort_by_key(|node| node.id);
        let main_key = MonoKey::Static {
            definition: definition_key.clone(),
        };
        DependencyGraph {
            definitions: DefinitionGraph {
                definitions: vec![Definition {
                    id: DefinitionId(0),
                    key: definition_key,
                    kind: DefinitionKind::Function,
                    parent: None,
                    origin,
                }],
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions: Vec::new(),
            proofs,
            mono_nodes: vec![MonoNode {
                id: MonoId(0),
                key: main_key,
                materialized_definition: None,
                allocation_observation: None,
            }],
            edges: vec![
                DependencyEdge {
                    from: GraphNode::Mono(MonoId(0)),
                    to: GraphNode::Proof(cycle),
                    kind: DependencyKind::SelectionProof {
                        relation: crate::dependency_graph::MonoDependencyKind::CompilerRequirement,
                        collection: crate::dependency_graph::MonoCollection::Used,
                    },
                    sites: vec![ObservationSite::CompilerGenerated],
                    evidence: EvidenceOrigin::Compiler,
                },
                DependencyEdge {
                    from: GraphNode::Proof(cycle),
                    to: GraphNode::Proof(obligation),
                    kind: DependencyKind::ProofRelation {
                        relation: crate::dependency_graph::ProofRelationKind::CycleMember,
                        ordinal: 0,
                    },
                    sites: Vec::new(),
                    evidence: EvidenceOrigin::PatchedObserver,
                },
            ],
            roots: vec![RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::ExternalSymbol,
            }],
        }
    }

    fn graph_with_trace_collection_order(reverse: bool) -> DependencyGraph {
        let mut graph = graph_with_proof_ids(ProofId(0), ProofId(1));
        graph.proofs.push(ProofNode {
            id: ProofId(2),
            key: ProofKey::Obligation {
                environment: term(3),
                predicate: term(4),
            },
            kind: ProofNodeKind::Obligation {
                environment: term(3),
                predicate: term(4),
                source: None,
                selection_nested: None,
                fulfillment_nested: None,
                query_trace: None,
            },
        });
        let projection = |id, environment, alias, owner| ProofNode {
            id,
            key: ProofKey::Projection {
                environment: term(environment),
                alias: term(alias),
            },
            kind: ProofNodeKind::Projection {
                environment: term(environment),
                alias: term(alias),
                source_kind: ProjectionSourceKind::NoApplicableCandidate,
                source: term(alias),
                outcome: ProjectionOutcome::NoProgress { term: term(alias) },
                selected_trait: None,
                selected_impl: None,
                selected_item: None,
                owners: vec![owner],
                nested: Vec::new(),
                query_trace: None,
                normalized_result: None,
            },
        };
        graph.proofs.push(projection(ProofId(3), 5, 6, ProofId(1)));
        graph.proofs.push(projection(ProofId(4), 7, 8, ProofId(2)));
        let second_cycle_key = ProofKey::Cycle {
            members: vec![graph.proofs[2].key.clone()],
            coinductive: true,
        };
        graph.proofs.push(ProofNode {
            id: ProofId(5),
            key: second_cycle_key,
            kind: ProofNodeKind::Cycle {
                members: vec![ProofId(2)],
                coinductive: true,
            },
        });

        let ordered = |forward: [ProofId; 2]| {
            if reverse {
                vec![forward[1], forward[0]]
            } else {
                forward.to_vec()
            }
        };
        let obligations = ordered([ProofId(1), ProofId(2)]);
        let trait_selections = obligations.clone();
        let projections = ordered([ProofId(3), ProofId(4)]);
        let fulfillments = obligations.clone();
        let cycles = ordered([ProofId(0), ProofId(5)]);
        let ProofNodeKind::Obligation { query_trace, .. } = &mut graph.proofs[1].kind else {
            panic!("the trace root must be an obligation")
        };
        *query_trace = Some(SolverTracePayload {
            root: ProofId(1),
            obligations: obligations.clone(),
            trait_selections: trait_selections.clone(),
            projections: projections.clone(),
            fulfillments: fulfillments.clone(),
            cycles: cycles.clone(),
        });
        for (relation, ids) in [
            (ProofRelationKind::TraceObligation, obligations),
            (ProofRelationKind::TraceTraitSelection, trait_selections),
            (ProofRelationKind::TraceProjection, projections),
            (ProofRelationKind::TraceFulfillment, fulfillments),
            (ProofRelationKind::TraceCycle, cycles),
        ] {
            graph.edges.extend(
                ids.into_iter()
                    .enumerate()
                    .map(|(ordinal, to)| DependencyEdge {
                        from: GraphNode::Proof(ProofId(1)),
                        to: GraphNode::Proof(to),
                        kind: DependencyKind::ProofRelation {
                            relation,
                            ordinal: u32::try_from(ordinal).unwrap(),
                        },
                        sites: Vec::new(),
                        evidence: EvidenceOrigin::PatchedObserver,
                    }),
            );
        }
        graph.edges.push(DependencyEdge {
            from: GraphNode::Proof(ProofId(1)),
            to: GraphNode::Proof(ProofId(1)),
            kind: DependencyKind::ProofRelation {
                relation: ProofRelationKind::QueryTraceRoot,
                ordinal: 0,
            },
            sites: Vec::new(),
            evidence: EvidenceOrigin::PatchedObserver,
        });
        graph.edges.push(DependencyEdge {
            from: GraphNode::Proof(ProofId(5)),
            to: GraphNode::Proof(ProofId(2)),
            kind: DependencyKind::ProofRelation {
                relation: ProofRelationKind::CycleMember,
                ordinal: 0,
            },
            sites: Vec::new(),
            evidence: EvidenceOrigin::PatchedObserver,
        });
        graph
    }

    fn two_item_inventory() -> SourceInventory {
        let source = Arc::<str>::from(";;");
        let (normalized, offsets) = OriginalOffsetMap::from_source(&source).unwrap();
        SourceInventory {
            original: source,
            normalized: Arc::from(normalized),
            offsets,
            units: vec![
                WrittenUnit {
                    id: SourceUnitId(0),
                    kind: WrittenUnitKind::CrateRoot,
                    full_range: ByteRange { start: 0, end: 2 },
                    parent: None,
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(0),
                    same_role_ordinal: 0,
                },
                WrittenUnit {
                    id: SourceUnitId(1),
                    kind: WrittenUnitKind::Item,
                    full_range: ByteRange { start: 0, end: 1 },
                    parent: Some(SourceUnitId(0)),
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(1),
                    same_role_ordinal: 0,
                },
                WrittenUnit {
                    id: SourceUnitId(2),
                    kind: WrittenUnitKind::Item,
                    full_range: ByteRange { start: 1, end: 2 },
                    parent: Some(SourceUnitId(0)),
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(2),
                    same_role_ordinal: 0,
                },
            ],
            pieces: vec![
                OwnedPiece {
                    range: ByteRange { start: 0, end: 1 },
                    owner: SourceUnitId(1),
                    kind: PieceKind::Token,
                },
                OwnedPiece {
                    range: ByteRange { start: 1, end: 2 },
                    owner: SourceUnitId(2),
                    kind: PieceKind::Token,
                },
            ],
            derive_targets: Vec::new(),
            macro_rules: Vec::new(),
            macro_templates: Vec::new(),
            macro_capture_slots: Vec::new(),
            macro_repetitions: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn two_macro_inventory() -> SourceInventory {
        let mut inventory = two_item_inventory();
        inventory.units[1].kind = WrittenUnitKind::MacroInvocation;
        inventory.units[2].kind = WrittenUnitKind::MacroInvocation;
        inventory
    }

    fn four_unit_inventory() -> SourceInventory {
        SourceInventory {
            original: Arc::from("abcd"),
            normalized: Arc::from("abcd"),
            offsets: OriginalOffsetMap::from_source("abcd").unwrap().1,
            units: vec![
                WrittenUnit {
                    id: SourceUnitId(0),
                    kind: WrittenUnitKind::CrateRoot,
                    full_range: ByteRange { start: 0, end: 4 },
                    parent: None,
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(0),
                    same_role_ordinal: 0,
                },
                WrittenUnit {
                    id: SourceUnitId(1),
                    kind: WrittenUnitKind::Item,
                    full_range: ByteRange { start: 1, end: 2 },
                    parent: Some(SourceUnitId(0)),
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(1),
                    same_role_ordinal: 0,
                },
                WrittenUnit {
                    id: SourceUnitId(2),
                    kind: WrittenUnitKind::Item,
                    full_range: ByteRange { start: 2, end: 3 },
                    parent: Some(SourceUnitId(0)),
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(2),
                    same_role_ordinal: 1,
                },
                WrittenUnit {
                    id: SourceUnitId(3),
                    kind: WrittenUnitKind::Item,
                    full_range: ByteRange { start: 3, end: 4 },
                    parent: Some(SourceUnitId(0)),
                    cfg_state: CfgState::Active,
                    atomic_group: AtomicGroupId(3),
                    same_role_ordinal: 2,
                },
            ],
            pieces: (0..4)
                .map(|start| OwnedPiece {
                    range: ByteRange {
                        start,
                        end: start + 1,
                    },
                    owner: SourceUnitId(start),
                    kind: PieceKind::Token,
                })
                .collect(),
            derive_targets: Vec::new(),
            macro_rules: Vec::new(),
            macro_templates: Vec::new(),
            macro_capture_slots: Vec::new(),
            macro_repetitions: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn external_definition(id: u32) -> ExternalDefinition {
        ExternalDefinition {
            id: ExternalDefinitionId(id),
            key: external_definition_key_for_fixture(ExternalDefinitionId(id)),
            path: format!("fixture::macro_{id}"),
        }
    }

    fn expansion_node(
        id: u32,
        parent: Option<ExpansionId>,
        written_invocation: Option<SourceUnitId>,
        definition: ExternalDefinitionId,
        invocation_range: Option<ByteRange>,
    ) -> ExpansionNode {
        let kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: format!("macro_{id}"),
        };
        let macro_definition = DefinitionTarget::External(definition);
        ExpansionNode {
            id: ExpansionId(id),
            key: ExpansionKey(vec![ExpansionKeyPart {
                kind: kind.clone(),
                fragment: Some(ExpansionFragmentKind::Items),
                implementation: Some(MacroImplementationKind::Declarative),
                invocation_range,
                node_range: invocation_range,
                target_range: None,
                macro_definition: Some(DefinitionReferenceKey::External(
                    external_definition_key_for_fixture(definition),
                )),
                selected_macro_rule: None,
                same_role_ordinal: 0,
            }]),
            kind,
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            discovered_in: parent,
            semantic_parent: parent,
            source_call_parent: parent,
            written_invocation,
            source_owner: Some(DefinitionId(0)),
            macro_definition: Some(macro_definition),
        }
    }

    fn external_definition_key_for_fixture(id: ExternalDefinitionId) -> ExternalDefinitionKey {
        ExternalDefinitionKey {
            crate_identity: 7,
            crate_name: "fixture".into(),
            def_path_hash: [id.0 as u8; 16],
        }
    }

    fn expansion_branch_edges(
        root: ExpansionId,
        child: ExpansionId,
        root_definition: ExternalDefinitionId,
        child_definition: ExternalDefinitionId,
        source_range: ByteRange,
    ) -> Vec<DependencyEdge> {
        let edge = |from, to, kind, sites| DependencyEdge {
            from,
            to,
            kind,
            sites,
            evidence: EvidenceOrigin::Compiler,
        };
        vec![
            edge(
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Expansion(root),
                DependencyKind::ExpansionUse,
                vec![ObservationSite::Source(source_range)],
            ),
            edge(
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Expansion(child),
                DependencyKind::ExpansionUse,
                vec![ObservationSite::CompilerGenerated],
            ),
            edge(
                GraphNode::Expansion(child),
                GraphNode::Expansion(root),
                DependencyKind::ExpansionDiscoveredIn,
                Vec::new(),
            ),
            edge(
                GraphNode::Expansion(child),
                GraphNode::Expansion(root),
                DependencyKind::ExpansionSemanticParent,
                Vec::new(),
            ),
            edge(
                GraphNode::Expansion(child),
                GraphNode::Expansion(root),
                DependencyKind::ExpansionSourceCallParent,
                Vec::new(),
            ),
            edge(
                GraphNode::Expansion(root),
                GraphNode::ExternalDefinition(root_definition),
                DependencyKind::MacroDefinition,
                Vec::new(),
            ),
            edge(
                GraphNode::Expansion(child),
                GraphNode::ExternalDefinition(child_definition),
                DependencyKind::MacroDefinition,
                Vec::new(),
            ),
        ]
    }

    #[derive(Clone, Copy)]
    enum SiblingWitness {
        UniqueGeneratedBy,
        UniqueExpansionUse,
        Empty,
        Duplicate,
    }

    fn graph_with_expansion_sibling_order(
        by_raw_ordinal: [DefinitionId; 3],
        witness: SiblingWitness,
    ) -> DependencyGraph {
        let definitions = (0..4)
            .map(|id| {
                let name = if id == 0 {
                    "main".to_owned()
                } else {
                    format!("product_{id}")
                };
                let origin = DefinitionOrigin::Written {
                    unit: SourceUnitId(id),
                    unit_range: ByteRange {
                        start: id,
                        end: id + 1,
                    },
                    anchor: ByteRange {
                        start: id,
                        end: id + 1,
                    },
                    unit_kind: WrittenUnitKind::Item,
                    unit_ordinal: id,
                };
                Definition {
                    id: DefinitionId(id),
                    key: DefinitionKey(vec![DefinitionKeyPart {
                        kind: DefinitionKind::Function,
                        origin: origin.key(),
                        name: Some(name),
                        same_role_ordinal: 0,
                    }]),
                    kind: DefinitionKind::Function,
                    parent: None,
                    origin,
                }
            })
            .collect::<Vec<_>>();
        let root_kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "outer".into(),
        };
        let root_part = ExpansionKeyPart {
            kind: root_kind.clone(),
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: Some(ByteRange { start: 8, end: 9 }),
            node_range: Some(ByteRange { start: 8, end: 9 }),
            target_range: None,
            macro_definition: None,
            selected_macro_rule: None,
            same_role_ordinal: 0,
        };
        let child_kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "inner".into(),
        };
        let child_part = ExpansionKeyPart {
            kind: child_kind.clone(),
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: None,
            node_range: None,
            target_range: None,
            macro_definition: None,
            selected_macro_rule: None,
            same_role_ordinal: 0,
        };
        let mut expansions = vec![ExpansionNode {
            id: ExpansionId(0),
            key: ExpansionKey(vec![root_part.clone()]),
            kind: root_kind,
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            discovered_in: None,
            semantic_parent: None,
            source_call_parent: None,
            written_invocation: None,
            source_owner: Some(DefinitionId(0)),
            macro_definition: None,
        }];
        for (raw_ordinal, &owner) in by_raw_ordinal.iter().enumerate() {
            let mut part = child_part.clone();
            part.same_role_ordinal = raw_ordinal as u32;
            expansions.push(ExpansionNode {
                id: ExpansionId(raw_ordinal as u32 + 1),
                key: ExpansionKey(vec![root_part.clone(), part]),
                kind: child_kind.clone(),
                fragment: Some(ExpansionFragmentKind::Items),
                implementation: Some(MacroImplementationKind::Declarative),
                discovered_in: Some(ExpansionId(0)),
                semantic_parent: Some(ExpansionId(0)),
                source_call_parent: Some(ExpansionId(0)),
                written_invocation: None,
                source_owner: Some(match witness {
                    SiblingWitness::UniqueGeneratedBy => DefinitionId(0),
                    SiblingWitness::UniqueExpansionUse
                    | SiblingWitness::Empty
                    | SiblingWitness::Duplicate => owner,
                }),
                macro_definition: None,
            });
        }
        let edge = |from, to, kind, sites| DependencyEdge {
            from,
            to,
            kind,
            sites,
            evidence: EvidenceOrigin::Compiler,
        };
        let mut edges = vec![edge(
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Expansion(ExpansionId(0)),
            DependencyKind::ExpansionUse,
            vec![ObservationSite::CompilerGenerated],
        )];
        for (raw_ordinal, &owner) in by_raw_ordinal.iter().enumerate() {
            let expansion = ExpansionId(raw_ordinal as u32 + 1);
            for kind in [
                DependencyKind::ExpansionDiscoveredIn,
                DependencyKind::ExpansionSemanticParent,
                DependencyKind::ExpansionSourceCallParent,
            ] {
                edges.push(edge(
                    GraphNode::Expansion(expansion),
                    GraphNode::Expansion(ExpansionId(0)),
                    kind,
                    Vec::new(),
                ));
            }
            match witness {
                SiblingWitness::UniqueGeneratedBy => edges.push(edge(
                    GraphNode::Definition(owner),
                    GraphNode::Expansion(expansion),
                    DependencyKind::GeneratedBy,
                    Vec::new(),
                )),
                SiblingWitness::UniqueExpansionUse => edges.push(edge(
                    GraphNode::Definition(owner),
                    GraphNode::Expansion(expansion),
                    DependencyKind::ExpansionUse,
                    vec![ObservationSite::CompilerGenerated],
                )),
                SiblingWitness::Empty => {}
                SiblingWitness::Duplicate => {
                    edges.push(edge(
                        GraphNode::Definition(owner),
                        GraphNode::Expansion(expansion),
                        DependencyKind::ExpansionUse,
                        vec![ObservationSite::CompilerGenerated],
                    ));
                    edges.push(edge(
                        GraphNode::Definition(DefinitionId(1)),
                        GraphNode::Expansion(expansion),
                        DependencyKind::GeneratedBy,
                        Vec::new(),
                    ));
                }
            }
        }
        let main_key = definitions[0].key.clone();
        DependencyGraph {
            definitions: DefinitionGraph {
                definitions,
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions,
            proofs: Vec::new(),
            mono_nodes: vec![MonoNode {
                id: MonoId(0),
                key: MonoKey::Static {
                    definition: main_key,
                },
                materialized_definition: None,
                allocation_observation: None,
            }],
            edges,
            roots: vec![RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::ExternalSymbol,
            }],
        }
    }

    #[derive(Clone, Copy)]
    enum IndirectSiblingWitness {
        Unique,
        Duplicate,
        Empty,
    }

    fn graph_with_indirect_expansion_sibling_order(
        by_raw_ordinal: [DefinitionId; 3],
        witness: IndirectSiblingWitness,
    ) -> DependencyGraph {
        let mut graph =
            graph_with_expansion_sibling_order(by_raw_ordinal, SiblingWitness::UniqueGeneratedBy);
        graph
            .edges
            .retain(|edge| edge.kind != DependencyKind::GeneratedBy);

        let descendant_kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "descendant".into(),
        };
        let descendant_part = ExpansionKeyPart {
            kind: descendant_kind.clone(),
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: None,
            node_range: None,
            target_range: None,
            macro_definition: None,
            selected_macro_rule: None,
            same_role_ordinal: 0,
        };
        let edge = |from, to, kind, sites| DependencyEdge {
            from,
            to,
            kind,
            sites,
            evidence: EvidenceOrigin::Compiler,
        };
        for (raw_ordinal, owner) in by_raw_ordinal.into_iter().enumerate() {
            let parent = ExpansionId(raw_ordinal as u32 + 1);
            let child = ExpansionId(raw_ordinal as u32 + 4);
            let mut key = graph.expansions[parent.0 as usize].key.clone();
            key.0.push(descendant_part.clone());
            graph.expansions.push(ExpansionNode {
                id: child,
                key,
                kind: descendant_kind.clone(),
                fragment: Some(ExpansionFragmentKind::Items),
                implementation: Some(MacroImplementationKind::Declarative),
                discovered_in: Some(parent),
                semantic_parent: Some(parent),
                source_call_parent: Some(parent),
                written_invocation: None,
                source_owner: Some(owner),
                macro_definition: None,
            });
            graph.edges.push(edge(
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Expansion(parent),
                DependencyKind::ExpansionUse,
                vec![ObservationSite::CompilerGenerated],
            ));
            for kind in [
                DependencyKind::ExpansionDiscoveredIn,
                DependencyKind::ExpansionSemanticParent,
                DependencyKind::ExpansionSourceCallParent,
            ] {
                graph.edges.push(edge(
                    GraphNode::Expansion(child),
                    GraphNode::Expansion(parent),
                    kind,
                    Vec::new(),
                ));
            }
            if !matches!(witness, IndirectSiblingWitness::Empty) {
                graph.edges.push(edge(
                    GraphNode::Definition(match witness {
                        IndirectSiblingWitness::Unique => owner,
                        IndirectSiblingWitness::Duplicate => DefinitionId(1),
                        IndirectSiblingWitness::Empty => unreachable!(),
                    }),
                    GraphNode::Expansion(child),
                    DependencyKind::GeneratedBy,
                    Vec::new(),
                ));
            }
            graph.edges.push(edge(
                GraphNode::Definition(owner),
                GraphNode::Expansion(child),
                DependencyKind::ExpansionUse,
                vec![ObservationSite::CompilerGenerated],
            ));
        }
        graph
    }

    fn graph_with_structural_expansion_sibling_order(
        by_raw_ordinal: [DefinitionId; 3],
        witness: IndirectSiblingWitness,
    ) -> DependencyGraph {
        let mut graph = graph_with_indirect_expansion_sibling_order(by_raw_ordinal, witness);
        for (raw_ordinal, owner) in by_raw_ordinal.into_iter().enumerate() {
            let child = raw_ordinal + 4;
            graph.expansions[child].key.0[2].selected_macro_rule = Some(ByteRange {
                start: 100 + owner.0,
                end: 101 + owner.0,
            });
        }
        graph
    }

    fn remove_parent_expansion_use_for_owner(
        graph: &mut DependencyGraph,
        by_raw_ordinal: [DefinitionId; 3],
        owner: DefinitionId,
    ) {
        let raw_ordinal = by_raw_ordinal
            .iter()
            .position(|candidate| *candidate == owner)
            .expect("the owner must identify one sibling");
        let target = GraphNode::Expansion(ExpansionId(raw_ordinal as u32 + 1));
        graph.edges.retain(|edge| {
            !(edge.kind == DependencyKind::ExpansionUse
                && edge.from == GraphNode::Definition(DefinitionId(0))
                && edge.to == target)
        });
    }

    fn add_descendant_generated_by_for_owner(
        graph: &mut DependencyGraph,
        by_raw_ordinal: [DefinitionId; 3],
        owner: DefinitionId,
    ) {
        let raw_ordinal = by_raw_ordinal
            .iter()
            .position(|candidate| *candidate == owner)
            .expect("the owner must identify one sibling");
        graph.edges.push(DependencyEdge {
            from: GraphNode::Definition(owner),
            to: GraphNode::Expansion(ExpansionId(raw_ordinal as u32 + 4)),
            kind: DependencyKind::GeneratedBy,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        });
    }

    #[test]
    fn numeric_allocation_offsets_have_one_canonical_site() {
        assert_eq!(
            snapshot_observation_site(&ObservationSite::AllocationOffset(1)),
            snapshot_observation_site(&ObservationSite::AllocationOffset(u64::MAX))
        );
        assert_eq!(
            snapshot_observation_site(&ObservationSite::VTableSlot(1)),
            SnapshotObservationSite::VTableSlot(1)
        );
    }

    #[test]
    fn dense_proof_ids_do_not_participate_in_identity_or_payload() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_proof_ids(ProofId(0), ProofId(1)))
                .unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_proof_ids(ProofId(1), ProofId(0)))
                .unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn query_local_trace_collection_order_does_not_participate_in_identity() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_trace_collection_order(false)).unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_trace_collection_order(true)).unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn query_local_trace_collections_are_semantic_sets() {
        let graph = graph_with_trace_collection_order(false);
        let ProofNodeKind::Obligation {
            query_trace: Some(trace),
            ..
        } = &graph.proofs[1].kind
        else {
            panic!("the trace root must have a query trace")
        };
        let unique = snapshot_solver_trace(&graph, trace).unwrap();
        let mut reordered_duplicates = trace.clone();
        for ids in [
            &mut reordered_duplicates.obligations,
            &mut reordered_duplicates.trait_selections,
            &mut reordered_duplicates.projections,
            &mut reordered_duplicates.fulfillments,
            &mut reordered_duplicates.cycles,
        ] {
            ids.reverse();
            ids.extend_from_within(..);
        }

        assert_eq!(
            snapshot_solver_trace(&graph, &reordered_duplicates).unwrap(),
            unique
        );
        assert_eq!(unique.obligations.len(), 2);
        assert_eq!(unique.trait_selections.len(), 2);
        assert_eq!(unique.projections.len(), 2);
        assert_eq!(unique.fulfillments.len(), 2);
        assert_eq!(unique.cycles.len(), 2);
    }

    #[test]
    fn used_collection_subsumes_only_the_same_mentioned_observation() {
        let fixture = snapshot();
        let from = SnapshotEdgeFrom::Node(SnapshotNodeKey::Mono(
            snapshot_entry_instance(&fixture).clone(),
        ));
        let mono_to = SnapshotNodeKey::Mono(MonoKey::Static {
            definition: definition_key("required", 10),
        });
        let proof_to = SnapshotNodeKey::Proof(ProofKey::Obligation {
            environment: term(10),
            predicate: term(11),
        });
        let first = SnapshotObservationSite::Source(ByteRange { start: 1, end: 2 });
        let second = SnapshotObservationSite::Source(ByteRange { start: 3, end: 4 });
        let edge = |to: &SnapshotNodeKey, kind, sites| SnapshotEdge {
            from: from.clone(),
            to: to.clone(),
            kind,
            sites,
        };
        let used = edge(
            &mono_to,
            DependencyKind::Mono {
                relation: crate::dependency_graph::MonoDependencyKind::ConstAllocation,
                collection: MonoCollection::Used,
            },
            vec![first],
        );
        let mentioned = edge(
            &mono_to,
            DependencyKind::Mono {
                relation: crate::dependency_graph::MonoDependencyKind::ConstAllocation,
                collection: MonoCollection::Mentioned,
            },
            vec![first, second],
        );
        let selection_used = edge(
            &proof_to,
            DependencyKind::SelectionProof {
                relation: crate::dependency_graph::MonoDependencyKind::VTableConstruction,
                collection: MonoCollection::Used,
            },
            vec![SnapshotObservationSite::CompilerGenerated],
        );
        let selection_mentioned = edge(
            &proof_to,
            DependencyKind::SelectionProof {
                relation: crate::dependency_graph::MonoDependencyKind::VTableConstruction,
                collection: MonoCollection::Mentioned,
            },
            vec![SnapshotObservationSite::CompilerGenerated],
        );

        assert_eq!(
            canonicalize_collection_edges(BTreeSet::from([
                used.clone(),
                mentioned.clone(),
                selection_used.clone(),
                selection_mentioned,
            ])),
            BTreeSet::from([
                used.clone(),
                edge(
                    &mono_to,
                    DependencyKind::Mono {
                        relation: crate::dependency_graph::MonoDependencyKind::ConstAllocation,
                        collection: MonoCollection::Mentioned,
                    },
                    vec![second],
                ),
                selection_used,
            ]),
        );
        let used_only = canonicalize_collection_edges(BTreeSet::from([used]));
        let mentioned_only = canonicalize_collection_edges(BTreeSet::from([mentioned]));
        assert_ne!(used_only, mentioned_only);

        let mut original = fixture.clone();
        original.edges = mentioned_only;
        let mut reduced = fixture;
        reduced.edges = used_only;
        assert!(matches!(
            original.first_difference(&reduced),
            Some(SnapshotDiff::Edge { .. })
        ));
        assert!(matches!(
            reduced.first_difference(&original),
            Some(SnapshotDiff::Edge { .. })
        ));
    }

    #[test]
    fn source_associated_item_is_independent_of_inlined_mir_owner() {
        let caller_a = SnapshotNodeKey::Mono(MonoKey::Static {
            definition: definition_key("caller_a", 10),
        });
        let caller_b = SnapshotNodeKey::Mono(MonoKey::Static {
            definition: definition_key("caller_b", 20),
        });
        let target = SnapshotNodeKey::Proof(ProofKey::Obligation {
            environment: term(12),
            predicate: term(13),
        });
        let other_target = SnapshotNodeKey::Proof(ProofKey::Obligation {
            environment: term(12),
            predicate: term(14),
        });
        let source = SnapshotObservationSite::Source(ByteRange { start: 40, end: 41 });
        let second_source = SnapshotObservationSite::Source(ByteRange { start: 42, end: 43 });
        let kind = DependencyKind::SelectionProof {
            relation: crate::dependency_graph::MonoDependencyKind::SourceAssociatedItem,
            collection: MonoCollection::Mentioned,
        };
        let make_edge =
            |from: &SnapshotNodeKey,
             to: &SnapshotNodeKey,
             kind: DependencyKind,
             sites: Vec<SnapshotObservationSite>| SnapshotEdge {
                from: SnapshotEdgeFrom::Node(from.clone()),
                to: to.clone(),
                kind,
                sites,
            };
        let project = |edges: Vec<SnapshotEdge>| {
            canonicalize_collection_edges(
                edges
                    .into_iter()
                    .flat_map(project_source_associated_item)
                    .collect(),
            )
        };

        let original_edges = project(vec![
            make_edge(
                &caller_a,
                &target,
                kind.clone(),
                vec![source, second_source],
            ),
            make_edge(&caller_b, &target, kind.clone(), vec![source]),
        ]);
        let reduced_edges = project(vec![make_edge(
            &caller_b,
            &target,
            kind.clone(),
            vec![source, second_source],
        )]);
        assert_eq!(original_edges, reduced_edges);
        assert!(
            original_edges
                .iter()
                .all(|edge| edge.from == SnapshotEdgeFrom::SourceAssociatedItem)
        );

        let mixed = project_source_associated_item(make_edge(
            &caller_a,
            &target,
            kind.clone(),
            vec![
                source,
                SnapshotObservationSite::ExternalSource,
                SnapshotObservationSite::CompilerGenerated,
            ],
        ));
        assert_eq!(mixed.len(), 3);
        assert!(mixed.iter().any(|edge| {
            edge.from == SnapshotEdgeFrom::SourceAssociatedItem && edge.sites == vec![source]
        }));
        assert!(mixed.iter().any(|edge| {
            edge.from == SnapshotEdgeFrom::SourceAssociatedItem
                && edge.sites == vec![SnapshotObservationSite::ExternalSource]
        }));
        assert!(mixed.iter().any(|edge| {
            edge.from == SnapshotEdgeFrom::Node(caller_a.clone())
                && edge.sites == vec![SnapshotObservationSite::CompilerGenerated]
        }));

        assert_eq!(
            project_source_associated_item(make_edge(
                &caller_a,
                &target,
                kind.clone(),
                vec![SnapshotObservationSite::ExternalSource],
            )),
            project_source_associated_item(make_edge(
                &caller_b,
                &target,
                kind.clone(),
                vec![SnapshotObservationSite::ExternalSource],
            ))
        );

        assert_ne!(
            project_source_associated_item(make_edge(
                &caller_a,
                &target,
                kind.clone(),
                vec![SnapshotObservationSite::CompilerGenerated],
            )),
            project_source_associated_item(make_edge(
                &caller_b,
                &target,
                kind.clone(),
                vec![SnapshotObservationSite::CompilerGenerated],
            ))
        );
        assert_ne!(
            original_edges,
            project(vec![make_edge(
                &caller_a,
                &other_target,
                kind.clone(),
                vec![source, second_source],
            )])
        );
        assert_ne!(
            original_edges,
            project(vec![make_edge(
                &caller_a,
                &target,
                kind,
                vec![
                    source,
                    SnapshotObservationSite::Source(ByteRange { start: 43, end: 44 })
                ],
            )])
        );

        let ordinary = DependencyKind::SelectionProof {
            relation: crate::dependency_graph::MonoDependencyKind::DirectCall,
            collection: MonoCollection::Mentioned,
        };
        assert_ne!(
            project_source_associated_item(make_edge(
                &caller_a,
                &target,
                ordinary.clone(),
                vec![source],
            )),
            project_source_associated_item(make_edge(&caller_b, &target, ordinary, vec![source],))
        );
    }

    #[test]
    fn only_top_level_trace_relation_ordinals_are_query_local() {
        for relation in [
            ProofRelationKind::TraceObligation,
            ProofRelationKind::TraceTraitSelection,
            ProofRelationKind::TraceProjection,
            ProofRelationKind::TraceFulfillment,
            ProofRelationKind::TraceCycle,
        ] {
            assert_eq!(
                snapshot_dependency_kind(&DependencyKind::ProofRelation {
                    relation,
                    ordinal: 7,
                }),
                DependencyKind::ProofRelation {
                    relation,
                    ordinal: 0,
                }
            );
        }
        for relation in [
            ProofRelationKind::QueryTraceRoot,
            ProofRelationKind::TraitSelectionNested,
            ProofRelationKind::ProjectionNested,
            ProofRelationKind::FulfillmentNested,
            ProofRelationKind::CycleMember,
        ] {
            let kind = DependencyKind::ProofRelation {
                relation,
                ordinal: 7,
            };
            assert_eq!(snapshot_dependency_kind(&kind), kind);
        }
    }

    #[test]
    fn original_snapshot_excludes_only_deleted_source_observations() {
        let mut original_graph = graph_with_proof_ids(ProofId(0), ProofId(1));
        let retained_edge = DependencyEdge {
            from: GraphNode::Definition(DefinitionId(0)),
            to: GraphNode::Definition(DefinitionId(0)),
            kind: DependencyKind::Definition(crate::graph::DependencyKind::ValuePath),
            sites: vec![ObservationSite::Source(ByteRange { start: 0, end: 1 })],
            evidence: EvidenceOrigin::Compiler,
        };
        original_graph.edges.push(retained_edge.clone());
        original_graph.edges.push(DependencyEdge {
            sites: vec![ObservationSite::Source(ByteRange { start: 1, end: 2 })],
            ..retained_edge.clone()
        });
        let mut reduced_graph = graph_with_proof_ids(ProofId(0), ProofId(1));
        reduced_graph.edges.push(DependencyEdge {
            evidence: EvidenceOrigin::Derived,
            ..retained_edge
        });
        let retention = Retention {
            semantic_required: BTreeSet::new(),
            compile_required: BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Proof(ProofId(0)),
                GraphNode::Proof(ProofId(1)),
                GraphNode::Mono(MonoId(0)),
            ]),
            retained_units: BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
            outputless_macro_expansions: BTreeSet::new(),
        };

        let inventory = two_item_inventory();
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();
        let original =
            CompilerDecisionSnapshot::original(&original_graph, &inventory, &retention, &rewrite)
                .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        assert_eq!(original, reduced);
    }

    #[test]
    fn original_and_reduced_snapshots_preserve_generic_function_and_use_roots() {
        // Generic functions and re-export paths have no monomorphic entry node;
        // their compiler-selected definitions are the semantic root witnesses.
        let definitions = vec![
            written_definition(0, DefinitionKind::Function, WrittenUnitKind::Item, 0, 1),
            written_definition(1, DefinitionKind::Use, WrittenUnitKind::UseItem, 1, 2),
        ];
        let expected_roots = definitions
            .iter()
            .map(|definition| SnapshotRoot {
                node: SnapshotNodeKey::Definition(definition.key.clone()),
                reason: RootReason::ExplicitEntry,
            })
            .collect::<BTreeSet<_>>();
        let graph = DependencyGraph {
            definitions: DefinitionGraph {
                definitions,
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions: Vec::new(),
            proofs: Vec::new(),
            mono_nodes: Vec::new(),
            edges: Vec::new(),
            roots: vec![
                RootRecord {
                    node: GraphNode::Definition(DefinitionId(0)),
                    reason: RootReason::ExplicitEntry,
                },
                RootRecord {
                    node: GraphNode::Definition(DefinitionId(1)),
                    reason: RootReason::ExplicitEntry,
                },
            ],
        };
        let inventory = two_item_inventory();
        let retained_units = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)]);
        let retention = Retention {
            semantic_required: BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
            ]),
            compile_required: BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Definition(DefinitionId(1)),
            ]),
            retained_units,
            outputless_macro_expansions: BTreeSet::new(),
        };
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();

        let original =
            CompilerDecisionSnapshot::original(&graph, &inventory, &retention, &rewrite).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&graph).unwrap();

        assert_eq!(original.roots, expected_roots);
        assert_eq!(original, reduced);
    }

    #[test]
    fn original_snapshot_excludes_only_removed_use_item_prefixes() {
        let graph = DependencyGraph {
            definitions: DefinitionGraph {
                definitions: vec![
                    written_definition(0, DefinitionKind::Use, WrittenUnitKind::UseItem, 0, 1),
                    written_definition(1, DefinitionKind::Use, WrittenUnitKind::UseItem, 1, 2),
                    written_definition(2, DefinitionKind::Use, WrittenUnitKind::UseLeaf, 1, 2),
                    written_definition(3, DefinitionKind::Function, WrittenUnitKind::Item, 1, 2),
                ],
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions: Vec::new(),
            proofs: Vec::new(),
            mono_nodes: Vec::new(),
            edges: Vec::new(),
            roots: Vec::new(),
        };
        let pieces = vec![crate::rewrite::SourcePiece {
            output_range: ByteRange { start: 0, end: 1 },
            original_range: ByteRange { start: 0, end: 1 },
        }];

        assert_eq!(
            selected_node_survives_rewrite(
                &graph,
                &pieces,
                &[],
                GraphNode::Definition(DefinitionId(0)),
            ),
            Ok(Some(GraphNode::Definition(DefinitionId(0))))
        );
        assert_eq!(
            selected_node_survives_rewrite(
                &graph,
                &pieces,
                &[],
                GraphNode::Definition(DefinitionId(1)),
            ),
            Ok(None)
        );
        for id in [DefinitionId(2), DefinitionId(3)] {
            assert_eq!(
                selected_node_survives_rewrite(&graph, &pieces, &[], GraphNode::Definition(id)),
                Ok(Some(GraphNode::Definition(id)))
            );
        }
    }

    #[test]
    fn original_snapshot_excludes_expansions_from_deleted_macro_invocations() {
        let main_key = definition_key("main", 0);
        let main_definition = Definition {
            id: DefinitionId(0),
            key: main_key.clone(),
            kind: DefinitionKind::Function,
            parent: None,
            origin: DefinitionOrigin::Written {
                unit: SourceUnitId(0),
                unit_range: ByteRange { start: 0, end: 2 },
                anchor: ByteRange { start: 0, end: 1 },
                unit_kind: WrittenUnitKind::Item,
                unit_ordinal: 0,
            },
        };
        let external_definitions = (0..4).map(external_definition).collect::<Vec<_>>();
        let expansions = vec![
            expansion_node(
                0,
                None,
                Some(SourceUnitId(1)),
                ExternalDefinitionId(0),
                Some(ByteRange { start: 0, end: 1 }),
            ),
            expansion_node(1, Some(ExpansionId(0)), None, ExternalDefinitionId(1), None),
            expansion_node(
                2,
                None,
                Some(SourceUnitId(2)),
                ExternalDefinitionId(2),
                Some(ByteRange { start: 1, end: 2 }),
            ),
            expansion_node(3, Some(ExpansionId(2)), None, ExternalDefinitionId(3), None),
        ];
        let retained_edges = expansion_branch_edges(
            ExpansionId(0),
            ExpansionId(1),
            ExternalDefinitionId(0),
            ExternalDefinitionId(1),
            ByteRange { start: 0, end: 1 },
        );
        let deleted_edges = expansion_branch_edges(
            ExpansionId(2),
            ExpansionId(3),
            ExternalDefinitionId(2),
            ExternalDefinitionId(3),
            ByteRange { start: 1, end: 2 },
        );
        let mono = MonoNode {
            id: MonoId(0),
            key: MonoKey::Static {
                definition: main_key,
            },
            materialized_definition: None,
            allocation_observation: None,
        };
        let mut edges = retained_edges.clone();
        edges.extend(deleted_edges);
        let original_graph = DependencyGraph {
            definitions: DefinitionGraph {
                definitions: vec![main_definition.clone()],
                external_definitions: external_definitions.clone(),
                edges: Vec::new(),
            },
            expansions: expansions.clone(),
            proofs: Vec::new(),
            mono_nodes: vec![mono.clone()],
            edges,
            roots: vec![RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::ExternalSymbol,
            }],
        };
        let reduced_graph = DependencyGraph {
            definitions: DefinitionGraph {
                definitions: vec![main_definition],
                external_definitions: external_definitions[..2].to_vec(),
                edges: Vec::new(),
            },
            expansions: expansions[..2].to_vec(),
            proofs: Vec::new(),
            mono_nodes: vec![mono],
            edges: retained_edges,
            roots: vec![RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::ExternalSymbol,
            }],
        };
        let compile_required = BTreeSet::from_iter(
            [
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Mono(MonoId(0)),
            ]
            .into_iter()
            .chain((0..4).map(|id| GraphNode::ExternalDefinition(ExternalDefinitionId(id))))
            .chain((0..4).map(|id| GraphNode::Expansion(ExpansionId(id)))),
        );
        let retention = Retention {
            semantic_required: BTreeSet::new(),
            compile_required,
            retained_units: BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
            outputless_macro_expansions: BTreeSet::new(),
        };
        let inventory = two_macro_inventory();
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();

        assert_eq!(
            surviving_expansions(&original_graph, &inventory, &retention.retained_units),
            Ok(vec![true, true, false, false])
        );
        let mut cyclic_graph = original_graph.clone();
        cyclic_graph.expansions[1].discovered_in = None;
        cyclic_graph.expansions[0].discovered_in = Some(ExpansionId(1));
        cyclic_graph.expansions[3].discovered_in = None;
        cyclic_graph.expansions[2].discovered_in = Some(ExpansionId(3));
        assert_eq!(
            surviving_expansions(&cyclic_graph, &inventory, &retention.retained_units),
            Ok(vec![true, true, false, false])
        );
        for kind in [
            DependencyKind::ExpansionDiscoveredIn,
            DependencyKind::ExpansionSemanticParent,
            DependencyKind::ExpansionSourceCallParent,
        ] {
            assert!(original_graph.edges.iter().any(|edge| {
                edge.from == GraphNode::Expansion(ExpansionId(3))
                    && edge.to == GraphNode::Expansion(ExpansionId(2))
                    && edge.kind == kind
            }));
        }

        let original =
            CompilerDecisionSnapshot::original(&original_graph, &inventory, &retention, &rewrite)
                .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        for definition in &external_definitions[..2] {
            assert!(
                original
                    .nodes
                    .contains_key(&SnapshotNodeKey::ExternalDefinition(definition.key.clone()))
            );
        }
        for definition in &external_definitions[2..] {
            assert!(
                !original
                    .nodes
                    .contains_key(&SnapshotNodeKey::ExternalDefinition(definition.key.clone()))
            );
        }
        for expansion in &expansions[..2] {
            assert!(
                original
                    .nodes
                    .contains_key(&SnapshotNodeKey::Expansion(expansion.key.clone()))
            );
        }
        for expansion in &expansions[2..] {
            assert!(
                !original
                    .nodes
                    .contains_key(&SnapshotNodeKey::Expansion(expansion.key.clone()))
            );
        }
        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn snapshots_exclude_only_validated_outputless_macro_expansions() {
        let graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::UniqueExpansionUse,
        );
        let outputless = ExpansionId(2);
        let retained_key = SnapshotNodeKey::Expansion(graph.expansions[1].key.clone());
        let all_nodes = BTreeSet::from_iter(
            graph
                .definitions
                .definitions
                .iter()
                .map(|definition| GraphNode::Definition(definition.id))
                .chain(
                    graph
                        .expansions
                        .iter()
                        .map(|expansion| GraphNode::Expansion(expansion.id)),
                )
                .chain(graph.roots.iter().map(|root| root.node)),
        );
        let inventory = four_unit_inventory();
        let retention = Retention {
            semantic_required: BTreeSet::new(),
            compile_required: all_nodes,
            retained_units: inventory.units.iter().map(|unit| unit.id).collect(),
            outputless_macro_expansions: BTreeSet::from([outputless]),
        };
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();

        let original =
            CompilerDecisionSnapshot::original(&graph, &inventory, &retention, &rewrite).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced_excluding_outputless_macros(
            &graph,
            &retention.outputless_macro_expansions,
        )
        .unwrap();
        let unfiltered = CompilerDecisionSnapshot::reduced(&graph).unwrap();

        let expansion_count = |snapshot: &CompilerDecisionSnapshot| {
            snapshot
                .nodes
                .keys()
                .filter(|key| matches!(key, SnapshotNodeKey::Expansion(_)))
                .count()
        };
        assert_eq!(expansion_count(&original), 3);
        assert_eq!(expansion_count(&reduced), 3);
        assert_eq!(expansion_count(&unfiltered), 4);
        assert!(original.nodes.contains_key(&retained_key));
        assert!(reduced.nodes.contains_key(&retained_key));
        assert_eq!(original, reduced);
        assert!(unfiltered.first_difference(&reduced).is_some());

        assert_eq!(
            CompilerDecisionSnapshot::reduced_excluding_outputless_macros(
                &graph,
                &BTreeSet::from([ExpansionId(99)]),
            ),
            Err(SnapshotError::InvalidNode)
        );
    }

    #[test]
    fn outputless_sibling_removal_compacts_ambiguous_expansion_ordinals() {
        let original_graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Duplicate,
        );
        let outputless = ExpansionId(2);
        let all_nodes = BTreeSet::from_iter(
            original_graph
                .definitions
                .definitions
                .iter()
                .map(|definition| GraphNode::Definition(definition.id))
                .chain(
                    original_graph
                        .expansions
                        .iter()
                        .map(|expansion| GraphNode::Expansion(expansion.id)),
                )
                .chain(original_graph.roots.iter().map(|root| root.node)),
        );
        let inventory = four_unit_inventory();
        let retention = Retention {
            semantic_required: BTreeSet::new(),
            compile_required: all_nodes,
            retained_units: inventory.units.iter().map(|unit| unit.id).collect(),
            outputless_macro_expansions: BTreeSet::from([outputless]),
        };
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();
        let original =
            CompilerDecisionSnapshot::original(&original_graph, &inventory, &retention, &rewrite)
                .unwrap();

        let mut reduced_graph = original_graph.clone();
        reduced_graph.expansions.remove(outputless.0 as usize);
        let shifted = reduced_graph
            .expansions
            .get_mut(outputless.0 as usize)
            .expect("the trailing sibling must shift into the removed slot");
        shifted.id = outputless;
        shifted
            .key
            .0
            .last_mut()
            .expect("the sibling key must have a leaf")
            .same_role_ordinal = 1;
        let remap = |node: &mut GraphNode| match node {
            GraphNode::Expansion(id) if *id == ExpansionId(3) => *id = outputless,
            _ => {}
        };
        reduced_graph.edges.retain(|edge| {
            edge.from != GraphNode::Expansion(outputless)
                && edge.to != GraphNode::Expansion(outputless)
        });
        for edge in &mut reduced_graph.edges {
            remap(&mut edge.from);
            remap(&mut edge.to);
        }
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn generated_definition_witnesses_canonicalize_expansion_sibling_order() {
        let original = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::UniqueGeneratedBy,
        ))
        .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
            SiblingWitness::UniqueGeneratedBy,
        ))
        .unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn descendant_generated_definition_witnesses_canonicalize_expansion_sibling_order() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_indirect_expansion_sibling_order(
                [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
                IndirectSiblingWitness::Unique,
            ))
            .unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_indirect_expansion_sibling_order(
                [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
                IndirectSiblingWitness::Unique,
            ))
            .unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn ambiguous_descendant_generated_definition_witnesses_preserve_raw_order() {
        for witness in [
            IndirectSiblingWitness::Duplicate,
            IndirectSiblingWitness::Empty,
        ] {
            let original =
                CompilerDecisionSnapshot::reduced(&graph_with_indirect_expansion_sibling_order(
                    [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
                    witness,
                ))
                .unwrap();
            let reduced =
                CompilerDecisionSnapshot::reduced(&graph_with_indirect_expansion_sibling_order(
                    [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
                    witness,
                ))
                .unwrap();

            assert_ne!(original, reduced);
            assert!(original.first_difference(&reduced).is_some());
        }
    }

    #[test]
    fn distinct_child_structures_canonicalize_unwitnessed_expansion_siblings() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_structural_expansion_sibling_order(
                [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
                IndirectSiblingWitness::Empty,
            ))
            .unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_structural_expansion_sibling_order(
                [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
                IndirectSiblingWitness::Empty,
            ))
            .unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn ambiguous_generated_witnesses_block_child_structure_refinement() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_structural_expansion_sibling_order(
                [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
                IndirectSiblingWitness::Duplicate,
            ))
            .unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_structural_expansion_sibling_order(
                [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
                IndirectSiblingWitness::Duplicate,
            ))
            .unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn partially_observed_expansion_uses_block_child_structure_refinement() {
        let original_order = [DefinitionId(1), DefinitionId(2), DefinitionId(3)];
        let reduced_order = [DefinitionId(3), DefinitionId(1), DefinitionId(2)];
        let mut original = graph_with_structural_expansion_sibling_order(
            original_order,
            IndirectSiblingWitness::Empty,
        );
        let mut reduced = graph_with_structural_expansion_sibling_order(
            reduced_order,
            IndirectSiblingWitness::Empty,
        );
        remove_parent_expansion_use_for_owner(&mut original, original_order, DefinitionId(1));
        remove_parent_expansion_use_for_owner(&mut reduced, reduced_order, DefinitionId(1));

        let original = CompilerDecisionSnapshot::reduced(&original).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced).unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn partially_observed_generated_descendants_block_child_structure_refinement() {
        let original_order = [DefinitionId(1), DefinitionId(2), DefinitionId(3)];
        let reduced_order = [DefinitionId(3), DefinitionId(1), DefinitionId(2)];
        let mut original = graph_with_structural_expansion_sibling_order(
            original_order,
            IndirectSiblingWitness::Empty,
        );
        let mut reduced = graph_with_structural_expansion_sibling_order(
            reduced_order,
            IndirectSiblingWitness::Empty,
        );
        add_descendant_generated_by_for_owner(&mut original, original_order, DefinitionId(1));
        add_descendant_generated_by_for_owner(&mut reduced, reduced_order, DefinitionId(1));

        let original = CompilerDecisionSnapshot::reduced(&original).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced).unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn changed_descendant_expansion_owner_remains_a_decision_mismatch() {
        let original_graph = graph_with_indirect_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            IndirectSiblingWitness::Unique,
        );
        let mut reduced_graph = original_graph.clone();
        reduced_graph.expansions[6].source_owner = Some(DefinitionId(2));
        let edge = reduced_graph
            .edges
            .iter_mut()
            .find(|edge| {
                edge.kind == DependencyKind::ExpansionUse
                    && edge.to == GraphNode::Expansion(ExpansionId(6))
            })
            .expect("the third descendant must have an expansion-use owner");
        edge.from = GraphNode::Definition(DefinitionId(2));

        let original = CompilerDecisionSnapshot::reduced(&original_graph).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn expansion_use_witnesses_canonicalize_expansion_sibling_order() {
        let original = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::UniqueExpansionUse,
        ))
        .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
            SiblingWitness::UniqueExpansionUse,
        ))
        .unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn removed_expansion_use_sites_do_not_participate_in_identity() {
        let mut graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::UniqueExpansionUse,
        );
        for edge in &mut graph.edges {
            if edge.kind == DependencyKind::ExpansionUse
                && edge.to != GraphNode::Expansion(ExpansionId(0))
            {
                edge.sites = vec![ObservationSite::Source(ByteRange { start: 1, end: 2 })];
            }
        }
        let selected = BTreeSet::from_iter(
            (0..4)
                .map(|id| GraphNode::Definition(DefinitionId(id)))
                .chain((0..4).map(|id| GraphNode::Expansion(ExpansionId(id)))),
        );
        let inventory = two_item_inventory();
        let retained_units = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);
        let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();

        for id in 1..4 {
            assert_eq!(
                expansion_use_witness(
                    &graph,
                    &selected,
                    ExpansionId(id),
                    Some((&source_sites, &retained_units)),
                ),
                Ok(BTreeSet::new())
            );
        }
    }

    #[test]
    fn changed_expansion_use_owners_remain_a_decision_mismatch() {
        let original_graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::UniqueExpansionUse,
        );
        let mut reduced_graph = original_graph.clone();
        reduced_graph.expansions[3].source_owner = Some(DefinitionId(2));
        let edge = reduced_graph
            .edges
            .iter_mut()
            .find(|edge| {
                edge.kind == DependencyKind::ExpansionUse
                    && edge.to == GraphNode::Expansion(ExpansionId(3))
            })
            .expect("the third sibling must have an expansion-use owner");
        edge.from = GraphNode::Definition(DefinitionId(2));

        let original = CompilerDecisionSnapshot::reduced(&original_graph).unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn a_selected_singleton_expansion_uses_ordinal_zero_without_a_witness() {
        let graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Empty,
        );
        let selected = BTreeSet::from([
            GraphNode::Expansion(ExpansionId(0)),
            GraphNode::Expansion(ExpansionId(3)),
        ]);

        assert_eq!(graph.expansions[3].key.0[1].same_role_ordinal, 2);
        let keys = snapshot_expansion_keys(&graph, &selected, None, &BTreeSet::new()).unwrap();
        assert_eq!(keys[3].0[1].same_role_ordinal, 0);
    }

    #[test]
    fn missing_expansion_sibling_witnesses_preserve_raw_order() {
        let graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Empty,
        );
        let selected = BTreeSet::from_iter((0..4).map(|id| GraphNode::Expansion(ExpansionId(id))));

        let keys = snapshot_expansion_keys(&graph, &selected, None, &BTreeSet::new()).unwrap();

        assert_eq!(
            keys[1..]
                .iter()
                .map(|key| key.0[1].same_role_ordinal)
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
    }

    #[test]
    fn only_validated_outputless_siblings_are_removed_from_ambiguous_ordinals() {
        let graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Duplicate,
        );
        let selected = BTreeSet::from([
            GraphNode::Expansion(ExpansionId(0)),
            GraphNode::Expansion(ExpansionId(1)),
            GraphNode::Expansion(ExpansionId(3)),
        ]);

        let ordinary = snapshot_expansion_keys(&graph, &selected, None, &BTreeSet::new()).unwrap();
        let filtered =
            snapshot_expansion_keys(&graph, &selected, None, &BTreeSet::from([ExpansionId(2)]))
                .unwrap();

        assert_eq!(ordinary[3].0[1].same_role_ordinal, 2);
        assert_eq!(filtered[3].0[1].same_role_ordinal, 1);
    }

    #[test]
    fn outputless_ordinal_filter_only_groups_the_affected_deep_sibling_role() {
        const DEPTH: usize = 1_024;
        let kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "recursive".into(),
        };
        let part = ExpansionKeyPart {
            kind: kind.clone(),
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: None,
            node_range: None,
            target_range: None,
            macro_definition: None,
            selected_macro_rule: None,
            same_role_ordinal: 0,
        };
        let mut key = Vec::new();
        let mut expansions = Vec::with_capacity(DEPTH);
        for index in 0..DEPTH {
            key.push(part.clone());
            let id = ExpansionId(index as u32);
            expansions.push(ExpansionNode {
                id,
                key: ExpansionKey(key.clone()),
                kind: kind.clone(),
                fragment: part.fragment,
                implementation: part.implementation,
                discovered_in: (index != 0).then(|| ExpansionId(index as u32 - 1)),
                semantic_parent: None,
                source_call_parent: None,
                written_invocation: None,
                source_owner: None,
                macro_definition: None,
            });
        }
        let graph = DependencyGraph {
            definitions: DefinitionGraph {
                definitions: Vec::new(),
                external_definitions: Vec::new(),
                edges: Vec::new(),
            },
            expansions,
            proofs: Vec::new(),
            mono_nodes: Vec::new(),
            edges: Vec::new(),
            roots: Vec::new(),
        };

        let outputless = ExpansionId(DEPTH as u32 - 1);
        let (filtered, filtered_work) =
            outputless_filtered_expansion_ordinals(&graph, &BTreeSet::from([outputless])).unwrap();
        assert_eq!(filtered[DEPTH - 2], Some(0));
        assert_eq!(filtered[DEPTH - 1], None);
        assert_eq!(filtered_work.expansion_visits, DEPTH);
        assert_eq!(filtered_work.grouped_expansions, 1);
    }

    #[test]
    fn ambiguous_generated_definition_witnesses_preserve_raw_order() {
        let original = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Duplicate,
        ))
        .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&graph_with_expansion_sibling_order(
            [DefinitionId(3), DefinitionId(1), DefinitionId(2)],
            SiblingWitness::Duplicate,
        ))
        .unwrap();

        assert_ne!(original, reduced);
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn reduced_snapshot_preserves_every_reason_for_a_root_node() {
        let mut graph = graph_with_proof_ids(ProofId(0), ProofId(1));
        graph.roots.push(RootRecord {
            node: GraphNode::Mono(MonoId(0)),
            reason: RootReason::ExplicitEntry,
        });
        let node = graph.mono_nodes[0].key.clone();

        let snapshot = CompilerDecisionSnapshot::reduced(&graph).unwrap();

        assert_eq!(
            snapshot.roots,
            BTreeSet::from([
                SnapshotRoot {
                    node: SnapshotNodeKey::Mono(node.clone()),
                    reason: RootReason::ExternalSymbol,
                },
                SnapshotRoot {
                    node: SnapshotNodeKey::Mono(node),
                    reason: RootReason::ExplicitEntry,
                },
            ])
        );
    }

    #[test]
    fn first_difference_reports_a_missing_root() {
        let original = snapshot();
        let mut reduced = original.clone();
        let root = reduced
            .roots
            .pop_first()
            .expect("the fixture snapshot has one entry root");

        assert_eq!(
            original.first_difference(&reduced),
            Some(SnapshotDiff::Root {
                original: Some(root),
                reduced: None,
            })
        );
    }

    #[test]
    fn first_difference_reports_a_root_reason_change() {
        let original = snapshot();
        let mut reduced = original.clone();
        let mut root = reduced
            .roots
            .pop_first()
            .expect("the fixture snapshot has one entry root");
        root.reason = RootReason::ExternalSymbol;
        reduced.roots.insert(root);

        assert!(matches!(
            original.first_difference(&reduced),
            Some(SnapshotDiff::Root { .. })
        ));
    }

    #[test]
    fn first_difference_reports_the_exact_typed_edge() {
        let mut original = snapshot();
        let mut reduced = original.clone();
        let definition = SnapshotNodeKey::Definition(snapshot_entry_definition(&original).clone());
        let mono = SnapshotNodeKey::Mono(snapshot_entry_instance(&original).clone());
        let source = vec![SnapshotObservationSite::Source(ByteRange {
            start: 4,
            end: 8,
        })];
        let original_edge = SnapshotEdge {
            from: SnapshotEdgeFrom::Node(mono.clone()),
            to: definition.clone(),
            kind: DependencyKind::Definition(crate::graph::DependencyKind::ValuePath),
            sites: source.clone(),
        };
        let reduced_edge = SnapshotEdge {
            from: SnapshotEdgeFrom::Node(mono),
            to: definition,
            kind: DependencyKind::Definition(crate::graph::DependencyKind::TypePath),
            sites: source,
        };
        original.edges.insert(original_edge.clone());
        reduced.edges.insert(reduced_edge.clone());

        assert_eq!(
            original.first_difference(&reduced),
            Some(SnapshotDiff::Edge {
                original: Some(original_edge),
                reduced: None,
            })
        );
    }

    #[test]
    fn node_payload_difference_is_reported_under_the_semantic_key() {
        let original = snapshot();
        let mut reduced = original.clone();
        let mono = SnapshotNodeKey::Mono(snapshot_entry_instance(&original).clone());
        let target = DefinitionReferenceKey::Local(snapshot_entry_definition(&original).clone());
        reduced.nodes.insert(
            mono.clone(),
            SnapshotNodeDecision::Mono {
                materialized_definition: Some(target),
            },
        );

        assert_eq!(
            original.first_difference(&reduced),
            Some(SnapshotDiff::Node {
                key: mono,
                original: Some(SnapshotNodeDecision::Mono {
                    materialized_definition: None,
                }),
                reduced: Some(SnapshotNodeDecision::Mono {
                    materialized_definition: Some(DefinitionReferenceKey::Local(
                        snapshot_entry_definition(&original).clone(),
                    )),
                }),
            })
        );
    }
}
