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
    AllocationPathSite, AllocationRootKey, BuiltinTraitTarget, DefinitionReferenceKey,
    DependencyGraph, DependencyKind, ExpansionId, ExpansionKey, ExpansionKeyPart, ExpansionKind,
    GraphNode, MacroImplementationKind, MonoId, MonoInstanceKey, MonoInstanceRole, MonoKey,
    ObservationSite, ProjectionOutcome, ProjectionSourceKind, ProofId, ProofKey, ProofNodeKind,
    ProofRelationKind, RootReason, SelectionSource, SelectionSourceKind, SolverTracePayload,
    SpecializationNode, SpecializationNodeKind,
};
use crate::digest::sha256;
use crate::graph::{
    DefinitionId, DefinitionKey, DefinitionOriginKey, DefinitionTarget, ExternalDefinitionId,
    ExternalDefinitionKey,
};
use crate::retention::{Retention, source_site_is_retained};
use crate::rewrite::SourceRewrite;
use crate::source::{ByteRange, SourceInventory};

const SNAPSHOT_SCHEMA: u8 = 3;

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
pub(crate) struct SnapshotEdge {
    pub from: SnapshotNodeKey,
    pub to: SnapshotNodeKey,
    pub kind: DependencyKind,
    pub sites: Vec<SnapshotObservationSite>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SnapshotRoot {
    pub node: MonoKey,
    pub reason: RootReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompilerDecisionSnapshot {
    main_definition: DefinitionKey,
    main_instance: MonoKey,
    compiler_required_roots: BTreeSet<SnapshotRoot>,
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
    MainDefinition {
        original: DefinitionKey,
        reduced: DefinitionKey,
    },
    MainInstance {
        original: MonoKey,
        reduced: MonoKey,
    },
    CompilerRequiredRoot {
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
        selected.insert(GraphNode::Mono(graph.main_instance));
        selected.extend(
            graph
                .compiler_required_roots
                .iter()
                .map(|root| GraphNode::Mono(root.node)),
        );
        if !selected.is_subset(&permitted) {
            return Err(SnapshotError::InvalidRoot);
        }

        let source_filter = Some((source, &retention.retained_units));
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
        Self::build(graph, &selected, source_filter)
    }

    /// Builds the observed decision set from the reduced analysis.  Every
    /// local definition is a root so a newly introduced retained definition
    /// cannot hide merely because it is not reachable from `main`.
    pub(crate) fn reduced(graph: &DependencyGraph) -> Result<Self, SnapshotError> {
        let mut selected = graph
            .definitions
            .definitions
            .iter()
            .map(|definition| GraphNode::Definition(definition.id))
            .collect::<BTreeSet<_>>();
        selected.insert(GraphNode::Mono(graph.main_instance));
        selected.extend(
            graph
                .compiler_required_roots
                .iter()
                .map(|root| GraphNode::Mono(root.node)),
        );

        let mut work = selected.iter().copied().collect::<Vec<_>>();
        while let Some(from) = work.pop() {
            for edge in graph.edges.iter().filter(|edge| edge.from == from) {
                if selected.insert(edge.to) {
                    work.push(edge.to);
                }
            }
        }
        Self::build(graph, &selected, None)
    }

    pub(crate) fn hash(&self) -> [u8; 32] {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"RIDSNAP");
        put_u8(&mut bytes, SNAPSHOT_SCHEMA);
        put_definition_key(&mut bytes, &self.main_definition);
        put_mono_key(&mut bytes, &self.main_instance);
        put_len(&mut bytes, self.compiler_required_roots.len());
        for root in &self.compiler_required_roots {
            put_snapshot_root(&mut bytes, root);
        }
        put_len(&mut bytes, self.nodes.len());
        for (key, decision) in &self.nodes {
            put_snapshot_node_key(&mut bytes, key);
            put_snapshot_node_decision(&mut bytes, decision);
        }
        put_len(&mut bytes, self.edges.len());
        for edge in &self.edges {
            put_snapshot_edge(&mut bytes, edge);
        }

        sha256(bytes)
    }

    pub(crate) fn first_difference(&self, reduced: &Self) -> Option<SnapshotDiff> {
        if self.main_definition != reduced.main_definition {
            return Some(SnapshotDiff::MainDefinition {
                original: self.main_definition.clone(),
                reduced: reduced.main_definition.clone(),
            });
        }
        if self.main_instance != reduced.main_instance {
            return Some(SnapshotDiff::MainInstance {
                original: self.main_instance.clone(),
                reduced: reduced.main_instance.clone(),
            });
        }
        if let Some((original, reduced)) = first_set_difference(
            &self.compiler_required_roots,
            &reduced.compiler_required_roots,
        ) {
            return Some(SnapshotDiff::CompilerRequiredRoot { original, reduced });
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
        source_filter: Option<(&SourceInventory, &BTreeSet<crate::source::SourceUnitId>)>,
    ) -> Result<Self, SnapshotError> {
        let expansion_keys = snapshot_expansion_keys(graph, selected, source_filter)?;
        let main_definition = definition_key(graph, graph.main_definition)?.clone();
        let main_instance = mono_key(graph, graph.main_instance)?.clone();
        if !selected.contains(&GraphNode::Definition(graph.main_definition))
            || !selected.contains(&GraphNode::Mono(graph.main_instance))
        {
            return Err(SnapshotError::InvalidRoot);
        }

        let mut compiler_required_roots = BTreeSet::new();
        for root in &graph.compiler_required_roots {
            if !selected.contains(&GraphNode::Mono(root.node))
                || !compiler_required_roots.insert(SnapshotRoot {
                    node: mono_key(graph, root.node)?.clone(),
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
            edges.insert(SnapshotEdge {
                from: node_key(graph, &expansion_keys, edge.from)?,
                to: node_key(graph, &expansion_keys, edge.to)?,
                kind: snapshot_dependency_kind(&edge.kind),
                sites,
            });
        }

        Ok(Self {
            main_definition,
            main_instance,
            compiler_required_roots,
            nodes,
            edges,
        })
    }
}

fn snapshot_expansion_keys(
    graph: &DependencyGraph,
    selected: &BTreeSet<GraphNode>,
    source_filter: Option<(&SourceInventory, &BTreeSet<crate::source::SourceUnitId>)>,
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
    source_filter: Option<(&SourceInventory, &BTreeSet<crate::source::SourceUnitId>)>,
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
    source_filter: Option<(&SourceInventory, &BTreeSet<crate::source::SourceUnitId>)>,
) -> Result<Option<Vec<SnapshotObservationSite>>, SnapshotError> {
    let mut sites = BTreeSet::new();
    for site in observations {
        if let ObservationSite::Source(range) = site
            && let Some((source, retained_units)) = source_filter
            && !source_site_is_retained(source, retained_units, *range)
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
    let mut surviving = graph
        .expansions
        .iter()
        .enumerate()
        .map(|(index, node)| {
            if node.id.0 as usize != index {
                return Err(SnapshotError::InvalidNode);
            }
            let Some(unit) = node.written_invocation else {
                return Ok(true);
            };
            let written = source
                .units
                .get(unit.0 as usize)
                .filter(|written| {
                    written.id == unit
                        && written.kind == crate::source::WrittenUnitKind::MacroInvocation
                        && written.cfg_state == crate::source::CfgState::Active
                })
                .ok_or(SnapshotError::InvalidNode)?;
            Ok(retained_units.contains(&written.id))
        })
        .collect::<Result<Vec<_>, _>>()?;

    loop {
        let mut changed = false;
        for node in &graph.expansions {
            let index = node.id.0 as usize;
            if !surviving[index] {
                continue;
            }
            for parent in [
                node.discovered_in,
                node.semantic_parent,
                node.source_call_parent,
            ]
            .into_iter()
            .flatten()
            {
                let parent_survives = graph
                    .expansions
                    .get(parent.0 as usize)
                    .filter(|node| node.id == parent)
                    .and_then(|_| surviving.get(parent.0 as usize))
                    .copied()
                    .ok_or(SnapshotError::InvalidNode)?;
                if !parent_survives {
                    surviving[index] = false;
                    changed = true;
                    break;
                }
            }
        }
        if !changed {
            return Ok(surviving);
        }
    }
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

fn put_snapshot_root(bytes: &mut Vec<u8>, root: &SnapshotRoot) {
    put_mono_key(bytes, &root.node);
    put_u8(bytes, root.reason as u8);
}

fn put_snapshot_node_key(bytes: &mut Vec<u8>, key: &SnapshotNodeKey) {
    match key {
        SnapshotNodeKey::Definition(key) => {
            put_u8(bytes, 0);
            put_definition_key(bytes, key);
        }
        SnapshotNodeKey::ExternalDefinition(key) => {
            put_u8(bytes, 1);
            put_external_definition_key(bytes, key);
        }
        SnapshotNodeKey::Expansion(key) => {
            put_u8(bytes, 2);
            put_expansion_key(bytes, key);
        }
        SnapshotNodeKey::Proof(key) => {
            put_u8(bytes, 3);
            put_proof_key(bytes, key);
        }
        SnapshotNodeKey::Mono(key) => {
            put_u8(bytes, 4);
            put_mono_key(bytes, key);
        }
    }
}

fn put_snapshot_node_decision(bytes: &mut Vec<u8>, decision: &SnapshotNodeDecision) {
    match decision {
        SnapshotNodeDecision::Definition => put_u8(bytes, 0),
        SnapshotNodeDecision::ExternalDefinition => put_u8(bytes, 1),
        SnapshotNodeDecision::Expansion(decision) => {
            put_u8(bytes, 2);
            put_expansion_kind(bytes, &decision.kind);
            put_option(bytes, decision.fragment.as_ref(), |bytes, value| {
                put_u8(bytes, *value as u8)
            });
            put_option(bytes, decision.implementation.as_ref(), |bytes, value| {
                put_u8(bytes, *value as u8)
            });
            put_option(bytes, decision.discovered_in.as_ref(), put_expansion_key);
            put_option(bytes, decision.semantic_parent.as_ref(), put_expansion_key);
            put_option(
                bytes,
                decision.source_call_parent.as_ref(),
                put_expansion_key,
            );
            put_option(bytes, decision.source_owner.as_ref(), put_definition_key);
            put_option(
                bytes,
                decision.macro_definition.as_ref(),
                put_definition_reference_key,
            );
        }
        SnapshotNodeDecision::Proof(decision) => {
            put_u8(bytes, 3);
            put_proof_decision(bytes, decision);
        }
        SnapshotNodeDecision::Mono {
            materialized_definition,
        } => {
            put_u8(bytes, 4);
            put_option(
                bytes,
                materialized_definition.as_ref(),
                put_definition_reference_key,
            );
        }
    }
}

fn put_proof_decision(bytes: &mut Vec<u8>, decision: &SnapshotProofDecision) {
    match decision {
        SnapshotProofDecision::Obligation {
            environment,
            predicate,
            source,
            selection_nested,
            fulfillment_nested,
            query_trace,
        } => {
            put_u8(bytes, 0);
            put_term(bytes, environment);
            put_term(bytes, predicate);
            put_option(bytes, source.as_ref(), put_selection_source);
            put_option(bytes, selection_nested.as_ref(), |bytes, keys| {
                put_proof_keys(bytes, keys)
            });
            put_option(bytes, fulfillment_nested.as_ref(), |bytes, keys| {
                put_proof_keys(bytes, keys)
            });
            put_option(bytes, query_trace.as_ref(), put_solver_trace);
        }
        SnapshotProofDecision::Projection {
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
        } => {
            put_u8(bytes, 1);
            put_term(bytes, environment);
            put_term(bytes, alias);
            put_u8(bytes, *source_kind as u8);
            put_term(bytes, source);
            put_projection_outcome(bytes, outcome);
            put_option(bytes, selected_trait.as_ref(), put_proof_key);
            put_option(bytes, selected_impl.as_ref(), put_definition_reference_key);
            put_option(bytes, selected_item.as_ref(), put_definition_reference_key);
            put_proof_keys(bytes, owners);
            put_proof_keys(bytes, nested);
            put_option(bytes, query_trace.as_ref(), put_solver_trace);
            put_option(bytes, normalized_result.as_ref(), put_term);
        }
        SnapshotProofDecision::AssociatedItem {
            request,
            raw_instance,
            codegen_instance,
            selection,
            source_kind,
            leaf,
            defining_node,
            finalizing_node,
            ancestor_path,
        } => {
            put_u8(bytes, 2);
            put_term(bytes, request);
            put_mono_instance_key(bytes, raw_instance);
            put_mono_instance_key(bytes, codegen_instance);
            put_proof_key(bytes, selection);
            put_u8(bytes, *source_kind as u8);
            put_option(bytes, leaf.as_ref(), put_definition_reference_key);
            put_option(bytes, defining_node.as_ref(), put_specialization_node);
            put_option(bytes, finalizing_node.as_ref(), put_specialization_node);
            put_len(bytes, ancestor_path.len());
            for node in ancestor_path {
                put_specialization_node(bytes, node);
            }
        }
        SnapshotProofDecision::Cycle {
            members,
            coinductive,
        } => {
            put_u8(bytes, 3);
            put_proof_keys(bytes, members);
            put_bool(bytes, *coinductive);
        }
    }
}

fn put_selection_source(bytes: &mut Vec<u8>, source: &SnapshotSelectionSource) {
    put_u8(bytes, source.kind as u8);
    put_term(bytes, &source.term);
    put_option(
        bytes,
        source.implementation.as_ref(),
        put_definition_reference_key,
    );
    put_option(bytes, source.builtin_trait.as_ref(), |bytes, target| {
        put_u8(bytes, target.kind as u8);
        put_definition_reference_key(bytes, &target.target);
    });
}

fn put_solver_trace(bytes: &mut Vec<u8>, trace: &SnapshotSolverTrace) {
    put_proof_key(bytes, &trace.root);
    put_proof_keys(bytes, &trace.obligations);
    put_proof_keys(bytes, &trace.trait_selections);
    put_proof_keys(bytes, &trace.projections);
    put_proof_keys(bytes, &trace.fulfillments);
    put_proof_keys(bytes, &trace.cycles);
}

fn put_specialization_node(bytes: &mut Vec<u8>, node: &SnapshotSpecializationNode) {
    put_u8(bytes, node.kind as u8);
    put_definition_reference_key(bytes, &node.target);
}

fn put_snapshot_edge(bytes: &mut Vec<u8>, edge: &SnapshotEdge) {
    put_snapshot_node_key(bytes, &edge.from);
    put_snapshot_node_key(bytes, &edge.to);
    put_dependency_kind(bytes, &edge.kind);
    put_len(bytes, edge.sites.len());
    for site in &edge.sites {
        match site {
            SnapshotObservationSite::Source(range) => {
                put_u8(bytes, 0);
                put_range(bytes, *range);
            }
            SnapshotObservationSite::ExternalSource => put_u8(bytes, 1),
            SnapshotObservationSite::AllocationReference => put_u8(bytes, 2),
            SnapshotObservationSite::VTableSlot(slot) => {
                put_u8(bytes, 3);
                put_u64(bytes, *slot);
            }
            SnapshotObservationSite::CompilerGenerated => put_u8(bytes, 4),
        }
    }
}

fn put_dependency_kind(bytes: &mut Vec<u8>, kind: &DependencyKind) {
    match kind {
        DependencyKind::Definition(kind) => {
            put_u8(bytes, 0);
            put_u8(bytes, *kind as u8);
        }
        DependencyKind::ExpansionDiscoveredIn => put_u8(bytes, 1),
        DependencyKind::ExpansionSemanticParent => put_u8(bytes, 2),
        DependencyKind::ExpansionSourceCallParent => put_u8(bytes, 3),
        DependencyKind::MacroDefinition => put_u8(bytes, 4),
        DependencyKind::ExpansionUse => put_u8(bytes, 5),
        DependencyKind::GeneratedBy => put_u8(bytes, 6),
        DependencyKind::SelectionProof {
            relation,
            collection,
        } => {
            put_u8(bytes, 7);
            put_u8(bytes, *relation as u8);
            put_u8(bytes, *collection as u8);
        }
        DependencyKind::ProofRelation { relation, ordinal } => {
            put_u8(bytes, 8);
            put_u8(bytes, *relation as u8);
            put_u32(bytes, *ordinal);
        }
        DependencyKind::MaterializesDefinition => put_u8(bytes, 9),
        DependencyKind::Mono {
            relation,
            collection,
        } => {
            put_u8(bytes, 10);
            put_u8(bytes, *relation as u8);
            put_u8(bytes, *collection as u8);
        }
    }
}

fn put_definition_key(bytes: &mut Vec<u8>, key: &DefinitionKey) {
    put_len(bytes, key.0.len());
    for part in &key.0 {
        put_u8(bytes, part.kind.rank());
        put_definition_origin_key(bytes, &part.origin);
        put_option(bytes, part.name.as_ref(), |bytes, name| {
            put_str(bytes, name)
        });
        put_u32(bytes, part.same_role_ordinal);
    }
}

fn put_definition_origin_key(bytes: &mut Vec<u8>, origin: &DefinitionOriginKey) {
    match origin {
        DefinitionOriginKey::Written { anchor, unit_kind } => {
            put_u8(bytes, 0);
            put_range(bytes, *anchor);
            put_u8(bytes, unit_kind.rank());
        }
        DefinitionOriginKey::Expanded {
            invocation_range,
            generated_role,
        } => {
            put_u8(bytes, 1);
            put_range(bytes, *invocation_range);
            put_option(bytes, generated_role.as_ref(), |bytes, role| {
                put_u8(bytes, *role as u8)
            });
        }
        DefinitionOriginKey::CompilerGenerated { role } => {
            put_u8(bytes, 2);
            put_u8(bytes, *role as u8);
        }
        DefinitionOriginKey::Injected { role } => {
            put_u8(bytes, 3);
            put_u8(bytes, *role as u8);
        }
    }
}

fn put_external_definition_key(bytes: &mut Vec<u8>, key: &ExternalDefinitionKey) {
    put_u64(bytes, key.crate_identity);
    put_str(bytes, &key.crate_name);
    put_raw(bytes, &key.def_path_hash);
}

fn put_definition_reference_key(bytes: &mut Vec<u8>, key: &DefinitionReferenceKey) {
    match key {
        DefinitionReferenceKey::Local(key) => {
            put_u8(bytes, 0);
            put_definition_key(bytes, key);
        }
        DefinitionReferenceKey::External(key) => {
            put_u8(bytes, 1);
            put_external_definition_key(bytes, key);
        }
    }
}

fn put_expansion_key(bytes: &mut Vec<u8>, key: &ExpansionKey) {
    put_len(bytes, key.0.len());
    for part in &key.0 {
        put_expansion_kind(bytes, &part.kind);
        put_option(bytes, part.fragment.as_ref(), |bytes, fragment| {
            put_u8(bytes, *fragment as u8)
        });
        put_option(
            bytes,
            part.implementation.as_ref(),
            |bytes, implementation| put_u8(bytes, *implementation as u8),
        );
        put_option(bytes, part.invocation_range.as_ref(), |bytes, range| {
            put_range(bytes, *range)
        });
        put_option(bytes, part.node_range.as_ref(), |bytes, range| {
            put_range(bytes, *range)
        });
        put_option(bytes, part.target_range.as_ref(), |bytes, range| {
            put_range(bytes, *range)
        });
        put_option(
            bytes,
            part.macro_definition.as_ref(),
            put_definition_reference_key,
        );
        put_option(bytes, part.selected_macro_rule.as_ref(), |bytes, range| {
            put_range(bytes, *range)
        });
        put_u32(bytes, part.same_role_ordinal);
    }
}

fn put_expansion_kind(bytes: &mut Vec<u8>, kind: &ExpansionKind) {
    match kind {
        ExpansionKind::Macro { style, name } => {
            put_u8(bytes, 0);
            put_u8(bytes, *style as u8);
            put_str(bytes, name);
        }
        ExpansionKind::AstPass(kind) => {
            put_u8(bytes, 1);
            put_u8(bytes, *kind as u8);
        }
        ExpansionKind::Desugaring(kind) => {
            put_u8(bytes, 2);
            put_u8(bytes, *kind as u8);
        }
    }
}

fn put_proof_keys(bytes: &mut Vec<u8>, keys: &[ProofKey]) {
    put_len(bytes, keys.len());
    for key in keys {
        put_proof_key(bytes, key);
    }
}

fn put_proof_key(bytes: &mut Vec<u8>, key: &ProofKey) {
    match key {
        ProofKey::Obligation {
            environment,
            predicate,
        } => {
            put_u8(bytes, 0);
            put_term(bytes, environment);
            put_term(bytes, predicate);
        }
        ProofKey::Projection { environment, alias } => {
            put_u8(bytes, 1);
            put_term(bytes, environment);
            put_term(bytes, alias);
        }
        ProofKey::AssociatedItem {
            request,
            raw_instance,
            codegen_instance,
        } => {
            put_u8(bytes, 2);
            put_term(bytes, request);
            put_mono_instance_key(bytes, raw_instance);
            put_mono_instance_key(bytes, codegen_instance);
        }
        ProofKey::Cycle {
            members,
            coinductive,
        } => {
            put_u8(bytes, 3);
            put_proof_keys(bytes, members);
            put_bool(bytes, *coinductive);
        }
    }
}

fn put_mono_key(bytes: &mut Vec<u8>, key: &MonoKey) {
    match key {
        MonoKey::Instance { instance, role } => {
            put_u8(bytes, 0);
            put_mono_instance_key(bytes, instance);
            put_mono_instance_role(bytes, *role);
        }
        MonoKey::Static { definition } => {
            put_u8(bytes, 1);
            put_definition_key(bytes, definition);
        }
        MonoKey::VTable {
            concrete_type,
            trait_reference,
        } => {
            put_u8(bytes, 2);
            put_term(bytes, concrete_type);
            put_option(bytes, trait_reference.as_ref(), put_term);
        }
        MonoKey::Allocation(allocation) => {
            put_u8(bytes, 3);
            put_allocation_root_key(bytes, &allocation.root);
            put_len(bytes, allocation.path.len());
            for part in &allocation.path {
                put_u8(bytes, part.relation as u8);
                put_u8(bytes, part.collection as u8);
                put_allocation_path_site(bytes, part.site);
                put_u32(bytes, part.same_role_ordinal);
            }
        }
    }
}

fn put_mono_instance_key(bytes: &mut Vec<u8>, key: &MonoInstanceKey) {
    put_definition_reference_key(bytes, &key.definition);
    put_term(bytes, &key.arguments);
    put_term(bytes, &key.kind);
}

fn put_mono_instance_role(bytes: &mut Vec<u8>, role: MonoInstanceRole) {
    match role {
        MonoInstanceRole::Callable => put_u8(bytes, 0),
        MonoInstanceRole::Const { promoted } => {
            put_u8(bytes, 1);
            put_option(bytes, promoted.as_ref(), |bytes, value| {
                put_u32(bytes, *value)
            });
        }
    }
}

fn put_allocation_root_key(bytes: &mut Vec<u8>, root: &AllocationRootKey) {
    match root {
        AllocationRootKey::Instance { instance, role } => {
            put_u8(bytes, 0);
            put_mono_instance_key(bytes, instance);
            put_mono_instance_role(bytes, *role);
        }
        AllocationRootKey::Static(definition) => {
            put_u8(bytes, 1);
            put_definition_key(bytes, definition);
        }
        AllocationRootKey::VTable {
            concrete_type,
            trait_reference,
        } => {
            put_u8(bytes, 2);
            put_term(bytes, concrete_type);
            put_option(bytes, trait_reference.as_ref(), put_term);
        }
    }
}

fn put_allocation_path_site(bytes: &mut Vec<u8>, site: AllocationPathSite) {
    match site {
        AllocationPathSite::Source(range) => {
            put_u8(bytes, 0);
            put_range(bytes, range);
        }
        AllocationPathSite::ExternalSource => put_u8(bytes, 1),
        AllocationPathSite::AllocationReference => put_u8(bytes, 2),
        AllocationPathSite::CompilerGenerated => put_u8(bytes, 3),
    }
}

fn put_projection_outcome(bytes: &mut Vec<u8>, outcome: &ProjectionOutcome) {
    match outcome {
        ProjectionOutcome::Progress { raw_term } => {
            put_u8(bytes, 0);
            put_term(bytes, raw_term);
        }
        ProjectionOutcome::NoProgress { term } => {
            put_u8(bytes, 1);
            put_term(bytes, term);
        }
    }
}

fn put_term(bytes: &mut Vec<u8>, term: &CanonicalCompilerTerm) {
    put_u32(bytes, term.schema_version);
    put_raw(bytes, &term.bytes);
}

fn put_option<T>(bytes: &mut Vec<u8>, value: Option<&T>, put: impl FnOnce(&mut Vec<u8>, &T)) {
    match value {
        Some(value) => {
            put_u8(bytes, 1);
            put(bytes, value);
        }
        None => put_u8(bytes, 0),
    }
}

fn put_range(bytes: &mut Vec<u8>, range: ByteRange) {
    put_u32(bytes, range.start);
    put_u32(bytes, range.end);
}

fn put_str(bytes: &mut Vec<u8>, value: &str) {
    put_raw(bytes, value.as_bytes());
}

fn put_raw(bytes: &mut Vec<u8>, value: &[u8]) {
    put_len(bytes, value.len());
    bytes.extend_from_slice(value);
}

fn put_len(bytes: &mut Vec<u8>, value: usize) {
    put_u64(
        bytes,
        u64::try_from(value).expect("owned compiler data length fits u64"),
    );
}

fn put_bool(bytes: &mut Vec<u8>, value: bool) {
    put_u8(bytes, u8::from(value));
}

fn put_u8(bytes: &mut Vec<u8>, value: u8) {
    bytes.push(value);
}

fn put_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::dependency_graph::{
        DependencyEdge, EvidenceOrigin, ExpansionFragmentKind, ExpansionKeyPart, ExpansionNode,
        MacroStyle, MonoNode, ProofNode,
    };
    use crate::graph::{
        Definition, DefinitionGraph, DefinitionKeyPart, DefinitionKind, DefinitionOrigin,
        ExternalDefinition,
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
        let main_definition = definition_key("main", 0);
        let main_instance = MonoKey::Static {
            definition: main_definition.clone(),
        };
        CompilerDecisionSnapshot {
            main_definition: main_definition.clone(),
            main_instance: main_instance.clone(),
            compiler_required_roots: BTreeSet::new(),
            nodes: BTreeMap::from([
                (
                    SnapshotNodeKey::Definition(main_definition),
                    SnapshotNodeDecision::Definition,
                ),
                (
                    SnapshotNodeKey::Mono(main_instance),
                    SnapshotNodeDecision::Mono {
                        materialized_definition: None,
                    },
                ),
            ]),
            edges: BTreeSet::new(),
        }
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
            main_definition: DefinitionId(0),
            main_instance: MonoId(0),
            compiler_required_roots: Vec::new(),
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
        let source = Arc::<str>::from("ab");
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
            macro_rules: Vec::new(),
            ownerless_attribute_invocations: Vec::new(),
        }
    }

    fn two_macro_inventory() -> SourceInventory {
        let mut inventory = two_item_inventory();
        inventory.units[1].kind = WrittenUnitKind::MacroInvocation;
        inventory.units[2].kind = WrittenUnitKind::MacroInvocation;
        inventory
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
            main_definition: DefinitionId(0),
            main_instance: MonoId(0),
            compiler_required_roots: Vec::new(),
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
        assert_eq!(original.hash(), reduced.hash());
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn query_local_trace_collection_order_does_not_participate_in_identity() {
        let original =
            CompilerDecisionSnapshot::reduced(&graph_with_trace_collection_order(false)).unwrap();
        let reduced =
            CompilerDecisionSnapshot::reduced(&graph_with_trace_collection_order(true)).unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.hash(), reduced.hash());
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
            main_semantic: BTreeSet::new(),
            compile_required: BTreeSet::from([
                GraphNode::Definition(DefinitionId(0)),
                GraphNode::Proof(ProofId(0)),
                GraphNode::Proof(ProofId(1)),
                GraphNode::Mono(MonoId(0)),
            ]),
            retained_units: BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
        };

        let inventory = two_item_inventory();
        let rewrite =
            crate::rewrite::rewrite_source(&inventory, &retention.retained_units).unwrap();
        let original =
            CompilerDecisionSnapshot::original(&original_graph, &inventory, &retention, &rewrite)
                .unwrap();
        let reduced = CompilerDecisionSnapshot::reduced(&reduced_graph).unwrap();

        assert_eq!(original, reduced);
        assert_eq!(original.hash(), reduced.hash());
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
            main_definition: DefinitionId(0),
            main_instance: MonoId(0),
            compiler_required_roots: Vec::new(),
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
            main_definition: DefinitionId(0),
            main_instance: MonoId(0),
            compiler_required_roots: Vec::new(),
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
            main_definition: DefinitionId(0),
            main_instance: MonoId(0),
            compiler_required_roots: Vec::new(),
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
            main_semantic: BTreeSet::new(),
            compile_required,
            retained_units: BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
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
        assert_eq!(original.hash(), reduced.hash());
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
        assert_eq!(original.hash(), reduced.hash());
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
        assert_eq!(original.hash(), reduced.hash());
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
            assert_ne!(original.hash(), reduced.hash());
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
        assert_eq!(original.hash(), reduced.hash());
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
        assert_ne!(original.hash(), reduced.hash());
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
        assert_ne!(original.hash(), reduced.hash());
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
        assert_ne!(original.hash(), reduced.hash());
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
        assert_ne!(original.hash(), reduced.hash());
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
        assert_eq!(original.hash(), reduced.hash());
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

        for id in 1..4 {
            assert_eq!(
                expansion_use_witness(
                    &graph,
                    &selected,
                    ExpansionId(id),
                    Some((&inventory, &retained_units)),
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
        assert_ne!(original.hash(), reduced.hash());
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
        let keys = snapshot_expansion_keys(&graph, &selected, None).unwrap();
        assert_eq!(keys[3].0[1].same_role_ordinal, 0);
    }

    #[test]
    fn missing_expansion_sibling_witnesses_preserve_raw_order() {
        let graph = graph_with_expansion_sibling_order(
            [DefinitionId(1), DefinitionId(2), DefinitionId(3)],
            SiblingWitness::Empty,
        );
        let selected = BTreeSet::from_iter((0..4).map(|id| GraphNode::Expansion(ExpansionId(id))));

        let keys = snapshot_expansion_keys(&graph, &selected, None).unwrap();

        assert_eq!(
            keys[1..]
                .iter()
                .map(|key| key.0[1].same_role_ordinal)
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
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
        assert_ne!(original.hash(), reduced.hash());
        assert!(original.first_difference(&reduced).is_some());
    }

    #[test]
    fn equal_snapshots_have_the_same_sha256() {
        let original = snapshot();
        let reduced = snapshot();

        assert_eq!(original, reduced);
        assert_eq!(original.hash(), reduced.hash());
        assert_eq!(original.first_difference(&reduced), None);
    }

    #[test]
    fn first_difference_reports_the_exact_typed_edge() {
        let mut original = snapshot();
        let mut reduced = original.clone();
        let definition = SnapshotNodeKey::Definition(original.main_definition.clone());
        let mono = SnapshotNodeKey::Mono(original.main_instance.clone());
        let source = vec![SnapshotObservationSite::Source(ByteRange {
            start: 4,
            end: 8,
        })];
        let original_edge = SnapshotEdge {
            from: mono.clone(),
            to: definition.clone(),
            kind: DependencyKind::Definition(crate::graph::DependencyKind::ValuePath),
            sites: source.clone(),
        };
        let reduced_edge = SnapshotEdge {
            from: mono,
            to: definition,
            kind: DependencyKind::Definition(crate::graph::DependencyKind::TypePath),
            sites: source,
        };
        original.edges.insert(original_edge.clone());
        reduced.edges.insert(reduced_edge.clone());

        assert_ne!(original.hash(), reduced.hash());
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
        let mono = SnapshotNodeKey::Mono(original.main_instance.clone());
        let target = DefinitionReferenceKey::Local(original.main_definition.clone());
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
                        original.main_definition.clone(),
                    )),
                }),
            })
        );
    }
}
