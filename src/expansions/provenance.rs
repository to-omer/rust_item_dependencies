//! Collection and querying of compiler expansion provenance.

#[cfg(any(rust_item_dependencies_patched, test))]
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
#[cfg(any(rust_item_dependencies_patched, test))]
use std::hash::{DefaultHasher, Hash, Hasher};
#[cfg(rust_item_dependencies_patched)]
use std::sync::Arc;

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{
    MacroDeclarativeExpansion, MacroExpansionOutputStructure,
    MacroImplementationKind as RustcImplementationKind, MacroInputTokenRange,
    MacroInvocationFragmentKind, MacroInvocationOrigin, MacroOutputTokenRange,
    MacroOwnerOutput as RustcMacroOwnerOutput, MacroTranscriberComponentKind,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::{AstPass, DesugaringKind as RustcDesugaringKind};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::{ExpnId, ExpnKind, MacroKind, Span};

#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{
    AstPassKind, DesugaringKind, ExpansionFragmentKind, ExpansionId, ExpansionKind,
    MacroImplementationKind, MacroStyle,
};
use crate::source::SourceInventory;
use crate::source::SourceUnitId;
#[cfg(any(rust_item_dependencies_patched, test))]
use crate::source::{ByteRange, MacroProductSource, SourceUnitIdentityKind};
#[cfg(rust_item_dependencies_patched)]
use crate::source::{
    DeclarativeContributorParent, DeclarativeGenerationParentState, EditableMacroSource,
    EditableMacroSourceResolver, EditableMacroSourceRole, MacroRuleSelectionIndex, SourceError,
    ValidatedDeclarativeOutput, ValidatedDeclarativeOutputMeaning, declarative_generation_parent,
    original_span_range, resolve_declarative_contributor_parent,
};

use super::ExpansionError;
#[cfg(any(rust_item_dependencies_patched, test))]
use super::output::MacroOutputRange;
#[cfg(rust_item_dependencies_patched)]
use super::output::{
    MacroProductIdentityRangeIndex, laminar_output_ranges, normalize_discarded_output_ranges,
    output_range, valid_discarded_output_relations,
};

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy)]
enum AncestorResolution<Id> {
    Target,
    Parent(Id),
    Absent,
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn memoized_ancestor_targets<Id>(
    starts: impl IntoIterator<Item = Id>,
    mut resolution: impl FnMut(Id) -> Option<AncestorResolution<Id>>,
) -> Option<(HashMap<Id, Option<Id>>, usize)>
where
    Id: Copy + Eq + Hash,
{
    let mut targets = HashMap::new();
    let mut resolved_nodes = 0;
    for start in starts {
        if targets.contains_key(&start) {
            continue;
        }
        let mut path = Vec::new();
        let mut active = HashSet::new();
        let mut current = start;
        let target = loop {
            if let Some(target) = targets.get(&current) {
                break *target;
            }
            if !active.insert(current) {
                return None;
            }
            path.push(current);
            resolved_nodes += 1;
            match resolution(current)? {
                AncestorResolution::Target => break Some(current),
                AncestorResolution::Parent(parent) => current = parent,
                AncestorResolution::Absent => break None,
            }
        };
        for node in path {
            targets.insert(node, target);
        }
    }
    Some((targets, resolved_nodes))
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn producer_preparation_plan<Id>(
    identity_required: Vec<Id>,
    coverage_required: Vec<Id>,
) -> Option<Vec<(Id, bool)>>
where
    Id: Copy + Eq + Hash,
{
    let mut identities = HashSet::with_capacity(identity_required.len());
    if identity_required
        .iter()
        .any(|&producer| !identities.insert(producer))
    {
        return None;
    }
    let coverage_count = coverage_required.len();
    let mut coverage = coverage_required.into_iter().collect::<HashSet<_>>();
    if coverage.len() != coverage_count {
        return None;
    }
    let plan = identity_required
        .into_iter()
        .map(|producer| (producer, coverage.remove(&producer)))
        .collect::<Vec<_>>();
    coverage.is_empty().then_some(plan)
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn dependency_postorder<Id>(
    starts: impl IntoIterator<Item = Id>,
    mut dependencies: impl FnMut(Id) -> Option<Vec<Id>>,
) -> Option<(Vec<Id>, usize)>
where
    Id: Copy + Eq + Hash,
{
    let mut states = HashMap::<Id, u8>::new();
    let mut order = Vec::new();
    let mut visits = 0;
    for start in starts {
        let mut stack = vec![(start, false)];
        while let Some((current, expanded)) = stack.pop() {
            match (states.get(&current).copied(), expanded) {
                (Some(2), _) => continue,
                (Some(1), false) => return None,
                (Some(1), true) => {
                    states.insert(current, 2);
                    order.push(current);
                }
                (None, false) => {
                    states.insert(current, 1);
                    visits += 1;
                    stack.push((current, true));
                    let dependencies = dependencies(current)?;
                    stack.extend(
                        dependencies
                            .into_iter()
                            .rev()
                            .map(|dependency| (dependency, false)),
                    );
                }
                (None, true) => return None,
                (Some(_), _) => return None,
            }
        }
    }
    Some((order, visits))
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroContributorSetId(u32);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct MacroContributorNode {
    local: Box<[SourceUnitId]>,
    parents: Box<[MacroContributorSetId]>,
}

/// Canonical, topologically ordered source-contributor sets.
///
/// A node owns only the source units introduced at that node and references
/// previously constructed nodes for inherited contributors. Transitive source
/// sets are never cached on individual nodes.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroContributorDag {
    nodes: Vec<MacroContributorNode>,
}

impl MacroContributorDag {
    pub(crate) fn nodes(
        &self,
    ) -> impl ExactSizeIterator<
        Item = (
            MacroContributorSetId,
            &[SourceUnitId],
            &[MacroContributorSetId],
        ),
    > {
        self.nodes.iter().enumerate().map(|(index, node)| {
            (
                MacroContributorSetId(index as u32),
                node.local.as_ref(),
                node.parents.as_ref(),
            )
        })
    }

    pub(crate) fn node(
        &self,
        id: MacroContributorSetId,
    ) -> Option<(&[SourceUnitId], &[MacroContributorSetId])> {
        self.nodes
            .get(id.0 as usize)
            .map(|node| (node.local.as_ref(), node.parents.as_ref()))
    }

    pub(crate) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn stored_fact_count(&self) -> usize {
        self.nodes
            .iter()
            .map(|node| node.local.len() + node.parents.len())
            .sum()
    }

    /// Returns a DAG with canonical parent-only union nodes appended.
    ///
    /// Existing identifiers remain a stable prefix. This lets later output
    /// validation add retention-only gates without changing the producer-local
    /// provenance roots that were observed while transcribing the macro.
    #[cfg(any(rust_item_dependencies_patched, test))]
    pub(super) fn with_parent_unions(
        &self,
        unions: &[Box<[MacroContributorSetId]>],
    ) -> Result<(Self, Vec<MacroContributorSetId>), ExpansionError> {
        let mut builder = MacroContributorDagBuilder::from_dag(self)?;
        let mut roots = Vec::with_capacity(unions.len());
        for parents in unions {
            if parents.is_empty() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let root = if let [root] = parents.as_ref() {
                *root
            } else {
                builder.intern(Vec::new(), parents.to_vec())?
            };
            roots.push(root);
        }
        Ok((builder.finish(), roots))
    }

    #[cfg(test)]
    fn sources_with_visits(
        &self,
        roots: &[MacroContributorSetId],
    ) -> Result<(Vec<SourceUnitId>, usize), ExpansionError> {
        contributor_sources_with_visits(&self.nodes, roots)
    }

    #[cfg(test)]
    pub(crate) fn test_source_singletons(max_source: Option<u32>) -> Self {
        let mut builder = MacroContributorDagBuilder::default();
        if let Some(max_source) = max_source {
            for source in 0..=max_source {
                let id = builder
                    .intern(vec![SourceUnitId(source)], Vec::new())
                    .unwrap();
                assert_eq!(id.0, source);
            }
        }
        builder.finish()
    }

    #[cfg(test)]
    pub(crate) fn test_source_chain(depth: u32) -> (Self, MacroContributorSetId) {
        assert!(depth > 0);
        let mut builder = MacroContributorDagBuilder::default();
        let mut parent = None;
        for source in 0..depth {
            parent = Some(
                builder
                    .intern(vec![SourceUnitId(source)], parent.into_iter().collect())
                    .unwrap(),
            );
        }
        (builder.finish(), parent.unwrap())
    }

    #[cfg(test)]
    pub(crate) fn test_empty_and_source_root(
        source: SourceUnitId,
    ) -> (Self, MacroContributorSetId, MacroContributorSetId) {
        let mut builder = MacroContributorDagBuilder::default();
        let empty = builder.intern(Vec::new(), Vec::new()).unwrap();
        let source = builder.intern(vec![source], Vec::new()).unwrap();
        (builder.finish(), empty, source)
    }

    #[cfg(test)]
    pub(crate) fn test_source_union(sources: &[SourceUnitId]) -> (Self, MacroContributorSetId) {
        assert!(!sources.is_empty());
        assert!(sources.windows(2).all(|pair| pair[0] < pair[1]));
        let mut builder = MacroContributorDagBuilder::default();
        let roots = sources
            .iter()
            .copied()
            .map(|source| builder.intern(vec![source], Vec::new()).unwrap())
            .collect::<Vec<_>>();
        let union = if let [root] = roots.as_slice() {
            *root
        } else {
            builder.intern(Vec::new(), roots).unwrap()
        };
        (builder.finish(), union)
    }
}

#[cfg(test)]
fn contributor_sources_with_visits(
    nodes: &[MacroContributorNode],
    roots: &[MacroContributorSetId],
) -> Result<(Vec<SourceUnitId>, usize), ExpansionError> {
    if roots.is_empty() || roots.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let mut sources = BTreeSet::new();
    let mut seen = vec![false; nodes.len()];
    let mut stack = roots.to_vec();
    let mut visits = 0;
    while let Some(id) = stack.pop() {
        let index = id.0 as usize;
        let Some(visited) = seen.get_mut(index) else {
            return Err(ExpansionError::IncompleteOrigin);
        };
        if std::mem::replace(visited, true) {
            continue;
        }
        visits += 1;
        let node = nodes.get(index).ok_or(ExpansionError::IncompleteOrigin)?;
        if node.parents.iter().any(|parent| parent.0 as usize >= index) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        sources.extend(node.local.iter().copied());
        stack.extend(node.parents.iter().copied());
    }
    if sources.is_empty() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok((sources.into_iter().collect(), visits))
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Default)]
struct MacroContributorDagBuilder {
    nodes: Vec<MacroContributorNode>,
    canonical: HashMap<u64, Vec<MacroContributorSetId>>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl MacroContributorDagBuilder {
    fn from_dag(dag: &MacroContributorDag) -> Result<Self, ExpansionError> {
        let mut builder = Self::default();
        for (expected, node) in dag.nodes.iter().enumerate() {
            let actual = builder.intern(node.local.to_vec(), node.parents.to_vec())?;
            if actual.0 as usize != expected {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        Ok(builder)
    }

    fn intern(
        &mut self,
        mut local: Vec<SourceUnitId>,
        mut parents: Vec<MacroContributorSetId>,
    ) -> Result<MacroContributorSetId, ExpansionError> {
        local.sort();
        local.dedup();
        parents.sort();
        parents.dedup();
        if parents
            .iter()
            .any(|parent| parent.0 as usize >= self.nodes.len())
        {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let mut hasher = DefaultHasher::new();
        for unit in &local {
            unit.0.hash(&mut hasher);
        }
        parents.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some(ids) = self.canonical.get(&hash) {
            for &id in ids {
                let node = self
                    .nodes
                    .get(id.0 as usize)
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                if node.local.as_ref() == local && node.parents.as_ref() == parents {
                    return Ok(id);
                }
            }
        }

        let id = MacroContributorSetId(
            self.nodes
                .len()
                .try_into()
                .map_err(|_| ExpansionError::IncompleteOrigin)?,
        );
        self.nodes.push(MacroContributorNode {
            local: local.into_boxed_slice(),
            parents: parents.into_boxed_slice(),
        });
        self.canonical.entry(hash).or_default().push(id);
        Ok(id)
    }

    fn view(&self) -> MacroContributorDagRef<'_> {
        MacroContributorDagRef { nodes: &self.nodes }
    }

    fn finish(self) -> MacroContributorDag {
        MacroContributorDag { nodes: self.nodes }
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy)]
struct MacroContributorDagRef<'a> {
    nodes: &'a [MacroContributorNode],
}

#[cfg(test)]
impl MacroContributorSetId {
    pub(crate) fn test_from_source_unit(source: SourceUnitId) -> Self {
        Self(source.0)
    }

    pub(crate) fn test_source_unit(self) -> SourceUnitId {
        SourceUnitId(self.0)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn collected_parent<Id: Copy>(
    recorded: bool,
    discovered_in: Option<Id>,
    source_call: Option<Id>,
) -> Option<Id> {
    if recorded { discovered_in } else { source_call }
}

#[cfg(test)]
mod ancestor_resolution_tests {
    use std::cell::Cell;

    use super::*;

    #[test]
    fn deep_shared_ancestor_paths_are_resolved_once() {
        const DEPTH: u32 = 1_024;
        let resolutions = Cell::new(0);
        let (targets, resolved_nodes) = memoized_ancestor_targets((0..DEPTH).rev(), |node| {
            resolutions.set(resolutions.get() + 1);
            Some(if node == 0 {
                AncestorResolution::Target
            } else {
                AncestorResolution::Parent(node - 1)
            })
        })
        .unwrap();

        assert_eq!(resolved_nodes, DEPTH as usize);
        assert_eq!(resolutions.get(), DEPTH as usize);
        for _ in 0..DEPTH {
            for node in 0..DEPTH {
                assert_eq!(targets.get(&node), Some(&Some(0)));
            }
        }
        assert_eq!(resolutions.get(), DEPTH as usize);
    }

    #[test]
    fn ancestor_cycles_are_rejected() {
        assert!(
            memoized_ancestor_targets([0_u32], |node| Some(AncestorResolution::Parent(1 - node)))
                .is_none()
        );
    }

    #[test]
    fn producer_preparation_is_unique_and_coverage_is_a_subset() {
        const PRODUCERS: u32 = 4_096;
        let plan = producer_preparation_plan(
            (0..PRODUCERS).collect(),
            (0..PRODUCERS).step_by(2).collect(),
        )
        .unwrap();

        assert_eq!(plan.len(), PRODUCERS as usize);
        assert!(
            plan.iter()
                .enumerate()
                .all(|(index, &(producer, coverage))| {
                    producer == index as u32 && coverage == (producer % 2 == 0)
                })
        );
        assert!(producer_preparation_plan(vec![0, 0], Vec::new()).is_none());
        assert!(producer_preparation_plan(vec![0], vec![1]).is_none());
        assert!(producer_preparation_plan(vec![0], vec![0, 0]).is_none());
    }

    #[test]
    fn collected_ancestry_uses_recorded_discovery_and_unrecorded_source_context() {
        assert_eq!(collected_parent(true, Some(1), Some(2)), Some(1));
        assert_eq!(collected_parent(false, Some(1), Some(2)), Some(2));

        let collected = HashSet::from([0_u32]);
        let facts = HashMap::from([
            (1_u32, (true, Some(0), Some(3))),
            (2, (false, None, Some(1))),
        ]);
        let (nearest, _) = memoized_ancestor_targets([2], |current| {
            if collected.contains(&current) {
                return Some(AncestorResolution::Target);
            }
            let &(recorded, discovered, source_call) = facts.get(&current)?;
            Some(
                collected_parent(recorded, discovered, source_call)
                    .map_or(AncestorResolution::Absent, AncestorResolution::Parent),
            )
        })
        .unwrap();
        assert_eq!(nearest.get(&2), Some(&Some(0)));
    }

    #[test]
    fn contributor_dependency_order_is_iterative_and_fails_closed() {
        const DEPTH: u32 = 1_024;
        let (order, visits) = dependency_postorder([DEPTH - 1], |node| {
            Some(if node == 0 {
                Vec::new()
            } else {
                vec![node - 1]
            })
        })
        .unwrap();
        assert_eq!(order, (0..DEPTH).collect::<Vec<_>>());
        assert_eq!(visits, DEPTH as usize);
        assert!(dependency_postorder([0_u32], |node| Some(vec![1 - node])).is_none());
        assert!(dependency_postorder([0_u32], |_| None).is_none());
    }

    #[test]
    fn contributor_dag_and_identity_frontiers_scale_with_shared_facts() {
        const DEPTH: usize = 1_024;
        let mut builder = MacroContributorDagBuilder::default();
        let mut roots = Vec::with_capacity(DEPTH);
        let mut parent = None;
        for _ in 0..DEPTH {
            let root = builder
                .intern(
                    vec![SourceUnitId(0)],
                    parent.into_iter().collect::<Vec<_>>(),
                )
                .unwrap();
            roots.push(root);
            parent = Some(root);
        }
        let dag = builder.finish();
        assert_eq!(dag.node_count(), DEPTH);
        assert!(dag.stored_fact_count() <= DEPTH * 2);

        let ancestry = SourceAncestryIndex::from_parents(vec![None]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let mut memo = IdentityFrontierMemo::new(1).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let mut emitted_basis_facts = 0;
        for &root in &roots {
            let mut index = ProductBasisRangeIndex::new(
                &ancestry,
                &excluded,
                context,
                &mut memo,
                MacroContributorDagRef { nodes: &dag.nodes },
                &[root],
            )
            .unwrap();
            let basis = index
                .intersection(MacroOutputRange { start: 0, end: 1 })
                .unwrap();
            emitted_basis_facts += basis.len();
            assert_eq!(basis, vec![SourceUnitId(0)]);
        }
        assert_eq!(emitted_basis_facts, DEPTH);
        assert!(memo.frontier_node_resolutions <= dag.node_count());
        assert!(memo.frontier_sets.nodes.len() <= DEPTH);
        assert!(memo.frontier_sets.enumeration_visits <= 1);

        let (sources, visits) = dag.sources_with_visits(&[*roots.last().unwrap()]).unwrap();
        assert_eq!(sources, vec![SourceUnitId(0)]);
        assert_eq!(visits, dag.node_count());
    }

    #[test]
    fn product_basis_ignores_cfg_discarded_output_ordinals() {
        let ancestry = SourceAncestryIndex::from_parents(vec![None, None]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let contributors = [
            vec![SourceUnitId(0)],
            vec![SourceUnitId(1)],
            vec![SourceUnitId(0)],
        ];
        with_flat_product_basis_index(&ancestry, &excluded, &contributors, |index| {
            assert!(
                index
                    .intersection(MacroOutputRange { start: 0, end: 3 })?
                    .is_empty()
            );
            Ok(())
        })
        .unwrap();
        with_flat_product_basis_index_excluding(
            &ancestry,
            &excluded,
            &contributors,
            &[MacroOutputRange { start: 1, end: 2 }],
            |index| {
                assert_eq!(
                    index.intersection(MacroOutputRange { start: 0, end: 3 })?,
                    vec![SourceUnitId(0)]
                );
                assert_eq!(
                    index.intersection(MacroOutputRange { start: 1, end: 2 }),
                    Err(ExpansionError::IncompleteOrigin),
                );
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn discarded_product_basis_queries_do_not_rescan_nested_discarded_ranges() {
        const DISCARDED: usize = 1_024;
        let token_count = DISCARDED * 3 + 1;
        let ancestry = SourceAncestryIndex::from_parents(vec![None]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let contributors = vec![vec![SourceUnitId(0)]; token_count];
        let discarded = (DISCARDED..DISCARDED * 2)
            .map(|ordinal| MacroOutputRange {
                start: ordinal as u32,
                end: ordinal as u32 + 1,
            })
            .collect::<Vec<_>>();

        with_flat_product_basis_index_excluding(
            &ancestry,
            &excluded,
            &contributors,
            &discarded,
            |index| {
                let (construction_work, query_work) = index.work();
                assert!(construction_work <= discarded.len() + token_count * 3);
                let query_levels = index.leaf_count.ilog2() as usize + 1;
                for padding in 0..DISCARDED {
                    assert_eq!(
                        index.intersection(MacroOutputRange {
                            start: (DISCARDED - padding) as u32,
                            end: (DISCARDED * 2 + 1 + padding) as u32,
                        })?,
                        vec![SourceUnitId(0)],
                    );
                }
                let (_, final_query_work) = index.work();
                assert!(
                    final_query_work - query_work <= DISCARDED * query_levels,
                    "each nested range query must visit only one segment-tree path per level",
                );
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn nested_source_frontiers_are_resolved_incrementally_per_contributor_node() {
        const DEPTH: usize = 1_024;
        let mut builder = MacroContributorDagBuilder::default();
        let mut roots = Vec::with_capacity(DEPTH);
        let mut parent = None;
        for source in 0..DEPTH {
            let root = builder
                .intern(
                    vec![SourceUnitId(source as u32)],
                    parent.into_iter().collect::<Vec<_>>(),
                )
                .unwrap();
            roots.push(root);
            parent = Some(root);
        }
        let dag = builder.finish();
        let ancestry = SourceAncestryIndex::from_parents(
            (0..DEPTH)
                .map(|source| (source > 0).then(|| SourceUnitId(source as u32 - 1)))
                .collect(),
        )
        .unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let mut memo = IdentityFrontierMemo::new(DEPTH).unwrap();
        let context = memo.context(Vec::new()).unwrap();

        for source in (0..DEPTH).rev() {
            let root = roots[source];
            let frontier = memo
                .resolve_frontier_set(
                    context,
                    MacroContributorDagRef { nodes: &dag.nodes },
                    &ancestry,
                    &excluded,
                    root,
                )
                .unwrap();
            assert_eq!(
                memo.materialize(frontier, &ancestry).unwrap(),
                [SourceUnitId(source as u32)]
            );
        }

        assert_eq!(memo.frontier_node_resolutions, DEPTH);
        assert_eq!(memo.frontier_node_resolutions, DEPTH);
        assert_eq!(memo.frontier_sets.enumeration_visits, DEPTH);
        assert!(
            memo.materialized
                .values()
                .map(|frontier| frontier.len())
                .sum::<usize>()
                <= DEPTH
        );
    }

    #[test]
    fn growing_contributor_chain_flattens_only_the_requested_terminal_set() {
        const DEPTH: usize = 1_024;
        let mut builder = MacroContributorDagBuilder::default();
        let mut parent = None;
        for source in 0..DEPTH {
            parent = Some(
                builder
                    .intern(
                        vec![SourceUnitId(source as u32)],
                        parent.into_iter().collect::<Vec<_>>(),
                    )
                    .unwrap(),
            );
        }
        let terminal = parent.unwrap();
        let dag = builder.finish();
        let ancestry = SourceAncestryIndex::from_parents(vec![None; DEPTH]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let mut memo = IdentityFrontierMemo::new(DEPTH).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let mut index = ProductBasisRangeIndex::new(
            &ancestry,
            &excluded,
            context,
            &mut memo,
            MacroContributorDagRef { nodes: &dag.nodes },
            &[terminal],
        )
        .unwrap();
        let basis = index
            .intersection(MacroOutputRange { start: 0, end: 1 })
            .unwrap();
        drop(index);

        assert_eq!(basis.len(), DEPTH);
        assert_eq!(memo.frontier_node_resolutions, DEPTH);
        let height = usize::from(memo.frontier_sets.height) + 1;
        assert!(memo.frontier_sets.nodes.len() <= DEPTH * height * 3);
        assert!(memo.frontier_sets.enumeration_visits <= DEPTH * 2);
        assert!(
            memo.materialized
                .values()
                .map(|frontier| frontier.len())
                .sum::<usize>()
                <= DEPTH,
            "only the terminal definition frontier is flattened",
        );
    }

    #[test]
    fn growing_frontiers_cost_no_more_than_the_emitted_bases() {
        const DEPTH: usize = 128;
        let mut builder = MacroContributorDagBuilder::default();
        let mut roots = Vec::with_capacity(DEPTH);
        let mut parent = None;
        for source in 0..DEPTH {
            let root = builder
                .intern(
                    vec![SourceUnitId(source as u32)],
                    parent.into_iter().collect::<Vec<_>>(),
                )
                .unwrap();
            roots.push(root);
            parent = Some(root);
        }
        let dag = builder.finish();
        let ancestry = SourceAncestryIndex::from_parents(vec![None; DEPTH]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let mut memo = IdentityFrontierMemo::new(DEPTH).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let mut emitted = 0;
        for (depth, &root) in roots.iter().enumerate() {
            let mut index = ProductBasisRangeIndex::new(
                &ancestry,
                &excluded,
                context,
                &mut memo,
                MacroContributorDagRef { nodes: &dag.nodes },
                &[root],
            )
            .unwrap();
            let basis = index
                .intersection(MacroOutputRange { start: 0, end: 1 })
                .unwrap();
            assert_eq!(basis.len(), depth + 1);
            emitted += basis.len();
        }
        assert_eq!(emitted, DEPTH * (DEPTH + 1) / 2);
        assert!(
            memo.materialized
                .values()
                .map(|frontier| frontier.len())
                .sum::<usize>()
                <= emitted,
        );
        assert!(memo.frontier_sets.enumeration_visits <= emitted * 3);
    }

    #[test]
    fn shared_large_frontier_is_flattened_only_for_the_emitted_basis() {
        const COMMON: usize = 128;
        const TOKENS: usize = 128;

        let template_root = SourceUnitId(COMMON as u32);
        let mut parents = vec![None; COMMON + 1];
        parents.extend(std::iter::repeat_n(Some(template_root), TOKENS));
        let ancestry = SourceAncestryIndex::from_parents(parents).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();

        let mut builder = MacroContributorDagBuilder::default();
        let shared = builder
            .intern(
                (0..COMMON)
                    .map(|source| SourceUnitId(source as u32))
                    .collect(),
                Vec::new(),
            )
            .unwrap();
        let roots = (0..TOKENS)
            .map(|token| {
                builder.intern(
                    vec![SourceUnitId((COMMON + 1 + token) as u32)],
                    vec![shared],
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let dag = builder.finish();
        assert!(dag.stored_fact_count() <= COMMON + TOKENS * 2);

        let mut memo = IdentityFrontierMemo::new(COMMON + 1 + TOKENS).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let mut index = ProductBasisRangeIndex::new(
            &ancestry,
            &excluded,
            context,
            &mut memo,
            MacroContributorDagRef { nodes: &dag.nodes },
            &roots,
        )
        .unwrap();
        let basis = index
            .intersection(MacroOutputRange {
                start: 0,
                end: TOKENS as u32,
            })
            .unwrap();
        drop(index);

        let expected = (0..=COMMON)
            .map(|source| SourceUnitId(source as u32))
            .collect::<Vec<_>>();
        assert_eq!(basis, expected);
        assert_eq!(memo.materialized.len(), 1);
        assert_eq!(
            memo.materialized
                .values()
                .map(|frontier| frontier.len())
                .sum::<usize>(),
            COMMON + 1,
        );
        assert!(
            memo.frontier_sets.enumeration_visits <= (COMMON + TOKENS) * 4,
            "shared frontier sources must not be enumerated once per token",
        );
    }

    #[test]
    fn shared_large_frontier_is_not_reenumerated_for_each_parent_union() {
        const COMMON: usize = 128;
        const PARENTS: usize = 128;

        let template_root = SourceUnitId(COMMON as u32);
        let mut parents = vec![None; COMMON + 1];
        parents.extend(std::iter::repeat_n(Some(template_root), PARENTS));
        let ancestry = SourceAncestryIndex::from_parents(parents).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();

        let mut builder = MacroContributorDagBuilder::default();
        let shared = builder
            .intern(
                (0..COMMON)
                    .map(|source| SourceUnitId(source as u32))
                    .collect(),
                Vec::new(),
            )
            .unwrap();
        let parent_roots = (0..PARENTS)
            .map(|parent| {
                builder.intern(
                    vec![SourceUnitId((COMMON + 1 + parent) as u32)],
                    vec![shared],
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let joined = builder.intern(Vec::new(), parent_roots).unwrap();
        let dag = builder.finish();
        assert!(dag.stored_fact_count() <= COMMON + PARENTS * 3);

        let mut memo = IdentityFrontierMemo::new(COMMON + 1 + PARENTS).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let frontier = memo
            .resolve_frontier_set(
                context,
                MacroContributorDagRef { nodes: &dag.nodes },
                &ancestry,
                &excluded,
                joined,
            )
            .unwrap();
        let materialized = memo.materialize(frontier, &ancestry).unwrap();
        let expected = (0..COMMON)
            .chain(COMMON + 1..COMMON + 1 + PARENTS)
            .map(|source| SourceUnitId(source as u32))
            .collect::<Vec<_>>();

        assert_eq!(materialized, expected);
        assert_eq!(memo.materialized.len(), 1);
        assert!(
            memo.frontier_sets.enumeration_visits <= (COMMON + PARENTS) * 4,
            "shared parent facts must not be enumerated once per union",
        );
    }

    #[test]
    fn persistent_frontier_intersection_matches_the_flat_oracle() {
        const SOURCE_COUNT: usize = 7;
        let ancestry = SourceAncestryIndex::from_parents(vec![
            None,
            Some(SourceUnitId(0)),
            Some(SourceUnitId(0)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(2)),
            None,
        ])
        .unwrap();

        for excluded_units in [
            Vec::new(),
            vec![SourceUnitId(3)],
            vec![SourceUnitId(4), SourceUnitId(5)],
        ] {
            let excluded = SourceAncestorExclusions::new(&ancestry, excluded_units).unwrap();
            let mut sets = PersistentFrontierSets::new(SOURCE_COUNT).unwrap();
            let mut frontiers = Vec::new();
            for mask in 0..(1_usize << SOURCE_COUNT) {
                let frontier = ancestry
                    .deepest_antichain((0..SOURCE_COUNT).filter_map(|source| {
                        let unit = SourceUnitId(source as u32);
                        (mask & (1 << source) != 0 && !excluded.contains(unit).unwrap())
                            .then_some(unit)
                    }))
                    .unwrap();
                let mut root = PersistentFrontierSets::EMPTY;
                for &source in &frontier {
                    root = sets.insert_source(root, source, &ancestry).unwrap();
                }
                frontiers.push((frontier, root));
            }

            for (left, left_root) in &frontiers {
                for (right, right_root) in &frontiers {
                    let expected_union = ancestry
                        .deepest_antichain(left.iter().chain(right).copied())
                        .unwrap();
                    let actual_union_root = sets.union(*left_root, *right_root, &ancestry).unwrap();
                    let actual_union = sets.enumerate(actual_union_root, &ancestry).unwrap();
                    assert_eq!(
                        actual_union, expected_union,
                        "union left={left:?}, right={right:?}"
                    );

                    let expected = ancestry
                        .intersect_frontiers(left, right, &excluded)
                        .unwrap();
                    let actual_root = sets
                        .intersection(*left_root, *right_root, &ancestry, &excluded)
                        .unwrap();
                    let actual = sets.enumerate(actual_root, &ancestry).unwrap();
                    assert_eq!(actual, expected, "left={left:?}, right={right:?}");
                }
            }
        }
    }

    #[test]
    fn repeated_frontier_pairs_share_their_intersection() {
        const TOKENS: usize = 1_024;
        let mut builder = MacroContributorDagBuilder::default();
        let left = builder.intern(vec![SourceUnitId(1)], Vec::new()).unwrap();
        let right = builder.intern(vec![SourceUnitId(2)], Vec::new()).unwrap();
        let dag = builder.finish();
        let roots = (0..TOKENS)
            .map(|index| if index % 2 == 0 { left } else { right })
            .collect::<Vec<_>>();
        let ancestry = SourceAncestryIndex::from_parents(vec![
            None,
            Some(SourceUnitId(0)),
            Some(SourceUnitId(0)),
        ])
        .unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        let mut memo = IdentityFrontierMemo::new(3).unwrap();
        let context = memo.context(Vec::new()).unwrap();
        let mut index = ProductBasisRangeIndex::new(
            &ancestry,
            &excluded,
            context,
            &mut memo,
            MacroContributorDagRef { nodes: &dag.nodes },
            &roots,
        )
        .unwrap();
        for _ in 0..128 {
            assert_eq!(
                index
                    .intersection(MacroOutputRange { start: 0, end: 3 })
                    .unwrap(),
                vec![SourceUnitId(0)],
            );
            assert_eq!(
                index
                    .intersection(MacroOutputRange { start: 1, end: 4 })
                    .unwrap(),
                vec![SourceUnitId(0)],
            );
        }
        drop(index);
        assert_eq!(memo.intersection_computations, 3);
        assert_eq!(memo.intersections.len(), 3);
    }

    #[test]
    fn contributor_nodes_are_canonicalized_by_content() {
        let mut builder = MacroContributorDagBuilder::default();
        let first = builder
            .intern(vec![SourceUnitId(1), SourceUnitId(0)], Vec::new())
            .unwrap();
        let same = builder
            .intern(
                vec![SourceUnitId(0), SourceUnitId(1), SourceUnitId(1)],
                Vec::new(),
            )
            .unwrap();
        assert_eq!(first, same);
        assert_eq!(builder.nodes.len(), 1);
        assert!(
            builder
                .intern(Vec::new(), vec![MacroContributorSetId(99)])
                .is_err()
        );

        let malformed = MacroContributorDag {
            nodes: vec![MacroContributorNode {
                local: vec![SourceUnitId(0)].into_boxed_slice(),
                parents: vec![MacroContributorSetId(0)].into_boxed_slice(),
            }],
        };
        assert_eq!(
            malformed.sources_with_visits(&[MacroContributorSetId(0)]),
            Err(ExpansionError::IncompleteOrigin),
        );
        assert_eq!(
            malformed.sources_with_visits(&[MacroContributorSetId(1)]),
            Err(ExpansionError::IncompleteOrigin),
        );
    }

    #[test]
    fn identity_source_conversion_is_memoized_per_source_unit() {
        const DEFINITIONS: usize = 1_024;
        let calls = Cell::new(0);
        let mut cache = BTreeMap::new();
        for _ in 0..DEFINITIONS {
            let source = memoized_identity_source(&mut cache, SourceUnitId(7), || {
                calls.set(calls.get() + 1);
                Ok(MacroProductSource {
                    kind: SourceUnitIdentityKind::Written(crate::source::WrittenUnitKind::Item),
                    range: ByteRange { start: 4, end: 9 },
                })
            })
            .unwrap();
            assert_eq!(source.range, ByteRange { start: 4, end: 9 });
        }
        assert_eq!(calls.get(), 1);
        assert_eq!(cache.len(), 1);
    }
}

/// Token-level source provenance prepared before definition identities are
/// assigned. The same prepared facts are later lowered into retention
/// coverage, so identity and retention cannot disagree about token origins.
#[cfg(rust_item_dependencies_patched)]
pub(crate) struct MacroProvenance {
    pub(super) origins: PreparedExpansionOrigins,
    pub(super) coverage_producer_order: Vec<ExpnId>,
    pub(super) producers: FxHashMap<ExpnId, PreparedProducer>,
    pub(super) contributor_dag: Arc<MacroContributorDag>,
    pub(super) token_contributors: FxHashMap<ExpnId, PreparedTokenContributors>,
    definition_bases: FxHashMap<u32, Vec<MacroProductSource>>,
    pub(super) outputless_producers: Vec<ExpnId>,
}

#[cfg(not(rust_item_dependencies_patched))]
pub(crate) struct MacroProvenance;

#[cfg(rust_item_dependencies_patched)]
pub(super) struct PreparedProducer {
    pub(super) output_token_count: u32,
    pub(super) definition_outputs: Vec<(rustc_hir::def_id::LocalDefId, MacroOutputRange)>,
    pub(super) child_outputs: Vec<(ExpnId, MacroOutputRange)>,
    pub(super) discarded_outputs: Vec<MacroOutputRange>,
    pub(super) owner_output: PreparedMacroOwnerOutput,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct PreparedMacroOwnerOutput {
    pub(super) complete: bool,
    pub(super) intrinsic: bool,
    pub(super) dependent_outputs: Vec<MacroOutputRange>,
    pub(super) required_outputs: Vec<MacroOutputRange>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone)]
pub(super) struct PreparedTokenContributors {
    by_ordinal: Vec<MacroContributorSetId>,
    leaf_count: usize,
    range_nodes: Vec<Option<MacroContributorSetId>>,
}

#[cfg(rust_item_dependencies_patched)]
impl PreparedTokenContributors {
    fn new(
        by_ordinal: Vec<MacroContributorSetId>,
        builder: &mut MacroContributorDagBuilder,
    ) -> Result<Self, ExpansionError> {
        let leaf_count = by_ordinal
            .len()
            .checked_next_power_of_two()
            .ok_or(ExpansionError::IncompleteOrigin)?
            .max(1);
        let node_count = leaf_count
            .checked_mul(2)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let mut range_nodes = vec![None; node_count];
        for (ordinal, &root) in by_ordinal.iter().enumerate() {
            range_nodes[leaf_count + ordinal] = Some(root);
        }
        for index in (1..leaf_count).rev() {
            range_nodes[index] = match (range_nodes[index * 2], range_nodes[index * 2 + 1]) {
                (Some(left), Some(right)) if left != right => {
                    Some(builder.intern(Vec::new(), vec![left, right])?)
                }
                (Some(root), _) | (_, Some(root)) => Some(root),
                (None, None) => None,
            };
        }
        Ok(Self {
            by_ordinal,
            leaf_count,
            range_nodes,
        })
    }

    pub(super) fn output_token_count(&self) -> Result<u32, ExpansionError> {
        self.by_ordinal
            .len()
            .try_into()
            .map_err(|_| ExpansionError::IncompleteOrigin)
    }

    pub(super) fn get(&self, ordinal: u32) -> Option<MacroContributorSetId> {
        self.by_ordinal.get(ordinal as usize).copied()
    }

    fn as_slice(&self) -> &[MacroContributorSetId] {
        &self.by_ordinal
    }

    pub(super) fn roots_for_range(
        &self,
        range: MacroOutputRange,
    ) -> Result<Vec<MacroContributorSetId>, ExpansionError> {
        let mut start = range.start as usize;
        let mut end = range.end as usize;
        if start >= end || end > self.by_ordinal.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        start += self.leaf_count;
        end += self.leaf_count;
        let mut roots = Vec::new();
        while start < end {
            if start % 2 == 1 {
                roots.push(
                    self.range_nodes
                        .get(start)
                        .copied()
                        .flatten()
                        .ok_or(ExpansionError::IncompleteOrigin)?,
                );
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                roots.push(
                    self.range_nodes
                        .get(end)
                        .copied()
                        .flatten()
                        .ok_or(ExpansionError::IncompleteOrigin)?,
                );
            }
            start /= 2;
            end /= 2;
        }
        roots.sort();
        roots.dedup();
        (!roots.is_empty())
            .then_some(roots)
            .ok_or(ExpansionError::IncompleteOrigin)
    }
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct PreparedExpansionOrigins {
    pub(super) ordered: Vec<PreparedExpansionOrigin>,
    by_compiler_id: FxHashMap<ExpnId, usize>,
    recorded: HashMap<ExpnId, Option<ExpnId>>,
    nearest_editable: HashMap<ExpnId, Option<ExpnId>>,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct PreparedExpansionOrigin {
    pub(super) compiler_id: ExpnId,
    pub(super) kind: ExpansionKind,
    pub(super) fragment: Option<ExpansionFragmentKind>,
    pub(super) implementation: Option<MacroImplementationKind>,
    pub(super) output_structure: Option<MacroExpansionOutputStructure>,
    pub(super) macro_definition: Option<rustc_hir::def_id::DefId>,
    pub(super) invocation_range: Option<ByteRange>,
    pub(super) node_range: Option<ByteRange>,
    pub(super) target_range: Option<ByteRange>,
    pub(super) target_span_is_present: bool,
    pub(super) selected_rule: Option<SelectedMacroRuleSource>,
    pub(super) editable_source: Option<EditableMacroSource>,
    pub(super) parents: PreparedExpansionParents,
    collected_parent: Option<ExpnId>,
    pub(super) parent_definition: Option<rustc_hir::def_id::LocalDefId>,
    pub(super) attribute_like: bool,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(super) struct PreparedExpansionParents {
    pub(super) discovered_in: Option<ExpnId>,
    pub(super) semantic: Option<ExpnId>,
    pub(super) source_call: Option<ExpnId>,
}

#[cfg(rust_item_dependencies_patched)]
impl PreparedExpansionParents {
    pub(super) fn identity(self) -> Option<ExpnId> {
        self.discovered_in.or(self.source_call).or(self.semantic)
    }

    fn generation(self) -> Option<ExpnId> {
        declarative_generation_parent(self.discovered_in, self.source_call)
    }
}

impl MacroProvenance {
    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn definition_basis(
        &self,
        definition: rustc_hir::def_id::LocalDefId,
    ) -> Option<&[MacroProductSource]> {
        self.definition_bases
            .get(&definition.local_def_index.as_u32())
            .map(Vec::as_slice)
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn nearest_editable_macro_origin(
        &self,
        expansion: ExpnId,
    ) -> Result<PreparedEditableMacroOrigin, ExpansionError> {
        self.origins.nearest_editable(expansion)
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn recorded_macro_expansion(
        &self,
        expansion: ExpnId,
    ) -> Result<Option<ExpnId>, ExpansionError> {
        self.origins
            .recorded(expansion)
            .map(|origin| origin.map(|origin| origin.compiler_id))
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn recorded_editable_macro_origin(
        &self,
        expansion: ExpnId,
    ) -> Result<Option<PreparedEditableMacroOrigin>, ExpansionError> {
        self.origins
            .recorded(expansion)?
            .map(PreparedExpansionOrigin::editable_origin)
            .transpose()
            .map(Option::flatten)
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn observed_expansion_ids(&self) -> impl Iterator<Item = ExpnId> + '_ {
        self.origins
            .ordered
            .iter()
            .filter(|origin| origin.parent_definition.is_some())
            .map(|origin| origin.compiler_id)
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(crate) fn macro_definition(
        &self,
        expansion: ExpnId,
    ) -> Result<Option<rustc_hir::def_id::DefId>, ExpansionError> {
        self.origins
            .get(expansion)
            .map(|origin| origin.macro_definition)
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    #[cfg(rust_item_dependencies_patched)]
    pub(super) fn nearest_collected_expansions(
        &self,
        starts: impl IntoIterator<Item = ExpnId>,
        collected: &FxHashMap<ExpnId, ExpansionId>,
    ) -> Result<FxHashMap<ExpnId, ExpansionId>, ExpansionError> {
        self.origins.nearest_collected(starts, collected)
    }

    #[cfg(not(rust_item_dependencies_patched))]
    pub(crate) fn definition_basis(
        &self,
        _definition: rustc_hir::def_id::LocalDefId,
    ) -> Option<&[crate::source::MacroProductSource]> {
        None
    }
}

#[cfg(not(rust_item_dependencies_patched))]
pub(crate) fn collect_macro_provenance(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
) -> Result<MacroProvenance, ExpansionError> {
    Ok(MacroProvenance)
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn collect_macro_provenance(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
) -> Result<MacroProvenance, ExpansionError> {
    let origins = PreparedExpansionOrigins::new(compiler, tcx, source)?;
    ProvenanceCollector::new(compiler, tcx, source, origins)?.collect()
}

#[cfg(rust_item_dependencies_patched)]
impl PreparedExpansionOrigins {
    fn new(
        compiler: &Compiler,
        tcx: TyCtxt<'_>,
        source: &SourceInventory,
    ) -> Result<Self, ExpansionError> {
        let origins = &tcx.resolutions(()).macro_invocation_origins;
        let source_resolver = EditableMacroSourceResolver::new(origins);
        let rule_index = source
            .macro_rule_selection_index()
            .map_err(expansion_source_error)?;
        let mut expansion_ids = Vec::<ExpnId>::new();
        let mut seen_expansions = FxHashSet::default();
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
            add_expansion_closure(origins, expansion, &mut seen_expansions, &mut expansion_ids);
            add_expansion_closure(
                origins,
                origin.discovered_in_expansion,
                &mut seen_expansions,
                &mut expansion_ids,
            );
        }
        for definition in tcx.iter_local_def_id() {
            add_expansion_closure(
                origins,
                tcx.expn_that_defined(definition.to_def_id()),
                &mut seen_expansions,
                &mut expansion_ids,
            );
        }
        expansion_ids.retain(|expansion| *expansion != ExpnId::root());
        expansion_ids.sort_by_key(|expansion| expansion.expn_hash().local_hash().as_u64());

        let mut ordered = Vec::with_capacity(expansion_ids.len());
        let mut by_compiler_id = FxHashMap::default();
        for compiler_id in expansion_ids {
            let origin = origins.get(&compiler_id);
            let data = compiler_id.expn_data();
            let kind = expansion_kind(&data.kind)?;
            let invocation_range = source_range(compiler, source, data.call_site)?;
            let node_range = origin
                .map(|origin| source_range(compiler, source, origin.invocation_node_span))
                .transpose()?
                .flatten();
            let target_range = origin
                .and_then(|origin| origin.target_span)
                .map(|span| source_range(compiler, source, span))
                .transpose()?
                .flatten();
            let editable_source = origin
                .map(|origin| {
                    source_resolver
                        .resolve(compiler, source, compiler_id)
                        .map_err(expansion_source_error)
                        .and_then(|editable| {
                            if origin.discovered_in_expansion == ExpnId::root()
                                && editable.is_none()
                            {
                                Err(ExpansionError::IncompleteOrigin)
                            } else {
                                Ok(editable)
                            }
                        })
                })
                .transpose()?
                .flatten();
            let selected_rule = origin
                .map(|origin| {
                    selected_macro_rule_source(compiler, tcx, source, &rule_index, origin)
                })
                .transpose()?
                .flatten();
            let discovered_in = origin
                .map(|origin| origin.discovered_in_expansion)
                .filter(|parent| *parent != ExpnId::root());
            let semantic = (data.parent != ExpnId::root()).then_some(data.parent);
            let source_call = data.call_site.ctxt().outer_expn();
            let source_call = (source_call != ExpnId::root() && source_call != compiler_id)
                .then_some(source_call);
            let collected_parent = collected_parent(origin.is_some(), discovered_in, source_call);
            let (mut discovered_in, mut semantic, mut source_call) =
                (discovered_in, semantic, source_call);
            if editable_source.is_some_and(|editable| {
                editable.role == EditableMacroSourceRole::TransparentAttribute
            }) {
                discovered_in = None;
                semantic = None;
                source_call = None;
            }
            let parents = PreparedExpansionParents {
                discovered_in,
                semantic,
                source_call,
            };
            let index = ordered.len();
            if by_compiler_id.insert(compiler_id, index).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            ordered.push(PreparedExpansionOrigin {
                compiler_id,
                kind,
                fragment: origin.map(|origin| fragment_kind(origin.fragment_kind)),
                implementation: origin
                    .map(|origin| implementation_kind(origin.implementation_kind)),
                output_structure: origin.and_then(|origin| origin.output_structure),
                macro_definition: data.macro_def_id,
                invocation_range,
                node_range,
                target_range,
                target_span_is_present: origin.is_some_and(|origin| origin.target_span.is_some()),
                selected_rule,
                editable_source,
                parents,
                collected_parent,
                parent_definition: origin.map(|origin| origin.parent_definition),
                attribute_like: matches!(
                    &data.kind,
                    ExpnKind::Macro(MacroKind::Attr | MacroKind::Derive, _)
                ),
            });
        }
        let entry = |compiler_id: ExpnId| {
            by_compiler_id
                .get(&compiler_id)
                .and_then(|&index| ordered.get(index))
                .filter(|origin| origin.compiler_id == compiler_id)
        };
        let compiler_ids = ordered
            .iter()
            .map(|origin| origin.compiler_id)
            .collect::<Vec<_>>();
        let (recorded, _) =
            memoized_ancestor_targets(compiler_ids.iter().copied(), |compiler_id| {
                let origin = entry(compiler_id)?;
                Some(if origin.parent_definition.is_some() {
                    AncestorResolution::Target
                } else if let Some(parent) = origin.parents.source_call {
                    AncestorResolution::Parent(parent)
                } else {
                    AncestorResolution::Absent
                })
            })
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let observed = ordered
            .iter()
            .filter(|origin| origin.parent_definition.is_some())
            .map(|origin| origin.compiler_id);
        let (nearest_editable, _) = memoized_ancestor_targets(observed, |compiler_id| {
            let origin = entry(compiler_id)?;
            Some(if origin.editable_source.is_some() {
                AncestorResolution::Target
            } else if let Some(parent) = origin.parents.discovered_in {
                match recorded.get(&parent)? {
                    Some(parent) => AncestorResolution::Parent(*parent),
                    None => AncestorResolution::Absent,
                }
            } else {
                AncestorResolution::Absent
            })
        })
        .ok_or(ExpansionError::IncompleteOrigin)?;
        Ok(Self {
            ordered,
            by_compiler_id,
            recorded,
            nearest_editable,
        })
    }

    fn get(&self, compiler_id: ExpnId) -> Option<&PreparedExpansionOrigin> {
        self.by_compiler_id
            .get(&compiler_id)
            .and_then(|&index| self.ordered.get(index))
            .filter(|origin| origin.compiler_id == compiler_id)
    }

    fn recorded(
        &self,
        compiler_id: ExpnId,
    ) -> Result<Option<&PreparedExpansionOrigin>, ExpansionError> {
        self.recorded
            .get(&compiler_id)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?
            .map(|recorded| self.get(recorded).ok_or(ExpansionError::IncompleteOrigin))
            .transpose()
    }

    fn nearest_editable(
        &self,
        compiler_id: ExpnId,
    ) -> Result<PreparedEditableMacroOrigin, ExpansionError> {
        let recorded = self
            .recorded(compiler_id)?
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let editable = self
            .nearest_editable
            .get(&recorded.compiler_id)
            .copied()
            .flatten()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        self.get(editable)
            .ok_or(ExpansionError::IncompleteOrigin)?
            .editable_origin()?
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    fn nearest_collected(
        &self,
        starts: impl IntoIterator<Item = ExpnId>,
        collected: &FxHashMap<ExpnId, ExpansionId>,
    ) -> Result<FxHashMap<ExpnId, ExpansionId>, ExpansionError> {
        let starts = starts.into_iter().collect::<Vec<_>>();
        let (nearest, _) = memoized_ancestor_targets(starts.iter().copied(), |compiler_id| {
            if collected.contains_key(&compiler_id) {
                return Some(AncestorResolution::Target);
            }
            let origin = self.get(compiler_id)?;
            Some(
                origin
                    .collected_parent
                    .map_or(AncestorResolution::Absent, AncestorResolution::Parent),
            )
        })
        .ok_or(ExpansionError::IncompleteOrigin)?;
        starts
            .into_iter()
            .map(|start| {
                let target = nearest
                    .get(&start)
                    .copied()
                    .flatten()
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                let id = collected
                    .get(&target)
                    .copied()
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                Ok((start, id))
            })
            .collect()
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(crate) struct PreparedEditableMacroOrigin {
    pub source: EditableMacroSource,
    pub target_range: Option<ByteRange>,
    pub target_span_is_present: bool,
    pub parent_definition: rustc_hir::def_id::LocalDefId,
}

#[cfg(rust_item_dependencies_patched)]
impl PreparedExpansionOrigin {
    pub(super) fn selected_rule_unit(&self) -> Option<SourceUnitId> {
        self.selected_rule.map(|selected| selected.unit)
    }

    pub(super) fn written_invocation(&self) -> Option<SourceUnitId> {
        self.editable_source.map(|source| source.unit)
    }

    fn editable_origin(&self) -> Result<Option<PreparedEditableMacroOrigin>, ExpansionError> {
        let Some(source) = self.editable_source else {
            return Ok(None);
        };
        Ok(Some(PreparedEditableMacroOrigin {
            source,
            target_range: self.target_range,
            target_span_is_present: self.target_span_is_present,
            parent_definition: self
                .parent_definition
                .ok_or(ExpansionError::IncompleteOrigin)?,
        }))
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct IndexedSourceUnit {
    pub(super) unit: SourceUnitId,
    pub(super) range: ByteRange,
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct IndexedInterval<T> {
    pub(super) start: u32,
    pub(super) end: u32,
    pub(super) value: T,
}

/// Start-ordered intervals with a range-maximum index over their end points.
///
/// The index supports both rightmost-containment lookup and overlap checks
/// without rescanning every interval for every nested product.
#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct IntervalStartIndex<T> {
    intervals: Vec<IndexedInterval<T>>,
    leaf_count: usize,
    maximum_ends: Vec<u32>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl<T: Copy> IntervalStartIndex<T> {
    pub(super) fn from_start_ordered(
        intervals: Vec<IndexedInterval<T>>,
    ) -> Result<Self, ExpansionError> {
        if intervals
            .windows(2)
            .any(|pair| pair[0].start > pair[1].start)
            || intervals
                .iter()
                .any(|interval| interval.start >= interval.end)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let leaf_count = intervals
            .len()
            .checked_next_power_of_two()
            .ok_or(ExpansionError::IncompleteOrigin)?
            .max(1);
        let node_count = leaf_count
            .checked_mul(2)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let mut maximum_ends = vec![0; node_count];
        for (index, interval) in intervals.iter().enumerate() {
            maximum_ends[leaf_count + index] = interval.end;
        }
        for index in (1..leaf_count).rev() {
            maximum_ends[index] = maximum_ends[index * 2].max(maximum_ends[index * 2 + 1]);
        }
        Ok(Self {
            intervals,
            leaf_count,
            maximum_ends,
        })
    }

    pub(super) fn lower_bound_start(&self, start: u32) -> usize {
        self.intervals
            .partition_point(|interval| interval.start < start)
    }

    fn upper_bound_start(&self, start: u32) -> usize {
        self.intervals
            .partition_point(|interval| interval.start <= start)
    }

    pub(super) fn innermost_container_with_probe(
        &self,
        start: u32,
        end: u32,
        mut probe: impl FnMut(),
    ) -> Option<T> {
        if start >= end {
            return None;
        }
        let after_start = self.upper_bound_start(start);
        self.rightmost_with_end_at_least_with_probe(0, after_start, end, &mut probe)
            .map(|index| self.intervals[index].value)
    }

    pub(super) fn maximum_end(&self, mut start: usize, mut end: usize) -> Option<u32> {
        if start >= end || end > self.intervals.len() {
            return None;
        }
        start += self.leaf_count;
        end += self.leaf_count;
        let mut maximum = 0;
        while start < end {
            if start % 2 == 1 {
                maximum = maximum.max(self.maximum_ends[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                maximum = maximum.max(self.maximum_ends[end]);
            }
            start /= 2;
            end /= 2;
        }
        Some(maximum)
    }

    fn rightmost_with_end_at_least(
        &self,
        start: usize,
        end: usize,
        minimum_end: u32,
    ) -> Option<usize> {
        self.rightmost_with_end_at_least_with_probe(start, end, minimum_end, &mut || {})
    }

    fn rightmost_with_end_at_least_with_probe(
        &self,
        start: usize,
        end: usize,
        minimum_end: u32,
        probe: &mut impl FnMut(),
    ) -> Option<usize> {
        if start >= end || end > self.intervals.len() {
            return None;
        }
        self.rightmost_in_node(1, 0, self.leaf_count, &(start..end), minimum_end, probe)
    }

    fn rightmost_in_node(
        &self,
        node: usize,
        node_start: usize,
        node_end: usize,
        query: &std::ops::Range<usize>,
        minimum_end: u32,
        probe: &mut impl FnMut(),
    ) -> Option<usize> {
        probe();
        if node_end <= query.start
            || query.end <= node_start
            || self.maximum_ends[node] < minimum_end
        {
            return None;
        }
        if node_end - node_start == 1 {
            return (node_start < self.intervals.len()).then_some(node_start);
        }
        let middle = node_start + (node_end - node_start) / 2;
        self.rightmost_in_node(node * 2 + 1, middle, node_end, query, minimum_end, probe)
            .or_else(|| {
                self.rightmost_in_node(node * 2, node_start, middle, query, minimum_end, probe)
            })
    }
}

/// A source-unit tree indexed for repeated containment queries.
///
/// Both template components and matcher elements already form validated
/// source hierarchies. Template lookup uses the flat containment index because
/// it needs only the innermost unit. Matcher lookup keeps the child hierarchy
/// because every containing repetition element is an output contributor.
#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct SourceUnitIntervalIndex {
    pub(super) root: SourceUnitId,
    pub(super) children: BTreeMap<SourceUnitId, Vec<IndexedSourceUnit>>,
    pub(super) flat: IntervalStartIndex<SourceUnitId>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl SourceUnitIntervalIndex {
    fn new(
        source: &SourceInventory,
        root: SourceUnitId,
        units: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<Self, ExpansionError> {
        let units = units.into_iter().collect::<Vec<_>>();
        let indexed = units.iter().copied().collect::<BTreeSet<_>>();
        if indexed.len() != units.len()
            || source
                .units
                .get(root.0 as usize)
                .is_none_or(|unit| unit.id != root)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let mut children = BTreeMap::<SourceUnitId, Vec<IndexedSourceUnit>>::new();
        for id in units {
            let unit = source
                .units
                .get(id.0 as usize)
                .filter(|unit| unit.id == id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let parent = unit.parent.ok_or(ExpansionError::IncompleteOrigin)?;
            if parent != root && !indexed.contains(&parent) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            children.entry(parent).or_default().push(IndexedSourceUnit {
                unit: id,
                range: unit.full_range,
            });
        }
        for (&parent, siblings) in &mut children {
            siblings.sort_by_key(|entry| (entry.range.start, entry.range.end, entry.unit));
            if siblings
                .windows(2)
                .any(|pair| pair[0].range.end > pair[1].range.start)
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let parent_range = source
                .units
                .get(parent.0 as usize)
                .filter(|unit| unit.id == parent)
                .map(|unit| unit.full_range)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if siblings
                .iter()
                .any(|child| !parent_range.contains(child.range))
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }

        let mut ordered = Vec::with_capacity(indexed.len());
        let mut pending = children
            .get(&root)
            .into_iter()
            .flatten()
            .rev()
            .copied()
            .collect::<Vec<_>>();
        while let Some(entry) = pending.pop() {
            ordered.push(IndexedInterval {
                start: entry.range.start,
                end: entry.range.end,
                value: entry.unit,
            });
            pending.extend(
                children
                    .get(&entry.unit)
                    .into_iter()
                    .flatten()
                    .rev()
                    .copied(),
            );
        }
        if ordered.len() != indexed.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let flat = IntervalStartIndex::from_start_ordered(ordered)?;
        Ok(Self {
            root,
            children,
            flat,
        })
    }

    fn containers(
        &self,
        range: ByteRange,
        reject_partial_overlap: bool,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        let mut result = Vec::new();
        let mut parent = self.root;
        loop {
            let Some(children) = self.children.get(&parent) else {
                return Ok(result);
            };
            let Some(child) = containing_child(children, range, reject_partial_overlap)? else {
                return Ok(result);
            };
            result.push(child.unit);
            if child.range == range {
                // An observed input range that exactly matches an outer
                // repetition element is fully represented by that element.
                // Its nested elements are contents of the same input, not
                // additional containers of the outer range.
                return Ok(result);
            }
            parent = child.unit;
        }
    }

    pub(super) fn innermost_container(
        &self,
        range: ByteRange,
    ) -> Result<Option<SourceUnitId>, ExpansionError> {
        if range.start > range.end {
            return Err(ExpansionError::IncompleteOrigin);
        }

        // Preserve the existing exact-range rule: when an observed range is
        // exactly an outer component, that component represents the complete
        // input even if it has an equal-range descendant.
        let exact = self.flat.intervals.partition_point(|interval| {
            interval.start < range.start
                || (interval.start == range.start && interval.end > range.end)
        });
        if let Some(interval) = self
            .flat
            .intervals
            .get(exact)
            .filter(|interval| interval.start == range.start && interval.end == range.end)
        {
            return Ok(Some(interval.value));
        }

        let end = self.flat.upper_bound_start(range.start);
        Ok(self
            .flat
            .rightmost_with_end_at_least(0, end, range.end)
            .map(|index| self.flat.intervals[index].value))
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) fn containing_child(
    children: &[IndexedSourceUnit],
    range: ByteRange,
    reject_partial_overlap: bool,
) -> Result<Option<IndexedSourceUnit>, ExpansionError> {
    if reject_partial_overlap && !range.is_empty() {
        let first_overlap = children.partition_point(|child| child.range.end <= range.start);
        if let Some(child) = children
            .get(first_overlap)
            .filter(|child| child.range.start < range.end)
        {
            if !child.range.contains(range) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            return Ok(Some(*child));
        }
        return Ok(None);
    }

    let after_start = children.partition_point(|child| child.range.start <= range.start);
    let mut candidates = [after_start.checked_sub(1), after_start.checked_sub(2)]
        .into_iter()
        .flatten()
        .filter_map(|index| children.get(index).copied())
        .filter(|child| child.range.contains(range))
        .collect::<Vec<_>>();
    candidates.sort_by_key(|child| (child.range.len(), child.unit));
    match candidates.as_slice() {
        [] => Ok(None),
        [child] => Ok(Some(*child)),
        [first, second, ..] if first.range.len() != second.range.len() => Ok(Some(*first)),
        _ => Err(ExpansionError::IncompleteOrigin),
    }
}

/// Validated ancestry and LCA queries for the source-unit forest.
///
/// Definition identity repeatedly intersects upward-closed contributor sets.
/// Euler intervals and binary lifting make those intersections depend on the
/// contributor frontier, rather than rescanning every ancestor pair.
#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct SourceAncestryIndex {
    parents: Vec<Option<SourceUnitId>>,
    depths: Vec<usize>,
    roots: Vec<SourceUnitId>,
    entries: Vec<usize>,
    exits: Vec<usize>,
    by_entry: Vec<SourceUnitId>,
    jumps: Vec<Vec<SourceUnitId>>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct SourceAncestorExclusions<'a> {
    ancestry: &'a SourceAncestryIndex,
    descendants: Vec<SourceUnitId>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl<'a> SourceAncestorExclusions<'a> {
    pub(super) fn new(
        ancestry: &'a SourceAncestryIndex,
        descendants: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<Self, ExpansionError> {
        let mut descendants = descendants.into_iter().collect::<Vec<_>>();
        for &unit in &descendants {
            ancestry.index(unit)?;
        }
        descendants.sort();
        descendants.dedup();
        Ok(Self {
            ancestry,
            descendants,
        })
    }

    fn contains(&self, unit: SourceUnitId) -> Result<bool, ExpansionError> {
        for &descendant in &self.descendants {
            if self.ancestry.is_ancestor(unit, descendant)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl SourceAncestryIndex {
    fn new(source: &SourceInventory) -> Result<Self, ExpansionError> {
        let mut parents = Vec::with_capacity(source.units.len());
        for (index, unit) in source.units.iter().enumerate() {
            if unit.id.0 as usize != index
                || unit.parent.is_some_and(|parent| {
                    parent == unit.id || parent.0 as usize >= source.units.len()
                })
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            parents.push(unit.parent);
        }
        Self::from_parents(parents)
    }

    pub(super) fn from_parents(parents: Vec<Option<SourceUnitId>>) -> Result<Self, ExpansionError> {
        let count = parents.len();
        let mut children = vec![Vec::<usize>::new(); count];
        let mut forest_roots = Vec::new();
        for (index, parent) in parents.iter().copied().enumerate() {
            if let Some(parent) = parent {
                let parent = parent.0 as usize;
                if parent >= count || parent == index {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                children[parent].push(index);
            } else {
                forest_roots.push(index);
            }
        }

        let mut depths = vec![0_usize; count];
        let mut roots = vec![SourceUnitId(u32::MAX); count];
        let mut entries = vec![usize::MAX; count];
        let mut exits = vec![usize::MAX; count];
        let mut next_entry = 0;
        for root in forest_roots {
            let root_id =
                SourceUnitId(u32::try_from(root).map_err(|_| ExpansionError::IncompleteOrigin)?);
            let mut pending = vec![(root, false)];
            while let Some((index, exiting)) = pending.pop() {
                if exiting {
                    exits[index] = next_entry;
                    continue;
                }
                if entries[index] != usize::MAX {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                entries[index] = next_entry;
                next_entry += 1;
                roots[index] = root_id;
                pending.push((index, true));
                for &child in children[index].iter().rev() {
                    depths[child] = depths[index]
                        .checked_add(1)
                        .ok_or(ExpansionError::IncompleteOrigin)?;
                    pending.push((child, false));
                }
            }
        }
        if next_entry != count || exits.contains(&usize::MAX) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut by_entry = vec![SourceUnitId(u32::MAX); count];
        for (index, &entry) in entries.iter().enumerate() {
            let unit =
                SourceUnitId(u32::try_from(index).map_err(|_| ExpansionError::IncompleteOrigin)?);
            if entry >= count || by_entry[entry].0 != u32::MAX {
                return Err(ExpansionError::IncompleteOrigin);
            }
            by_entry[entry] = unit;
        }

        let levels = usize::try_from(usize::BITS - count.max(1).leading_zeros())
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        let mut jumps = Vec::with_capacity(levels);
        jumps.push(
            parents
                .iter()
                .enumerate()
                .map(|(index, parent)| {
                    Ok(parent.unwrap_or(SourceUnitId(
                        u32::try_from(index).map_err(|_| ExpansionError::IncompleteOrigin)?,
                    )))
                })
                .collect::<Result<Vec<_>, ExpansionError>>()?,
        );
        for level in 1..levels {
            let previous = &jumps[level - 1];
            let current = previous
                .iter()
                .map(|ancestor| previous[ancestor.0 as usize])
                .collect();
            jumps.push(current);
        }
        Ok(Self {
            parents,
            depths,
            roots,
            entries,
            exits,
            by_entry,
            jumps,
        })
    }

    fn index(&self, unit: SourceUnitId) -> Result<usize, ExpansionError> {
        let index = unit.0 as usize;
        (index < self.parents.len())
            .then_some(index)
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    pub(super) fn entry(&self, unit: SourceUnitId) -> Result<usize, ExpansionError> {
        Ok(self.entries[self.index(unit)?])
    }

    fn interval(&self, unit: SourceUnitId) -> Result<(usize, usize), ExpansionError> {
        let index = self.index(unit)?;
        Ok((self.entries[index], self.exits[index]))
    }

    fn unit_at_entry(&self, entry: usize) -> Result<SourceUnitId, ExpansionError> {
        self.by_entry
            .get(entry)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    pub(super) fn is_ancestor(
        &self,
        ancestor: SourceUnitId,
        descendant: SourceUnitId,
    ) -> Result<bool, ExpansionError> {
        let ancestor = self.index(ancestor)?;
        let descendant = self.index(descendant)?;
        Ok(self.entries[ancestor] <= self.entries[descendant]
            && self.entries[descendant] < self.exits[ancestor])
    }

    pub(super) fn ancestors(
        &self,
        unit: SourceUnitId,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        let mut ancestors = Vec::new();
        let mut current = Some(unit);
        while let Some(unit) = current {
            let index = self.index(unit)?;
            ancestors.push(unit);
            current = self.parents[index];
        }
        Ok(ancestors)
    }

    fn lca(
        &self,
        left: SourceUnitId,
        right: SourceUnitId,
    ) -> Result<Option<SourceUnitId>, ExpansionError> {
        let mut left_index = self.index(left)?;
        let mut right_index = self.index(right)?;
        if self.roots[left_index] != self.roots[right_index] {
            return Ok(None);
        }
        if self.depths[left_index] < self.depths[right_index] {
            std::mem::swap(&mut left_index, &mut right_index);
        }
        let difference = self.depths[left_index] - self.depths[right_index];
        for level in 0..self.jumps.len() {
            if difference & (1 << level) != 0 {
                left_index = self.jumps[level][left_index].0 as usize;
            }
        }
        if left_index == right_index {
            return Ok(Some(SourceUnitId(
                u32::try_from(left_index).map_err(|_| ExpansionError::IncompleteOrigin)?,
            )));
        }
        for level in (0..self.jumps.len()).rev() {
            let left_ancestor = self.jumps[level][left_index].0 as usize;
            let right_ancestor = self.jumps[level][right_index].0 as usize;
            if left_ancestor != right_ancestor {
                left_index = left_ancestor;
                right_index = right_ancestor;
            }
        }
        Ok(self.parents[left_index])
    }

    pub(super) fn deepest_antichain(
        &self,
        units: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        let mut units = units.into_iter().collect::<Vec<_>>();
        for &unit in &units {
            self.index(unit)?;
        }
        units.sort_by_key(|unit| self.entries[unit.0 as usize]);
        units.dedup();
        let mut deepest = Vec::with_capacity(units.len());
        for unit in units {
            while let Some(&ancestor) = deepest.last() {
                if !self.is_ancestor(ancestor, unit)? {
                    break;
                }
                deepest.pop();
            }
            deepest.push(unit);
        }
        Ok(deepest)
    }

    pub(super) fn intersect_frontiers(
        &self,
        left: &[SourceUnitId],
        right: &[SourceUnitId],
        excluded: &SourceAncestorExclusions<'_>,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        if left.is_empty() || right.is_empty() {
            return Ok(Vec::new());
        }
        let mut colored = BTreeMap::<SourceUnitId, u8>::new();
        for &unit in left {
            self.index(unit)?;
            *colored.entry(unit).or_default() |= 1;
        }
        for &unit in right {
            self.index(unit)?;
            *colored.entry(unit).or_default() |= 2;
        }
        let mut ordered_colored = colored.keys().copied().collect::<Vec<_>>();
        ordered_colored.sort_by_key(|unit| self.entries[unit.0 as usize]);

        let mut nodes = ordered_colored.clone();
        for pair in ordered_colored.windows(2) {
            if let Some(lca) = self.lca(pair[0], pair[1])? {
                nodes.push(lca);
            }
        }
        nodes.sort_by_key(|unit| self.entries[unit.0 as usize]);
        nodes.dedup();

        let mut parents = vec![None; nodes.len()];
        let mut pending = Vec::<usize>::new();
        for index in 0..nodes.len() {
            while let Some(&ancestor) = pending.last() {
                if self.is_ancestor(nodes[ancestor], nodes[index])? {
                    break;
                }
                pending.pop();
            }
            parents[index] = pending.last().copied();
            pending.push(index);
        }

        let mut masks = nodes
            .iter()
            .map(|unit| colored.get(unit).copied().unwrap_or(0))
            .collect::<Vec<_>>();
        let mut has_common_child = vec![false; nodes.len()];
        let mut result = Vec::new();
        for index in (0..nodes.len()).rev() {
            if masks[index] == 3 && !has_common_child[index] && !excluded.contains(nodes[index])? {
                result.push(nodes[index]);
            }
            if let Some(parent) = parents[index] {
                if masks[index] == 3 {
                    has_common_child[parent] = true;
                }
                masks[parent] |= masks[index];
            }
        }
        result.sort_by_key(|unit| self.entries[unit.0 as usize]);
        Ok(result)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct ProductBasisRangeIndex<'a, 'm> {
    ancestry: &'a SourceAncestryIndex,
    excluded: &'a SourceAncestorExclusions<'a>,
    exclusion_context: u32,
    frontier_memo: &'m mut IdentityFrontierMemo,
    token_count: usize,
    leaf_count: usize,
    // `None` is the intersection identity for an output ordinal that was
    // discarded before it could contribute to a live product. It is distinct
    // from the valid empty frontier set produced by a live token whose sources
    // were all excluded from identity.
    frontiers: Vec<Option<PersistentFrontierSetId>>,
    #[cfg(test)]
    construction_work: usize,
    #[cfg(test)]
    query_work: usize,
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct PersistentFrontierSetId(u32);

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy)]
struct PersistentFrontierSetNode {
    height: u8,
    left: PersistentFrontierSetId,
    right: PersistentFrontierSetId,
    count: usize,
    first: usize,
}

/// Canonical persistent antichains in source-Euler order.
///
/// Contributor nodes retain only one root ID. Adding a deeper source replaces
/// its at-most-one retained ancestor, while adding an ancestor of an existing
/// source is a no-op. This preserves structural sharing for deep contributor
/// chains without flattening every prefix frontier.
#[cfg(any(rust_item_dependencies_patched, test))]
struct PersistentFrontierSets {
    source_count: usize,
    height: u8,
    nodes: Vec<PersistentFrontierSetNode>,
    canonical:
        HashMap<(u8, PersistentFrontierSetId, PersistentFrontierSetId), PersistentFrontierSetId>,
    unions: HashMap<(PersistentFrontierSetId, PersistentFrontierSetId), PersistentFrontierSetId>,
    #[cfg(test)]
    update_visits: usize,
    #[cfg(test)]
    enumeration_visits: usize,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl PersistentFrontierSets {
    const EMPTY: PersistentFrontierSetId = PersistentFrontierSetId(0);
    const LEAF: PersistentFrontierSetId = PersistentFrontierSetId(1);

    fn new(source_count: usize) -> Result<Self, ExpansionError> {
        let leaf_count = source_count
            .checked_next_power_of_two()
            .ok_or(ExpansionError::IncompleteOrigin)?
            .max(1);
        let height = u8::try_from(leaf_count.trailing_zeros())
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        Ok(Self {
            source_count,
            height,
            nodes: Vec::new(),
            canonical: HashMap::new(),
            unions: HashMap::new(),
            #[cfg(test)]
            update_visits: 0,
            #[cfg(test)]
            enumeration_visits: 0,
        })
    }

    fn branch(
        &mut self,
        height: u8,
        left: PersistentFrontierSetId,
        right: PersistentFrontierSetId,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        if height == 0 {
            return Err(ExpansionError::IncompleteOrigin);
        }
        if left == Self::EMPTY && right == Self::EMPTY {
            return Ok(Self::EMPTY);
        }
        let key = (height, left, right);
        if let Some(&id) = self.canonical.get(&key) {
            return Ok(id);
        }
        let count = self
            .count(left)?
            .checked_add(self.count(right)?)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let first = if left != Self::EMPTY {
            self.first(left, height - 1)?
        } else {
            (1_usize << (height - 1))
                .checked_add(self.first(right, height - 1)?)
                .ok_or(ExpansionError::IncompleteOrigin)?
        };
        let id = PersistentFrontierSetId(
            u32::try_from(self.nodes.len())
                .ok()
                .and_then(|index| index.checked_add(2))
                .ok_or(ExpansionError::IncompleteOrigin)?,
        );
        self.nodes.push(PersistentFrontierSetNode {
            height,
            left,
            right,
            count,
            first,
        });
        self.canonical.insert(key, id);
        Ok(id)
    }

    fn node(
        &self,
        id: PersistentFrontierSetId,
        height: u8,
    ) -> Result<PersistentFrontierSetNode, ExpansionError> {
        self.nodes
            .get(
                id.0.checked_sub(2)
                    .ok_or(ExpansionError::IncompleteOrigin)? as usize,
            )
            .copied()
            .filter(|node| node.height == height)
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    fn children(
        &self,
        id: PersistentFrontierSetId,
        height: u8,
    ) -> Result<(PersistentFrontierSetId, PersistentFrontierSetId), ExpansionError> {
        if height == 0 || id == Self::LEAF {
            return Err(ExpansionError::IncompleteOrigin);
        }
        if id == Self::EMPTY {
            return Ok((Self::EMPTY, Self::EMPTY));
        }
        let node = self.node(id, height)?;
        Ok((node.left, node.right))
    }

    fn count(&self, id: PersistentFrontierSetId) -> Result<usize, ExpansionError> {
        match id {
            Self::EMPTY => Ok(0),
            Self::LEAF => Ok(1),
            _ => self
                .nodes
                .get(
                    id.0.checked_sub(2)
                        .ok_or(ExpansionError::IncompleteOrigin)? as usize,
                )
                .map(|node| node.count)
                .ok_or(ExpansionError::IncompleteOrigin),
        }
    }

    fn first(&self, id: PersistentFrontierSetId, height: u8) -> Result<usize, ExpansionError> {
        match id {
            Self::EMPTY => Err(ExpansionError::IncompleteOrigin),
            Self::LEAF if height == 0 => Ok(0),
            Self::LEAF => Err(ExpansionError::IncompleteOrigin),
            _ => self.node(id, height).map(|node| node.first),
        }
    }

    fn contains_in_range(
        &self,
        root: PersistentFrontierSetId,
        start: usize,
        end: usize,
    ) -> Result<bool, ExpansionError> {
        if start >= end || end > self.source_count {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut stack = vec![(root, self.height, 0_usize, 1_usize << self.height)];
        while let Some((current, height, node_start, node_end)) = stack.pop() {
            if current == Self::EMPTY || node_end <= start || end <= node_start {
                continue;
            }
            if start <= node_start && node_end <= end {
                return Ok(true);
            }
            if height == 0 {
                if current != Self::LEAF {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                return Ok(true);
            }
            let (left, right) = self.children(current, height)?;
            let middle = node_start + (1_usize << (height - 1));
            stack.push((right, height - 1, middle, node_end));
            stack.push((left, height - 1, node_start, middle));
        }
        Ok(false)
    }

    fn predecessor(
        &self,
        root: PersistentFrontierSetId,
        before: usize,
    ) -> Result<Option<usize>, ExpansionError> {
        if before == 0 || root == Self::EMPTY {
            return Ok(None);
        }
        let mut stack = vec![(root, self.height, 0_usize)];
        while let Some((current, height, start)) = stack.pop() {
            if current == Self::EMPTY || start >= before {
                continue;
            }
            if height == 0 {
                if current != Self::LEAF || start >= self.source_count {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                return Ok(Some(start));
            }
            let (left, right) = self.children(current, height)?;
            let middle = start + (1_usize << (height - 1));
            stack.push((left, height - 1, start));
            stack.push((right, height - 1, middle));
        }
        Ok(None)
    }

    fn set_position(
        &mut self,
        root: PersistentFrontierSetId,
        position: usize,
        present: bool,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        if position >= self.source_count {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut current = root;
        let mut path = Vec::with_capacity(self.height as usize);
        for height in (1..=self.height).rev() {
            let (left, right) = self.children(current, height)?;
            let goes_right = position & (1_usize << (height - 1)) != 0;
            if goes_right {
                path.push((height, true, left));
                current = right;
            } else {
                path.push((height, false, right));
                current = left;
            }
        }
        if current != Self::EMPTY && current != Self::LEAF {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut result = if present { Self::LEAF } else { Self::EMPTY };
        while let Some((height, went_right, sibling)) = path.pop() {
            result = if went_right {
                self.branch(height, sibling, result)?
            } else {
                self.branch(height, result, sibling)?
            };
        }
        #[cfg(test)]
        {
            self.update_visits += usize::from(self.height) + 1;
        }
        Ok(result)
    }

    fn insert_source(
        &mut self,
        root: PersistentFrontierSetId,
        source: SourceUnitId,
        ancestry: &SourceAncestryIndex,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        let (entry, exit) = ancestry.interval(source)?;
        if self.contains_in_range(root, entry, exit)? {
            return Ok(root);
        }
        let mut result = root;
        if let Some(ancestor_entry) = self.predecessor(root, entry)? {
            let ancestor = ancestry.unit_at_entry(ancestor_entry)?;
            if ancestry.is_ancestor(ancestor, source)? {
                result = self.set_position(result, ancestor_entry, false)?;
            }
        }
        self.set_position(result, entry, true)
    }

    fn union(
        &mut self,
        left: PersistentFrontierSetId,
        right: PersistentFrontierSetId,
        ancestry: &SourceAncestryIndex,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        if left == Self::EMPTY || left == right {
            return Ok(right);
        }
        if right == Self::EMPTY {
            return Ok(left);
        }
        let pair = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        if let Some(&union) = self.unions.get(&pair) {
            return Ok(union);
        }
        let (_, left_only, right_only) = self.partition_frontiers(left, right, self.height)?;
        let (additional, mut result) = if self.count(left_only)? <= self.count(right_only)? {
            (left_only, right)
        } else {
            (right_only, left)
        };
        for source in self.enumerate(additional, ancestry)? {
            result = self.insert_source(result, source, ancestry)?;
        }
        self.unions.insert(pair, result);
        Ok(result)
    }

    fn intersection(
        &mut self,
        left: PersistentFrontierSetId,
        right: PersistentFrontierSetId,
        ancestry: &SourceAncestryIndex,
        excluded: &SourceAncestorExclusions<'_>,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        if left == right || left == Self::EMPTY || right == Self::EMPTY {
            return Ok(if left == right { left } else { Self::EMPTY });
        }

        let (common, left_only, right_only) = self.partition_frontiers(left, right, self.height)?;
        let left_only = self.enumerate(left_only, ancestry)?;
        let right_only = self.enumerate(right_only, ancestry)?;
        let mut result = common;
        for source in ancestry.intersect_frontiers(&left_only, &right_only, excluded)? {
            result = self.insert_source(result, source, ancestry)?;
        }
        Ok(result)
    }

    fn partition_frontiers(
        &mut self,
        left: PersistentFrontierSetId,
        right: PersistentFrontierSetId,
        height: u8,
    ) -> Result<
        (
            PersistentFrontierSetId,
            PersistentFrontierSetId,
            PersistentFrontierSetId,
        ),
        ExpansionError,
    > {
        if left == right {
            return Ok((left, Self::EMPTY, Self::EMPTY));
        }
        if left == Self::EMPTY {
            return Ok((Self::EMPTY, Self::EMPTY, right));
        }
        if right == Self::EMPTY {
            return Ok((Self::EMPTY, left, Self::EMPTY));
        }
        if height == 0 {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let (left_left, left_right) = self.children(left, height)?;
        let (right_left, right_right) = self.children(right, height)?;
        let (common_left, left_only_left, right_only_left) =
            self.partition_frontiers(left_left, right_left, height - 1)?;
        let (common_right, left_only_right, right_only_right) =
            self.partition_frontiers(left_right, right_right, height - 1)?;
        Ok((
            self.branch(height, common_left, common_right)?,
            self.branch(height, left_only_left, left_only_right)?,
            self.branch(height, right_only_left, right_only_right)?,
        ))
    }

    fn enumerate_subtree(
        &mut self,
        root: PersistentFrontierSetId,
        height: u8,
        start: usize,
        ancestry: &SourceAncestryIndex,
        sources: &mut Vec<SourceUnitId>,
    ) -> Result<(), ExpansionError> {
        let mut stack = vec![(root, height, start)];
        while let Some((current, height, start)) = stack.pop() {
            if current == Self::EMPTY {
                continue;
            }
            if self.count(current)? == 1 {
                let entry = start
                    .checked_add(self.first(current, height)?)
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                if entry >= self.source_count {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                #[cfg(test)]
                {
                    self.enumeration_visits += 1;
                }
                sources.push(ancestry.unit_at_entry(entry)?);
                continue;
            }
            #[cfg(test)]
            {
                self.enumeration_visits += 1;
            }
            if height == 0 {
                if current != Self::LEAF || start >= self.source_count {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                sources.push(ancestry.unit_at_entry(start)?);
                continue;
            }
            let (left, right) = self.children(current, height)?;
            let half = 1_usize << (height - 1);
            stack.push((right, height - 1, start + half));
            stack.push((left, height - 1, start));
        }
        Ok(())
    }

    fn enumerate(
        &mut self,
        root: PersistentFrontierSetId,
        ancestry: &SourceAncestryIndex,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        let mut sources = Vec::with_capacity(self.count(root)?);
        self.enumerate_subtree(root, self.height, 0, ancestry, &mut sources)?;
        Ok(sources)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct IdentityFrontierMemo {
    contexts: BTreeMap<Vec<SourceUnitId>, u32>,
    frontier_sets: PersistentFrontierSets,
    resolved_nodes: HashMap<(u32, MacroContributorSetId), PersistentFrontierSetId>,
    intersections:
        HashMap<(u32, PersistentFrontierSetId, PersistentFrontierSetId), PersistentFrontierSetId>,
    materialized: HashMap<PersistentFrontierSetId, Box<[SourceUnitId]>>,
    #[cfg(test)]
    intersection_computations: usize,
    #[cfg(test)]
    frontier_node_resolutions: usize,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl IdentityFrontierMemo {
    fn new(source_count: usize) -> Result<Self, ExpansionError> {
        Ok(Self {
            contexts: BTreeMap::new(),
            frontier_sets: PersistentFrontierSets::new(source_count)?,
            resolved_nodes: HashMap::new(),
            intersections: HashMap::new(),
            materialized: HashMap::new(),
            #[cfg(test)]
            intersection_computations: 0,
            #[cfg(test)]
            frontier_node_resolutions: 0,
        })
    }

    fn context(&mut self, mut excluded: Vec<SourceUnitId>) -> Result<u32, ExpansionError> {
        excluded.sort();
        excluded.dedup();
        if let Some(&context) = self.contexts.get(&excluded) {
            return Ok(context);
        }
        let context = self
            .contexts
            .len()
            .try_into()
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        self.contexts.insert(excluded, context);
        Ok(context)
    }

    fn resolve_frontier_set(
        &mut self,
        context: u32,
        dag: MacroContributorDagRef<'_>,
        ancestry: &SourceAncestryIndex,
        excluded: &SourceAncestorExclusions<'_>,
        root: MacroContributorSetId,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        let mut stack = vec![(root, false)];
        while let Some((current, expanded)) = stack.pop() {
            if self.resolved_nodes.contains_key(&(context, current)) {
                continue;
            }
            let index = current.0 as usize;
            let node = dag
                .nodes
                .get(index)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if node.parents.iter().any(|parent| parent.0 as usize >= index) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            if !expanded {
                stack.push((current, true));
                stack.extend(
                    node.parents
                        .iter()
                        .rev()
                        .copied()
                        .filter(|parent| !self.resolved_nodes.contains_key(&(context, *parent)))
                        .map(|parent| (parent, false)),
                );
                continue;
            }

            let mut frontier = PersistentFrontierSets::EMPTY;
            for &parent in &node.parents {
                let parent = *self
                    .resolved_nodes
                    .get(&(context, parent))
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                frontier = self.frontier_sets.union(frontier, parent, ancestry)?;
            }
            for &source in &node.local {
                if !excluded.contains(source)? {
                    frontier = self
                        .frontier_sets
                        .insert_source(frontier, source, ancestry)?;
                }
            }
            if self
                .resolved_nodes
                .insert((context, current), frontier)
                .is_some()
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            #[cfg(test)]
            {
                self.frontier_node_resolutions += 1;
            }
        }
        self.resolved_nodes
            .get(&(context, root))
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    fn intersection(
        &mut self,
        context: u32,
        ancestry: &SourceAncestryIndex,
        excluded: &SourceAncestorExclusions<'_>,
        left: PersistentFrontierSetId,
        right: PersistentFrontierSetId,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        if left == right {
            return Ok(left);
        }
        let (left, right) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        if let Some(&intersection) = self.intersections.get(&(context, left, right)) {
            return Ok(intersection);
        }
        let intersection = self
            .frontier_sets
            .intersection(left, right, ancestry, excluded)?;
        self.intersections
            .insert((context, left, right), intersection);
        #[cfg(test)]
        {
            self.intersection_computations += 1;
        }
        Ok(intersection)
    }

    fn materialize(
        &mut self,
        frontier: PersistentFrontierSetId,
        ancestry: &SourceAncestryIndex,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        if let Some(materialized) = self.materialized.get(&frontier) {
            return Ok(materialized.to_vec());
        }
        let materialized = self.frontier_sets.enumerate(frontier, ancestry)?;
        self.materialized
            .insert(frontier, materialized.clone().into_boxed_slice());
        Ok(materialized)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl<'a, 'm> ProductBasisRangeIndex<'a, 'm> {
    fn new(
        ancestry: &'a SourceAncestryIndex,
        excluded: &'a SourceAncestorExclusions<'a>,
        exclusion_context: u32,
        frontier_memo: &'m mut IdentityFrontierMemo,
        contributor_dag: MacroContributorDagRef<'_>,
        token_contributors: &[MacroContributorSetId],
    ) -> Result<Self, ExpansionError> {
        Self::new_excluding(
            ancestry,
            excluded,
            exclusion_context,
            frontier_memo,
            contributor_dag,
            token_contributors,
            &[],
        )
    }

    fn new_excluding(
        ancestry: &'a SourceAncestryIndex,
        excluded: &'a SourceAncestorExclusions<'a>,
        exclusion_context: u32,
        frontier_memo: &'m mut IdentityFrontierMemo,
        contributor_dag: MacroContributorDagRef<'_>,
        token_contributors: &[MacroContributorSetId],
        discarded_ranges: &[MacroOutputRange],
    ) -> Result<Self, ExpansionError> {
        let token_count = token_contributors.len();
        let leaf_count = token_count
            .checked_next_power_of_two()
            .ok_or(ExpansionError::IncompleteOrigin)?
            .max(1);
        let node_count = leaf_count
            .checked_mul(2)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        #[cfg(test)]
        let mut construction_work = 0;
        let mut previous_end = None;
        for &range in discarded_ranges {
            #[cfg(test)]
            {
                construction_work += 1;
            }
            if range.start >= range.end
                || range.end as usize > token_count
                || previous_end.is_some_and(|end| range.start < end)
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            previous_end = Some(range.end);
        }

        let mut frontiers = vec![None; node_count];
        let mut discarded_index = 0;
        for (ordinal, &root) in token_contributors.iter().enumerate() {
            #[cfg(test)]
            {
                construction_work += 1;
            }
            while discarded_ranges
                .get(discarded_index)
                .is_some_and(|range| range.end as usize <= ordinal)
            {
                #[cfg(test)]
                {
                    construction_work += 1;
                }
                discarded_index += 1;
            }
            let discarded = discarded_ranges.get(discarded_index).is_some_and(|range| {
                range.start as usize <= ordinal && ordinal < range.end as usize
            });
            if !discarded {
                frontiers[leaf_count + ordinal] = Some(frontier_memo.resolve_frontier_set(
                    exclusion_context,
                    contributor_dag,
                    ancestry,
                    excluded,
                    root,
                )?);
            }
        }
        for index in (1..leaf_count).rev() {
            #[cfg(test)]
            {
                construction_work += 1;
            }
            let left = frontiers[index * 2];
            let right = frontiers[index * 2 + 1];
            frontiers[index] = match (left, right) {
                (Some(left), Some(right)) if left != right => Some(frontier_memo.intersection(
                    exclusion_context,
                    ancestry,
                    excluded,
                    left,
                    right,
                )?),
                (Some(frontier), _) | (_, Some(frontier)) => Some(frontier),
                (None, None) => None,
            };
        }
        Ok(Self {
            ancestry,
            excluded,
            exclusion_context,
            frontier_memo,
            token_count,
            leaf_count,
            frontiers,
            #[cfg(test)]
            construction_work,
            #[cfg(test)]
            query_work: 0,
        })
    }

    pub(super) fn intersection(
        &mut self,
        range: MacroOutputRange,
    ) -> Result<Vec<SourceUnitId>, ExpansionError> {
        let result = self.intersection_frontier(range)?;
        self.frontier_memo.materialize(result, self.ancestry)
    }

    #[cfg(test)]
    fn work(&self) -> (usize, usize) {
        (self.construction_work, self.query_work)
    }

    fn intersection_frontier(
        &mut self,
        range: MacroOutputRange,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        let mut start = range.start as usize;
        let mut end = range.end as usize;
        if start >= end || end > self.token_count {
            return Err(ExpansionError::IncompleteOrigin);
        }
        start += self.leaf_count;
        end += self.leaf_count;
        let mut result = None::<PersistentFrontierSetId>;
        while start < end {
            #[cfg(test)]
            {
                self.query_work += 1;
            }
            if start % 2 == 1 {
                if let Some(frontier) = self.frontiers[start] {
                    result = Some(self.merge(result, frontier)?);
                }
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                if let Some(frontier) = self.frontiers[end] {
                    result = Some(self.merge(result, frontier)?);
                }
            }
            start /= 2;
            end /= 2;
        }
        result.ok_or(ExpansionError::IncompleteOrigin)
    }

    fn merge(
        &mut self,
        current: Option<PersistentFrontierSetId>,
        next: PersistentFrontierSetId,
    ) -> Result<PersistentFrontierSetId, ExpansionError> {
        match current {
            Some(current) if current == next => Ok(current),
            Some(current) => self.frontier_memo.intersection(
                self.exclusion_context,
                self.ancestry,
                self.excluded,
                current,
                next,
            ),
            None => Ok(next),
        }
    }
}

#[cfg(test)]
pub(super) fn with_flat_product_basis_index<R>(
    ancestry: &SourceAncestryIndex,
    excluded: &SourceAncestorExclusions<'_>,
    token_contributors: &[Vec<SourceUnitId>],
    query: impl FnOnce(&mut ProductBasisRangeIndex<'_, '_>) -> Result<R, ExpansionError>,
) -> Result<R, ExpansionError> {
    with_flat_product_basis_index_excluding(ancestry, excluded, token_contributors, &[], query)
}

#[cfg(test)]
fn with_flat_product_basis_index_excluding<R>(
    ancestry: &SourceAncestryIndex,
    excluded: &SourceAncestorExclusions<'_>,
    token_contributors: &[Vec<SourceUnitId>],
    discarded_ranges: &[MacroOutputRange],
    query: impl FnOnce(&mut ProductBasisRangeIndex<'_, '_>) -> Result<R, ExpansionError>,
) -> Result<R, ExpansionError> {
    let mut builder = MacroContributorDagBuilder::default();
    let roots = token_contributors
        .iter()
        .map(|contributors| builder.intern(contributors.clone(), Vec::new()))
        .collect::<Result<Vec<_>, _>>()?;
    let mut memo = IdentityFrontierMemo::new(ancestry.parents.len())?;
    let context = memo.context(Vec::new())?;
    let mut index = ProductBasisRangeIndex::new_excluding(
        ancestry,
        excluded,
        context,
        &mut memo,
        builder.view(),
        &roots,
        discarded_ranges,
    )?;
    query(&mut index)
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Default, Eq, PartialEq)]
struct PendingContributorSet {
    local: Vec<SourceUnitId>,
    parent_tokens: Vec<(ExpnId, u32)>,
    parent_ranges: Vec<(ExpnId, MacroOutputRange)>,
}

#[cfg(rust_item_dependencies_patched)]
impl PendingContributorSet {
    fn normalize(&mut self) {
        self.local.sort();
        self.local.dedup();
        self.parent_tokens.sort_by_key(|(parent, ordinal)| {
            (parent.krate.as_u32(), parent.local_id.as_u32(), *ordinal)
        });
        self.parent_tokens.dedup();
        self.parent_ranges.sort_by_key(|(parent, range)| {
            (
                parent.krate.as_u32(),
                parent.local_id.as_u32(),
                range.start,
                range.end,
            )
        });
        self.parent_ranges.dedup();
    }

    fn is_empty(&self) -> bool {
        self.local.is_empty() && self.parent_tokens.is_empty() && self.parent_ranges.is_empty()
    }

    fn content_hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        for unit in &self.local {
            unit.0.hash(&mut hasher);
        }
        self.parent_tokens.hash(&mut hasher);
        for (parent, range) in &self.parent_ranges {
            parent.hash(&mut hasher);
            range.start.hash(&mut hasher);
            range.end.hash(&mut hasher);
        }
        hasher.finish()
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct PendingInputId(u32);

#[cfg(rust_item_dependencies_patched)]
struct ResolvedPendingInputs {
    roots: Vec<Option<MacroContributorSetId>>,
    #[cfg(test)]
    fact_visits: usize,
}

#[cfg(rust_item_dependencies_patched)]
impl ResolvedPendingInputs {
    fn new(count: usize) -> Self {
        Self {
            roots: vec![None; count],
            #[cfg(test)]
            fact_visits: 0,
        }
    }

    fn get(&self, id: PendingInputId) -> Result<Option<MacroContributorSetId>, ExpansionError> {
        self.roots
            .get(id.0 as usize)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    fn insert(
        &mut self,
        id: PendingInputId,
        root: MacroContributorSetId,
        fact_count: usize,
    ) -> Result<(), ExpansionError> {
        let slot = self
            .roots
            .get_mut(id.0 as usize)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        if slot.replace(root).is_some() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        #[cfg(test)]
        {
            self.fact_visits = self
                .fact_visits
                .checked_add(fact_count)
                .ok_or(ExpansionError::IncompleteOrigin)?;
        }
        #[cfg(not(test))]
        let _ = fact_count;
        Ok(())
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Default)]
struct PendingTokenContributors {
    local: Vec<SourceUnitId>,
    inputs: Vec<PendingInputId>,
}

#[cfg(rust_item_dependencies_patched)]
struct PendingProducerContributors {
    base: PendingContributorSet,
    tokens: Vec<PendingTokenContributors>,
}

#[cfg(all(test, rust_item_dependencies_patched))]
mod pending_input_tests {
    use super::*;

    #[test]
    fn forwarded_input_ranges_are_resolved_once_and_shared_by_output_tokens() {
        const TOKENS: usize = 1_024;
        let parent = ExpnId::root();
        let mut builder = MacroContributorDagBuilder::default();
        let parent_roots = (0..TOKENS)
            .map(|source| builder.intern(vec![SourceUnitId(source as u32)], Vec::new()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let parent_tokens = PreparedTokenContributors::new(parent_roots, &mut builder).unwrap();
        let prepared = FxHashMap::from_iter([(parent, parent_tokens)]);

        let input = PendingContributorSet {
            parent_tokens: (0..TOKENS)
                .map(|ordinal| (parent, ordinal as u32))
                .collect(),
            ..PendingContributorSet::default()
        };
        let pending_inputs = vec![input];
        let input_id = PendingInputId(0);
        let pending = PendingProducerContributors {
            base: PendingContributorSet {
                local: vec![SourceUnitId(TOKENS as u32)],
                ..PendingContributorSet::default()
            },
            tokens: (0..TOKENS)
                .map(|_| PendingTokenContributors {
                    local: Vec::new(),
                    inputs: vec![input_id],
                })
                .collect(),
        };
        let mut resolved = ResolvedPendingInputs::new(1);
        let output = ProvenanceCollector::build_token_contributors(
            &pending,
            &pending_inputs,
            &mut resolved,
            &prepared,
            &mut builder,
        )
        .unwrap();

        assert_eq!(resolved.fact_visits, TOKENS);
        assert!(resolved.get(input_id).unwrap().is_some());
        assert!(output.as_slice().windows(2).all(|pair| pair[0] == pair[1]));
        assert!(builder.nodes.len() <= TOKENS * 3);
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn memoized_identity_source(
    cache: &mut BTreeMap<SourceUnitId, MacroProductSource>,
    id: SourceUnitId,
    compute: impl FnOnce() -> Result<MacroProductSource, ExpansionError>,
) -> Result<MacroProductSource, ExpansionError> {
    if let Some(source) = cache.get(&id) {
        return Ok(*source);
    }
    let source = compute()?;
    cache.insert(id, source);
    Ok(source)
}

#[cfg(rust_item_dependencies_patched)]
struct ProvenanceCollector<'a> {
    compiler: &'a Compiler,
    source: &'a SourceInventory,
    origins: &'a rustc_data_structures::unord::UnordMap<ExpnId, MacroInvocationOrigin>,
    prepared: PreparedExpansionOrigins,
    child_outputs: FxHashMap<ExpnId, Vec<(ExpnId, MacroOutputTokenRange)>>,
    template_indices: BTreeMap<SourceUnitId, SourceUnitIntervalIndex>,
    repetition_indices: BTreeMap<(SourceUnitId, SourceUnitId), SourceUnitIntervalIndex>,
    source_ancestry: SourceAncestryIndex,
    identity_ranges: MacroProductIdentityRangeIndex,
    input_cache: FxHashMap<(ExpnId, u32, u32, u32, bool), Option<PendingInputId>>,
    pending_inputs: Vec<PendingContributorSet>,
    input_canonical: FxHashMap<u64, Vec<PendingInputId>>,
    template_cache: FxHashMap<(ExpnId, usize), Option<SourceUnitId>>,
    identity_source_cache: BTreeMap<SourceUnitId, MacroProductSource>,
    identity_source_kinds: Vec<Option<crate::source::DeclarativeSourceUnitKind>>,
    identity_frontier_memo: IdentityFrontierMemo,
    valid_output_origins: FxHashSet<ExpnId>,
}

#[cfg(rust_item_dependencies_patched)]
impl<'a> ProvenanceCollector<'a> {
    fn new<'tcx: 'a>(
        compiler: &'a Compiler,
        tcx: TyCtxt<'tcx>,
        source: &'a SourceInventory,
        prepared: PreparedExpansionOrigins,
    ) -> Result<Self, ExpansionError> {
        let origins = &tcx.resolutions(()).macro_invocation_origins;

        let mut child_outputs =
            FxHashMap::<ExpnId, Vec<(ExpnId, MacroOutputTokenRange)>>::default();
        for expansion in prepared
            .ordered
            .iter()
            .filter(|expansion| expansion.parent_definition.is_some())
        {
            let Some(observation) = origins
                .get(&expansion.compiler_id)
                .and_then(|origin| origin.declarative_expansion.as_ref())
                .and_then(|observation| ValidatedDeclarativeOutput::new(observation))
                .map(ValidatedDeclarativeOutput::observation)
            else {
                continue;
            };
            for child in &observation.child_expansions {
                child_outputs
                    .entry(child.expansion)
                    .or_default()
                    .push((expansion.compiler_id, child.output));
            }
        }

        let source_ancestry = SourceAncestryIndex::new(source)?;
        let identity_ranges =
            MacroProductIdentityRangeIndex::new(&source.original, &source.pieces)?;
        let identity_source_kinds = source
            .declarative_unit_kinds()
            .map_err(expansion_source_error)?;
        let mut template_units = BTreeMap::<SourceUnitId, Vec<SourceUnitId>>::new();
        for template in &source.macro_templates {
            template_units
                .entry(template.rule)
                .or_default()
                .push(template.unit);
        }
        let template_indices = template_units
            .into_iter()
            .map(|(rule, units)| {
                SourceUnitIntervalIndex::new(source, rule, units).map(|index| (rule, index))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;

        let mut repetition_units =
            BTreeMap::<(SourceUnitId, SourceUnitId), Vec<SourceUnitId>>::new();
        for repetition in &source.macro_repetitions {
            repetition_units
                .entry((repetition.invocation, repetition.rule))
                .or_default()
                .extend(repetition.elements.iter().map(|element| element.unit));
        }
        let repetition_indices = repetition_units
            .into_iter()
            .map(|(key @ (invocation, _), units)| {
                SourceUnitIntervalIndex::new(source, invocation, units).map(|index| (key, index))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;

        Ok(Self {
            compiler,
            source,
            origins,
            prepared,
            child_outputs,
            template_indices,
            repetition_indices,
            source_ancestry,
            identity_ranges,
            input_cache: FxHashMap::default(),
            pending_inputs: Vec::new(),
            input_canonical: FxHashMap::default(),
            template_cache: FxHashMap::default(),
            identity_source_cache: BTreeMap::new(),
            identity_source_kinds,
            identity_frontier_memo: IdentityFrontierMemo::new(source.units.len())?,
            valid_output_origins: FxHashSet::default(),
        })
    }

    fn collect(mut self) -> Result<MacroProvenance, ExpansionError> {
        let mut outputless_producers = self
            .prepared
            .ordered
            .iter()
            .filter_map(|raw| {
                let output_structure = raw.output_structure?;
                if output_structure == MacroExpansionOutputStructure::Empty {
                    return Some(raw.compiler_id);
                }
                if raw.implementation != Some(MacroImplementationKind::Declarative)
                    || !raw
                        .macro_definition
                        .is_some_and(|definition| definition.is_local())
                {
                    return None;
                }
                let expansion = self
                    .origins
                    .get(&raw.compiler_id)?
                    .declarative_expansion
                    .as_ref()
                    .and_then(|expansion| ValidatedDeclarativeOutputMeaning::new(expansion))?
                    .observation();
                (!expansion.owner_output.intrinsic
                    && expansion.owner_output.dependent_outputs.is_empty()
                    && expansion.owner_output.required_outputs.is_empty()
                    && expansion.definitions.is_empty()
                    && expansion.child_expansions.is_empty())
                .then_some(raw.compiler_id)
            })
            .collect::<Vec<_>>();
        outputless_producers.sort_by_key(|producer| producer.expn_hash().local_hash().as_u64());
        if outputless_producers
            .windows(2)
            .any(|pair| pair[0] == pair[1])
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let outputless_producer_set = outputless_producers
            .iter()
            .copied()
            .collect::<FxHashSet<_>>();

        // Output meaning is independent of whether this source was refined
        // into editable macro components. Record every nonempty, complete
        // local declarative output census; direct empty outputs enter the
        // separate structural seed inventory above.
        let mut producers = FxHashMap::default();
        for raw in &self.prepared.ordered {
            if raw.implementation != Some(MacroImplementationKind::Declarative)
                || !raw
                    .macro_definition
                    .is_some_and(|definition| definition.is_local())
                || outputless_producer_set.contains(&raw.compiler_id)
            {
                continue;
            }
            let Some(expansion) = self
                .origins
                .get(&raw.compiler_id)
                .and_then(|origin| origin.declarative_expansion.as_ref())
                .and_then(|expansion| ValidatedDeclarativeOutputMeaning::new(expansion))
                .map(ValidatedDeclarativeOutputMeaning::observation)
            else {
                continue;
            };
            if producers
                .insert(raw.compiler_id, Self::prepare_producer(expansion)?)
                .is_some()
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }

        let mut split_producers = Vec::new();
        for raw in self
            .prepared
            .ordered
            .iter()
            .filter(|raw| raw.implementation == Some(MacroImplementationKind::Declarative))
        {
            let Some(selected_rule) = raw.selected_rule_unit() else {
                continue;
            };
            if self.template_indices.contains_key(&selected_rule)
                || raw.written_invocation().is_some_and(|invocation| {
                    self.repetition_indices
                        .contains_key(&(invocation, selected_rule))
                })
            {
                split_producers.push(raw.compiler_id);
            }
        }

        // A producer whose source was split needs precise output coverage.
        // A local declarative descendant with complete output provenance and
        // one matching contributor parent is part of that same conditional
        // output tree: binding such a child's definitions back to the written
        // ancestor invocation would materialize dead siblings. Keep coverage
        // closed both towards the written invocation and through exactly those
        // descendants. Children without complete provenance keep their ordinary
        // ExpansionUse carrier instead.
        let mut coverage_children = FxHashMap::<ExpnId, Vec<ExpnId>>::default();
        let mut coverage_parents = FxHashMap::default();
        for (&parent, producer) in &producers {
            for &(child, _) in &producer.child_outputs {
                if !producers.contains_key(&child) {
                    continue;
                }
                let raw = self.raw_expansion(child)?;
                if self.complete_contributor_parent(raw)? != Some(Some(parent)) {
                    continue;
                }
                if coverage_parents.insert(child, parent).is_some() {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                coverage_children.entry(parent).or_default().push(child);
            }
        }
        for children in coverage_children.values_mut() {
            children.sort_by_key(|child| child.expn_hash().local_hash().as_u64());
            children.dedup();
        }
        let mut required = Vec::new();
        let mut required_set = FxHashSet::default();
        let mut required_parents = FxHashMap::default();
        let mut pending = split_producers;
        while let Some(compiler_id) = pending.pop() {
            if !required_set.insert(compiler_id) {
                continue;
            }
            let raw = self.raw_expansion(compiler_id)?;
            if raw.implementation != Some(MacroImplementationKind::Declarative)
                || raw.selected_rule_unit().is_none()
                || self
                    .origins
                    .get(&compiler_id)
                    .and_then(|origin| origin.declarative_expansion.as_ref())
                    .and_then(|expansion| ValidatedDeclarativeOutputMeaning::new(expansion))
                    .is_none()
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let parent = self.contributor_parent(raw)?;
            if coverage_parents
                .get(&compiler_id)
                .is_some_and(|expected| parent != Some(*expected))
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            if let Some(parent) = parent {
                pending.push(parent);
            }
            pending.extend(
                coverage_children
                    .get(&compiler_id)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
            if required_parents.insert(compiler_id, parent).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            required.push(compiler_id);
        }

        // Every generated producer must have one complete path to a written
        // invocation. Memoize already rooted suffixes so a deeply nested
        // macro chain is traversed once rather than once per producer.
        let mut rooted = FxHashSet::default();
        for &producer in &required {
            let mut path = Vec::new();
            let mut active = FxHashSet::default();
            let mut current = producer;
            loop {
                if rooted.contains(&current) {
                    break;
                }
                if !active.insert(current) {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                path.push(current);
                let parent = required_parents
                    .get(&current)
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                let Some(parent) = parent else {
                    break;
                };
                current = *parent;
            }
            rooted.extend(path);
        }
        if rooted.len() != required.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }

        required.sort_by_key(|producer| producer.expn_hash().local_hash().as_u64());
        let coverage_required = required
            .into_iter()
            .filter(|producer| !outputless_producer_set.contains(producer))
            .collect();

        // Definition identity must not depend on whether this analysis found
        // a currently removable source component. A prior reduction can make
        // the last split component disappear while definitions from the same
        // complete producer remain. Build identity for every complete local
        // declarative producer that has one complete declarative path to a
        // written invocation. This eligibility is independent of the smaller
        // coverage set above.
        let mut identity_parents = FxHashMap::default();
        let mut identity_children = FxHashMap::<ExpnId, Vec<ExpnId>>::default();
        let mut identity_roots = Vec::new();
        for raw in &self.prepared.ordered {
            if raw.parent_definition.is_none() {
                continue;
            }
            let compiler_id = raw.compiler_id;
            let Some(parent) = self.complete_contributor_parent(raw)? else {
                continue;
            };
            if parent.is_none() {
                identity_roots.push(compiler_id);
            }
            identity_parents.insert(compiler_id, parent);
            if let Some(parent) = parent {
                identity_children
                    .entry(parent)
                    .or_default()
                    .push(compiler_id);
            }
        }
        let mut identity_required = FxHashSet::default();
        let mut pending = identity_roots;
        while let Some(compiler_id) = pending.pop() {
            if !identity_required.insert(compiler_id) {
                continue;
            }
            pending.extend(
                identity_children
                    .get(&compiler_id)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        if identity_required.iter().any(|compiler_id| {
            identity_parents.get(compiler_id).is_none_or(|parent| {
                parent.is_some_and(|parent| !identity_required.contains(&parent))
            })
        }) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut identity_required = identity_required.into_iter().collect::<Vec<_>>();
        identity_required.sort_by_key(|producer| producer.expn_hash().local_hash().as_u64());

        let preparation = producer_preparation_plan(identity_required, coverage_required)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let mut pending = FxHashMap::default();
        for &(compiler_id, requires_coverage) in &preparation {
            let expansion = self
                .origins
                .get(&compiler_id)
                .and_then(|origin| origin.declarative_expansion.as_ref())
                .and_then(|expansion| ValidatedDeclarativeOutput::new(expansion))
                .map(ValidatedDeclarativeOutput::observation)
                .cloned()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let contributors = self.prepare_pending_contributors(compiler_id, &expansion)?;
            if pending
                .insert(compiler_id, (expansion, requires_coverage, contributors))
                .is_some()
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        let starts = preparation
            .iter()
            .map(|(compiler_id, _)| *compiler_id)
            .collect::<Vec<_>>();
        let (preparation_order, _) = dependency_postorder(starts, |compiler_id| {
            let (_, _, contributors) = pending.get(&compiler_id)?;
            let mut dependencies = contributors
                .base
                .parent_ranges
                .iter()
                .map(|(parent, _)| *parent)
                .chain(
                    contributors
                        .base
                        .parent_tokens
                        .iter()
                        .map(|(parent, _)| *parent),
                )
                .collect::<Vec<_>>();
            let mut input_ids = contributors
                .tokens
                .iter()
                .flat_map(|token| token.inputs.iter().copied())
                .collect::<Vec<_>>();
            input_ids.sort();
            input_ids.dedup();
            for input in input_ids {
                let input = self.pending_inputs.get(input.0 as usize)?;
                dependencies.extend(input.parent_ranges.iter().map(|(parent, _)| *parent));
                dependencies.extend(input.parent_tokens.iter().map(|(parent, _)| *parent));
            }
            dependencies.sort_by_key(|parent| parent.expn_hash().local_hash().as_u64());
            dependencies.dedup();
            Some(dependencies)
        })
        .ok_or(ExpansionError::IncompleteOrigin)?;

        let mut contributor_builder = MacroContributorDagBuilder::default();
        let mut token_contributors = FxHashMap::default();
        let mut definition_bases = FxHashMap::default();
        let mut resolved_inputs = ResolvedPendingInputs::new(self.pending_inputs.len());
        for compiler_id in preparation_order {
            let (expansion, requires_coverage, pending_contributors) = pending
                .remove(&compiler_id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let prepared_tokens = Self::build_token_contributors(
                &pending_contributors,
                &self.pending_inputs,
                &mut resolved_inputs,
                &token_contributors,
                &mut contributor_builder,
            )?;
            self.prepare_definition_bases(
                compiler_id,
                &expansion,
                &prepared_tokens,
                contributor_builder.view(),
                &mut definition_bases,
            )?;
            if requires_coverage && !producers.contains_key(&compiler_id) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            if token_contributors
                .insert(compiler_id, prepared_tokens)
                .is_some()
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        if !pending.is_empty() || token_contributors.len() != preparation.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let coverage_producer_order = preparation
            .iter()
            .filter_map(|&(producer, requires_coverage)| requires_coverage.then_some(producer))
            .collect();
        Ok(MacroProvenance {
            origins: self.prepared,
            coverage_producer_order,
            producers,
            contributor_dag: Arc::new(contributor_builder.finish()),
            token_contributors,
            definition_bases,
            outputless_producers,
        })
    }

    fn contributor_parent(
        &self,
        raw: &PreparedExpansionOrigin,
    ) -> Result<Option<ExpnId>, ExpansionError> {
        let generation_parent = raw.parents.generation();
        let parent_state = if let Some(parent) = generation_parent {
            let candidate = self
                .prepared
                .get(parent)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if !matches!(&candidate.kind, ExpansionKind::Macro { .. }) {
                Some(DeclarativeGenerationParentState::Opaque)
            } else {
                match (candidate.implementation, candidate.macro_definition) {
                    (Some(MacroImplementationKind::Declarative), Some(definition))
                        if !definition.is_local() =>
                    {
                        Some(DeclarativeGenerationParentState::Opaque)
                    }
                    (Some(MacroImplementationKind::Declarative), Some(definition))
                        if definition.is_local()
                            && candidate.selected_rule_unit().is_some()
                            && candidate.parent_definition.is_some() =>
                    {
                        Some(DeclarativeGenerationParentState::RefinedLocal {
                            link_complete: self.parent_link_complete(raw.compiler_id, parent)?,
                        })
                    }
                    (Some(MacroImplementationKind::Declarative), _) | (None, _) => {
                        Some(DeclarativeGenerationParentState::LocalIncomplete)
                    }
                    (
                        Some(
                            MacroImplementationKind::Builtin | MacroImplementationKind::Procedural,
                        ),
                        _,
                    ) => Some(DeclarativeGenerationParentState::Opaque),
                    (
                        Some(
                            MacroImplementationKind::Legacy
                            | MacroImplementationKind::InertAttribute
                            | MacroImplementationKind::GlobDelegation,
                        ),
                        _,
                    ) => Some(DeclarativeGenerationParentState::Opaque),
                }
            }
        } else {
            None
        };
        match resolve_declarative_contributor_parent(
            generation_parent,
            raw.written_invocation().is_some(),
            parent_state,
        ) {
            DeclarativeContributorParent::Root => Ok(None),
            DeclarativeContributorParent::Parent(parent) => Ok(Some(parent)),
            DeclarativeContributorParent::Incomplete => Err(ExpansionError::IncompleteOrigin),
        }
    }

    fn complete_contributor_parent(
        &self,
        raw: &PreparedExpansionOrigin,
    ) -> Result<Option<Option<ExpnId>>, ExpansionError> {
        let compiler_id = raw.compiler_id;
        let complete = raw.implementation == Some(MacroImplementationKind::Declarative)
            && raw.selected_rule_unit().is_some()
            && raw
                .macro_definition
                .is_some_and(|definition| definition.is_local())
            && self
                .origins
                .get(&compiler_id)
                .and_then(|origin| origin.declarative_expansion.as_ref())
                .and_then(|expansion| ValidatedDeclarativeOutput::new(expansion))
                .is_some();
        if !complete {
            return Ok(None);
        }
        match self.contributor_parent(raw) {
            Ok(parent) => Ok(Some(parent)),
            Err(ExpansionError::IncompleteOrigin) => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn parent_link_complete(&self, child: ExpnId, parent: ExpnId) -> Result<bool, ExpansionError> {
        let Some(observation) = self
            .origins
            .get(&parent)
            .and_then(|origin| origin.declarative_expansion.as_ref())
            .and_then(|observation| ValidatedDeclarativeOutput::new(observation))
            .map(ValidatedDeclarativeOutput::observation)
        else {
            return Ok(false);
        };
        let output_token_count = u32::try_from(observation.output_tokens.len())
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        let matching = self
            .child_outputs
            .get(&child)
            .into_iter()
            .flatten()
            .filter(|(candidate_parent, _)| *candidate_parent == parent)
            .collect::<Vec<_>>();
        Ok(matches!(matching.as_slice(), [(_, output)] if output_range(
            *output,
            output_token_count,
        ).is_ok()))
    }

    fn prepare_producer(
        expansion: &MacroDeclarativeExpansion,
    ) -> Result<PreparedProducer, ExpansionError> {
        let output_token_count = u32::try_from(expansion.output_tokens.len())
            .map_err(|_| ExpansionError::IncompleteOrigin)?;

        let mut definition_outputs = Vec::new();
        let mut observed_definitions = FxHashSet::default();
        for definition in &expansion.definitions {
            let raw_id = definition.definition.local_def_index.as_u32();
            let output = output_range(definition.output, output_token_count)?;
            if !observed_definitions.insert(raw_id) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            definition_outputs.push((definition.definition, output));
        }
        definition_outputs.sort_by_key(|(definition, output)| {
            (
                output.start,
                output.end,
                definition.local_def_index.as_u32(),
            )
        });

        let mut child_outputs = Vec::with_capacity(expansion.child_expansions.len());
        for child in &expansion.child_expansions {
            child_outputs.push((
                child.expansion,
                output_range(child.output, output_token_count)?,
            ));
        }
        child_outputs.sort_by_key(|(child, output)| {
            (
                output.start,
                output.end,
                child.expn_hash().local_hash().as_u64(),
            )
        });
        if child_outputs.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let discarded_outputs = discarded_output_ranges(expansion, output_token_count)?;
        if !valid_discarded_output_relations(
            &discarded_outputs,
            output_token_count,
            definition_outputs
                .iter()
                .map(|(_, output)| *output)
                .chain(child_outputs.iter().map(|(_, output)| *output)),
        ) {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let RustcMacroOwnerOutput {
            complete,
            intrinsic,
            dependent_outputs,
            required_outputs,
        } = &expansion.owner_output;
        let (dependent_outputs, required_outputs) = if *complete {
            let dependent_outputs = dependent_outputs
                .iter()
                .map(|&output| output_range(output, output_token_count))
                .collect::<Result<Vec<_>, _>>()?;
            let required_outputs = required_outputs
                .iter()
                .map(|&output| output_range(output, output_token_count))
                .collect::<Result<Vec<_>, _>>()?;
            if dependent_outputs
                .windows(2)
                .chain(required_outputs.windows(2))
                .any(|pair| pair[0] >= pair[1])
                || dependent_outputs
                    .iter()
                    .any(|output| required_outputs.binary_search(output).is_ok())
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            (dependent_outputs, required_outputs)
        } else {
            (Vec::new(), Vec::new())
        };
        let owner_output = PreparedMacroOwnerOutput {
            complete: *complete,
            intrinsic: *intrinsic,
            dependent_outputs,
            required_outputs,
        };

        Ok(PreparedProducer {
            output_token_count,
            definition_outputs,
            child_outputs,
            discarded_outputs,
            owner_output,
        })
    }

    fn prepare_definition_bases(
        &mut self,
        compiler_id: ExpnId,
        expansion: &MacroDeclarativeExpansion,
        token_contributors: &PreparedTokenContributors,
        contributor_dag: MacroContributorDagRef<'_>,
        definition_bases: &mut FxHashMap<u32, Vec<MacroProductSource>>,
    ) -> Result<(), ExpansionError> {
        let output_token_count = token_contributors.output_token_count()?;
        if output_token_count as usize != expansion.output_tokens.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let raw = self.raw_expansion(compiler_id)?;
        let excluded = [raw.selected_rule_unit(), raw.written_invocation()]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let mut observed_definitions = FxHashSet::default();
        let mut definitions = Vec::with_capacity(expansion.definitions.len());
        for definition in &expansion.definitions {
            let raw_id = definition.definition.local_def_index.as_u32();
            let output = output_range(definition.output, output_token_count)?;
            if !observed_definitions.insert(raw_id) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            definitions.push((raw_id, output));
        }
        if !laminar_output_ranges(definitions.iter().map(|(_, output)| *output)) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        if definitions.is_empty() {
            return Ok(());
        }
        let discarded_outputs = discarded_output_ranges(expansion, output_token_count)?;
        if !valid_discarded_output_relations(
            &discarded_outputs,
            output_token_count,
            definitions.iter().map(|(_, output)| *output),
        ) {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let exclusion_context = self.identity_frontier_memo.context(excluded.clone())?;
        let excluded_ancestors = SourceAncestorExclusions::new(&self.source_ancestry, excluded)?;
        let mut range_index = ProductBasisRangeIndex::new_excluding(
            &self.source_ancestry,
            &excluded_ancestors,
            exclusion_context,
            &mut self.identity_frontier_memo,
            contributor_dag,
            token_contributors.as_slice(),
            &discarded_outputs,
        )?;
        let mut by_range = BTreeMap::<MacroOutputRange, Vec<SourceUnitId>>::new();
        let mut raw_bases = Vec::with_capacity(definitions.len());
        for (raw_id, output) in definitions {
            let basis = if let Some(basis) = by_range.get(&output) {
                basis.clone()
            } else {
                let basis = range_index.intersection(output)?;
                by_range.insert(output, basis.clone());
                basis
            };
            raw_bases.push((raw_id, basis));
        }
        drop(range_index);
        for (raw_id, basis) in raw_bases {
            let mut basis = basis
                .into_iter()
                .map(|unit| self.identity_source(unit))
                .collect::<Result<Vec<_>, _>>()?;
            basis.sort();
            if basis.windows(2).any(|pair| pair[0] == pair[1]) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            if definition_bases.insert(raw_id, basis).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        Ok(())
    }

    fn identity_source(&mut self, id: SourceUnitId) -> Result<MacroProductSource, ExpansionError> {
        let source = self.source;
        let identity_ranges = &self.identity_ranges;
        let identity_kind = self
            .identity_source_kinds
            .get(id.0 as usize)
            .copied()
            .flatten();
        memoized_identity_source(&mut self.identity_source_cache, id, || {
            let unit = source
                .units
                .get(id.0 as usize)
                .filter(|unit| unit.id == id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            Ok(MacroProductSource {
                kind: identity_kind.map_or(
                    SourceUnitIdentityKind::Written(unit.kind),
                    SourceUnitIdentityKind::Declarative,
                ),
                range: identity_ranges.identity_range(unit.full_range)?,
            })
        })
    }

    fn prepare_pending_contributors(
        &mut self,
        compiler_id: ExpnId,
        expansion: &MacroDeclarativeExpansion,
    ) -> Result<PendingProducerContributors, ExpansionError> {
        self.validate_output_origins(compiler_id, expansion)?;
        let base = self.pending_base_contributors(compiler_id)?;
        if base.is_empty() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut tokens = Vec::with_capacity(expansion.output_tokens.len());
        for output in &expansion.output_tokens {
            let mut pending = PendingTokenContributors::default();
            if let Some(template) = self.template_contributor(compiler_id, output.component)? {
                pending.local.push(template);
            }
            for input in output.input_contributors.iter().copied().chain(
                output
                    .iterations
                    .iter()
                    .flat_map(|iteration| iteration.input_contributors.iter().copied()),
            ) {
                if let Some(input) = self.input_contributors(compiler_id, input)? {
                    pending.inputs.push(input);
                }
            }
            pending.local.sort();
            pending.local.dedup();
            pending.inputs.sort();
            pending.inputs.dedup();
            tokens.push(pending);
        }
        Ok(PendingProducerContributors { base, tokens })
    }

    fn validate_output_origins(
        &mut self,
        compiler_id: ExpnId,
        expansion: &MacroDeclarativeExpansion,
    ) -> Result<(), ExpansionError> {
        if self.valid_output_origins.contains(&compiler_id) {
            return Ok(());
        }
        if !valid_declarative_output_origins(expansion) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        self.valid_output_origins.insert(compiler_id);
        Ok(())
    }

    fn pending_base_contributors(
        &self,
        expansion_id: ExpnId,
    ) -> Result<PendingContributorSet, ExpansionError> {
        let raw = self.raw_expansion(expansion_id)?;
        let written_invocation = raw.written_invocation();
        let selected_rule = raw.selected_rule_unit();
        let mut contributors = PendingContributorSet::default();
        if let Some(invocation) = written_invocation {
            contributors.local.push(invocation);
        }
        if let Some(parent) = self.contributor_parent(raw)? {
            let parent_outputs = self
                .child_outputs
                .get(&expansion_id)
                .map(Vec::as_slice)
                .unwrap_or_default();
            let mut matching = parent_outputs
                .iter()
                .filter(|(candidate, _)| *candidate == parent);
            let Some((observed_parent, raw_output)) = matching.next() else {
                return Err(ExpansionError::IncompleteOrigin);
            };
            if matching.next().is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let output = output_range(
                *raw_output,
                u32::try_from(
                    self.expansion_observation(*observed_parent)?
                        .output_tokens
                        .len(),
                )
                .map_err(|_| ExpansionError::IncompleteOrigin)?,
            )?;
            contributors.parent_ranges.push((*observed_parent, output));
        } else if written_invocation.is_none() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        if let Some(rule) = selected_rule {
            contributors.local.push(rule);
        }
        Ok(contributors)
    }

    fn build_token_contributors(
        pending: &PendingProducerContributors,
        pending_inputs: &[PendingContributorSet],
        resolved_inputs: &mut ResolvedPendingInputs,
        prepared: &FxHashMap<ExpnId, PreparedTokenContributors>,
        builder: &mut MacroContributorDagBuilder,
    ) -> Result<PreparedTokenContributors, ExpansionError> {
        fn build_direct_set(
            pending: &PendingContributorSet,
            prepared: &FxHashMap<ExpnId, PreparedTokenContributors>,
            builder: &mut MacroContributorDagBuilder,
        ) -> Result<MacroContributorSetId, ExpansionError> {
            let mut parents = Vec::new();
            for &(parent, ordinal) in &pending.parent_tokens {
                parents.push(
                    prepared
                        .get(&parent)
                        .and_then(|tokens| tokens.get(ordinal))
                        .ok_or(ExpansionError::IncompleteOrigin)?,
                );
            }
            for &(parent, range) in &pending.parent_ranges {
                parents.extend(
                    prepared
                        .get(&parent)
                        .ok_or(ExpansionError::IncompleteOrigin)?
                        .roots_for_range(range)?,
                );
            }
            builder.intern(pending.local.clone(), parents)
        }

        let base = build_direct_set(&pending.base, prepared, builder)?;
        let mut by_ordinal = Vec::with_capacity(pending.tokens.len());
        for token in &pending.tokens {
            let mut parents = Vec::with_capacity(token.inputs.len() + 1);
            parents.push(base);
            for &input in &token.inputs {
                let root = if let Some(root) = resolved_inputs.get(input)? {
                    root
                } else {
                    let pending = pending_inputs
                        .get(input.0 as usize)
                        .ok_or(ExpansionError::IncompleteOrigin)?;
                    let root = build_direct_set(pending, prepared, builder)?;
                    let fact_count = pending
                        .local
                        .len()
                        .checked_add(pending.parent_tokens.len())
                        .and_then(|count| count.checked_add(pending.parent_ranges.len()))
                        .ok_or(ExpansionError::IncompleteOrigin)?;
                    resolved_inputs.insert(input, root, fact_count)?;
                    root
                };
                parents.push(root);
            }
            by_ordinal.push(builder.intern(token.local.clone(), parents)?);
        }
        PreparedTokenContributors::new(by_ordinal, builder)
    }

    fn template_contributor(
        &mut self,
        expansion_id: ExpnId,
        component_index: usize,
    ) -> Result<Option<SourceUnitId>, ExpansionError> {
        let key = (expansion_id, component_index);
        if let Some(contributor) = self.template_cache.get(&key) {
            return Ok(*contributor);
        }
        let contributor = {
            let raw = self.raw_expansion(expansion_id)?;
            let Some(rule) = raw.selected_rule_unit() else {
                self.template_cache.insert(key, None);
                return Ok(None);
            };
            let component = self
                .expansion_observation(expansion_id)?
                .components
                .get(component_index)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let range =
                match original_span_range(self.compiler, &self.source.offsets, component.span) {
                    Ok(range) => range,
                    Err(SourceError::InvalidSpan) => {
                        self.template_cache.insert(key, None);
                        return Ok(None);
                    }
                    Err(error) => return Err(expansion_source_error(error)),
                };
            self.template_indices
                .get(&rule)
                .map(|index| index.innermost_container(range))
                .transpose()?
                .flatten()
        };
        self.template_cache.insert(key, contributor);
        Ok(contributor)
    }

    fn input_contributors(
        &mut self,
        expansion_id: ExpnId,
        input: MacroInputTokenRange,
    ) -> Result<Option<PendingInputId>, ExpansionError> {
        let key = (
            expansion_id,
            input.input_stream,
            input.start,
            input.end,
            input.complete,
        );
        if let Some(&input) = self.input_cache.get(&key) {
            return Ok(input);
        }
        let mut contributors = self.compute_input_contributors(expansion_id, input)?;
        contributors.normalize();
        let input = if contributors.is_empty() {
            None
        } else {
            let hash = contributors.content_hash();
            let existing = self.input_canonical.get(&hash).and_then(|ids| {
                ids.iter().copied().find(|id| {
                    self.pending_inputs
                        .get(id.0 as usize)
                        .is_some_and(|candidate| candidate == &contributors)
                })
            });
            Some(if let Some(id) = existing {
                id
            } else {
                let id = PendingInputId(
                    self.pending_inputs
                        .len()
                        .try_into()
                        .map_err(|_| ExpansionError::IncompleteOrigin)?,
                );
                self.pending_inputs.push(contributors);
                self.input_canonical.entry(hash).or_default().push(id);
                id
            })
        };
        self.input_cache.insert(key, input);
        Ok(input)
    }

    fn compute_input_contributors(
        &mut self,
        expansion_id: ExpnId,
        input: MacroInputTokenRange,
    ) -> Result<PendingContributorSet, ExpansionError> {
        if !input.complete || input.start > input.end {
            return Err(ExpansionError::IncompleteOrigin);
        }
        enum InputOrigin {
            Parent {
                expansion: ExpnId,
                ordinals: Vec<u32>,
            },
            Written {
                start: Span,
                end: Span,
            },
        }
        let origin = {
            let matcher = self
                .expansion_observation(expansion_id)?
                .matcher
                .as_ref()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let stream = matcher
                .input_streams
                .get(input.input_stream as usize)
                .filter(|stream| stream.complete)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if input.end as usize > stream.tokens.len() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            if let Some(parent) = &stream.parent_output {
                if parent.tokens.len() != stream.tokens.len() {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                InputOrigin::Parent {
                    expansion: parent.expansion,
                    ordinals: parent.tokens[input.start as usize..input.end as usize].to_vec(),
                }
            } else {
                if stream.boundaries.len() != stream.tokens.len() + 1 {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                InputOrigin::Written {
                    start: stream.boundaries[input.start as usize],
                    end: stream.boundaries[input.end as usize],
                }
            }
        };
        if let InputOrigin::Parent {
            expansion,
            ordinals,
        } = origin
        {
            let raw = self.raw_expansion(expansion_id)?;
            match self.contributor_parent(raw)? {
                Some(parent) if parent == expansion => {}
                None if raw.written_invocation().is_some() => {
                    return Ok(PendingContributorSet::default());
                }
                _ => return Err(ExpansionError::IncompleteOrigin),
            }
            return Ok(PendingContributorSet {
                parent_tokens: ordinals
                    .into_iter()
                    .map(|ordinal| (expansion, ordinal))
                    .collect(),
                ..PendingContributorSet::default()
            });
        }

        let InputOrigin::Written {
            start: start_span,
            end: end_span,
        } = origin
        else {
            unreachable!()
        };
        let start = original_span_range(self.compiler, &self.source.offsets, start_span)
            .map_err(expansion_source_error)?;
        let end = original_span_range(self.compiler, &self.source.offsets, end_span)
            .map_err(expansion_source_error)?;
        if !start.is_empty() || !end.is_empty() || start.start > end.end {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let input_range = ByteRange {
            start: start.start,
            end: end.end,
        };
        let raw = self.raw_expansion(expansion_id)?;
        let (Some(invocation), Some(rule)) = (raw.written_invocation(), raw.selected_rule_unit())
        else {
            return Ok(PendingContributorSet::default());
        };
        self.repetition_indices
            .get(&(invocation, rule))
            .map(|index| index.containers(input_range, true))
            .transpose()
            .map(|contributors| PendingContributorSet {
                local: contributors.unwrap_or_default(),
                ..PendingContributorSet::default()
            })
    }

    fn raw_expansion(
        &self,
        compiler_id: ExpnId,
    ) -> Result<&PreparedExpansionOrigin, ExpansionError> {
        self.prepared
            .get(compiler_id)
            .filter(|expansion| expansion.parent_definition.is_some())
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    fn expansion_observation(
        &self,
        compiler_id: ExpnId,
    ) -> Result<&MacroDeclarativeExpansion, ExpansionError> {
        self.origins
            .get(&compiler_id)
            .and_then(|origin| origin.declarative_expansion.as_deref())
            .and_then(ValidatedDeclarativeOutput::new)
            .map(ValidatedDeclarativeOutput::observation)
            .ok_or(ExpansionError::IncompleteOrigin)
    }
}

#[cfg(rust_item_dependencies_patched)]
fn discarded_output_ranges(
    expansion: &MacroDeclarativeExpansion,
    output_token_count: u32,
) -> Result<Vec<MacroOutputRange>, ExpansionError> {
    let discarded = expansion
        .discarded_outputs
        .iter()
        .map(|&output| output_range(output, output_token_count))
        .collect::<Result<Vec<_>, _>>()?;
    normalize_discarded_output_ranges(discarded, output_token_count)
}

#[cfg(rust_item_dependencies_patched)]
fn valid_declarative_output_origins(expansion: &MacroDeclarativeExpansion) -> bool {
    if expansion
        .components
        .iter()
        .any(|component| component.kind == MacroTranscriberComponentKind::MetaVarExpr)
    {
        return false;
    }
    let parents = expansion
        .components
        .iter()
        .map(|component| component.parent)
        .collect::<Vec<_>>();
    let repetitions = expansion
        .components
        .iter()
        .map(|component| component.kind == MacroTranscriberComponentKind::Repetition)
        .collect::<Vec<_>>();
    let Some(repetition_index) = ComponentRepetitionIndex::new(&parents, &repetitions) else {
        return false;
    };
    expansion.output_tokens.iter().all(|output| {
        repetition_index.matches(
            output.component,
            output
                .iterations
                .iter()
                .map(|iteration| iteration.repetition_component),
        )
    })
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct ComponentRepetitionIndex {
    pub(super) nearest: Vec<Option<usize>>,
    pub(super) previous: Vec<Option<usize>>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl ComponentRepetitionIndex {
    pub(super) fn new(parents: &[Option<usize>], repetitions: &[bool]) -> Option<Self> {
        if parents.len() != repetitions.len() {
            return None;
        }
        const UNVISITED: u8 = 0;
        const VISITING: u8 = 1;
        const COMPLETE: u8 = 2;
        let mut states = vec![UNVISITED; parents.len()];
        let mut nearest = vec![None; parents.len()];
        let mut previous = vec![None; parents.len()];
        for start in 0..parents.len() {
            if states[start] == COMPLETE {
                continue;
            }
            let mut pending = Vec::new();
            let mut current = start;
            loop {
                match states.get(current).copied()? {
                    COMPLETE => break,
                    VISITING => return None,
                    UNVISITED => {
                        states[current] = VISITING;
                        pending.push(current);
                        let Some(parent) = parents[current] else {
                            break;
                        };
                        if parent >= parents.len() {
                            return None;
                        }
                        current = parent;
                    }
                    _ => return None,
                }
            }
            while let Some(component) = pending.pop() {
                let parent_repetition = parents[component].and_then(|parent| nearest[parent]);
                if repetitions[component] {
                    previous[component] = parent_repetition;
                    nearest[component] = Some(component);
                } else {
                    nearest[component] = parent_repetition;
                }
                states[component] = COMPLETE;
            }
        }
        Some(Self { nearest, previous })
    }

    pub(super) fn matches(
        &self,
        component: usize,
        mut observed: impl DoubleEndedIterator<Item = usize>,
    ) -> bool {
        let Some(mut expected) = self.nearest.get(component).copied() else {
            return false;
        };
        while let Some(observed) = observed.next_back() {
            if expected != Some(observed) {
                return false;
            }
            expected = self.previous[observed];
        }
        expected.is_none()
    }
}

#[cfg(rust_item_dependencies_patched)]
fn add_expansion_closure(
    origins: &rustc_data_structures::unord::UnordMap<ExpnId, MacroInvocationOrigin>,
    expansion: ExpnId,
    seen: &mut FxHashSet<ExpnId>,
    output: &mut Vec<ExpnId>,
) {
    let mut pending = vec![expansion];
    while let Some(expansion) = pending.pop() {
        if expansion == ExpnId::root() || !seen.insert(expansion) {
            continue;
        }
        output.push(expansion);
        let data = expansion.expn_data();
        let source_call_parent = data.call_site.ctxt().outer_expn();
        if source_call_parent != expansion {
            pending.push(source_call_parent);
        }
        pending.push(data.parent);
        if let Some(origin) = origins.get(&expansion) {
            pending.push(origin.discovered_in_expansion);
        }
    }
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_kind(kind: &ExpnKind) -> Result<ExpansionKind, ExpansionError> {
    Ok(match kind {
        ExpnKind::Root => return Err(ExpansionError::IncompleteOrigin),
        ExpnKind::Macro(style, name) => ExpansionKind::Macro {
            style: match style {
                MacroKind::Bang => MacroStyle::Bang,
                MacroKind::Attr => MacroStyle::Attribute,
                MacroKind::Derive => MacroStyle::Derive,
            },
            name: name.to_string(),
        },
        ExpnKind::AstPass(pass) => ExpansionKind::AstPass(match pass {
            AstPass::StdImports => AstPassKind::StandardImports,
            AstPass::TestHarness => AstPassKind::TestHarness,
            AstPass::ProcMacroHarness => AstPassKind::ProcMacroHarness,
        }),
        ExpnKind::Desugaring(kind) => ExpansionKind::Desugaring(match kind {
            RustcDesugaringKind::QuestionMark => DesugaringKind::QuestionMark,
            RustcDesugaringKind::TryBlock => DesugaringKind::TryBlock,
            RustcDesugaringKind::YeetExpr => DesugaringKind::YeetExpression,
            RustcDesugaringKind::OpaqueTy => DesugaringKind::OpaqueType,
            RustcDesugaringKind::Async => DesugaringKind::Async,
            RustcDesugaringKind::Await => DesugaringKind::Await,
            RustcDesugaringKind::ForLoop => DesugaringKind::ForLoop,
            RustcDesugaringKind::WhileLoop => DesugaringKind::WhileLoop,
            RustcDesugaringKind::BoundModifier => DesugaringKind::BoundModifier,
            RustcDesugaringKind::Contract => DesugaringKind::Contract,
            RustcDesugaringKind::PatTyRange => DesugaringKind::PatternTypeRange,
            RustcDesugaringKind::FormatLiteral { source: true } => {
                DesugaringKind::WrittenFormatLiteral
            }
            RustcDesugaringKind::FormatLiteral { source: false } => {
                DesugaringKind::ExpandedFormatLiteral
            }
            RustcDesugaringKind::RangeExpr => DesugaringKind::RangeExpression,
        }),
    })
}

#[cfg(rust_item_dependencies_patched)]
fn fragment_kind(kind: MacroInvocationFragmentKind) -> ExpansionFragmentKind {
    match kind {
        MacroInvocationFragmentKind::OptExpr => ExpansionFragmentKind::OptionalExpression,
        MacroInvocationFragmentKind::MethodReceiverExpr => {
            ExpansionFragmentKind::MethodReceiverExpression
        }
        MacroInvocationFragmentKind::Expr => ExpansionFragmentKind::Expression,
        MacroInvocationFragmentKind::Pat => ExpansionFragmentKind::Pattern,
        MacroInvocationFragmentKind::Ty => ExpansionFragmentKind::Type,
        MacroInvocationFragmentKind::Stmts => ExpansionFragmentKind::Statements,
        MacroInvocationFragmentKind::Items => ExpansionFragmentKind::Items,
        MacroInvocationFragmentKind::TraitItems => ExpansionFragmentKind::TraitItems,
        MacroInvocationFragmentKind::ImplItems => ExpansionFragmentKind::ImplItems,
        MacroInvocationFragmentKind::TraitImplItems => ExpansionFragmentKind::TraitImplItems,
        MacroInvocationFragmentKind::ForeignItems => ExpansionFragmentKind::ForeignItems,
        MacroInvocationFragmentKind::Arms => ExpansionFragmentKind::Arms,
        MacroInvocationFragmentKind::ExprFields => ExpansionFragmentKind::ExpressionFields,
        MacroInvocationFragmentKind::PatFields => ExpansionFragmentKind::PatternFields,
        MacroInvocationFragmentKind::GenericParams => ExpansionFragmentKind::GenericParameters,
        MacroInvocationFragmentKind::Params => ExpansionFragmentKind::Parameters,
        MacroInvocationFragmentKind::FieldDefs => ExpansionFragmentKind::FieldDefinitions,
        MacroInvocationFragmentKind::Variants => ExpansionFragmentKind::Variants,
        MacroInvocationFragmentKind::WherePredicates => ExpansionFragmentKind::WherePredicates,
        MacroInvocationFragmentKind::Crate => ExpansionFragmentKind::Crate,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn implementation_kind(kind: RustcImplementationKind) -> MacroImplementationKind {
    match kind {
        RustcImplementationKind::Builtin => MacroImplementationKind::Builtin,
        RustcImplementationKind::Declarative => MacroImplementationKind::Declarative,
        RustcImplementationKind::Procedural => MacroImplementationKind::Procedural,
        RustcImplementationKind::Legacy => MacroImplementationKind::Legacy,
        RustcImplementationKind::InertAttribute => MacroImplementationKind::InertAttribute,
        RustcImplementationKind::GlobDelegation => MacroImplementationKind::GlobDelegation,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn source_range(
    compiler: &Compiler,
    source: &SourceInventory,
    span: Span,
) -> Result<Option<ByteRange>, ExpansionError> {
    if span.is_dummy() {
        return Ok(None);
    }
    let source_map = compiler.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos {
        return Err(ExpansionError::InvalidSpan);
    }
    if start.sf.name.short().to_string() != "main.rs" {
        return Ok(None);
    }
    original_span_range(compiler, &source.offsets, span)
        .map(Some)
        .map_err(|_| ExpansionError::InvalidSpan)
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(super) struct SelectedMacroRuleSource {
    pub(super) range: ByteRange,
    pub(super) unit: SourceUnitId,
}

#[cfg(rust_item_dependencies_patched)]
fn selected_macro_rule_source(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    rule_index: &MacroRuleSelectionIndex,
    origin: &MacroInvocationOrigin,
) -> Result<Option<SelectedMacroRuleSource>, ExpansionError> {
    let Some(selection) = origin.selected_macro_rule else {
        return Ok(None);
    };
    let resolutions = tcx.resolutions(());
    let rules = resolutions
        .macro_rules_definitions
        .get(&selection.definition)
        .ok_or(ExpansionError::IncompleteOrigin)?;
    let rule = rules
        .get(selection.rule_index)
        .ok_or(ExpansionError::IncompleteOrigin)?;
    if resolutions
        .expn_that_defined
        .contains_key(&selection.definition)
    {
        return Ok(None);
    }
    let start =
        source_range(compiler, source, rule.start_span)?.ok_or(ExpansionError::IncompleteOrigin)?;
    let end =
        source_range(compiler, source, rule.end_span)?.ok_or(ExpansionError::IncompleteOrigin)?;
    let range = ByteRange {
        start: start.start,
        end: end.end,
    };
    if range.start >= range.end {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let Some(unit) = rule_index
        .selected_rule(range)
        .map_err(expansion_source_error)?
    else {
        return Ok(None);
    };
    Ok(Some(SelectedMacroRuleSource { range, unit }))
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_source_error(error: SourceError) -> ExpansionError {
    match error {
        SourceError::InvalidSpan => ExpansionError::InvalidSpan,
        SourceError::SourceTooLarge
        | SourceError::NormalizationMismatch
        | SourceError::InvalidInventory
        | SourceError::IncompleteAttributeObservation
        | SourceError::IncompleteDeriveObservation
        | SourceError::IncompleteMacroRuleObservation
        | SourceError::IncompleteDeclarativeMacroObservation
        | SourceError::IncompleteProceduralMacroObservation => ExpansionError::IncompleteOrigin,
    }
}
