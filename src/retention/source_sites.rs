use std::cmp::Reverse;
use std::collections::BTreeMap;

use crate::source::{ByteRange, CfgState, SourceInventory, SourceUnitId};

use super::RetentionError;

type OwnerRank = (u32, Reverse<u32>);

#[derive(Clone, Copy)]
struct OwnerRecord {
    id: SourceUnitId,
    range: ByteRange,
}

#[derive(Clone, Copy, Default)]
struct MinNode {
    left: usize,
    right: usize,
    best: Option<OwnerRank>,
}

/// Immutable containment index for compiler observation ranges.
///
/// Versions are ordered by source-unit start. Each version stores the best
/// owner rank by end position, so a containing unit is found without scanning
/// every written unit. Tied owners are reported from their rank bucket.
pub(crate) struct SourceSiteOwnerIndex {
    starts: Vec<u32>,
    roots: Vec<usize>,
    ends: Vec<u32>,
    nodes: Vec<MinNode>,
    owners_by_rank: BTreeMap<OwnerRank, Vec<OwnerRecord>>,
    #[cfg(test)]
    build_unit_visits: usize,
    #[cfg(test)]
    build_tree_node_visits: usize,
}

impl SourceSiteOwnerIndex {
    pub(crate) fn new(source: &SourceInventory) -> Result<Self, RetentionError> {
        let depths = source_unit_depths(source)?;
        let mut records = source
            .units
            .iter()
            .filter(|unit| unit.cfg_state == CfgState::Active)
            .map(|unit| {
                (
                    unit.full_range.start,
                    unit.full_range.end,
                    (unit.full_range.len(), Reverse(depths[unit.id.0 as usize])),
                    unit.id,
                )
            })
            .collect::<Vec<_>>();
        records.sort_unstable();

        let mut ends = records.iter().map(|record| record.1).collect::<Vec<_>>();
        ends.sort_unstable();
        ends.dedup();
        let mut index = Self {
            starts: Vec::new(),
            roots: Vec::new(),
            ends,
            nodes: vec![MinNode::default()],
            owners_by_rank: BTreeMap::new(),
            #[cfg(test)]
            build_unit_visits: 0,
            #[cfg(test)]
            build_tree_node_visits: 0,
        };
        let mut root = 0;
        let mut cursor = 0;
        while cursor < records.len() {
            let start = records[cursor].0;
            while cursor < records.len() && records[cursor].0 == start {
                let (_, end, rank, id) = records[cursor];
                let end_index = index
                    .ends
                    .binary_search(&end)
                    .expect("an indexed owner end was collected");
                root = index.insert(root, 0, index.ends.len(), end_index, rank);
                index
                    .owners_by_rank
                    .entry(rank)
                    .or_default()
                    .push(OwnerRecord {
                        id,
                        range: ByteRange { start, end },
                    });
                #[cfg(test)]
                {
                    index.build_unit_visits += 1;
                }
                cursor += 1;
            }
            index.starts.push(start);
            index.roots.push(root);
        }
        for owners in index.owners_by_rank.values_mut() {
            owners.sort_unstable_by_key(|owner| (owner.range.start, owner.id));
        }
        Ok(index)
    }

    pub(super) fn owners(&self, site: ByteRange) -> Result<Vec<SourceUnitId>, RetentionError> {
        self.owners_with_work(site).map(|(owners, _)| owners)
    }

    fn owners_with_work(
        &self,
        site: ByteRange,
    ) -> Result<(Vec<SourceUnitId>, SourceSiteQueryWork), RetentionError> {
        let version = self.starts.partition_point(|&start| start <= site.start);
        if version == 0 {
            return Err(RetentionError::InvalidGraph);
        }
        let first_end = self.ends.partition_point(|&end| end < site.end);
        if first_end == self.ends.len() {
            return Err(RetentionError::InvalidGraph);
        }
        let mut work = SourceSiteQueryWork::default();
        let rank = self
            .suffix_best(
                self.roots[version - 1],
                0,
                self.ends.len(),
                first_end,
                &mut work,
            )
            .ok_or(RetentionError::InvalidGraph)?;
        let candidates = self
            .owners_by_rank
            .get(&rank)
            .ok_or(RetentionError::InvalidGraph)?;
        let first_start = site.end.saturating_sub(rank.0);
        let begin = candidates.partition_point(|owner| owner.range.start < first_start);
        let end = candidates.partition_point(|owner| owner.range.start <= site.start);
        let mut owners = Vec::new();
        for owner in &candidates[begin..end] {
            #[cfg(test)]
            {
                work.owner_visits += 1;
            }
            if owner.range.contains(site) {
                owners.push(owner.id);
            }
        }
        if owners.is_empty() {
            return Err(RetentionError::InvalidGraph);
        }
        owners.sort_unstable();
        Ok((owners, work))
    }

    fn insert(
        &mut self,
        previous: usize,
        begin: usize,
        end: usize,
        position: usize,
        rank: OwnerRank,
    ) -> usize {
        #[cfg(test)]
        {
            self.build_tree_node_visits += 1;
        }
        let mut node = self.nodes[previous];
        if end - begin == 1 {
            node.best = Some(node.best.map_or(rank, |best| best.min(rank)));
        } else {
            let middle = begin + (end - begin) / 2;
            if position < middle {
                node.left = self.insert(node.left, begin, middle, position, rank);
            } else {
                node.right = self.insert(node.right, middle, end, position, rank);
            }
            node.best = min_rank(self.nodes[node.left].best, self.nodes[node.right].best);
        }
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    fn suffix_best(
        &self,
        node: usize,
        begin: usize,
        end: usize,
        first: usize,
        _work: &mut SourceSiteQueryWork,
    ) -> Option<OwnerRank> {
        if node == 0 || end <= first {
            return None;
        }
        #[cfg(test)]
        {
            _work.tree_node_visits += 1;
        }
        if first <= begin {
            return self.nodes[node].best;
        }
        let middle = begin + (end - begin) / 2;
        min_rank(
            self.suffix_best(self.nodes[node].left, begin, middle, first, _work),
            self.suffix_best(self.nodes[node].right, middle, end, first, _work),
        )
    }

    #[cfg(test)]
    pub(super) fn test_query(
        &self,
        site: ByteRange,
    ) -> Result<(Vec<SourceUnitId>, SourceSiteQueryWork), RetentionError> {
        self.owners_with_work(site)
    }

    #[cfg(test)]
    pub(super) fn test_build_unit_visits(&self) -> usize {
        self.build_unit_visits
    }

    #[cfg(test)]
    pub(super) fn test_build_tree_node_visits(&self) -> usize {
        self.build_tree_node_visits
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct SourceSiteQueryWork {
    #[cfg(test)]
    pub(super) tree_node_visits: usize,
    #[cfg(test)]
    pub(super) owner_visits: usize,
}

fn min_rank(left: Option<OwnerRank>, right: Option<OwnerRank>) -> Option<OwnerRank> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.min(right)),
        (Some(rank), None) | (None, Some(rank)) => Some(rank),
        (None, None) => None,
    }
}

fn source_unit_depths(source: &SourceInventory) -> Result<Vec<u32>, RetentionError> {
    let mut depths = vec![None::<u32>; source.units.len()];
    let mut states = vec![0_u8; source.units.len()];
    for (index, unit) in source.units.iter().enumerate() {
        if unit.id.0 as usize != index
            || unit.full_range.start > unit.full_range.end
            || unit.full_range.end as usize > source.original.len()
        {
            return Err(RetentionError::InvalidGraph);
        }
    }
    for start in 0..source.units.len() {
        if depths[start].is_some() {
            continue;
        }
        let mut path = Vec::new();
        let mut cursor = start;
        loop {
            if let Some(depth) = depths[cursor] {
                let mut next_depth = depth;
                while let Some(unit) = path.pop() {
                    next_depth = next_depth
                        .checked_add(1)
                        .ok_or(RetentionError::InvalidGraph)?;
                    depths[unit] = Some(next_depth);
                    states[unit] = 2;
                }
                break;
            }
            if states[cursor] == 1 {
                return Err(RetentionError::InvalidGraph);
            }
            states[cursor] = 1;
            path.push(cursor);
            let Some(parent) = source.units[cursor].parent else {
                let root = path.pop().expect("the current unit was added to its path");
                depths[root] = Some(0);
                states[root] = 2;
                let mut next_depth = 0_u32;
                while let Some(unit) = path.pop() {
                    next_depth = next_depth
                        .checked_add(1)
                        .ok_or(RetentionError::InvalidGraph)?;
                    depths[unit] = Some(next_depth);
                    states[unit] = 2;
                }
                break;
            };
            let parent = parent.0 as usize;
            if parent >= source.units.len() || parent == cursor {
                return Err(RetentionError::InvalidGraph);
            }
            cursor = parent;
        }
    }
    depths
        .into_iter()
        .map(|depth| depth.ok_or(RetentionError::InvalidGraph))
        .collect()
}
