#[cfg(rust_item_dependencies_patched)]
use std::collections::{BTreeMap, BTreeSet};

#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{MacroDeclarativeExpansion, MacroTranscriberComponentKind, TyCtxt};

#[cfg(rust_item_dependencies_patched)]
use crate::macro_output::{MacroOutputRange, ValidatedDeclarativeOutputMeaning};
#[cfg(rust_item_dependencies_patched)]
use crate::source::syntax::{ParserToken, ParserTokenRewriteGuard};
#[cfg(any(rust_item_dependencies_patched, test))]
use crate::source::{ByteRange, SourceError};
#[cfg(rust_item_dependencies_patched)]
use crate::source::{SourceInventory, SourceUnitId, WrittenUnitKind, original_span_range};

#[cfg(rust_item_dependencies_patched)]
use super::capture::{TemplateCaptureObservation, capture_observation_for_expansion};

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct TemplateCandidate {
    pub(super) rule: SourceUnitId,
    pub(super) range: ByteRange,
    pub(super) is_use: bool,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct TemplateExpansionCandidates {
    pub(super) candidates: Vec<TemplateCandidate>,
    pub(super) blocked_repetition_contents: Vec<ByteRange>,
    pub(super) captures: Option<TemplateCaptureObservation>,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn template_candidates_for_expansion(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &SourceInventory,
    parser_tokens: &[ParserToken],
    rewrite_guard: &ParserTokenRewriteGuard<'_>,
    rule: SourceUnitId,
    validated: ValidatedDeclarativeOutputMeaning<'_>,
) -> Result<Option<TemplateExpansionCandidates>, SourceError> {
    let expansion = validated.observation();
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
    let direct_repetition_outputs = expansion.output_tokens.iter().try_fold(
        vec![false; expansion.components.len()],
        |mut direct, origin| {
            if origin.component >= expansion.components.len() {
                return None;
            }
            if repetitions[origin.component] {
                direct[origin.component] = true;
            }
            Some(direct)
        },
    );
    let Some(direct_repetition_outputs) = direct_repetition_outputs else {
        return Ok(None);
    };
    let Some(repetition_output_closure) =
        component_flag_closure(&parents, &direct_repetition_outputs)
    else {
        return Ok(None);
    };
    let mut products = Vec::new();
    for definition in validated.definitions() {
        products.push((
            definition.output(),
            matches!(
                tcx.def_kind(definition.definition()),
                rustc_hir::def::DefKind::Use
            ),
        ));
    }
    for child in validated.children() {
        products.push((child.output(), false));
    }
    let discarded_outputs = validated.ledger().discarded_outputs();
    let mut output_ranges = products.clone();
    output_ranges.extend(
        discarded_outputs
            .iter()
            .copied()
            .map(|range| (range, false)),
    );

    let rule_range = inventory
        .units
        .get(rule.0 as usize)
        .filter(|unit| unit.id == rule && unit.kind == WrittenUnitKind::MacroRule)
        .ok_or(SourceError::InvalidInventory)?
        .full_range;
    let token_ranges = template_token_source_ranges(
        compiler,
        inventory,
        rule_range,
        expansion,
        &repetition_output_closure.ancestors,
        output_ranges.iter().map(|(range, _)| *range),
    )?;
    let token_ranges = TemplateTokenRangeIndex::new(&token_ranges)?;
    let captures = capture_observation_for_expansion(
        compiler,
        inventory,
        parser_tokens,
        rewrite_guard,
        rule_range,
        expansion,
        &output_ranges,
    )?;
    let mut candidates = BTreeMap::<ByteRange, bool>::new();
    for (output, is_use) in output_ranges {
        let Some(range) = token_ranges.source_range(output.start, output.end) else {
            continue;
        };
        match candidates.entry(range) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(is_use);
            }
            std::collections::btree_map::Entry::Occupied(entry) if *entry.get() == is_use => {}
            std::collections::btree_map::Entry::Occupied(_) => return Ok(None),
        }
    }
    let mut blocked_repetition_contents = Vec::new();
    for (component, is_repetition) in repetitions.iter().copied().enumerate() {
        if !is_repetition {
            continue;
        }
        let range = match original_span_range(
            compiler,
            &inventory.offsets,
            expansion.components[component].span,
        ) {
            Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
            Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
            Err(error) => return Err(error),
        };
        if repetition_output_closure.descendants[component]
            || !rewrite_guard.deletion_preserves_identity(range)
        {
            blocked_repetition_contents.push(range);
            continue;
        }
        match candidates.entry(range) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(false);
            }
            std::collections::btree_map::Entry::Occupied(entry) if !*entry.get() => {}
            std::collections::btree_map::Entry::Occupied(_) => return Ok(None),
        }
    }
    Ok(Some(TemplateExpansionCandidates {
        candidates: candidates
            .into_iter()
            .map(|(range, is_use)| TemplateCandidate {
                rule,
                range,
                is_use,
            })
            .collect(),
        blocked_repetition_contents,
        captures,
    }))
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct ComponentFlagClosure {
    pub(super) ancestors: Vec<bool>,
    pub(super) descendants: Vec<bool>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) fn component_flag_closure(
    parents: &[Option<usize>],
    marked: &[bool],
) -> Option<ComponentFlagClosure> {
    if parents.len() != marked.len() {
        return None;
    }
    // 0 is unseen, 1 is on the current parent chain, and 2 is known to reach
    // a root. Resolve the forest once and reuse its parent-before-child order
    // for the reverse descendant closure.
    let mut states = vec![0_u8; parents.len()];
    let mut ancestors = vec![false; parents.len()];
    let mut resolved = Vec::with_capacity(parents.len());
    for start in 0..parents.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = Some(start);
        let inherited = loop {
            let Some(index) = current else {
                break false;
            };
            if index >= parents.len() {
                return None;
            }
            match states[index] {
                0 => {
                    states[index] = 1;
                    path.push(index);
                    current = parents[index];
                }
                1 => return None,
                2 => break ancestors[index],
                _ => unreachable!("component traversal state is internal"),
            }
        };
        let mut inherited = inherited;
        for index in path.into_iter().rev() {
            inherited |= marked[index];
            ancestors[index] = inherited;
            states[index] = 2;
            resolved.push(index);
        }
    }
    let mut descendants = marked.to_vec();
    for index in resolved.into_iter().rev() {
        if descendants[index]
            && let Some(parent) = parents[index]
        {
            descendants[parent] = true;
        }
    }
    Some(ComponentFlagClosure {
        ancestors,
        descendants,
    })
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn blocked_range_index(
    ranges: impl IntoIterator<Item = (SourceUnitId, ByteRange)>,
) -> Result<BTreeMap<SourceUnitId, Vec<ByteRange>>, SourceError> {
    let mut by_rule = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    for (rule, range) in ranges {
        if range.is_empty() {
            return Err(SourceError::IncompleteDeclarativeMacroObservation);
        }
        by_rule.entry(rule).or_default().push(range);
    }
    for ranges in by_rule.values_mut() {
        ranges.sort_by_key(|range| (range.start, std::cmp::Reverse(range.end)));
        let mut outermost = Vec::<ByteRange>::with_capacity(ranges.len());
        for range in ranges.drain(..) {
            if outermost.last().is_some_and(|outer| outer.contains(range)) {
                continue;
            }
            if outermost
                .last()
                .is_some_and(|previous| previous.end > range.start)
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
            outermost.push(range);
        }
        *ranges = outermost;
    }
    Ok(by_rule)
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn range_index_contains(
    index: &BTreeMap<SourceUnitId, Vec<ByteRange>>,
    rule: SourceUnitId,
    range: ByteRange,
) -> bool {
    let Some(ranges) = index.get(&rule) else {
        return false;
    };
    let end = ranges.partition_point(|candidate| candidate.start <= range.start);
    end > 0 && ranges[end - 1].contains(range)
}

#[cfg(test)]
pub(super) fn component_repetition_ancestors(
    parents: &[Option<usize>],
    repetitions: &[bool],
) -> Option<Vec<bool>> {
    component_flag_closure(parents, repetitions).map(|closure| closure.ancestors)
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct TemplateTokenRangeIndex {
    token_count: u32,
    leaf_count: usize,
    invalid_prefix: Vec<u32>,
    minimum_starts: Vec<u32>,
    maximum_ends: Vec<u32>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl TemplateTokenRangeIndex {
    pub(super) fn new(ranges: &[Option<ByteRange>]) -> Result<Self, SourceError> {
        let token_count = u32::try_from(ranges.len()).map_err(|_| SourceError::SourceTooLarge)?;
        let leaf_count = ranges
            .len()
            .max(1)
            .checked_next_power_of_two()
            .ok_or(SourceError::SourceTooLarge)?;
        let tree_len = leaf_count
            .checked_mul(2)
            .ok_or(SourceError::SourceTooLarge)?;
        let mut minimum_starts = vec![u32::MAX; tree_len];
        let mut maximum_ends = vec![0; tree_len];
        let mut invalid_prefix = Vec::with_capacity(ranges.len() + 1);
        invalid_prefix.push(0_u32);
        for (index, range) in ranges.iter().enumerate() {
            let valid = range.filter(|range| !range.is_empty());
            invalid_prefix.push(
                invalid_prefix[index]
                    .checked_add(valid.is_none() as u32)
                    .ok_or(SourceError::SourceTooLarge)?,
            );
            if let Some(range) = valid {
                minimum_starts[leaf_count + index] = range.start;
                maximum_ends[leaf_count + index] = range.end;
            }
        }
        for index in (1..leaf_count).rev() {
            minimum_starts[index] = minimum_starts[index * 2].min(minimum_starts[index * 2 + 1]);
            maximum_ends[index] = maximum_ends[index * 2].max(maximum_ends[index * 2 + 1]);
        }
        Ok(Self {
            token_count,
            leaf_count,
            invalid_prefix,
            minimum_starts,
            maximum_ends,
        })
    }

    pub(super) fn source_range(&self, start: u32, end: u32) -> Option<ByteRange> {
        if start >= end
            || end > self.token_count
            || self.invalid_prefix[end as usize] != self.invalid_prefix[start as usize]
        {
            return None;
        }
        let mut left = self.leaf_count + start as usize;
        let mut right = self.leaf_count + end as usize;
        let mut minimum_start = u32::MAX;
        let mut maximum_end = 0;
        while left < right {
            if left % 2 == 1 {
                minimum_start = minimum_start.min(self.minimum_starts[left]);
                maximum_end = maximum_end.max(self.maximum_ends[left]);
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                minimum_start = minimum_start.min(self.minimum_starts[right]);
                maximum_end = maximum_end.max(self.maximum_ends[right]);
            }
            left /= 2;
            right /= 2;
        }
        (minimum_start < maximum_end).then_some(ByteRange {
            start: minimum_start,
            end: maximum_end,
        })
    }
}

#[cfg(rust_item_dependencies_patched)]
fn template_token_source_ranges(
    compiler: &Compiler,
    inventory: &SourceInventory,
    rule_range: ByteRange,
    expansion: &MacroDeclarativeExpansion,
    blocked_components: &[bool],
    product_ranges: impl Iterator<Item = MacroOutputRange>,
) -> Result<Vec<Option<ByteRange>>, SourceError> {
    let mut coverage_delta = vec![0_i64; expansion.output_tokens.len() + 1];
    for range in product_ranges {
        coverage_delta[range.start as usize] += 1;
        coverage_delta[range.end as usize] -= 1;
    }
    let mut coverage = 0_i64;
    expansion
        .output_tokens
        .iter()
        .enumerate()
        .map(|(index, origin)| {
            coverage += coverage_delta[index];
            if coverage == 0 {
                return Ok(None);
            }
            if blocked_components
                .get(origin.component)
                .copied()
                .unwrap_or(true)
            {
                return Ok(None);
            }
            let component = &expansion.components[origin.component];
            match original_span_range(compiler, &inventory.offsets, component.span) {
                Ok(range) if !range.is_empty() && rule_range.contains(range) => Ok(Some(range)),
                Ok(_) | Err(SourceError::InvalidSpan) => Ok(None),
                Err(error) => Err(error),
            }
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
type ClassifiedTemplate = (TemplateCandidate, WrittenUnitKind, Option<ByteRange>);

#[cfg(rust_item_dependencies_patched)]
pub(super) fn classify_template_candidates(
    candidates: &BTreeSet<TemplateCandidate>,
) -> Result<Vec<ClassifiedTemplate>, SourceError> {
    let mut by_range = BTreeMap::<(SourceUnitId, ByteRange), bool>::new();
    for candidate in candidates {
        if by_range
            .insert((candidate.rule, candidate.range), candidate.is_use)
            .is_some()
        {
            return Err(SourceError::IncompleteDeclarativeMacroObservation);
        }
    }
    let mut candidates = by_range
        .into_iter()
        .map(|((rule, range), is_use)| TemplateCandidate {
            rule,
            range,
            is_use,
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| {
        (
            candidate.rule,
            candidate.range.start,
            std::cmp::Reverse(candidate.range.end),
        )
    });

    let mut parents = vec![None; candidates.len()];
    let mut stack = Vec::<usize>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        while let Some(&ancestor) = stack.last() {
            if candidates[ancestor].rule != candidate.rule
                || candidates[ancestor].range.end <= candidate.range.start
            {
                stack.pop();
            } else {
                break;
            }
        }
        if let Some(&parent) = stack.last() {
            if candidates[parent].rule != candidate.rule
                || !candidates[parent].range.contains(candidate.range)
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
            parents[index] = Some(parent);
        }
        stack.push(index);
    }

    let mut contains_use_descendant = vec![false; candidates.len()];
    for index in (0..candidates.len()).rev() {
        if let Some(parent) = parents[index] {
            contains_use_descendant[parent] |=
                candidates[index].is_use || contains_use_descendant[index];
        }
    }
    let mut outermost_use_ancestor = vec![None; candidates.len()];
    for index in 0..candidates.len() {
        let Some(parent) = parents[index] else {
            continue;
        };
        outermost_use_ancestor[index] =
            outermost_use_ancestor[parent].or_else(|| candidates[parent].is_use.then_some(parent));
    }

    let mut kinds = vec![None; candidates.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        let containing_use_item =
            outermost_use_ancestor[index].map(|ancestor| candidates[ancestor].range);
        let contains_use_child = contains_use_descendant[index];
        let contained_by_use_child = containing_use_item.is_some();
        let kind = if candidate.is_use && contains_use_child && !contained_by_use_child {
            WrittenUnitKind::UseItem
        } else if candidate.is_use && !contains_use_child && containing_use_item.is_some() {
            kinds[index] = Some(WrittenUnitKind::UseLeaf);
            continue;
        } else if candidate.is_use && (contains_use_child || contained_by_use_child) {
            // Intermediate use-tree prefixes are represented by the enclosing
            // UseItem and the terminal leaves, matching the ordinary AST path.
            continue;
        } else {
            WrittenUnitKind::NestedItem
        };
        kinds[index] = Some(kind);
    }

    let mut nearest_emitted_ancestor = vec![None; candidates.len()];
    for index in 0..candidates.len() {
        let Some(parent) = parents[index] else {
            continue;
        };
        nearest_emitted_ancestor[index] = if kinds[parent].is_some() {
            Some(parent)
        } else {
            nearest_emitted_ancestor[parent]
        };
    }

    let mut layout = candidates
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| {
            kinds[index].map(|kind| {
                (
                    *candidate,
                    kind,
                    nearest_emitted_ancestor[index].map(|parent| candidates[parent].range),
                )
            })
        })
        .collect::<Vec<_>>();
    layout.sort_by_key(|(candidate, kind, _)| {
        (
            candidate.rule,
            candidate.range.start,
            std::cmp::Reverse(candidate.range.end),
            kind.rank(),
        )
    });
    Ok(layout)
}
