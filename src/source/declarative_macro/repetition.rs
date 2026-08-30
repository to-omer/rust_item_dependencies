#[cfg(rust_item_dependencies_patched)]
use std::collections::{BTreeMap, BTreeSet};

#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::MacroMatcherObservation;

#[cfg(rust_item_dependencies_patched)]
use crate::source::{
    ByteRange, CfgState, PendingUnit, SourceError, SourceInventory, SourceUnitId, WrittenUnit,
    WrittenUnitKind, original_span_range,
};

#[cfg(rust_item_dependencies_patched)]
use super::capture::matcher_input_source_range;

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(super) struct PendingElementFacts {
    pub(super) unit: u32,
    pub(super) separator_after: Option<ByteRange>,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct PendingRepetitionFacts {
    pub(super) invocation: u32,
    pub(super) rule: u32,
    pub(super) matcher_range: ByteRange,
    pub(super) parent: u32,
    pub(super) repetition_path: Vec<u32>,
    pub(super) input_range: ByteRange,
    pub(super) elements: Vec<PendingElementFacts>,
    pub(super) minimum: u32,
    pub(super) maximum: Option<u32>,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct MatcherRepetitionDraft {
    pub(super) units: Vec<PendingUnit>,
    pub(super) facts: Vec<PendingRepetitionFacts>,
    pub(super) next_temporary: u32,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn matcher_repetitions(
    compiler: &Compiler,
    inventory: &SourceInventory,
    invocation: &WrittenUnit,
    rule: SourceUnitId,
    matcher: &MacroMatcherObservation,
    next_temporary: u32,
) -> Result<Option<MatcherRepetitionDraft>, SourceError> {
    let Some(paths) = matcher_repetition_paths(matcher) else {
        return Ok(None);
    };
    if matcher.input_streams.iter().any(|stream| {
        !stream.complete
            || stream.parent_output.is_some()
            || stream.boundaries.len() != stream.tokens.len() + 1
    }) {
        return Ok(None);
    }

    let mut local_pending = Vec::new();
    let mut local_next = next_temporary;
    let mut elements = BTreeMap::<(usize, &[usize], usize), u32>::new();
    let mut facts = Vec::new();
    let mut repetition_indices = (0..matcher.repetitions.len()).collect::<Vec<_>>();
    repetition_indices.sort_by_key(|&index| {
        (
            paths[&matcher.repetitions[index].matcher_index].len(),
            matcher.repetitions[index].matcher_index,
        )
    });

    for index in repetition_indices {
        let repetition = &matcher.repetitions[index];
        let Some(path) = paths.get(&repetition.matcher_index) else {
            return Ok(None);
        };
        let matcher_range = match original_span_range(compiler, &inventory.offsets, repetition.span)
        {
            Ok(range) if !range.is_empty() => range,
            Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
            Err(error) => return Err(error),
        };
        let rule_range = inventory.units[rule.0 as usize].full_range;
        if !rule_range.contains(matcher_range) {
            return Ok(None);
        }
        for instance in &repetition.instances {
            if instance.path.len() + 1 != path.len()
                || instance.input.input_stream != repetition.input_stream
                || !instance.input.complete
            {
                return Ok(None);
            }
            let parent = match repetition.parent_matcher_index {
                None if instance.path.is_empty() => invocation.id.0,
                None => return Ok(None),
                Some(parent_matcher) => {
                    let Some((&parent_iteration, parent_path)) = instance.path.split_last() else {
                        return Ok(None);
                    };
                    let Some(&parent) =
                        elements.get(&(parent_matcher, parent_path, parent_iteration))
                    else {
                        return Ok(None);
                    };
                    parent
                }
            };
            let Some(input_range) =
                matcher_input_source_range(compiler, inventory, matcher, instance.input)?
            else {
                return Ok(None);
            };
            let mut pending_elements = Vec::new();
            let mut previous_end = None;
            for (iteration_index, iteration) in instance.iterations.iter().enumerate() {
                if iteration.path.len() != instance.path.len() + 1
                    || !iteration.path.starts_with(&instance.path)
                    || iteration.path.last() != Some(&iteration_index)
                    || iteration.body.input_stream != repetition.input_stream
                    || !iteration.body.complete
                {
                    return Ok(None);
                }
                let Some(body) =
                    matcher_input_source_range(compiler, inventory, matcher, iteration.body)?
                else {
                    return Ok(None);
                };
                if body.is_empty()
                    || !input_range.contains(body)
                    || previous_end.is_some_and(|end| end > body.start)
                {
                    return Ok(None);
                }
                let separator_after = match iteration.separator_after {
                    Some(separator) => {
                        if separator.input_stream != repetition.input_stream || !separator.complete
                        {
                            return Ok(None);
                        }
                        let Some(separator) =
                            matcher_input_source_range(compiler, inventory, matcher, separator)?
                        else {
                            return Ok(None);
                        };
                        if separator.is_empty()
                            || separator.start < body.end
                            || !input_range.contains(separator)
                        {
                            return Ok(None);
                        }
                        Some(separator)
                    }
                    None => None,
                };
                previous_end = Some(separator_after.map_or(body.end, |separator| separator.end));
                let temporary_id = local_next;
                local_next = local_next
                    .checked_add(1)
                    .ok_or(SourceError::SourceTooLarge)?;
                local_pending.push(PendingUnit {
                    temporary_id,
                    kind: WrittenUnitKind::NestedItem,
                    full_range: body,
                    parent: Some(parent),
                    cfg_state: CfgState::Active,
                    // An exact invocation has an independently observed
                    // matcher ledger, so each repetition element is an
                    // independent deletion unit even when the invocation
                    // itself is nested in an atomic item. Procedural-macro
                    // opaque ranges are merged again after this refinement.
                    atomic_representative: temporary_id,
                    syntax_ordinal: temporary_id,
                });
                if elements
                    .insert(
                        (
                            repetition.matcher_index,
                            instance.path.as_slice(),
                            iteration_index,
                        ),
                        temporary_id,
                    )
                    .is_some()
                {
                    return Ok(None);
                }
                pending_elements.push(PendingElementFacts {
                    unit: temporary_id,
                    separator_after,
                });
            }
            if instance
                .iterations
                .last()
                .is_some_and(|iteration| iteration.separator_after.is_some())
            {
                return Ok(None);
            }
            facts.push(PendingRepetitionFacts {
                invocation: invocation.id.0,
                rule: rule.0,
                matcher_range,
                parent,
                repetition_path: path.clone(),
                input_range,
                elements: pending_elements,
                minimum: repetition.kleene.min,
                maximum: repetition.kleene.max,
            });
        }
    }
    Ok(Some(MatcherRepetitionDraft {
        units: local_pending,
        facts,
        next_temporary: local_next,
    }))
}

#[cfg(rust_item_dependencies_patched)]
fn matcher_repetition_paths(
    matcher: &MacroMatcherObservation,
) -> Option<BTreeMap<usize, Vec<u32>>> {
    let repetitions = matcher
        .repetitions
        .iter()
        .map(|repetition| (repetition.matcher_index, repetition))
        .collect::<BTreeMap<_, _>>();
    if repetitions.len() != matcher.repetitions.len() {
        return None;
    }
    let mut paths = BTreeMap::<usize, Vec<u32>>::new();
    for &matcher_index in repetitions.keys() {
        if paths.contains_key(&matcher_index) {
            continue;
        }
        let mut suffix = Vec::new();
        let mut active = BTreeSet::new();
        let mut current = Some(matcher_index);
        while let Some(index) = current {
            if let Some(prefix) = paths.get(&index).cloned() {
                let mut path = prefix;
                while let Some(index) = suffix.pop() {
                    path.push(u32::try_from(index).ok()?);
                    paths.insert(index, path.clone());
                }
                break;
            }
            if !active.insert(index) {
                return None;
            }
            let repetition = repetitions.get(&index)?;
            suffix.push(index);
            current = repetition.parent_matcher_index;
        }
        if !suffix.is_empty() {
            let mut path = Vec::new();
            while let Some(index) = suffix.pop() {
                path.push(u32::try_from(index).ok()?);
                paths.insert(index, path.clone());
            }
        }
    }
    Some(paths)
}
