#[cfg(any(rust_item_dependencies_patched, test))]
use std::collections::BTreeMap;
#[cfg(rust_item_dependencies_patched)]
use std::collections::BTreeSet;

use crate::source::ByteRange;
#[cfg(rust_item_dependencies_patched)]
use crate::source::syntax::ParserTokenRewriteGuard;
use crate::source::syntax::{ParserToken, tokenize_parser_tokens};

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{
    MacroDeclarativeExpansion, MacroInputTokenRange, MacroMatcherObservation,
    MacroTranscriberComponentKind,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::ExpnId;

#[cfg(rust_item_dependencies_patched)]
use crate::source::{
    CfgState, EditableMacroSourceResolver, SourceError, SourceInventory, WrittenUnitKind,
    original_span_range,
};

#[cfg(rust_item_dependencies_patched)]
use crate::macro_output::MacroOutputRange;

#[cfg(rust_item_dependencies_patched)]
pub(super) struct TemplateCaptureObservation {
    components: BTreeSet<ByteRange>,
    component_captures: BTreeMap<ByteRange, ByteRange>,
    slots: Vec<ObservedCaptureSlot>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct ObservedCaptureSlot {
    matcher_capture_range: ByteRange,
    matcher_deletion_range: ByteRange,
    input_capture_range: ByteRange,
    input_deletion_range: ByteRange,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) struct CaptureSlotDraft {
    pub(super) matcher_capture_range: ByteRange,
    pub(super) matcher_deletion_range: ByteRange,
    pub(super) trigger_units: Vec<u32>,
    pub(super) inputs: Vec<PendingCaptureInputFacts>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(super) struct PendingCaptureInputFacts {
    pub(super) invocation: u32,
    pub(super) capture_range: ByteRange,
    pub(super) deletion_range: ByteRange,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn matcher_input_source_range(
    compiler: &Compiler,
    inventory: &SourceInventory,
    matcher: &MacroMatcherObservation,
    range: MacroInputTokenRange,
) -> Result<Option<ByteRange>, SourceError> {
    if !range.complete || range.start > range.end {
        return Ok(None);
    }
    let Some(stream) = matcher.input_streams.get(range.input_stream as usize) else {
        return Ok(None);
    };
    if !stream.complete
        || stream.parent_output.is_some()
        || stream.boundaries.len() != stream.tokens.len() + 1
        || range.end as usize > stream.tokens.len()
    {
        return Ok(None);
    }
    let start = original_span_range(
        compiler,
        &inventory.offsets,
        stream.boundaries[range.start as usize],
    );
    let end = original_span_range(
        compiler,
        &inventory.offsets,
        stream.boundaries[range.end as usize],
    );
    match (start, end) {
        (Ok(start), Ok(end)) if start.is_empty() && end.is_empty() && start.start <= end.end => {
            Ok(Some(ByteRange {
                start: start.start,
                end: end.end,
            }))
        }
        (Err(SourceError::InvalidSpan), _) | (_, Err(SourceError::InvalidSpan)) => Ok(None),
        (Err(error), _) | (_, Err(error)) => Err(error),
        _ => Ok(None),
    }
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn capture_observation_for_expansion(
    compiler: &Compiler,
    inventory: &SourceInventory,
    parser_tokens: &[ParserToken],
    rewrite_guard: &ParserTokenRewriteGuard<'_>,
    rule_range: ByteRange,
    expansion: &MacroDeclarativeExpansion,
    classified_outputs: &[(MacroOutputRange, bool)],
) -> Result<Option<TemplateCaptureObservation>, SourceError> {
    let Some(matcher) = expansion
        .matcher
        .as_ref()
        .filter(|matcher| expansion.complete && matcher.invocation_refinement_safe)
    else {
        return Ok(None);
    };
    if expansion
        .components
        .iter()
        .any(|component| component.kind == MacroTranscriberComponentKind::MetaVarExpr)
    {
        return Ok(None);
    }

    let mut slots = Vec::new();
    let mut captures_by_input = BTreeMap::<(u32, u32, u32), ByteRange>::new();
    let mut fixed_separators = BTreeMap::<(u32, u32, u32), ByteRange>::new();
    let mut matcher_ranges = BTreeSet::new();
    let mut input_ranges = Vec::new();
    for capture in matcher
        .captures
        .iter()
        .filter(|capture| capture.path.is_empty())
    {
        if !capture.input.complete
            || capture.input_stream != capture.input.input_stream
            || capture.input.start >= capture.input.end
        {
            return Ok(None);
        }
        let matcher_capture_range =
            match original_span_range(compiler, &inventory.offsets, capture.metavar_span) {
                Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
                Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
                Err(error) => return Err(error),
            };
        let Some((matcher_deletion_range, matcher_separator)) =
            capture_deletion_layout(parser_tokens, matcher_capture_range)
        else {
            return Ok(None);
        };
        if !rule_range.contains(matcher_deletion_range)
            || !rewrite_guard.deletion_preserves_identity(matcher_deletion_range)
            || !matcher_ranges.insert(matcher_deletion_range)
        {
            return Ok(None);
        }

        let Some(input_capture_range) =
            matcher_input_source_range(compiler, inventory, matcher, capture.input)?
        else {
            return Ok(None);
        };
        if input_capture_range.is_empty() {
            return Ok(None);
        }
        let stream = &matcher.input_streams[capture.input_stream as usize];
        let input_deletion_range = if let Some(matcher_separator) = matcher_separator {
            let Some(separator_span) = stream.tokens.get(capture.input.end as usize) else {
                return Ok(None);
            };
            let Some(separator_end) = capture.input.end.checked_add(1) else {
                return Ok(None);
            };
            if fixed_separators
                .insert(
                    (capture.input_stream, capture.input.end, separator_end),
                    matcher_capture_range,
                )
                .is_some()
            {
                return Ok(None);
            }
            let input_separator =
                match original_span_range(compiler, &inventory.offsets, *separator_span) {
                    Ok(range) if !range.is_empty() => range,
                    Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
                    Err(error) => return Err(error),
                };
            if input_capture_range.end > input_separator.start
                || !same_single_parser_token(
                    &inventory.original,
                    matcher_separator,
                    input_separator,
                )
            {
                return Ok(None);
            }
            ByteRange {
                start: input_capture_range.start,
                end: input_separator.end,
            }
        } else {
            if capture.input.end as usize != stream.tokens.len() {
                return Ok(None);
            }
            input_capture_range
        };
        if !rewrite_guard.deletion_preserves_identity(input_deletion_range) {
            return Ok(None);
        }
        input_ranges.push((capture.input_stream, capture.input));
        if captures_by_input
            .insert(
                (capture.input_stream, capture.input.start, capture.input.end),
                matcher_capture_range,
            )
            .is_some()
        {
            return Ok(None);
        }
        slots.push(ObservedCaptureSlot {
            matcher_capture_range,
            matcher_deletion_range,
            input_capture_range,
            input_deletion_range,
        });
    }
    input_ranges.sort_by_key(|(stream, range)| (*stream, range.start, range.end));
    if input_ranges.windows(2).any(|pair| {
        pair[0].0 == pair[1].0 && pair[0].1.start < pair[1].1.end && pair[1].1.start < pair[0].1.end
    }) {
        return Ok(None);
    }
    slots.sort_by_key(|slot| slot.matcher_capture_range);

    let mut components = BTreeSet::new();
    let mut component_ranges = vec![None; expansion.components.len()];
    for (index, component) in expansion.components.iter().enumerate() {
        if component.kind != MacroTranscriberComponentKind::MetaVar {
            continue;
        }
        let range = match original_span_range(compiler, &inventory.offsets, component.span) {
            Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
            Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
            Err(error) => return Err(error),
        };
        if !components.insert(range) {
            return Ok(None);
        }
        component_ranges[index] = Some(range);
    }

    let mut classified_delta = vec![0_i64; expansion.output_tokens.len() + 1];
    for (range, _) in classified_outputs {
        classified_delta[range.start as usize] += 1;
        classified_delta[range.end as usize] -= 1;
    }
    let mut coverage = 0_i64;
    let classified_output = classified_delta
        .into_iter()
        .take(expansion.output_tokens.len())
        .map(|delta| {
            coverage += delta;
            coverage > 0
        })
        .collect::<Vec<_>>();
    let mut component_captures = BTreeMap::new();
    for (ordinal, output) in expansion.output_tokens.iter().enumerate() {
        let Some(component) = expansion.components.get(output.component) else {
            return Ok(None);
        };
        if component.kind != MacroTranscriberComponentKind::MetaVar {
            continue;
        }
        let Some(component_range) = component_ranges[output.component] else {
            return Ok(None);
        };
        if !classified_output[ordinal] {
            return Ok(None);
        }
        let mut matched = BTreeSet::new();
        let mut separator_owners = BTreeSet::new();
        for input in &output.input_contributors {
            if !input.complete {
                return Ok(None);
            }
            let key = (input.input_stream, input.start, input.end);
            if let Some(&capture) = captures_by_input.get(&key) {
                matched.insert(capture);
            } else if let Some(&capture) = fixed_separators.get(&key) {
                separator_owners.insert(capture);
            } else {
                return Ok(None);
            }
        }
        let mut matched = matched.into_iter();
        let Some(matcher_capture_range) = matched.next() else {
            return Ok(None);
        };
        if matched.next().is_some() {
            return Ok(None);
        }
        if separator_owners
            .iter()
            .any(|owner| *owner != matcher_capture_range)
        {
            return Ok(None);
        }
        if component_captures
            .insert(component_range, matcher_capture_range)
            .is_some_and(|previous| previous != matcher_capture_range)
        {
            return Ok(None);
        }
    }

    Ok(Some(TemplateCaptureObservation {
        components,
        component_captures,
        slots,
    }))
}

pub(super) fn capture_deletion_layout(
    tokens: &[ParserToken],
    capture: ByteRange,
) -> Option<(ByteRange, Option<ByteRange>)> {
    if capture.is_empty() {
        return None;
    }
    let first = tokens.partition_point(|token| token.range.end <= capture.start);
    let end = tokens.partition_point(|token| token.range.start < capture.end);
    let captured = tokens.get(first..end)?;
    if captured.first()?.range.start != capture.start
        || captured.last()?.range.end != capture.end
        || captured.iter().any(|token| !capture.contains(token.range))
    {
        return None;
    }
    let previous = tokens.get(first.checked_sub(1)?)?;
    if !matches!(previous.text.as_str(), "(" | "{" | "[" | "," | ";") {
        return None;
    }
    let next = tokens.get(end)?;
    if matches!(next.text.as_str(), "," | ";") {
        return Some((
            ByteRange {
                start: capture.start,
                end: next.range.end,
            },
            Some(next.range),
        ));
    }
    matches!(next.text.as_str(), ")" | "}" | "]").then_some((capture, None))
}

pub(super) fn same_single_parser_token(source: &str, left: ByteRange, right: ByteRange) -> bool {
    let Some(left) = source.get(left.start as usize..left.end as usize) else {
        return false;
    };
    let Some(right) = source.get(right.start as usize..right.end as usize) else {
        return false;
    };
    let Ok(left) = tokenize_parser_tokens(left) else {
        return false;
    };
    let Ok(right) = tokenize_parser_tokens(right) else {
        return false;
    };
    matches!((left.as_slice(), right.as_slice()), ([left], [right]) if left.same_identity(right))
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn capture_slot_drafts_for_rule(
    compiler: &Compiler,
    inventory: &SourceInventory,
    source_resolver: &EditableMacroSourceResolver<'_>,
    selected: &[ExpnId],
    eligible: &FxHashSet<ExpnId>,
    observations: &FxHashMap<ExpnId, TemplateCaptureObservation>,
    template_candidates: &[(ByteRange, u32)],
    expected_selections: usize,
) -> Result<Option<Vec<CaptureSlotDraft>>, SourceError> {
    if selected.len() != expected_selections || selected.is_empty() {
        return Ok(None);
    }

    let mut invocations = BTreeSet::new();
    let mut expected_components = None;
    let mut component_captures = BTreeMap::<ByteRange, ByteRange>::new();
    let mut slots = BTreeMap::<ByteRange, (ByteRange, Vec<PendingCaptureInputFacts>)>::new();
    let mut expected_slot_ranges = None;
    for &expansion in selected {
        if !eligible.contains(&expansion) {
            return Ok(None);
        }
        let Some(observation) = observations.get(&expansion) else {
            return Ok(None);
        };
        if expected_components
            .as_ref()
            .is_some_and(|expected| expected != &observation.components)
        {
            return Ok(None);
        }
        expected_components.get_or_insert_with(|| observation.components.clone());
        for (&component, &capture) in &observation.component_captures {
            if component_captures
                .insert(component, capture)
                .is_some_and(|previous| previous != capture)
            {
                return Ok(None);
            }
        }

        let Some(editable) = source_resolver.resolve(compiler, inventory, expansion)? else {
            return Ok(None);
        };
        let Some(invocation) = editable.exact_invocation else {
            return Ok(None);
        };
        if !invocations.insert(invocation)
            || inventory
                .units
                .get(invocation.0 as usize)
                .is_none_or(|unit| {
                    unit.id != invocation
                        || unit.kind != WrittenUnitKind::MacroInvocation
                        || unit.cfg_state != CfgState::Active
                })
        {
            return Ok(None);
        }

        let slot_ranges = observation
            .slots
            .iter()
            .map(|slot| slot.matcher_capture_range)
            .collect::<BTreeSet<_>>();
        if expected_slot_ranges
            .as_ref()
            .is_some_and(|expected| expected != &slot_ranges)
        {
            return Ok(None);
        }
        expected_slot_ranges.get_or_insert(slot_ranges);
        for slot in &observation.slots {
            match slots.entry(slot.matcher_capture_range) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert((
                        slot.matcher_deletion_range,
                        vec![PendingCaptureInputFacts {
                            invocation: invocation.0,
                            capture_range: slot.input_capture_range,
                            deletion_range: slot.input_deletion_range,
                        }],
                    ));
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    if entry.get().0 != slot.matcher_deletion_range {
                        return Ok(None);
                    }
                    entry.get_mut().1.push(PendingCaptureInputFacts {
                        invocation: invocation.0,
                        capture_range: slot.input_capture_range,
                        deletion_range: slot.input_deletion_range,
                    });
                }
            }
        }
    }

    let components = expected_components.unwrap_or_default();
    if component_captures.keys().copied().collect::<BTreeSet<_>>() != components {
        return Ok(None);
    }
    let Some(component_units) = template_component_units(&components, template_candidates) else {
        return Ok(None);
    };
    let Some(mut trigger_units_by_capture) = capture_trigger_units_with_work(
        slots.keys().copied(),
        &component_captures,
        &component_units,
        || {},
    ) else {
        return Ok(None);
    };

    let mut drafts = Vec::with_capacity(slots.len());
    for (matcher_capture_range, (matcher_deletion_range, mut inputs)) in slots {
        inputs.sort_by_key(|input| input.invocation);
        let Some(trigger_units) = trigger_units_by_capture.remove(&matcher_capture_range) else {
            return Ok(None);
        };
        drafts.push(CaptureSlotDraft {
            matcher_capture_range,
            matcher_deletion_range,
            trigger_units,
            inputs,
        });
    }
    Ok(Some(drafts))
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) fn capture_trigger_units_with_work(
    slot_ranges: impl IntoIterator<Item = ByteRange>,
    component_captures: &BTreeMap<ByteRange, ByteRange>,
    component_units: &BTreeMap<ByteRange, u32>,
    mut visit: impl FnMut(),
) -> Option<BTreeMap<ByteRange, Vec<u32>>> {
    let mut by_capture = slot_ranges
        .into_iter()
        .map(|capture| (capture, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for (&component, &capture) in component_captures {
        visit();
        let unit = *component_units.get(&component)?;
        by_capture.get_mut(&capture)?.push(unit);
    }
    for units in by_capture.values_mut() {
        units.sort_unstable();
        units.dedup();
    }
    Some(by_capture)
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn template_component_units(
    components: &BTreeSet<ByteRange>,
    candidates: &[(ByteRange, u32)],
) -> Option<BTreeMap<ByteRange, u32>> {
    let components = components.iter().copied().collect::<Vec<_>>();
    if components
        .windows(2)
        .any(|pair| pair[0].end > pair[1].start)
    {
        return None;
    }

    let mut result = BTreeMap::new();
    let mut stack = Vec::<(ByteRange, u32)>::new();
    let mut candidate = 0;
    for component in components {
        while candidates
            .get(candidate)
            .is_some_and(|(range, _)| range.start <= component.start)
        {
            let (next, unit) = candidates[candidate];
            while stack
                .last()
                .is_some_and(|(range, _)| range.end <= next.start)
            {
                stack.pop();
            }
            if stack
                .last()
                .is_some_and(|(parent, _)| !parent.contains(next))
            {
                return None;
            }
            stack.push((next, unit));
            candidate += 1;
        }
        while stack
            .last()
            .is_some_and(|(range, _)| range.end <= component.start)
        {
            stack.pop();
        }
        let &(_, unit) = stack
            .last()
            .filter(|(range, _)| range.contains(component))?;
        result.insert(component, unit);
    }
    Some(result)
}
