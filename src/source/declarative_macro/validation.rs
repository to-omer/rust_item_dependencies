use std::collections::{BTreeMap, BTreeSet};

use rustc_lexer::{FrontmatterAllowed, tokenize};

use crate::source::syntax::{ParserTokenRewriteGuard, is_trivia, tokenize_parser_tokens};
use crate::source::{
    ByteRange, CfgState, MacroRuleSourceFacts, SourceError, SourceUnitId, WrittenUnit,
    WrittenUnitKind, validate_macro_rule_facts,
};

use super::capture::{capture_deletion_layout, same_single_parser_token};
use super::{MacroCaptureSlotSourceFacts, MacroRepetitionSourceFacts, MacroTemplateSourceFacts};

pub(crate) fn validate_declarative_macro_source_facts(
    original: &str,
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    repetitions: &[MacroRepetitionSourceFacts],
) -> Result<(), SourceError> {
    let census = declarative_unit_census(units)?;
    validate_macro_rule_facts(units, macro_rules)?;
    validate_refined_rule_links(units, macro_rules, templates, capture_slots, repetitions)?;
    validate_templates(units, templates, capture_slots, &census.template_units)?;
    validate_capture_slots(original, units, macro_rules, templates, capture_slots)?;
    validate_repetitions(original, units, repetitions, &census.matcher_units)
}

pub(in crate::source) fn declarative_unit_kinds(
    units: &[WrittenUnit],
) -> Result<Vec<Option<super::super::DeclarativeSourceUnitKind>>, SourceError> {
    Ok(declarative_unit_census(units)?.kinds)
}

pub(super) struct DeclarativeUnitCensus {
    kinds: Vec<Option<super::super::DeclarativeSourceUnitKind>>,
    template_units: BTreeSet<SourceUnitId>,
    matcher_units: BTreeSet<SourceUnitId>,
}

#[derive(Clone, Copy)]
pub(super) enum DeclarativeBoundary {
    Rule,
    Invocation,
}

pub(super) fn declarative_unit_census(
    units: &[WrittenUnit],
) -> Result<DeclarativeUnitCensus, SourceError> {
    // Resolve the nearest syntax boundary once per unit. The parser does not
    // create children inside macro token trees; those children appear only
    // when the patched observer refines a rule template or matcher input.
    let mut states = vec![0_u8; units.len()];
    let mut boundaries = vec![None; units.len()];
    for start in 0..units.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        let boundary = loop {
            match states.get(current).copied() {
                Some(2) => break boundaries[current],
                Some(1) | None => return Err(SourceError::InvalidInventory),
                Some(0) => {}
                _ => unreachable!("source ancestor traversal state is internal"),
            }
            states[current] = 1;
            path.push(current);
            let unit = &units[current];
            if unit.id.0 as usize != current {
                return Err(SourceError::InvalidInventory);
            }
            match unit.kind {
                WrittenUnitKind::MacroRule => break Some(DeclarativeBoundary::Rule),
                WrittenUnitKind::MacroInvocation => {
                    break Some(DeclarativeBoundary::Invocation);
                }
                _ => {}
            }
            let Some(parent) = unit.parent else {
                break None;
            };
            let parent_index = parent.0 as usize;
            if units.get(parent_index).is_none_or(|unit| unit.id != parent) {
                return Err(SourceError::InvalidInventory);
            }
            current = parent_index;
        };
        for index in path.into_iter().rev() {
            states[index] = 2;
            boundaries[index] = boundary;
        }
    }

    let mut kinds = vec![None; units.len()];
    let mut template_units = BTreeSet::new();
    let mut matcher_units = BTreeSet::new();
    for unit in units {
        if unit.cfg_state != CfgState::Active {
            continue;
        }
        let boundary = unit
            .parent
            .and_then(|parent| boundaries.get(parent.0 as usize).copied().flatten());
        match (boundary, unit.kind) {
            (
                Some(DeclarativeBoundary::Rule),
                WrittenUnitKind::NestedItem | WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf,
            ) => {
                template_units.insert(unit.id);
                if unit.kind == WrittenUnitKind::NestedItem {
                    kinds[unit.id.0 as usize] =
                        Some(super::super::DeclarativeSourceUnitKind::TemplateComponent);
                }
            }
            (Some(DeclarativeBoundary::Invocation), WrittenUnitKind::NestedItem) => {
                matcher_units.insert(unit.id);
                kinds[unit.id.0 as usize] =
                    Some(super::super::DeclarativeSourceUnitKind::MatcherElement);
            }
            _ => {}
        }
    }
    Ok(DeclarativeUnitCensus {
        kinds,
        template_units,
        matcher_units,
    })
}

pub(super) fn validate_refined_rule_links(
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    repetitions: &[MacroRepetitionSourceFacts],
) -> Result<(), SourceError> {
    let mut refined_rules = BTreeMap::new();
    for facts in macro_rules {
        let MacroRuleSourceFacts::Refined {
            rules,
            observed_selections,
            ..
        } = facts
        else {
            continue;
        };
        if rules.windows(2).any(|pair| {
            units[pair[0].0 as usize].full_range.start >= units[pair[1].0 as usize].full_range.start
        }) {
            return Err(SourceError::InvalidInventory);
        }
        let observed = observed_selections.iter().copied().collect::<BTreeSet<_>>();
        for (index, &rule) in rules.iter().enumerate() {
            if refined_rules
                .insert(rule, (index == 0, observed.contains(&rule)))
                .is_some()
            {
                return Err(SourceError::InvalidInventory);
            }
        }
    }

    if templates.iter().any(|template| {
        refined_rules
            .get(&template.rule)
            .is_none_or(|(_, observed)| !observed)
    }) || capture_slots.iter().any(|slot| {
        refined_rules
            .get(&slot.rule)
            .is_none_or(|(first, observed)| !first || !observed)
    }) || repetitions.iter().any(|repetition| {
        refined_rules
            .get(&repetition.rule)
            .is_none_or(|(first, observed)| !first || !observed)
    }) {
        return Err(SourceError::InvalidInventory);
    }
    Ok(())
}

pub(super) fn validate_templates(
    units: &[WrittenUnit],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    expected: &BTreeSet<SourceUnitId>,
) -> Result<(), SourceError> {
    if templates.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceError::InvalidInventory);
    }

    let macro_rule_ancestors = nearest_macro_rule_ancestors(units)?;
    let mut actual = BTreeSet::new();
    for facts in templates {
        let unit = active_unit(units, facts.unit)?;
        let rule = active_unit(units, facts.rule)?;
        if !matches!(
            unit.kind,
            WrittenUnitKind::NestedItem | WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf
        ) || rule.kind != WrittenUnitKind::MacroRule
            || unit.full_range.is_empty()
            || macro_rule_ancestors[unit.id.0 as usize] != Some(rule.id)
            || !actual.insert(unit.id)
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    let capture_units = capture_slots
        .iter()
        .map(|slot| slot.unit)
        .collect::<BTreeSet<_>>();
    if capture_units.len() != capture_slots.len() || !actual.is_disjoint(&capture_units) {
        return Err(SourceError::InvalidInventory);
    }
    actual.extend(capture_units);
    (actual == *expected)
        .then_some(())
        .ok_or(SourceError::InvalidInventory)
}

pub(super) fn nearest_macro_rule_ancestors(
    units: &[WrittenUnit],
) -> Result<Vec<Option<SourceUnitId>>, SourceError> {
    // 0 is unresolved, 1 is on the current parent chain, and 2 is resolved.
    let mut states = vec![0_u8; units.len()];
    let mut ancestors = vec![None; units.len()];
    for start in 0..units.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        let ancestor = loop {
            match states.get(current).copied() {
                Some(2) => break ancestors[current],
                Some(1) | None => return Err(SourceError::InvalidInventory),
                Some(0) => {}
                _ => unreachable!("source ancestor traversal state is internal"),
            }
            states[current] = 1;
            path.push(current);
            let unit = &units[current];
            if unit.id.0 as usize != current {
                return Err(SourceError::InvalidInventory);
            }
            if unit.kind == WrittenUnitKind::MacroRule {
                break Some(unit.id);
            }
            let Some(parent) = unit.parent else {
                break None;
            };
            let parent_index = parent.0 as usize;
            if units.get(parent_index).is_none_or(|unit| unit.id != parent) {
                return Err(SourceError::InvalidInventory);
            }
            current = parent_index;
        };
        for index in path.into_iter().rev() {
            states[index] = 2;
            ancestors[index] = ancestor;
        }
    }
    Ok(ancestors)
}

pub(super) fn validate_capture_slots(
    original: &str,
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    slots: &[MacroCaptureSlotSourceFacts],
) -> Result<(), SourceError> {
    if slots.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceError::InvalidInventory);
    }
    if slots.is_empty() {
        return Ok(());
    }
    let parser_tokens =
        tokenize_parser_tokens(original).map_err(|_| SourceError::InvalidInventory)?;
    let rewrite_guard =
        ParserTokenRewriteGuard::new(original).map_err(|_| SourceError::InvalidInventory)?;
    let template_rules = templates
        .iter()
        .map(|template| (template.unit, template.rule))
        .collect::<BTreeMap<_, _>>();
    let slot_units = slots.iter().map(|slot| slot.unit).collect::<BTreeSet<_>>();
    if slot_units.len() != slots.len() {
        return Err(SourceError::InvalidInventory);
    }

    let mut rule_selection_counts = BTreeMap::new();
    for facts in macro_rules {
        let MacroRuleSourceFacts::Refined {
            rules,
            observed_selections,
            ..
        } = facts
        else {
            continue;
        };
        let Some(&first) = rules.first() else {
            return Err(SourceError::InvalidInventory);
        };
        if !observed_selections.is_empty()
            && observed_selections
                .iter()
                .all(|selection| *selection == first)
        {
            rule_selection_counts.insert(first, observed_selections.len());
        }
    }

    let mut matcher_deletions = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    let mut input_deletions = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    let mut invocations_by_rule = BTreeMap::<SourceUnitId, BTreeSet<SourceUnitId>>::new();
    let mut capture_order =
        BTreeMap::<(SourceUnitId, SourceUnitId), Vec<(ByteRange, ByteRange)>>::new();
    for slot in slots {
        let unit = active_unit(units, slot.unit)?;
        let rule = active_unit(units, slot.rule)?;
        let Some(&selection_count) = rule_selection_counts.get(&rule.id) else {
            return Err(SourceError::InvalidInventory);
        };
        if unit.kind != WrittenUnitKind::NestedItem
            || rule.kind != WrittenUnitKind::MacroRule
            || unit.parent != Some(rule.id)
            || slot.matcher_capture_range.is_empty()
            || !unit.full_range.contains(slot.matcher_capture_range)
            || !capture_slot_unit_shape(original, unit.full_range)
            || slot.trigger_units.windows(2).any(|pair| pair[0] >= pair[1])
            || slot.inputs.windows(2).any(|pair| pair[0] >= pair[1])
            || slot.inputs.len() != selection_count
        {
            return Err(SourceError::InvalidInventory);
        }
        let Some((matcher_deletion, matcher_separator)) =
            capture_deletion_layout(&parser_tokens, slot.matcher_capture_range)
        else {
            return Err(SourceError::InvalidInventory);
        };
        if matcher_deletion != unit.full_range
            || !rewrite_guard.deletion_preserves_identity(matcher_deletion)
        {
            return Err(SourceError::InvalidInventory);
        }
        matcher_deletions
            .entry(rule.id)
            .or_default()
            .push(matcher_deletion);

        for &trigger in &slot.trigger_units {
            let trigger = active_unit(units, trigger)?;
            if slot_units.contains(&trigger.id) || template_rules.get(&trigger.id) != Some(&rule.id)
            {
                return Err(SourceError::InvalidInventory);
            }
        }

        let mut slot_invocations = BTreeSet::new();
        for input in &slot.inputs {
            let invocation = active_unit(units, input.invocation)?;
            if invocation.kind != WrittenUnitKind::MacroInvocation
                || input.capture_range.is_empty()
                || input.deletion_range.start != input.capture_range.start
                || !input.deletion_range.contains(input.capture_range)
                || !invocation.full_range.contains(input.deletion_range)
                || !rewrite_guard.deletion_preserves_identity(input.deletion_range)
                || !slot_invocations.insert(invocation.id)
            {
                return Err(SourceError::InvalidInventory);
            }
            match matcher_separator {
                Some(separator) => {
                    if input.deletion_range == input.capture_range
                        || !same_single_parser_token(
                            original,
                            separator,
                            ByteRange {
                                start: input.capture_range.end,
                                end: input.deletion_range.end,
                            },
                        )
                    {
                        return Err(SourceError::InvalidInventory);
                    }
                }
                None if input.deletion_range != input.capture_range => {
                    return Err(SourceError::InvalidInventory);
                }
                None => {}
            }
            input_deletions
                .entry(invocation.id)
                .or_default()
                .push(input.deletion_range);
            capture_order
                .entry((rule.id, invocation.id))
                .or_default()
                .push((slot.matcher_capture_range, input.capture_range));
        }
        if invocations_by_rule
            .insert(rule.id, slot_invocations.clone())
            .is_some_and(|previous| previous != slot_invocations)
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    for captures in capture_order.values_mut() {
        captures.sort_by_key(|(matcher, _)| *matcher);
        if captures.windows(2).any(|pair| pair[0].1 >= pair[1].1) {
            return Err(SourceError::InvalidInventory);
        }
    }

    for ranges in matcher_deletions
        .values_mut()
        .chain(input_deletions.values_mut())
    {
        ranges.sort();
        if ranges
            .windows(2)
            .any(|pair| ranges_overlap(pair[0], pair[1]))
        {
            return Err(SourceError::InvalidInventory);
        }
    }
    Ok(())
}

pub(super) fn capture_slot_unit_shape(source: &str, range: ByteRange) -> bool {
    let Some(source) = source.get(range.start as usize..range.end as usize) else {
        return false;
    };
    let Ok(tokens) = tokenize_parser_tokens(source) else {
        return false;
    };
    let body = match tokens.as_slice() {
        [body @ .., separator] if matches!(separator.text.as_str(), "," | ";") => body,
        body => body,
    };
    matches!(body, [dollar, _, colon, _] if dollar.text == "$" && colon.text == ":")
}

pub(super) fn validate_repetitions(
    original: &str,
    units: &[WrittenUnit],
    repetitions: &[MacroRepetitionSourceFacts],
    expected_matcher_elements: &BTreeSet<SourceUnitId>,
) -> Result<(), SourceError> {
    if repetitions
        .windows(2)
        .any(|pair| repetition_key(&pair[0]) >= repetition_key(&pair[1]))
    {
        return Err(SourceError::InvalidInventory);
    }

    let expected_elements = repetitions
        .iter()
        .flat_map(|repetition| repetition.elements.iter().map(|element| element.unit))
        .collect::<BTreeSet<_>>();
    let mut actual_elements = BTreeSet::new();
    let mut element_owners = BTreeMap::new();
    let mut invocation_rules = BTreeMap::new();
    let mut matcher_identities = BTreeMap::<(SourceUnitId, &[u32]), ByteRange>::new();
    let mut sequence_inputs = Vec::new();

    for repetition in repetitions {
        let invocation = active_unit(units, repetition.invocation)?;
        let rule = active_unit(units, repetition.rule)?;
        let parent = active_unit(units, repetition.parent)?;
        if invocation.kind != WrittenUnitKind::MacroInvocation
            || rule.kind != WrittenUnitKind::MacroRule
            || !(parent.kind == WrittenUnitKind::MacroInvocation
                || expected_elements.contains(&parent.id))
            || repetition.repetition_path.is_empty()
            || repetition.minimum > 1
            || !matches!(
                (repetition.minimum, repetition.maximum),
                (0 | 1, None) | (0, Some(1))
            )
            || !valid_range(original, repetition.matcher_range)
            || repetition.matcher_range.is_empty()
            || !rule.full_range.contains(repetition.matcher_range)
            || !valid_range(original, repetition.input_range)
            || !parent.full_range.contains(repetition.input_range)
            || repetition
                .maximum
                .is_some_and(|maximum| repetition.elements.len() as u32 > maximum)
            || (repetition.elements.len() as u32) < repetition.minimum
        {
            return Err(SourceError::InvalidInventory);
        }
        if invocation_rules
            .insert(invocation.id, rule.id)
            .is_some_and(|previous| previous != rule.id)
        {
            return Err(SourceError::InvalidInventory);
        }
        let matcher_key = (rule.id, repetition.repetition_path.as_slice());
        if matcher_identities
            .insert(matcher_key, repetition.matcher_range)
            .is_some_and(|previous| previous != repetition.matcher_range)
        {
            return Err(SourceError::InvalidInventory);
        }
        sequence_inputs.push((
            invocation.id,
            parent.id,
            repetition.repetition_path.as_slice(),
            repetition.input_range,
        ));

        if repetition.parent == repetition.invocation {
            if parent.id != invocation.id {
                return Err(SourceError::InvalidInventory);
            }
        } else if !expected_elements.contains(&parent.id) {
            return Err(SourceError::InvalidInventory);
        }

        let elements = repetition
            .elements
            .iter()
            .map(|facts| active_unit(units, facts.unit))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some((first, last)) = elements.first().zip(elements.last()) {
            if repetition.input_range.start != first.full_range.start
                || repetition.input_range.end != last.full_range.end
            {
                return Err(SourceError::InvalidInventory);
            }
        } else if !repetition.input_range.is_empty() {
            return Err(SourceError::InvalidInventory);
        }

        let mut previous = None;
        let separated = repetition
            .elements
            .first()
            .and_then(|element| element.separator_after)
            .is_some();
        let mut separator_identity = None;
        for (index, (element_facts, element)) in
            repetition.elements.iter().zip(&elements).enumerate()
        {
            if element.kind != WrittenUnitKind::NestedItem
                || element.parent != Some(parent.id)
                || !actual_elements.insert(element.id)
                || !repetition.input_range.contains(element.full_range)
                || element.full_range.is_empty()
                || previous
                    .is_some_and(|previous: ByteRange| previous.end > element.full_range.start)
            {
                return Err(SourceError::InvalidInventory);
            }
            previous = Some(element.full_range);
            element_owners.insert(
                element.id,
                (
                    repetition.invocation,
                    repetition.rule,
                    repetition.repetition_path.as_slice(),
                ),
            );

            let separator = element_facts.separator_after;
            let has_following = index + 1 < repetition.elements.len();
            if separator.is_some() != (has_following && separated) {
                return Err(SourceError::InvalidInventory);
            }
            if let Some(separator) = separator {
                let next = elements
                    .get(index + 1)
                    .ok_or(SourceError::InvalidInventory)?;
                if !valid_range(original, separator)
                    || separator.is_empty()
                    || separator.start < element.full_range.end
                    || separator.end > next.full_range.start
                    || !repetition.input_range.contains(separator)
                    || !range_is_trivia(
                        original,
                        ByteRange {
                            start: element.full_range.end,
                            end: separator.start,
                        },
                    )
                    || !range_is_trivia(
                        original,
                        ByteRange {
                            start: separator.end,
                            end: next.full_range.start,
                        },
                    )
                {
                    return Err(SourceError::InvalidInventory);
                }
                let identity =
                    separator_token(original, separator).ok_or(SourceError::InvalidInventory)?;
                if separator_identity
                    .replace(identity.clone())
                    .is_some_and(|previous| previous != identity)
                {
                    return Err(SourceError::InvalidInventory);
                }
            } else if let Some(next) = elements.get(index + 1)
                && !range_is_trivia(
                    original,
                    ByteRange {
                        start: element.full_range.end,
                        end: next.full_range.start,
                    },
                )
            {
                return Err(SourceError::InvalidInventory);
            }
        }
    }

    if actual_elements != expected_elements || actual_elements != *expected_matcher_elements {
        return Err(SourceError::InvalidInventory);
    }

    for repetition in repetitions {
        if repetition.parent == repetition.invocation {
            continue;
        }
        let Some((parent_invocation, parent_rule, parent_path)) =
            element_owners.get(&repetition.parent)
        else {
            return Err(SourceError::InvalidInventory);
        };
        if *parent_invocation != repetition.invocation
            || *parent_rule != repetition.rule
            || parent_path.len() + 1 != repetition.repetition_path.len()
            || repetition.repetition_path[..parent_path.len()] != parent_path[..]
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    sequence_inputs.sort_by_key(|(invocation, parent, _, range)| {
        (*invocation, *parent, range.start, range.end)
    });
    if sequence_inputs.windows(2).any(|pair| {
        pair[0].0 == pair[1].0 && pair[0].1 == pair[1].1 && ranges_overlap(pair[0].3, pair[1].3)
    }) {
        return Err(SourceError::InvalidInventory);
    }

    let mut matcher_siblings = BTreeMap::<(SourceUnitId, &[u32]), Vec<ByteRange>>::new();
    for ((rule, path), range) in &matcher_identities {
        let (_, parent_path) = path.split_last().ok_or(SourceError::InvalidInventory)?;
        if !parent_path.is_empty() {
            let parent_range = matcher_identities
                .get(&(*rule, parent_path))
                .ok_or(SourceError::InvalidInventory)?;
            if !parent_range.contains(*range) || parent_range == range {
                return Err(SourceError::InvalidInventory);
            }
        }
        matcher_siblings
            .entry((*rule, parent_path))
            .or_default()
            .push(*range);
    }
    for ranges in matcher_siblings.values_mut() {
        ranges.sort_by_key(|range| (range.start, range.end));
        if ranges
            .windows(2)
            .any(|pair| ranges_overlap(pair[0], pair[1]))
        {
            return Err(SourceError::InvalidInventory);
        }
    }
    Ok(())
}

pub(super) fn repetition_key(
    repetition: &MacroRepetitionSourceFacts,
) -> (SourceUnitId, SourceUnitId, &[u32]) {
    (
        repetition.invocation,
        repetition.parent,
        &repetition.repetition_path,
    )
}

pub(super) fn ranges_overlap(left: ByteRange, right: ByteRange) -> bool {
    left.start < right.end && right.start < left.end
}

pub(super) fn range_is_trivia(source: &str, range: ByteRange) -> bool {
    let Some(input) = source.get(range.start as usize..range.end as usize) else {
        return false;
    };
    let mut length = 0_u32;
    for token in tokenize(input, FrontmatterAllowed::No) {
        let Some(end) = length.checked_add(token.len) else {
            return false;
        };
        length = end;
        if !is_trivia(token.kind) {
            return false;
        }
    }
    length == range.len()
}

pub(super) fn separator_token(source: &str, range: ByteRange) -> Option<String> {
    let input = source.get(range.start as usize..range.end as usize)?;
    let tokens = tokenize_parser_tokens(input).ok()?;
    match tokens.as_slice() {
        [token] => Some(token.text.clone()),
        _ => None,
    }
}

pub(super) fn active_unit(
    units: &[WrittenUnit],
    id: SourceUnitId,
) -> Result<&WrittenUnit, SourceError> {
    units
        .get(id.0 as usize)
        .filter(|unit| unit.id == id && unit.cfg_state == CfgState::Active)
        .ok_or(SourceError::InvalidInventory)
}

pub(super) fn valid_range(source: &str, range: ByteRange) -> bool {
    range.start <= range.end
        && range.end as usize <= source.len()
        && source.is_char_boundary(range.start as usize)
        && source.is_char_boundary(range.end as usize)
}
