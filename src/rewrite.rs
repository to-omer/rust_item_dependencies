//! Deterministic source deletion over the written-source inventory.

mod macro_repetition;

pub(crate) use macro_repetition::MacroRepetitionTokenRequirements;
use macro_repetition::macro_repetition_deletions;

use std::collections::{BTreeMap, BTreeSet};

use crate::source::syntax::{
    Delimiter, DelimiterPair, SourceSyntaxError, SourceToken, comma_list_segments,
    tokenize_balanced_range,
};
use crate::source::{
    AtomicGroupId, ByteRange, DeriveTargetSourceFacts, SourceInventory, SourceUnitId, WrittenUnit,
    WrittenUnitKind, derive_attribute_layout, validate_declarative_macro_source_facts,
    validate_derive_target_facts,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourceRewrite {
    pub source: String,
    pub pieces: Vec<SourcePiece>,
    original_len: u32,
}

impl SourceRewrite {
    pub(crate) fn original_range(&self, range: ByteRange) -> Result<ByteRange, SourceRewriteError> {
        let source_len =
            u32::try_from(self.source.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
        if range.start > range.end
            || range.end > source_len
            || !self.source.is_char_boundary(range.start as usize)
            || !self.source.is_char_boundary(range.end as usize)
            || !self.valid_piece_map(source_len)
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        let start = self.original_offset(range.start, true)?;
        let end = self.original_offset(range.end, range.start == range.end)?;
        (start <= end)
            .then_some(ByteRange { start, end })
            .ok_or(SourceRewriteError::InvalidInventory)
    }

    pub(crate) fn original_crate_range(
        &self,
        range: ByteRange,
    ) -> Result<ByteRange, SourceRewriteError> {
        let source_len =
            u32::try_from(self.source.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
        if range
            != (ByteRange {
                start: 0,
                end: source_len,
            })
            || !self.valid_piece_map(source_len)
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        Ok(ByteRange {
            start: 0,
            end: self.original_len,
        })
    }

    fn original_offset(&self, offset: u32, right_biased: bool) -> Result<u32, SourceRewriteError> {
        let piece = if right_biased {
            self.pieces
                .iter()
                .find(|piece| piece.output_range.start <= offset && offset < piece.output_range.end)
                .or_else(|| {
                    self.pieces
                        .iter()
                        .find(|piece| piece.output_range.start == offset)
                })
                .or_else(|| {
                    self.pieces
                        .last()
                        .filter(|piece| piece.output_range.end == offset)
                })
        } else {
            self.pieces
                .iter()
                .find(|piece| piece.output_range.start < offset && offset <= piece.output_range.end)
                .or_else(|| {
                    self.pieces
                        .iter()
                        .rev()
                        .find(|piece| piece.output_range.end == offset)
                })
        };
        let Some(piece) = piece else {
            return (offset == 0 && self.pieces.is_empty())
                .then_some(0)
                .ok_or(SourceRewriteError::InvalidInventory);
        };
        piece
            .original_range
            .start
            .checked_add(offset - piece.output_range.start)
            .ok_or(SourceRewriteError::InvalidInventory)
    }

    fn valid_piece_map(&self, source_len: u32) -> bool {
        let mut output_cursor = 0;
        let mut original_cursor = 0;
        for piece in &self.pieces {
            if piece.output_range.start != output_cursor
                || piece.output_range.start >= piece.output_range.end
                || piece.original_range.start >= piece.original_range.end
                || piece.output_range.len() != piece.original_range.len()
                || piece.original_range.start < original_cursor
                || piece.original_range.end > self.original_len
            {
                return false;
            }
            output_cursor = piece.output_range.end;
            original_cursor = piece.original_range.end;
        }
        output_cursor == source_len && (source_len == 0 || !self.pieces.is_empty())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourcePiece {
    pub output_range: ByteRange,
    pub original_range: ByteRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum SourceRewriteError {
    InvalidInventory,
    InvalidRetention,
    InvalidUseTree,
}

pub(crate) fn rewrite_source(
    inventory: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<SourceRewrite, SourceRewriteError> {
    let piece_boundaries = validate_inventory(inventory)?;
    validate_retention(inventory, retained)?;

    let mut deletions = frontier_deletions(inventory, retained)?;
    for item in inventory
        .units
        .iter()
        .filter(|unit| unit.kind == WrittenUnitKind::UseItem && retained.contains(&unit.id))
    {
        deletions.extend(rewrite_use_item(inventory, item, retained)?);
    }
    for facts in &inventory.derive_targets {
        let DeriveTargetSourceFacts::Complete { attributes, .. } = facts else {
            continue;
        };
        for attribute in attributes {
            if retained.contains(&attribute.attribute) {
                deletions.extend(rewrite_derive_attribute(inventory, attribute, retained)?);
            }
        }
    }
    deletions.extend(macro_repetition_deletions(
        inventory,
        retained,
        &piece_boundaries,
    )?);

    deletions.sort();
    let deletions = merge_deletions(&inventory.original, deletions, &piece_boundaries)?;
    splice(&inventory.original, &deletions)
}

fn validate_inventory(inventory: &SourceInventory) -> Result<BTreeSet<u32>, SourceRewriteError> {
    let source = inventory.original.as_ref();
    let source_len =
        u32::try_from(source.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
    let roots = inventory
        .units
        .iter()
        .filter(|unit| unit.parent.is_none())
        .collect::<Vec<_>>();
    if roots.len() != 1
        || roots[0].kind != WrittenUnitKind::CrateRoot
        || roots[0].full_range
            != (ByteRange {
                start: 0,
                end: source_len,
            })
    {
        return Err(SourceRewriteError::InvalidInventory);
    }

    for (index, unit) in inventory.units.iter().enumerate() {
        if unit.id != SourceUnitId(index as u32)
            || !valid_range(source, unit.full_range)
            || unit
                .parent
                .is_some_and(|parent| parent.0 as usize >= inventory.units.len())
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        if let Some(parent) = unit.parent
            && (parent == unit.id
                || !inventory.units[parent.0 as usize]
                    .full_range
                    .contains(unit.full_range))
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        if unit.kind == WrittenUnitKind::InactiveCfgComponent
            && (unit.cfg_state != crate::source::CfgState::Inactive
                || unit.parent.is_none_or(|parent| {
                    inventory.units[parent.0 as usize].cfg_state != crate::source::CfgState::Active
                }))
        {
            return Err(SourceRewriteError::InvalidInventory);
        }

        let mut cursor = unit.parent;
        let mut depth = 0_usize;
        while let Some(parent) = cursor {
            depth += 1;
            if depth > inventory.units.len() {
                return Err(SourceRewriteError::InvalidInventory);
            }
            cursor = inventory.units[parent.0 as usize].parent;
        }
    }

    for leaf in inventory
        .units
        .iter()
        .filter(|unit| unit.kind == WrittenUnitKind::UseLeaf)
    {
        let Some(parent) = leaf.parent else {
            return Err(SourceRewriteError::InvalidInventory);
        };
        if inventory.units[parent.0 as usize].kind != WrittenUnitKind::UseItem
            || leaf.full_range.start == leaf.full_range.end
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
    }
    let mut piece_boundaries = BTreeSet::from([0, source_len]);
    let mut cursor = 0_u32;
    for piece in &inventory.pieces {
        if piece.range.start != cursor
            || piece.range.start == piece.range.end
            || !valid_range(source, piece.range)
            || inventory
                .units
                .get(piece.owner.0 as usize)
                .is_none_or(|owner| !owner.full_range.contains(piece.range))
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        piece_boundaries.insert(piece.range.start);
        piece_boundaries.insert(piece.range.end);
        cursor = piece.range.end;
    }
    if cursor != source_len
        || inventory.units.iter().any(|unit| {
            !piece_boundaries.contains(&unit.full_range.start)
                || !piece_boundaries.contains(&unit.full_range.end)
        })
    {
        return Err(SourceRewriteError::InvalidInventory);
    }
    validate_derive_target_facts(&inventory.units, &inventory.derive_targets)
        .map_err(|_| SourceRewriteError::InvalidInventory)?;
    validate_declarative_macro_source_facts(
        &inventory.original,
        &inventory.units,
        &inventory.macro_rules,
        &inventory.macro_templates,
        &inventory.macro_repetitions,
    )
    .map_err(|_| SourceRewriteError::InvalidInventory)?;
    Ok(piece_boundaries)
}

fn validate_retention(
    inventory: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<(), SourceRewriteError> {
    if retained
        .iter()
        .any(|unit| unit.0 as usize >= inventory.units.len())
    {
        return Err(SourceRewriteError::InvalidRetention);
    }
    let root = inventory
        .units
        .iter()
        .find(|unit| unit.parent.is_none())
        .ok_or(SourceRewriteError::InvalidInventory)?;
    if !retained.contains(&root.id)
        || inventory.units.iter().any(|unit| {
            retained.contains(&unit.id)
                && unit
                    .parent
                    .is_some_and(|parent| !retained.contains(&parent))
        })
    {
        return Err(SourceRewriteError::InvalidRetention);
    }

    let mut groups = BTreeMap::<AtomicGroupId, bool>::new();
    for unit in &inventory.units {
        let state = retained.contains(&unit.id);
        if groups
            .insert(unit.atomic_group, state)
            .is_some_and(|previous| previous != state)
        {
            return Err(SourceRewriteError::InvalidRetention);
        }
    }
    Ok(())
}

fn frontier_deletions(
    inventory: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let matcher_elements = inventory
        .macro_repetitions
        .iter()
        .flat_map(|repetition| repetition.elements.iter().map(|element| element.unit))
        .collect::<BTreeSet<_>>();
    let derive_elements = inventory
        .derive_targets
        .iter()
        .filter_map(|facts| match facts {
            DeriveTargetSourceFacts::Complete { attributes, .. } => Some(attributes),
            DeriveTargetSourceFacts::Opaque { .. } => None,
        })
        .flat_map(|attributes| attributes.iter())
        .flat_map(|attribute| attribute.elements.iter().copied())
        .collect::<BTreeSet<_>>();
    inventory
        .units
        .iter()
        .filter(|unit| {
            unit.kind != WrittenUnitKind::UseLeaf
                && !matcher_elements.contains(&unit.id)
                && !derive_elements.contains(&unit.id)
                && !retained.contains(&unit.id)
                && unit.parent.is_some_and(|parent| retained.contains(&parent))
        })
        .map(|unit| {
            if unit.full_range.start == unit.full_range.end {
                Err(SourceRewriteError::InvalidInventory)
            } else {
                Ok(unit.full_range)
            }
        })
        .collect()
}

fn rewrite_derive_attribute(
    inventory: &SourceInventory,
    facts: &crate::source::DeriveAttributeSourceFacts,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let attribute = inventory
        .units
        .get(facts.attribute.0 as usize)
        .filter(|attribute| attribute.id == facts.attribute)
        .ok_or(SourceRewriteError::InvalidInventory)?;
    let elements = facts
        .elements
        .iter()
        .map(|element| {
            inventory
                .units
                .get(element.0 as usize)
                .filter(|unit| unit.id == *element)
                .ok_or(SourceRewriteError::InvalidInventory)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let retained_count = elements
        .iter()
        .filter(|element| retained.contains(&element.id))
        .count();
    if retained_count == elements.len() {
        return Ok(Vec::new());
    }
    if retained_count == 0 {
        return Err(SourceRewriteError::InvalidRetention);
    }

    let ranges = elements
        .iter()
        .map(|element| element.full_range)
        .collect::<Vec<_>>();
    let layout = derive_attribute_layout(&inventory.original, attribute.full_range, &ranges)
        .map_err(|_| SourceRewriteError::InvalidInventory)?;
    let elements_by_range = elements
        .iter()
        .map(|element| (element.full_range, element.id))
        .collect::<BTreeMap<_, _>>();
    let retained_layout = layout
        .iter()
        .map(|entry| {
            elements_by_range
                .get(&entry.element)
                .map(|element| retained.contains(element))
                .ok_or(SourceRewriteError::InvalidInventory)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut deletions = Vec::new();
    let mut index = 0;
    while index < layout.len() {
        if retained_layout[index] {
            index += 1;
            continue;
        }
        let first = index;
        while index < layout.len() && !retained_layout[index] {
            index += 1;
        }
        let last = index - 1;
        let deletion = if index < layout.len() || layout[last].following_comma.is_some() {
            let comma = layout[last]
                .following_comma
                .ok_or(SourceRewriteError::InvalidInventory)?;
            ByteRange {
                start: layout[first].segment.start,
                end: comma.end,
            }
        } else {
            let comma = layout[first]
                .previous_comma
                .ok_or(SourceRewriteError::InvalidRetention)?;
            ByteRange {
                start: comma.start,
                end: layout[last].segment.end,
            }
        };
        if deletion.is_empty() {
            return Err(SourceRewriteError::InvalidInventory);
        }
        deletions.push(deletion);
    }
    Ok(deletions)
}

fn rewrite_use_item(
    inventory: &SourceInventory,
    item: &WrittenUnit,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let mut leaves = inventory
        .units
        .iter()
        .filter(|unit| unit.kind == WrittenUnitKind::UseLeaf && unit.parent == Some(item.id))
        .collect::<Vec<_>>();
    leaves.sort_by_key(|leaf| leaf.full_range);
    if leaves
        .windows(2)
        .any(|pair| pair[0].full_range.end > pair[1].full_range.start)
    {
        return Err(SourceRewriteError::InvalidUseTree);
    }
    if leaves.is_empty() {
        return Ok(Vec::new());
    }

    let retained_count = leaves
        .iter()
        .filter(|leaf| retained.contains(&leaf.id))
        .count();
    if retained_count == leaves.len() {
        return Ok(Vec::new());
    }
    if retained_count == 0 {
        return Err(SourceRewriteError::InvalidRetention);
    }

    let (tokens, delimiter_pairs) = tokenize_balanced_range(&inventory.original, item.full_range)
        .map_err(|error| match error {
        SourceSyntaxError::InvalidRange => SourceRewriteError::InvalidInventory,
        SourceSyntaxError::SourceTooLarge | SourceSyntaxError::InvalidSyntax => {
            SourceRewriteError::InvalidUseTree
        }
    })?;
    let ranges = leaves
        .iter()
        .map(|leaf| leaf.full_range)
        .collect::<Vec<_>>();
    let pair = enclosing_brace(&tokens, &delimiter_pairs, &ranges, None)
        .ok_or(SourceRewriteError::InvalidUseTree)?;
    let mut deletions = Vec::new();
    rewrite_group(
        &tokens,
        &delimiter_pairs,
        pair,
        &leaves,
        retained,
        &mut deletions,
    )?;
    Ok(deletions)
}

fn enclosing_brace(
    tokens: &[SourceToken],
    delimiter_pairs: &[DelimiterPair],
    leaves: &[ByteRange],
    within: Option<ByteRange>,
) -> Option<DelimiterPair> {
    delimiter_pairs
        .iter()
        .copied()
        .filter(|pair| pair.delimiter == Delimiter::Brace)
        .filter_map(|pair| {
            let range = ByteRange {
                start: tokens[pair.open].range.end,
                end: tokens[pair.close].range.start,
            };
            if within.is_some_and(|outer| !outer.contains(range))
                || !leaves.iter().all(|leaf| range.contains(*leaf))
            {
                return None;
            }
            Some((range.len(), pair))
        })
        .min_by_key(|(size, pair)| (*size, pair.open, pair.close))
        .map(|(_, pair)| pair)
}

fn rewrite_group(
    tokens: &[SourceToken],
    delimiter_pairs: &[DelimiterPair],
    pair: DelimiterPair,
    leaves: &[&WrittenUnit],
    retained: &BTreeSet<SourceUnitId>,
    deletions: &mut Vec<ByteRange>,
) -> Result<(), SourceRewriteError> {
    let segments =
        comma_list_segments(tokens, pair).map_err(|_| SourceRewriteError::InvalidUseTree)?;
    let mut assigned = BTreeSet::new();

    for list_segment in segments {
        let segment = list_segment.range;
        let segment_leaves = leaves
            .iter()
            .copied()
            .filter(|leaf| segment.contains(leaf.full_range))
            .collect::<Vec<_>>();
        if segment_leaves.is_empty() {
            continue;
        }
        for leaf in &segment_leaves {
            if !assigned.insert(leaf.id) {
                return Err(SourceRewriteError::InvalidUseTree);
            }
        }

        let kept = segment_leaves
            .iter()
            .filter(|leaf| retained.contains(&leaf.id))
            .count();
        if kept == segment_leaves.len() {
            continue;
        }
        if kept == 0 {
            let deletion = if let Some(comma) = list_segment.following_comma {
                ByteRange {
                    start: segment.start,
                    end: comma.end,
                }
            } else if let Some(comma) = list_segment.previous_comma {
                ByteRange {
                    start: comma.start,
                    end: segment.end,
                }
            } else {
                return Err(SourceRewriteError::InvalidUseTree);
            };
            if deletion.start == deletion.end {
                return Err(SourceRewriteError::InvalidUseTree);
            }
            deletions.push(deletion);
            continue;
        }

        let leaf_ranges = segment_leaves
            .iter()
            .map(|leaf| leaf.full_range)
            .collect::<Vec<_>>();
        let child = enclosing_brace(tokens, delimiter_pairs, &leaf_ranges, Some(segment))
            .filter(|child| *child != pair)
            .ok_or(SourceRewriteError::InvalidUseTree)?;
        rewrite_group(
            tokens,
            delimiter_pairs,
            child,
            &segment_leaves,
            retained,
            deletions,
        )?;
    }

    if assigned.len() != leaves.len() {
        return Err(SourceRewriteError::InvalidUseTree);
    }
    Ok(())
}

fn merge_deletions(
    source: &str,
    deletions: Vec<ByteRange>,
    piece_boundaries: &BTreeSet<u32>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let mut merged = Vec::<ByteRange>::new();
    for deletion in deletions {
        validate_deletion_range(source, deletion, piece_boundaries)?;
        if let Some(previous) = merged.last_mut()
            && deletion.start <= previous.end
        {
            previous.end = previous.end.max(deletion.end);
        } else {
            merged.push(deletion);
        }
    }
    Ok(merged)
}

fn validate_deletion_range(
    source: &str,
    deletion: ByteRange,
    piece_boundaries: &BTreeSet<u32>,
) -> Result<(), SourceRewriteError> {
    if deletion.start == deletion.end
        || !valid_range(source, deletion)
        || !piece_boundaries.contains(&deletion.start)
        || !piece_boundaries.contains(&deletion.end)
    {
        return Err(SourceRewriteError::InvalidInventory);
    }
    Ok(())
}

fn splice(source: &str, deletions: &[ByteRange]) -> Result<SourceRewrite, SourceRewriteError> {
    let source_len =
        u32::try_from(source.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
    let removed = deletions
        .iter()
        .map(|range| range.len() as usize)
        .sum::<usize>();
    let mut output = String::with_capacity(source.len().saturating_sub(removed));
    let mut pieces = Vec::new();
    let mut cursor = 0_u32;
    for deletion in deletions {
        append_piece(source, &mut output, &mut pieces, cursor, deletion.start)?;
        cursor = deletion.end;
    }
    append_piece(source, &mut output, &mut pieces, cursor, source_len)?;
    Ok(SourceRewrite {
        source: output,
        pieces,
        original_len: source_len,
    })
}

fn append_piece(
    source: &str,
    output: &mut String,
    pieces: &mut Vec<SourcePiece>,
    start: u32,
    end: u32,
) -> Result<(), SourceRewriteError> {
    if start == end {
        return Ok(());
    }
    let bytes = source
        .get(start as usize..end as usize)
        .ok_or(SourceRewriteError::InvalidInventory)?;
    let output_start =
        u32::try_from(output.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
    output.push_str(bytes);
    let output_end =
        u32::try_from(output.len()).map_err(|_| SourceRewriteError::InvalidInventory)?;
    pieces.push(SourcePiece {
        output_range: ByteRange {
            start: output_start,
            end: output_end,
        },
        original_range: ByteRange { start, end },
    });
    Ok(())
}

fn valid_range(source: &str, range: ByteRange) -> bool {
    range.start <= range.end
        && range.end as usize <= source.len()
        && source.is_char_boundary(range.start as usize)
        && source.is_char_boundary(range.end as usize)
}

#[cfg(test)]
#[path = "rewrite/tests.rs"]
mod tests;
