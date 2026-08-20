//! Deterministic source deletion over the written-source inventory.

use std::collections::{BTreeMap, BTreeSet};

use rustc_lexer::{FrontmatterAllowed, TokenKind, tokenize};

use crate::source::{
    AtomicGroupId, ByteRange, SourceInventory, SourceUnitId, WrittenUnit, WrittenUnitKind,
    validate_macro_rule_facts,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LexToken {
    kind: TokenKind,
    range: ByteRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
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
    validate_macro_rule_facts(&inventory.units, &inventory.macro_rules)
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
    inventory
        .units
        .iter()
        .filter(|unit| {
            unit.kind != WrittenUnitKind::UseLeaf
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

    let tokens = lex_range(&inventory.original, item.full_range)?;
    let brace_pairs = delimiter_pairs(&tokens)?;
    let ranges = leaves
        .iter()
        .map(|leaf| leaf.full_range)
        .collect::<Vec<_>>();
    let (open, close) = enclosing_brace(&tokens, &brace_pairs, &ranges, None)
        .ok_or(SourceRewriteError::InvalidUseTree)?;
    let mut deletions = Vec::new();
    rewrite_group(
        &tokens,
        &brace_pairs,
        open,
        close,
        &leaves,
        retained,
        &mut deletions,
    )?;
    Ok(deletions)
}

fn lex_range(source: &str, range: ByteRange) -> Result<Vec<LexToken>, SourceRewriteError> {
    let input = source
        .get(range.start as usize..range.end as usize)
        .ok_or(SourceRewriteError::InvalidInventory)?;
    let mut offset = range.start;
    let mut tokens = Vec::new();
    for token in tokenize(input, FrontmatterAllowed::No) {
        let end = offset
            .checked_add(token.len)
            .ok_or(SourceRewriteError::InvalidUseTree)?;
        tokens.push(LexToken {
            kind: token.kind,
            range: ByteRange { start: offset, end },
        });
        offset = end;
    }
    if offset != range.end {
        return Err(SourceRewriteError::InvalidUseTree);
    }
    Ok(tokens)
}

fn delimiter_pairs(tokens: &[LexToken]) -> Result<BTreeMap<usize, usize>, SourceRewriteError> {
    let mut stack = Vec::<(Delimiter, usize)>::new();
    let mut braces = BTreeMap::new();
    for (index, token) in tokens.iter().enumerate() {
        let opening = match token.kind {
            TokenKind::OpenParen => Some(Delimiter::Parenthesis),
            TokenKind::OpenBrace => Some(Delimiter::Brace),
            TokenKind::OpenBracket => Some(Delimiter::Bracket),
            _ => None,
        };
        if let Some(delimiter) = opening {
            stack.push((delimiter, index));
            continue;
        }
        let closing = match token.kind {
            TokenKind::CloseParen => Some(Delimiter::Parenthesis),
            TokenKind::CloseBrace => Some(Delimiter::Brace),
            TokenKind::CloseBracket => Some(Delimiter::Bracket),
            _ => None,
        };
        let Some(delimiter) = closing else {
            continue;
        };
        let Some((opening, opening_index)) = stack.pop() else {
            return Err(SourceRewriteError::InvalidUseTree);
        };
        if opening != delimiter {
            return Err(SourceRewriteError::InvalidUseTree);
        }
        if delimiter == Delimiter::Brace {
            braces.insert(opening_index, index);
        }
    }
    if !stack.is_empty() {
        return Err(SourceRewriteError::InvalidUseTree);
    }
    Ok(braces)
}

fn enclosing_brace(
    tokens: &[LexToken],
    brace_pairs: &BTreeMap<usize, usize>,
    leaves: &[ByteRange],
    within: Option<ByteRange>,
) -> Option<(usize, usize)> {
    brace_pairs
        .iter()
        .filter_map(|(&open, &close)| {
            let range = ByteRange {
                start: tokens[open].range.end,
                end: tokens[close].range.start,
            };
            if within.is_some_and(|outer| !outer.contains(range))
                || !leaves.iter().all(|leaf| range.contains(*leaf))
            {
                return None;
            }
            Some((range.len(), open, close))
        })
        .min()
        .map(|(_, open, close)| (open, close))
}

fn rewrite_group(
    tokens: &[LexToken],
    brace_pairs: &BTreeMap<usize, usize>,
    open: usize,
    close: usize,
    leaves: &[&WrittenUnit],
    retained: &BTreeSet<SourceUnitId>,
    deletions: &mut Vec<ByteRange>,
) -> Result<(), SourceRewriteError> {
    let commas = direct_commas(tokens, open, close)?;
    let group_start = tokens[open].range.end;
    let group_end = tokens[close].range.start;
    let mut assigned = BTreeSet::new();

    for segment_index in 0..=commas.len() {
        let previous = segment_index
            .checked_sub(1)
            .and_then(|index| commas.get(index).copied());
        let following = commas.get(segment_index).copied();
        let segment = ByteRange {
            start: previous.map_or(group_start, |comma| tokens[comma].range.end),
            end: following.map_or(group_end, |comma| tokens[comma].range.start),
        };
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
            let deletion = if let Some(comma) = following {
                ByteRange {
                    start: segment.start,
                    end: tokens[comma].range.end,
                }
            } else if let Some(comma) = previous {
                ByteRange {
                    start: tokens[comma].range.start,
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
        let (child_open, child_close) =
            enclosing_brace(tokens, brace_pairs, &leaf_ranges, Some(segment))
                .filter(|pair| *pair != (open, close))
                .ok_or(SourceRewriteError::InvalidUseTree)?;
        rewrite_group(
            tokens,
            brace_pairs,
            child_open,
            child_close,
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

fn direct_commas(
    tokens: &[LexToken],
    open: usize,
    close: usize,
) -> Result<Vec<usize>, SourceRewriteError> {
    let mut stack = Vec::new();
    let mut commas = Vec::new();
    for (index, token) in tokens.iter().enumerate().take(close).skip(open + 1) {
        let opening = match token.kind {
            TokenKind::OpenParen => Some(Delimiter::Parenthesis),
            TokenKind::OpenBrace => Some(Delimiter::Brace),
            TokenKind::OpenBracket => Some(Delimiter::Bracket),
            _ => None,
        };
        if let Some(delimiter) = opening {
            stack.push(delimiter);
            continue;
        }
        let closing = match token.kind {
            TokenKind::CloseParen => Some(Delimiter::Parenthesis),
            TokenKind::CloseBrace => Some(Delimiter::Brace),
            TokenKind::CloseBracket => Some(Delimiter::Bracket),
            _ => None,
        };
        if let Some(delimiter) = closing {
            if stack.pop() != Some(delimiter) {
                return Err(SourceRewriteError::InvalidUseTree);
            }
            continue;
        }
        if token.kind == TokenKind::Comma && stack.is_empty() {
            commas.push(index);
        }
    }
    if !stack.is_empty() {
        return Err(SourceRewriteError::InvalidUseTree);
    }
    Ok(commas)
}

fn merge_deletions(
    source: &str,
    deletions: Vec<ByteRange>,
    piece_boundaries: &BTreeSet<u32>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let mut merged = Vec::<ByteRange>::new();
    for deletion in deletions {
        if deletion.start == deletion.end
            || !valid_range(source, deletion)
            || !piece_boundaries.contains(&deletion.start)
            || !piece_boundaries.contains(&deletion.end)
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
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
mod tests {
    use std::sync::Arc;

    use crate::source::{
        CfgState, OriginalOffsetMap, OwnedPiece, PieceKind, SourceInventory, WrittenUnit,
    };

    use super::*;

    #[test]
    fn rewrites_nested_use_leaves_and_maps_every_retained_byte() {
        let source = "use x::{a, /* b */ b, c};\nfn dead() {}\nfn main() {}\n";
        let inventory = inventory(
            source,
            &[
                unit(WrittenUnitKind::UseItem, 0, 25, 0, 1),
                unit(WrittenUnitKind::UseLeaf, 8, 9, 1, 2),
                unit(WrittenUnitKind::UseLeaf, 19, 20, 1, 3),
                unit(WrittenUnitKind::UseLeaf, 22, 23, 1, 4),
                unit(WrittenUnitKind::Item, 26, 38, 0, 5),
                unit(WrittenUnitKind::Item, 39, 51, 0, 6),
            ],
        );
        let retained = BTreeSet::from([
            SourceUnitId(0),
            SourceUnitId(1),
            SourceUnitId(3),
            SourceUnitId(6),
        ]);

        let actual = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(actual.source, "use x::{ /* b */ b};\n\nfn main() {}\n");
        assert_eq!(
            actual.pieces,
            vec![
                piece(0, 8, 0, 8),
                piece(8, 18, 10, 20),
                piece(18, 21, 23, 26),
                piece(21, 35, 38, 52),
            ]
        );
        assert_piece_map(&inventory.original, &actual);
    }

    #[test]
    fn keeps_original_encoding_while_removing_nested_first_middle_and_last_leaves() {
        let source = concat!(
            "\u{feff}use crate::{α, nested::{first, /* 二 */ second, third}, glob::*};\r\n",
            "fn main() {}\r\n",
        );
        let use_range = marker(
            source,
            "use crate::{α, nested::{first, /* 二 */ second, third}, glob::*};",
        );
        let alpha = marker(source, "α");
        let first = marker(source, "first");
        let second = marker(source, "second");
        let third = marker(source, "third");
        let glob = marker(source, "glob::*");
        let main = marker(source, "fn main() {}");
        let inventory = inventory(
            source,
            &[
                unit(
                    WrittenUnitKind::UseItem,
                    use_range.start,
                    use_range.end,
                    0,
                    1,
                ),
                unit(WrittenUnitKind::UseLeaf, alpha.start, alpha.end, 1, 2),
                unit(WrittenUnitKind::UseLeaf, first.start, first.end, 1, 3),
                unit(WrittenUnitKind::UseLeaf, second.start, second.end, 1, 4),
                unit(WrittenUnitKind::UseLeaf, third.start, third.end, 1, 5),
                unit(WrittenUnitKind::UseLeaf, glob.start, glob.end, 1, 6),
                unit(WrittenUnitKind::Item, main.start, main.end, 0, 7),
            ],
        );
        let retained = BTreeSet::from([
            SourceUnitId(0),
            SourceUnitId(1),
            SourceUnitId(2),
            SourceUnitId(4),
            SourceUnitId(7),
        ]);

        let actual = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(
            actual.source,
            concat!(
                "\u{feff}use crate::{α, nested::{ /* 二 */ second}};\r\n",
                "fn main() {}\r\n",
            )
        );
        assert_piece_map(&inventory.original, &actual);
    }

    #[test]
    fn deleting_a_use_item_deletes_every_leaf() {
        let source = "use x::{a, b};\nfn main() {}\n";
        let inventory = inventory(
            source,
            &[
                unit(WrittenUnitKind::UseItem, 0, 14, 0, 1),
                unit(WrittenUnitKind::UseLeaf, 8, 9, 1, 2),
                unit(WrittenUnitKind::UseLeaf, 11, 12, 1, 3),
                unit(WrittenUnitKind::Item, 15, 27, 0, 4),
            ],
        );
        let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(4)]);

        let actual = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(actual.source, "\nfn main() {}\n");
        assert_eq!(actual.pieces, vec![piece(0, 14, 14, 28)]);

        assert_eq!(
            rewrite_source(
                &inventory,
                &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(4)])
            ),
            Err(SourceRewriteError::InvalidRetention)
        );
    }

    #[test]
    fn preserves_or_deletes_an_empty_use_item() {
        let source = "use {};fn main(){}";
        let inventory = inventory(
            source,
            &[
                unit(WrittenUnitKind::UseItem, 0, 7, 0, 1),
                unit(WrittenUnitKind::Item, 7, 18, 0, 2),
            ],
        );

        let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)]);
        let unchanged = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(unchanged.source, source);
        assert_piece_map(&inventory.original, &unchanged);

        let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(2)]);
        let reduced = rewrite_source(&inventory, &retained).unwrap();
        assert_eq!(reduced.source, "fn main(){}");
        assert_eq!(reduced.pieces, vec![piece(0, 11, 7, 18)]);
        assert_piece_map(&inventory.original, &reduced);
    }

    #[test]
    fn rejects_retention_that_splits_parents_or_atomic_groups() {
        let source = "mod m { fn f() {} }\n";
        let inventory = inventory(
            source,
            &[
                unit(WrittenUnitKind::InlineModule, 0, 19, 0, 1),
                unit(WrittenUnitKind::Item, 8, 17, 1, 2),
                unit(WrittenUnitKind::MacroInvocation, 8, 17, 2, 2),
            ],
        );
        assert_eq!(
            rewrite_source(
                &inventory,
                &BTreeSet::from([SourceUnitId(0), SourceUnitId(2), SourceUnitId(3)])
            ),
            Err(SourceRewriteError::InvalidRetention)
        );
        assert_eq!(
            rewrite_source(
                &inventory,
                &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
            ),
            Err(SourceRewriteError::InvalidRetention)
        );
    }

    #[test]
    fn rejects_invalid_utf8_piece_and_use_tree_boundaries() {
        let mut broken = inventory("日\n", &[unit(WrittenUnitKind::Item, 1, 3, 0, 1)]);
        assert_eq!(
            rewrite_source(&broken, &BTreeSet::from([SourceUnitId(0)])),
            Err(SourceRewriteError::InvalidInventory)
        );

        broken = inventory(
            "fn main() {}\n",
            &[unit(WrittenUnitKind::Item, 0, 12, 0, 1)],
        );
        broken.pieces.pop();
        assert_eq!(
            rewrite_source(&broken, &BTreeSet::from([SourceUnitId(0)])),
            Err(SourceRewriteError::InvalidInventory)
        );

        let malformed = inventory(
            "use x::a;\n",
            &[
                unit(WrittenUnitKind::UseItem, 0, 9, 0, 1),
                unit(WrittenUnitKind::UseLeaf, 4, 5, 1, 2),
                unit(WrittenUnitKind::UseLeaf, 7, 8, 1, 3),
            ],
        );
        assert_eq!(
            rewrite_source(
                &malformed,
                &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
            ),
            Err(SourceRewriteError::InvalidUseTree)
        );
    }

    #[test]
    fn an_already_rewritten_source_is_byte_identical() {
        let source = "fn main() {}\r\n// 終\r\n";
        let first =
            rewrite_source(&inventory(source, &[]), &BTreeSet::from([SourceUnitId(0)])).unwrap();
        let second = rewrite_source(
            &inventory(&first.source, &[]),
            &BTreeSet::from([SourceUnitId(0)]),
        )
        .unwrap();

        assert_eq!(first.source, source);
        assert_eq!(second.source, first.source);
        assert_eq!(
            second.pieces,
            vec![piece(0, source.len() as u32, 0, source.len() as u32)]
        );
    }

    fn inventory(source: &str, children: &[WrittenUnit]) -> SourceInventory {
        let (normalized, offsets) = OriginalOffsetMap::from_source(source).unwrap();
        let mut units = vec![WrittenUnit {
            id: SourceUnitId(0),
            kind: WrittenUnitKind::CrateRoot,
            full_range: ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            parent: None,
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(0),
            same_role_ordinal: 0,
        }];
        for mut child in children.iter().cloned() {
            child.id = SourceUnitId(units.len() as u32);
            units.push(child);
        }
        let pieces = source
            .char_indices()
            .map(|(start, value)| OwnedPiece {
                range: ByteRange {
                    start: start as u32,
                    end: (start + value.len_utf8()) as u32,
                },
                owner: SourceUnitId(0),
                kind: PieceKind::Trivia,
            })
            .collect();
        SourceInventory {
            original: Arc::from(source),
            normalized: Arc::from(normalized),
            offsets,
            units,
            pieces,
            macro_rules: Vec::new(),
        }
    }

    fn unit(kind: WrittenUnitKind, start: u32, end: u32, parent: u32, group: u32) -> WrittenUnit {
        WrittenUnit {
            id: SourceUnitId(u32::MAX),
            kind,
            full_range: ByteRange { start, end },
            parent: Some(SourceUnitId(parent)),
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(group),
            same_role_ordinal: 0,
        }
    }

    fn marker(source: &str, marker: &str) -> ByteRange {
        let start = source.find(marker).unwrap();
        ByteRange {
            start: start as u32,
            end: (start + marker.len()) as u32,
        }
    }

    fn piece(
        output_start: u32,
        output_end: u32,
        original_start: u32,
        original_end: u32,
    ) -> SourcePiece {
        SourcePiece {
            output_range: ByteRange {
                start: output_start,
                end: output_end,
            },
            original_range: ByteRange {
                start: original_start,
                end: original_end,
            },
        }
    }

    fn assert_piece_map(original: &str, rewrite: &SourceRewrite) {
        let mut cursor = 0_u32;
        for piece in &rewrite.pieces {
            assert_eq!(piece.output_range.start, cursor);
            assert_eq!(piece.output_range.len(), piece.original_range.len());
            assert_eq!(
                &rewrite.source[piece.output_range.start as usize..piece.output_range.end as usize],
                &original[piece.original_range.start as usize..piece.original_range.end as usize]
            );
            cursor = piece.output_range.end;
        }
        assert_eq!(cursor as usize, rewrite.source.len());
    }

    #[test]
    fn maps_rewritten_ranges_back_with_directional_boundary_bias() {
        let rewrite = splice(
            "aaXXbbYYYcc",
            &[
                ByteRange { start: 2, end: 4 },
                ByteRange { start: 6, end: 9 },
            ],
        )
        .unwrap();
        assert_eq!(rewrite.source, "aabbcc");

        // A range spanning the full reduced source still follows the retained
        // endpoints; only an explicitly identified crate root may include a
        // deleted prefix or suffix.
        assert_eq!(rewrite.original_range(range(0, 6)), Ok(range(0, 11)));
        // A non-empty end at a piece boundary is left-biased.
        assert_eq!(rewrite.original_range(range(1, 2)), Ok(range(1, 2)));
        // A start (and therefore an empty range) at a boundary is right-biased.
        assert_eq!(rewrite.original_range(range(2, 2)), Ok(range(4, 4)));
        assert_eq!(rewrite.original_range(range(2, 3)), Ok(range(4, 5)));
        // A range spanning multiple retained pieces maps to the original
        // envelope, including the deleted gaps between its endpoints.
        assert_eq!(rewrite.original_range(range(1, 5)), Ok(range(1, 10)));
        assert_eq!(rewrite.original_range(range(6, 6)), Ok(range(11, 11)));
    }

    #[test]
    fn maps_crate_root_across_deleted_prefix_and_suffix() {
        let rewrite = splice(
            "XXabcYY",
            &[
                ByteRange { start: 0, end: 2 },
                ByteRange { start: 5, end: 7 },
            ],
        )
        .unwrap();
        assert_eq!(rewrite.source, "abc");
        assert_eq!(rewrite.original_range(range(0, 3)), Ok(range(2, 5)));
        assert_eq!(rewrite.original_crate_range(range(0, 3)), Ok(range(0, 7)));
        assert_eq!(rewrite.original_range(range(0, 0)), Ok(range(2, 2)));
        assert_eq!(rewrite.original_range(range(3, 3)), Ok(range(5, 5)));
    }

    #[test]
    fn range_mapping_preserves_utf8_boundaries() {
        let rewrite = splice("éXX界", &[ByteRange { start: 2, end: 4 }]).unwrap();
        assert_eq!(rewrite.source, "é界");
        assert_eq!(rewrite.original_range(range(2, 5)), Ok(range(4, 7)));
        assert_eq!(rewrite.original_range(range(2, 2)), Ok(range(4, 4)));
        assert_eq!(
            rewrite.original_range(range(1, 2)),
            Err(SourceRewriteError::InvalidInventory)
        );
    }

    fn range(start: u32, end: u32) -> ByteRange {
        ByteRange { start, end }
    }
}
