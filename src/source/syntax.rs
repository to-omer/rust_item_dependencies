//! Shared lexical structure for comma-separated Rust source lists.

use rustc_ast::token::{Token as AstToken, TokenKind as AstTokenKind};
use rustc_lexer::{FrontmatterAllowed, TokenKind, tokenize};
use rustc_span::DUMMY_SP;

#[cfg(test)]
use std::cell::Cell;

use super::ByteRange;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

impl Delimiter {
    fn opening(kind: TokenKind) -> Option<Self> {
        match kind {
            TokenKind::OpenParen => Some(Self::Parenthesis),
            TokenKind::OpenBrace => Some(Self::Brace),
            TokenKind::OpenBracket => Some(Self::Bracket),
            _ => None,
        }
    }

    fn closing(kind: TokenKind) -> Option<Self> {
        match kind {
            TokenKind::CloseParen => Some(Self::Parenthesis),
            TokenKind::CloseBrace => Some(Self::Brace),
            TokenKind::CloseBracket => Some(Self::Bracket),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SourceToken {
    pub kind: TokenKind,
    pub range: ByteRange,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParserToken {
    pub range: ByteRange,
    pub text: String,
    lexer_kind: TokenKind,
    punctuation: Option<AstTokenKind>,
}

impl ParserToken {
    pub(crate) fn same_identity(&self, other: &Self) -> bool {
        self.text == other.text
            && self.lexer_kind == other.lexer_kind
            && self.punctuation == other.punctuation
    }
}

pub(crate) struct ParserTokenRewriteGuard<'source> {
    source: &'source str,
    tokens: Vec<ParserToken>,
    pound_run_starts: Vec<usize>,
    pound_run_ends: Vec<usize>,
    #[cfg(test)]
    dependency_token_visits: Cell<usize>,
    #[cfg(test)]
    relexed_bytes: Cell<usize>,
}

impl<'source> ParserTokenRewriteGuard<'source> {
    pub(crate) fn new(source: &'source str) -> Result<Self, SourceSyntaxError> {
        #[cfg(test)]
        PARSER_TOKEN_REWRITE_GUARD_BUILDS.with(|count| count.set(count.get() + 1));
        let tokens = tokenize_parser_tokens(source)?;
        let (pound_run_starts, pound_run_ends) = pound_run_bounds(&tokens);
        #[cfg(test)]
        let dependency_token_visits = Cell::new(tokens.len());
        Ok(Self {
            source,
            tokens,
            pound_run_starts,
            pound_run_ends,
            #[cfg(test)]
            dependency_token_visits,
            #[cfg(test)]
            relexed_bytes: Cell::new(0),
        })
    }

    pub(crate) fn deletion_preserves_identity(&self, deletion: ByteRange) -> bool {
        self.trivia_separated_pound_deletion_preserves_identity(deletion)
            || self.deletions_preserve_identity(&[deletion])
    }

    pub(crate) fn deletion_dependency_window(&self, deletion: ByteRange) -> Option<ByteRange> {
        self.deletion_boundary(deletion)
            .map(ParserTokenDeletionBoundary::window)
    }

    pub(crate) fn deletions_preserve_identity(&self, deletions: &[ByteRange]) -> bool {
        if deletions.is_empty() || deletions.windows(2).any(|pair| pair[0].end > pair[1].start) {
            return false;
        }
        let Some(boundary) = self.deletion_boundary(deletions[0]) else {
            return false;
        };
        let window = boundary.window();
        for &deletion in &deletions[1..] {
            if self
                .deletion_boundary(deletion)
                .is_none_or(|boundary| boundary.window() != window)
            {
                return false;
            }
        }

        let mut rewritten = String::with_capacity(window.len() as usize);
        let mut cursor = window.start;
        for deletion in deletions {
            let Some(retained) = self.source.get(cursor as usize..deletion.start as usize) else {
                return false;
            };
            rewritten.push_str(retained);
            cursor = deletion.end;
        }
        let Some(retained) = self.source.get(cursor as usize..window.end as usize) else {
            return false;
        };
        rewritten.push_str(retained);
        #[cfg(test)]
        self.relexed_bytes
            .set(self.relexed_bytes.get() + rewritten.len());
        let Ok(actual) = tokenize_parser_tokens(&rewritten) else {
            return false;
        };
        let mut deletion = 0;
        let mut actual = actual.iter();
        for original in &self.tokens[boundary.left_start..boundary.right_end] {
            while deletions
                .get(deletion)
                .is_some_and(|range| range.end <= original.range.start)
            {
                deletion += 1;
            }
            if deletions
                .get(deletion)
                .is_some_and(|range| range.contains(original.range))
            {
                continue;
            }
            let Some(rewritten) = actual.next() else {
                return false;
            };
            if !original.same_identity(rewritten) {
                return false;
            }
        }
        actual.next().is_none()
    }

    fn trivia_separated_pound_deletion_preserves_identity(&self, deletion: ByteRange) -> bool {
        let Some(boundary) = self.deletion_boundary(deletion) else {
            return false;
        };
        if boundary.deleted_end != boundary.deleted_start + 1 {
            return false;
        }
        let token = &self.tokens[boundary.deleted_start];
        if token.range != deletion || token.lexer_kind != TokenKind::Pound {
            return false;
        }
        let run_start = self.pound_run_starts[boundary.deleted_start];
        let run_end = self.pound_run_ends[boundary.deleted_start];
        (boundary.deleted_start > run_start
            && self.tokens[boundary.deleted_start - 1].range.end < token.range.start)
            || (boundary.deleted_start + 1 < run_end
                && token.range.end < self.tokens[boundary.deleted_start + 1].range.start)
    }

    fn deletion_boundary(&self, deletion: ByteRange) -> Option<ParserTokenDeletionBoundary> {
        if deletion.start >= deletion.end
            || deletion.end as usize > self.source.len()
            || !self.source.is_char_boundary(deletion.start as usize)
            || !self.source.is_char_boundary(deletion.end as usize)
        {
            return None;
        }
        let mut right_start = self
            .tokens
            .partition_point(|token| token.range.end <= deletion.start);
        let deleted_start = right_start;
        while let Some(token) = self.tokens.get(right_start) {
            if token.range.start >= deletion.end {
                break;
            }
            #[cfg(test)]
            self.dependency_token_visits
                .set(self.dependency_token_visits.get() + 1);
            if !deletion.contains(token.range) {
                return None;
            }
            right_start += 1;
        }
        let deleted_end = right_start;

        // A raw identifier or raw string prefix can inspect an unbounded run
        // of `#` tokens before deciding where the token starts and ends. Keep
        // that entire prefix in the local re-lexing window, then include one
        // unchanged token on either side so the rewritten token stream has
        // reached an original token boundary before it is accepted.
        let left_start = if deleted_start == 0 {
            0
        } else {
            let adjacent = deleted_start - 1;
            if self.tokens[adjacent].lexer_kind == TokenKind::Pound {
                self.pound_run_starts[adjacent].saturating_sub(2)
            } else {
                adjacent.saturating_sub(1)
            }
        };
        let right_end = if deleted_end < self.tokens.len() {
            let first = deleted_end;
            let dependency_end = if self.tokens[first].lexer_kind == TokenKind::Pound {
                self.pound_run_ends[first].saturating_add(2)
            } else {
                first.saturating_add(2)
            };
            dependency_end.min(self.tokens.len())
        } else {
            deleted_end
        };

        Some(ParserTokenDeletionBoundary {
            deleted_start,
            deleted_end,
            left_start,
            right_end,
            window_start: if left_start < deleted_start {
                self.tokens[left_start].range.start
            } else {
                deletion.start
            },
            window_end: if deleted_end < right_end {
                self.tokens[right_end - 1].range.end
            } else {
                deletion.end
            },
        })
    }

    #[cfg(test)]
    fn deletion_boundary_byte_len(&self, deletion: ByteRange) -> Option<usize> {
        let boundary = self.deletion_boundary(deletion)?;
        Some(
            (deletion.start - boundary.window_start) as usize
                + (boundary.window_end - deletion.end) as usize,
        )
    }

    #[cfg(test)]
    pub(crate) fn dependency_token_visits(&self) -> usize {
        self.dependency_token_visits.get()
    }

    #[cfg(test)]
    pub(crate) fn relexed_bytes(&self) -> usize {
        self.relexed_bytes.get()
    }
}

fn pound_run_bounds(tokens: &[ParserToken]) -> (Vec<usize>, Vec<usize>) {
    let mut starts = (0..tokens.len()).collect::<Vec<_>>();
    let mut ends = (1..=tokens.len()).collect::<Vec<_>>();
    let mut start = 0;
    while start < tokens.len() {
        if tokens[start].lexer_kind != TokenKind::Pound {
            start += 1;
            continue;
        }
        let mut end = start + 1;
        while end < tokens.len() && tokens[end].lexer_kind == TokenKind::Pound {
            end += 1;
        }
        starts[start..end].fill(start);
        ends[start..end].fill(end);
        start = end;
    }
    (starts, ends)
}

#[cfg(test)]
thread_local! {
    static PARSER_TOKEN_REWRITE_GUARD_BUILDS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_parser_token_rewrite_guard_build_count() {
    PARSER_TOKEN_REWRITE_GUARD_BUILDS.with(|count| count.set(0));
}

#[cfg(test)]
pub(crate) fn parser_token_rewrite_guard_build_count() -> usize {
    PARSER_TOKEN_REWRITE_GUARD_BUILDS.with(Cell::get)
}

#[derive(Clone, Copy)]
struct ParserTokenDeletionBoundary {
    deleted_start: usize,
    deleted_end: usize,
    left_start: usize,
    right_end: usize,
    window_start: u32,
    window_end: u32,
}

impl ParserTokenDeletionBoundary {
    fn window(self) -> ByteRange {
        ByteRange {
            start: self.window_start,
            end: self.window_end,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DelimiterPair {
    pub delimiter: Delimiter,
    pub open: usize,
    pub close: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct CommaListSegment {
    pub range: ByteRange,
    pub previous_comma: Option<ByteRange>,
    pub following_comma: Option<ByteRange>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SourceSyntaxError {
    InvalidRange,
    SourceTooLarge,
    InvalidSyntax,
}

pub(crate) fn is_trivia(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace
            | TokenKind::LineComment { doc_style: None }
            | TokenKind::BlockComment {
                doc_style: None,
                ..
            }
    )
}

/// Tokenizes source at the boundary used by rustc's token-tree parser.
/// `rustc_lexer` emits punctuation one character at a time, so adjacent
/// punctuation is glued with the pinned compiler's own rule.
pub(crate) fn tokenize_parser_tokens(source: &str) -> Result<Vec<ParserToken>, SourceSyntaxError> {
    let mut tokens: Vec<ParserToken> = Vec::new();
    let mut offset = 0_u32;
    let mut separated = true;
    for token in tokenize(source, FrontmatterAllowed::No) {
        let end = offset
            .checked_add(token.len)
            .ok_or(SourceSyntaxError::SourceTooLarge)?;
        let text = source
            .get(offset as usize..end as usize)
            .ok_or(SourceSyntaxError::InvalidSyntax)?;
        if is_trivia(token.kind) {
            separated = true;
            offset = end;
            continue;
        }

        let punctuation = parser_punctuation(text);
        if !separated
            && let Some(previous) = tokens.last_mut()
            && previous.range.end == offset
            && let (Some(previous_kind), Some(current_kind)) = (previous.punctuation, punctuation)
            && let Some(glued) =
                AstToken::new(previous_kind, DUMMY_SP).glue(&AstToken::new(current_kind, DUMMY_SP))
        {
            previous.range.end = end;
            previous.text.push_str(text);
            previous.punctuation = Some(glued.kind);
        } else {
            tokens.push(ParserToken {
                range: ByteRange { start: offset, end },
                text: text.to_owned(),
                lexer_kind: token.kind,
                punctuation,
            });
        }
        separated = false;
        offset = end;
    }
    if offset as usize != source.len() {
        return Err(SourceSyntaxError::InvalidSyntax);
    }
    Ok(tokens)
}

fn parser_punctuation(text: &str) -> Option<AstTokenKind> {
    Some(match text {
        "=" => AstTokenKind::Eq,
        "<" => AstTokenKind::Lt,
        ">" => AstTokenKind::Gt,
        "!" => AstTokenKind::Bang,
        "~" => AstTokenKind::Tilde,
        "+" => AstTokenKind::Plus,
        "-" => AstTokenKind::Minus,
        "*" => AstTokenKind::Star,
        "/" => AstTokenKind::Slash,
        "%" => AstTokenKind::Percent,
        "^" => AstTokenKind::Caret,
        "&" => AstTokenKind::And,
        "|" => AstTokenKind::Or,
        "@" => AstTokenKind::At,
        "." => AstTokenKind::Dot,
        "," => AstTokenKind::Comma,
        ";" => AstTokenKind::Semi,
        ":" => AstTokenKind::Colon,
        "#" => AstTokenKind::Pound,
        "$" => AstTokenKind::Dollar,
        "?" => AstTokenKind::Question,
        "'" => AstTokenKind::SingleQuote,
        _ => return None,
    })
}

pub(crate) fn tokenize_balanced_range(
    source: &str,
    range: ByteRange,
) -> Result<(Vec<SourceToken>, Vec<DelimiterPair>), SourceSyntaxError> {
    let input = source
        .get(range.start as usize..range.end as usize)
        .ok_or(SourceSyntaxError::InvalidRange)?;
    let mut offset = range.start;
    let mut tokens = Vec::new();
    let mut stack = Vec::new();
    let mut pairs = Vec::new();
    for token in tokenize(input, FrontmatterAllowed::No) {
        let end = offset
            .checked_add(token.len)
            .ok_or(SourceSyntaxError::SourceTooLarge)?;
        let index = tokens.len();
        if let Some(delimiter) = Delimiter::opening(token.kind) {
            stack.push((delimiter, index));
        } else if let Some(delimiter) = Delimiter::closing(token.kind) {
            let Some((opening, open)) = stack.pop() else {
                return Err(SourceSyntaxError::InvalidSyntax);
            };
            if opening != delimiter {
                return Err(SourceSyntaxError::InvalidSyntax);
            }
            pairs.push(DelimiterPair {
                delimiter,
                open,
                close: index,
            });
        }
        tokens.push(SourceToken {
            kind: token.kind,
            range: ByteRange { start: offset, end },
        });
        offset = end;
    }
    if offset != range.end || !stack.is_empty() {
        return Err(SourceSyntaxError::InvalidSyntax);
    }
    Ok((tokens, pairs))
}

pub(crate) fn comma_list_segments(
    tokens: &[SourceToken],
    pair: DelimiterPair,
) -> Result<Vec<CommaListSegment>, SourceSyntaxError> {
    let open = tokens
        .get(pair.open)
        .filter(|token| Delimiter::opening(token.kind) == Some(pair.delimiter))
        .ok_or(SourceSyntaxError::InvalidSyntax)?;
    let close = tokens
        .get(pair.close)
        .filter(|token| Delimiter::closing(token.kind) == Some(pair.delimiter))
        .ok_or(SourceSyntaxError::InvalidSyntax)?;
    if pair.open >= pair.close {
        return Err(SourceSyntaxError::InvalidSyntax);
    }

    let mut stack = Vec::new();
    let mut commas = Vec::new();
    for (index, token) in tokens
        .iter()
        .enumerate()
        .take(pair.close)
        .skip(pair.open + 1)
    {
        if let Some(delimiter) = Delimiter::opening(token.kind) {
            stack.push(delimiter);
            continue;
        }
        if let Some(delimiter) = Delimiter::closing(token.kind) {
            if stack.pop() != Some(delimiter) {
                return Err(SourceSyntaxError::InvalidSyntax);
            }
            continue;
        }
        if token.kind == TokenKind::Comma && stack.is_empty() {
            commas.push(index);
        }
    }
    if !stack.is_empty() {
        return Err(SourceSyntaxError::InvalidSyntax);
    }

    Ok((0..=commas.len())
        .map(|index| {
            let previous = index
                .checked_sub(1)
                .and_then(|index| commas.get(index).copied());
            let following = commas.get(index).copied();
            CommaListSegment {
                range: ByteRange {
                    start: previous.map_or(open.range.end, |comma| tokens[comma].range.end),
                    end: following.map_or(close.range.start, |comma| tokens[comma].range.start),
                },
                previous_comma: previous.map(|comma| tokens[comma].range),
                following_comma: following.map(|comma| tokens[comma].range),
            }
        })
        .collect())
}

#[cfg(test)]
mod parser_token_tests {
    use super::*;

    fn scanned_dependency_window(
        guard: &ParserTokenRewriteGuard<'_>,
        deletion: ByteRange,
    ) -> Option<ByteRange> {
        let mut deleted_end = guard
            .tokens
            .partition_point(|token| token.range.end <= deletion.start);
        let deleted_start = deleted_end;
        while let Some(token) = guard.tokens.get(deleted_end)
            && token.range.start < deletion.end
        {
            if !deletion.contains(token.range) {
                return None;
            }
            deleted_end += 1;
        }
        let mut left_start = deleted_start.saturating_sub(1);
        while left_start > 0 && guard.tokens[left_start].lexer_kind == TokenKind::Pound {
            left_start -= 1;
        }
        left_start = left_start.saturating_sub(1);
        let mut right_end = deleted_end;
        if right_end < guard.tokens.len() {
            right_end += 1;
            while right_end < guard.tokens.len()
                && guard.tokens[right_end - 1].lexer_kind == TokenKind::Pound
            {
                right_end += 1;
            }
            if right_end < guard.tokens.len() {
                right_end += 1;
            }
        }
        Some(ByteRange {
            start: if left_start < deleted_start {
                guard.tokens[left_start].range.start
            } else {
                deletion.start
            },
            end: if deleted_end < right_end {
                guard.tokens[right_end - 1].range.end
            } else {
                deletion.end
            },
        })
    }

    #[test]
    fn equal_text_with_a_different_lexer_kind_has_a_different_identity() {
        let identifier = tokenize_parser_tokens("foo").unwrap().remove(0);
        let unknown_prefix = tokenize_parser_tokens("foo\"bar\"").unwrap().remove(0);

        assert_eq!(identifier.text, unknown_prefix.text);
        assert_eq!(identifier.lexer_kind, TokenKind::Ident);
        assert_eq!(unknown_prefix.lexer_kind, TokenKind::UnknownPrefix);
        assert!(!identifier.same_identity(&unknown_prefix));
    }

    #[test]
    fn raw_and_guarded_lexer_kinds_remain_part_of_parser_token_identity() {
        let raw_identifier = tokenize_parser_tokens("r#name").unwrap().remove(0);
        let raw_lifetime = tokenize_parser_tokens("'r#name").unwrap().remove(0);
        let guarded_prefix = tokenize_parser_tokens("#\"").unwrap().remove(0);

        assert_eq!(raw_identifier.lexer_kind, TokenKind::RawIdent);
        assert_eq!(raw_lifetime.lexer_kind, TokenKind::RawLifetime);
        assert_eq!(guarded_prefix.lexer_kind, TokenKind::GuardedStrPrefix);
    }

    #[test]
    fn deletion_guard_looks_through_raw_identifier_lifetime_and_string_prefixes() {
        for (source, deletion) in [
            ("r #ident", ByteRange { start: 1, end: 2 }),
            ("'r #ident", ByteRange { start: 2, end: 3 }),
            ("br #\"body\"#", ByteRange { start: 2, end: 3 }),
            ("r###+\"body\"###", ByteRange { start: 4, end: 5 }),
        ] {
            let guard = ParserTokenRewriteGuard::new(source).unwrap();
            assert!(
                !guard.deletion_preserves_identity(deletion),
                "deleting {deletion:?} from {source:?} changes its tokenization and must be rejected"
            );
        }
    }

    #[test]
    fn many_deletion_checks_relex_only_their_local_token_boundaries() {
        const COUNT: usize = 1_024;
        let source = "foo+x>".repeat(COUNT);
        let guard = ParserTokenRewriteGuard::new(&source).unwrap();
        let deletions = (0..COUNT)
            .map(|index| {
                let start = (index * 6 + 4) as u32;
                ByteRange {
                    start,
                    end: start + 1,
                }
            })
            .collect::<Vec<_>>();

        assert!(
            deletions
                .iter()
                .all(|deletion| guard.deletion_preserves_identity(*deletion))
        );
        let checked_bytes = deletions
            .iter()
            .map(|deletion| guard.deletion_boundary_byte_len(*deletion).unwrap())
            .sum::<usize>();
        assert!(checked_bytes <= source.len() * 2);
    }

    #[test]
    fn precomputed_pound_runs_preserve_the_existing_dependency_windows() {
        for source in [
            "a b ### c d e",
            "### c d",
            "a b ###",
            "a # b ## c ### d",
            "r #ident br #\"body\"# r###+\"body\"###",
        ] {
            let guard = ParserTokenRewriteGuard::new(source).unwrap();
            for token in &guard.tokens {
                assert_eq!(
                    guard.deletion_dependency_window(token.range),
                    scanned_dependency_window(&guard, token.range),
                    "dependency window changed for {:?} in {source:?}",
                    token.text,
                );
            }
        }
    }

    #[test]
    fn alternating_deletions_in_one_pound_run_share_one_safe_cohort() {
        const COUNT: u32 = 32;
        let source = std::iter::repeat_n("#", COUNT as usize)
            .collect::<Vec<_>>()
            .join(" ");
        let guard = ParserTokenRewriteGuard::new(&source).unwrap();
        let deletions = (0..COUNT)
            .step_by(2)
            .map(|index| ByteRange {
                start: index * 2,
                end: index * 2 + 1,
            })
            .collect::<Vec<_>>();

        assert!(
            deletions
                .iter()
                .all(|&deletion| guard.deletion_preserves_identity(deletion))
        );
        assert!(
            deletions
                .iter()
                .all(|&deletion| guard.deletion_dependency_window(deletion)
                    == Some(ByteRange {
                        start: 0,
                        end: source.len() as u32,
                    }))
        );
        assert!(guard.deletions_preserve_identity(&deletions));
    }
}
