//! Shared lexical structure for comma-separated Rust source lists.

use rustc_lexer::{FrontmatterAllowed, TokenKind, tokenize};

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
