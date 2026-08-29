extern crate proc_macro;

use proc_macro::{Delimiter, Group, Spacing, Span, TokenStream, TokenTree};

fn with_span(input: TokenStream, span: Span) -> TokenStream {
    input
        .into_iter()
        .map(|token| match token {
            TokenTree::Group(group) => {
                let mut output = Group::new(group.delimiter(), with_span(group.stream(), span));
                output.set_span(span);
                TokenTree::Group(output)
            }
            TokenTree::Ident(mut identifier) => {
                identifier.set_span(span);
                TokenTree::Ident(identifier)
            }
            TokenTree::Punct(mut punctuation) => {
                punctuation.set_span(span);
                TokenTree::Punct(punctuation)
            }
            TokenTree::Literal(mut literal) => {
                literal.set_span(span);
                TokenTree::Literal(literal)
            }
        })
        .collect()
}

fn with_first_input_span(input: TokenStream, output: &str) -> TokenStream {
    let span = input
        .into_iter()
        .next()
        .expect("the marker token must be present")
        .span();
    with_span(
        output.parse().expect("the generated tokens must parse"),
        span,
    )
}

fn contains_identifier(input: TokenStream, expected: &str) -> bool {
    input.into_iter().any(|token| match token {
        TokenTree::Group(group) => contains_identifier(group.stream(), expected),
        TokenTree::Ident(identifier) => identifier.to_string() == expected,
        TokenTree::Literal(_) | TokenTree::Punct(_) => false,
    })
}

fn contains_group_starting_with_comma(input: TokenStream) -> bool {
    input.into_iter().any(|token| match token {
        TokenTree::Group(group) => {
            matches!(group.stream().into_iter().next(), Some(TokenTree::Punct(punctuation)) if punctuation.as_char() == ',')
                || contains_group_starting_with_comma(group.stream())
        }
        TokenTree::Ident(_) | TokenTree::Literal(_) | TokenTree::Punct(_) => false,
    })
}

fn contains_joint_comma_before(input: TokenStream, expected: &str) -> bool {
    let tokens = input.into_iter().collect::<Vec<_>>();
    tokens.windows(2).any(|pair| {
        matches!(
            pair,
            [TokenTree::Punct(punctuation), TokenTree::Ident(identifier)]
                if punctuation.as_char() == ','
                    && punctuation.spacing() == Spacing::Joint
                    && identifier.to_string() == expected
        )
    }) || tokens.into_iter().any(|token| match token {
        TokenTree::Group(group) => contains_joint_comma_before(group.stream(), expected),
        TokenTree::Ident(_) | TokenTree::Literal(_) | TokenTree::Punct(_) => false,
    })
}

#[proc_macro]
pub fn one(_input: TokenStream) -> TokenStream {
    "1".parse().expect("the generated expression must parse")
}

#[proc_macro]
pub fn make_unused(_input: TokenStream) -> TokenStream {
    "fn generated_unused() {}"
        .parse()
        .expect("the generated item must parse")
}

#[proc_macro]
pub fn empty(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro]
pub fn make_assembly(_input: TokenStream) -> TokenStream {
    "fn generated_assembly() { unsafe { core::arch::asm!(\"\"); } }"
        .parse()
        .expect("the generated assembly function must parse")
}

#[proc_macro]
pub fn emit_input_spanned_local(input: TokenStream) -> TokenStream {
    with_first_input_span(input, "local!();")
}

#[proc_macro]
pub fn emit_input_spanned_relay(input: TokenStream) -> TokenStream {
    with_first_input_span(input, "relay!(local!(););")
}

#[proc_macro]
pub fn configured_bang(input: TokenStream) -> TokenStream {
    assert!(!contains_identifier(input, "cfg_attr"));
    "fn generated() -> i32 { 1 }"
        .parse()
        .expect("the generated item must parse")
}

#[proc_macro]
pub fn punct_spacing(input: TokenStream) -> TokenStream {
    let mut tokens = input.into_iter();
    let punctuation = match (tokens.next(), tokens.next()) {
        (Some(TokenTree::Punct(punctuation)), None) => punctuation,
        _ => panic!("punct_spacing expects exactly one punctuation token"),
    };
    let result = match punctuation.spacing() {
        Spacing::Joint => "\"Joint\"",
        Spacing::Alone => "\"Alone\"",
    };
    result
        .parse()
        .expect("the generated string literal must parse")
}

#[proc_macro]
pub fn last_punct_spacing(input: TokenStream) -> TokenStream {
    fn tail_punctuation(input: TokenStream) -> Option<Option<Spacing>> {
        let mut last = None;
        for token in input {
            let current = match token {
                TokenTree::Group(group) if group.delimiter() == Delimiter::None => {
                    let Some(tail) = tail_punctuation(group.stream()) else {
                        continue;
                    };
                    tail
                }
                TokenTree::Punct(punctuation) => Some(punctuation.spacing()),
                TokenTree::Group(_) | TokenTree::Ident(_) | TokenTree::Literal(_) => None,
            };
            last = Some(current);
        }
        last
    }

    let result = match tail_punctuation(input) {
        Some(Some(Spacing::Joint)) => "\"Joint\"",
        Some(Some(Spacing::Alone)) => "\"Alone\"",
        None | Some(None) => panic!("last_punct_spacing expects a trailing punctuation token"),
    };
    result
        .parse()
        .expect("the generated string literal must parse")
}

#[proc_macro_attribute]
pub fn passthrough(_attribute: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn empty_attribute(_attribute: TokenStream, _item: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[proc_macro_attribute]
pub fn require_nested_cfg_attr(_attribute: TokenStream, item: TokenStream) -> TokenStream {
    assert!(contains_identifier(item.clone(), "cfg_attr"));
    item
}

#[proc_macro_derive(Answer)]
pub fn answer(input: TokenStream) -> TokenStream {
    let mut saw_item_kind = false;
    let name = input
        .into_iter()
        .find_map(|token| match token {
            TokenTree::Ident(identifier) if saw_item_kind => Some(identifier.to_string()),
            TokenTree::Ident(identifier)
                if matches!(identifier.to_string().as_str(), "struct" | "enum" | "union") =>
            {
                saw_item_kind = true;
                None
            }
            _ => None,
        })
        .expect("derive input must contain an item name");
    format!("impl {name} {{ fn answer() -> i32 {{ 1 }} }}")
        .parse()
        .expect("the generated impl must parse")
}

#[proc_macro_derive(ConfiguredInput)]
pub fn configured_input(input: TokenStream) -> TokenStream {
    assert!(!contains_identifier(input, "cfg_attr"));
    TokenStream::new()
}

#[proc_macro_derive(ConfiguredPunctuation)]
pub fn configured_punctuation(input: TokenStream) -> TokenStream {
    assert!(contains_group_starting_with_comma(input.clone()));
    assert!(contains_joint_comma_before(input, "tail"));
    TokenStream::new()
}

#[proc_macro]
pub fn panic_bang(_input: TokenStream) -> TokenStream {
    panic!("the denied function-like macro must not execute")
}

#[proc_macro_attribute]
pub fn panic_attr(_attribute: TokenStream, _item: TokenStream) -> TokenStream {
    panic!("the denied attribute macro must not execute")
}

#[proc_macro_derive(PanicDerive)]
pub fn panic_derive(_input: TokenStream) -> TokenStream {
    panic!("the denied derive macro must not execute")
}
