extern crate proc_macro;

use proc_macro::{TokenStream, TokenTree};

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

#[proc_macro_attribute]
pub fn passthrough(_attribute: TokenStream, item: TokenStream) -> TokenStream {
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
