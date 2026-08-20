#![feature(rustc_private)]

extern crate rustc_driver;

fn main() {
    let expected_abi = include_str!("../../../rustc-patches/patch-abi")
        .trim()
        .parse::<u32>()
        .expect("patch-abi must contain a u32");
    assert_eq!(
        rustc_driver::RUST_ITEM_DEPENDENCIES_BASE_REVISION,
        "969b803cbe1d4499f841ae0a49c637d8c70a0458"
    );
    assert_eq!(rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_ABI, expected_abi);
    assert_eq!(
        rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST,
        include_str!("../../../rustc-patches/queue-digest").trim()
    );
}
