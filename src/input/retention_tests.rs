use std::collections::BTreeSet;
#[cfg(rust_item_dependencies_patched)]
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
#[cfg(rust_item_dependencies_patched)]
use std::process::Stdio;

use super::{Edition, SourceInput, inspect_source};
#[cfg(rust_item_dependencies_patched)]
use super::{inspect_source_with_definitions, inspect_source_with_reduction};
#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{DependencyGraph, GraphNode};
#[cfg(rust_item_dependencies_patched)]
use crate::graph::{
    DefinitionGraph, DefinitionId, DefinitionKey, DefinitionOrigin, DefinitionTarget,
    DependencyKind as DefinitionDependencyKind,
};
use crate::rewrite::{SourceRewrite, rewrite_source};
use crate::source::{ByteRange, SourceInventory, WrittenUnitKind};

const ITEM_INPUT: &str = include_str!("../../tests/fixtures/retention/item_nested_module.input.rs");
const ITEM_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/item_nested_module.expected.rs");
const MACRO_INPUT: &str = include_str!("../../tests/fixtures/retention/macro_fixed_point.input.rs");
const MACRO_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/macro_fixed_point.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const DIRECT_MACRO_INPUT: &str =
    include_str!("../../tests/fixtures/retention/direct_macro_retention.input.rs");
#[cfg(rust_item_dependencies_patched)]
const DIRECT_MACRO_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/direct_macro_retention.expected.rs");
const MEMBER_INPUT: &str =
    include_str!("../../tests/fixtures/retention/trait_impl_members.input.rs");
const MEMBER_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/trait_impl_members.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const IMPL_SHELL_INPUT: &str = include_str!("../../tests/fixtures/retention/impl_shells.input.rs");
#[cfg(rust_item_dependencies_patched)]
const IMPL_SHELL_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/impl_shells.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const MACRO_IMPL_MEMBER_INPUT: &str =
    include_str!("../../tests/fixtures/retention/macro_generated_impl_member.input.rs");
#[cfg(rust_item_dependencies_patched)]
const MACRO_IMPL_MEMBER_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/macro_generated_impl_member.expected.rs");
const USE_INPUT: &[u8] = include_bytes!("../../tests/fixtures/retention/use_matrix.input.rs");
const USE_FIRST: &[u8] =
    include_bytes!("../../tests/fixtures/retention/use_matrix_first.expected.rs");
const USE_MIDDLE: &[u8] =
    include_bytes!("../../tests/fixtures/retention/use_matrix_middle.expected.rs");
const USE_LAST: &[u8] =
    include_bytes!("../../tests/fixtures/retention/use_matrix_last.expected.rs");
const USE_ALL: &[u8] = include_bytes!("../../tests/fixtures/retention/use_matrix_all.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const USE_RESOLUTION_INPUT: &str =
    include_str!("../../tests/fixtures/retention/use_resolution.input.rs");
#[cfg(rust_item_dependencies_patched)]
const USE_RESOLUTION_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/use_resolution.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const SYSROOT_MACRO_INPUT: &str =
    include_str!("../../tests/fixtures/retention/sysroot_macro_fixed_point.input.rs");
#[cfg(rust_item_dependencies_patched)]
const SYSROOT_MACRO_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/sysroot_macro_fixed_point.expected.rs");
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_IMPL_INPUT: &str = "trait T{fn f(&self);} struct S; impl T for S{fn f(&self){}} macro_rules! m{()=>{fn main(){} fn sibling(){S.f();}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_DEFAULT_IMPL_INPUT: &str = "trait T{fn f(&self){}} struct S; impl T for S{} macro_rules! m{()=>{fn main(){} fn sibling(){S.f();}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_BLANKET_IMPL_INPUT: &str = "trait T{fn f(&self);} struct S; impl<U> T for U{fn f(&self){}} macro_rules! m{()=>{fn main(){} fn sibling(){S.f();}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_IMPL_INPUT: &str = "trait Bound{} trait T{fn f(&self);} struct S; impl Bound for S{} struct Wrap<U>(U); impl<U:Bound> T for Wrap<U>{fn f(&self){}} macro_rules! m{()=>{fn main(){} fn sibling(){Wrap(S).f();}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_WHERE_CLAUSE_INPUT: &str = "trait T{} struct S; impl T for S{} macro_rules! m{()=>{fn main(){} fn sibling() where S:T {}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_ASSOC_CONST_SIGNATURE_INPUT: &str = "trait T{const N:usize;} struct S; impl T for S{const N:usize=1;} macro_rules! m{()=>{fn main(){} fn sibling(_: [(); <S as T>::N]){}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_ASSOC_TYPE_SIGNATURE_INPUT: &str = "trait T{type A;} struct S; impl T for S{type A=();} macro_rules! m{()=>{fn main(){} fn sibling(_: <S as T>::A){}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_OVERLOADED_AUTODEREF_INPUT: &str = "trait T{fn f(&self);} struct S; impl T for S{fn f(&self){}} struct W(S); impl std::ops::Deref for W{type Target=S;fn deref(&self)->&S{&self.0}} macro_rules! m{()=>{fn main(){} fn sibling(w:W){w.f();}}} m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_AUTODEREF_INPUT: &str = "trait Bound{}trait T{fn f(&self);}struct S;impl Bound for S{}impl T for S{fn f(&self){}}struct W<U>(U);impl<U:Bound> std::ops::Deref for W<U>{type Target=U;fn deref(&self)->&U{&self.0}}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling(w:W<S>){w.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_AUTODEREF_EXPECTED: &str = "trait Bound{}trait T{fn f(&self);}struct S;impl Bound for S{}impl T for S{fn f(&self){}}struct W<U>(U);impl<U:Bound> std::ops::Deref for W<U>{type Target=U;fn deref(&self)->&U{&self.0}}macro_rules! m{()=>{fn main(){}fn sibling(w:W<S>){w.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_GENERIC_BLANKET_INPUT: &str = "trait T{fn f(&self);}impl<U> T for U{fn f(&self){}}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling<U>(u:U){u.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_GENERIC_BLANKET_EXPECTED: &str = "trait T{fn f(&self);}impl<U> T for U{fn f(&self){}}macro_rules! m{()=>{fn main(){}fn sibling<U>(u:U){u.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_PARAM_INPUT: &str = "trait T{fn f(&self);}struct S;impl T for S{fn f(&self){}}macro_rules! m{()=>{fn main(){}fn sibling<U:T>(u:U){u.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_PARAM_EXPECTED: &str =
    "trait T{fn f(&self);}macro_rules! m{()=>{fn main(){}fn sibling<U:T>(u:U){u.f();}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_SIGNATURE_WF_INPUT: &str = "trait B{}struct Need<T:B>(T);struct S;impl B for S{}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling(_:Need<S>){}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_SIGNATURE_WF_EXPECTED: &str = "trait B{}struct Need<T:B>(T);struct S;impl B for S{}macro_rules! m{()=>{fn main(){}fn sibling(_:Need<S>){}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_SIGNATURE_WF_FORMS_INPUT: &str = "trait B{}struct S;impl B for S{}struct X<U:B=S>(U);trait Outer:B{}impl Outer for S{}trait T{type A:B;}impl T for S{type A=S;}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling(_:X,_:<S as T>::A)where S:Outer{}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_SIGNATURE_WF_FORMS_EXPECTED: &str = "trait B{}struct S;impl B for S{}struct X<U:B=S>(U);trait Outer:B{}impl Outer for S{}trait T{type A:B;}impl T for S{type A=S;}macro_rules! m{()=>{fn main(){}fn sibling(_:X,_:<S as T>::A)where S:Outer{}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_EXTERNAL_DEFAULT_OVERRIDE_INPUT: &str = "struct Reader;impl std::io::Read for Reader{fn read(&mut self,_:&mut[u8])->std::io::Result<usize>{Ok(0)}fn read_to_end(&mut self,_:&mut Vec<u8>)->std::io::Result<usize>{Ok(1)}fn read_to_string(&mut self,_:&mut String)->std::io::Result<usize>{Ok(2)}}macro_rules! m{()=>{fn main(){}fn sibling(){let mut r=Reader;let _=std::io::Read::read_to_end(&mut r,&mut Vec::new());}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_EXTERNAL_DEFAULT_OVERRIDE_EXPECTED: &str = "struct Reader;impl std::io::Read for Reader{fn read(&mut self,_:&mut[u8])->std::io::Result<usize>{Ok(0)}fn read_to_end(&mut self,_:&mut Vec<u8>)->std::io::Result<usize>{Ok(1)}}macro_rules! m{()=>{fn main(){}fn sibling(){let mut r=Reader;let _=std::io::Read::read_to_end(&mut r,&mut Vec::new());}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_COPY_INPUT: &str = "struct Inner;impl Clone for Inner{fn clone(&self)->Self{Inner}}impl Copy for Inner{}struct Outer(Inner);impl Clone for Outer{fn clone(&self)->Self{*self}}impl Copy for Outer{}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling(){require_copy::<Outer>();}fn require_copy<T:Copy>(){}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_COPY_EXPECTED: &str = "struct Inner;impl Clone for Inner{fn clone(&self)->Self{Inner}}impl Copy for Inner{}struct Outer(Inner);impl Clone for Outer{fn clone(&self)->Self{*self}}impl Copy for Outer{}macro_rules! m{()=>{fn main(){}fn sibling(){require_copy::<Outer>();}fn require_copy<T:Copy>(){}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const ORDINARY_COPY_MOVE_INPUT: &str = "struct S;impl Clone for S{fn clone(&self)->Self{S}}impl Copy for S{}struct Dead;fn main(){let x=S;let _a=x;let _b=x;}";
#[cfg(rust_item_dependencies_patched)]
const ORDINARY_COPY_MOVE_EXPECTED: &str = "struct S;impl Clone for S{fn clone(&self)->Self{S}}impl Copy for S{}fn main(){let x=S;let _a=x;let _b=x;}";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_DROP_INPUT: &str = "struct Value;impl Drop for Value{fn drop(&mut self){}}struct Dead;macro_rules! m{()=>{fn main(){}fn sibling(_:Value){}}}m!();";
#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_DROP_EXPECTED: &str = "struct Value;impl Drop for Value{fn drop(&mut self){}}macro_rules! m{()=>{fn main(){}fn sibling(_:Value){}}}m!();";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct UnitRef {
    kind: WrittenUnitKind,
    range: ByteRange,
}

const ITEM_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 170),
    unit(WrittenUnitKind::InlineModule, 17, 129),
    unit(WrittenUnitKind::Item, 50, 92),
    unit(WrittenUnitKind::Item, 92, 105),
    unit(WrittenUnitKind::Item, 129, 153),
];

const MACRO_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 212),
    unit(WrittenUnitKind::MacroDefinition, 0, 94),
    #[cfg(rust_item_dependencies_patched)]
    unit(WrittenUnitKind::MacroRule, 21, 93),
    unit(WrittenUnitKind::Item, 94, 119),
    unit(WrittenUnitKind::MacroInvocation, 130, 141),
];

#[cfg(rust_item_dependencies_patched)]
const DIRECT_MACRO_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 62),
    unit(WrittenUnitKind::Item, 33, 61),
    unit(WrittenUnitKind::MacroInvocation, 43, 60),
];

#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_IMPL_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 120),
    unit(WrittenUnitKind::Item, 0, 21),
    unit(WrittenUnitKind::TraitMember, 8, 20),
    unit(WrittenUnitKind::Item, 22, 31),
    unit(WrittenUnitKind::Item, 32, 59),
    unit(WrittenUnitKind::ImplMember, 45, 58),
    unit(WrittenUnitKind::MacroDefinition, 60, 114),
    unit(WrittenUnitKind::MacroRule, 75, 113),
    unit(WrittenUnitKind::MacroInvocation, 115, 120),
];

#[cfg(rust_item_dependencies_patched)]
const GENERATED_SIBLING_NESTED_COPY_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 290),
    unit(WrittenUnitKind::Item, 0, 13),
    unit(WrittenUnitKind::Item, 13, 63),
    unit(WrittenUnitKind::ImplMember, 34, 62),
    unit(WrittenUnitKind::Item, 63, 84),
    unit(WrittenUnitKind::Item, 84, 104),
    unit(WrittenUnitKind::Item, 104, 154),
    unit(WrittenUnitKind::ImplMember, 125, 153),
    unit(WrittenUnitKind::Item, 154, 175),
    unit(WrittenUnitKind::MacroDefinition, 187, 285),
    unit(WrittenUnitKind::MacroRule, 202, 284),
    unit(WrittenUnitKind::MacroInvocation, 285, 290),
];

#[cfg(rust_item_dependencies_patched)]
const ORDINARY_COPY_MOVE_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 117),
    unit(WrittenUnitKind::Item, 0, 9),
    unit(WrittenUnitKind::Item, 9, 51),
    unit(WrittenUnitKind::ImplMember, 26, 50),
    unit(WrittenUnitKind::Item, 51, 68),
    unit(WrittenUnitKind::Item, 80, 117),
];

const MEMBER_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 821),
    unit(WrittenUnitKind::Item, 0, 222),
    unit(WrittenUnitKind::TraitMember, 68, 80),
    unit(WrittenUnitKind::TraitMember, 80, 97),
    unit(WrittenUnitKind::TraitMember, 97, 125),
    unit(WrittenUnitKind::TraitMember, 125, 163),
    unit(WrittenUnitKind::TraitMember, 163, 189),
    unit(WrittenUnitKind::Item, 222, 236),
    unit(WrittenUnitKind::Item, 236, 421),
    unit(WrittenUnitKind::ImplMember, 293, 311),
    unit(WrittenUnitKind::ImplMember, 311, 330),
    unit(WrittenUnitKind::ImplMember, 330, 362),
    unit(WrittenUnitKind::ImplMember, 362, 388),
    unit(WrittenUnitKind::Item, 421, 668),
    unit(WrittenUnitKind::ImplMember, 520, 582),
    unit(WrittenUnitKind::Item, 668, 820),
];

#[cfg(rust_item_dependencies_patched)]
const SYSROOT_MACRO_RETAINED: &[UnitRef] = &[
    unit(WrittenUnitKind::CrateRoot, 0, 172),
    unit(WrittenUnitKind::Item, 0, 37),
    unit(WrittenUnitKind::MacroInvocation, 37, 115),
    unit(WrittenUnitKind::Item, 126, 171),
];

const USE_LEAVES: &[UnitRef] = &[
    unit(WrittenUnitKind::UseLeaf, 99, 119),
    unit(WrittenUnitKind::UseLeaf, 128, 140),
    unit(WrittenUnitKind::UseLeaf, 152, 163),
    unit(WrittenUnitKind::UseLeaf, 164, 176),
    unit(WrittenUnitKind::UseLeaf, 179, 180),
];

const fn unit(kind: WrittenUnitKind, start: u32, end: u32) -> UnitRef {
    UnitRef {
        kind,
        range: ByteRange { start, end },
    }
}

#[test]
fn retention_fixtures_have_exact_independent_byte_oracles() {
    assert_eq!((ITEM_INPUT.len(), ITEM_EXPECTED.len()), (170, 72));
    assert_eq!((MACRO_INPUT.len(), MACRO_EXPECTED.len()), (212, 131));
    #[cfg(rust_item_dependencies_patched)]
    assert_eq!(
        (DIRECT_MACRO_INPUT.len(), DIRECT_MACRO_EXPECTED.len()),
        (62, 29)
    );
    assert_eq!((MEMBER_INPUT.len(), MEMBER_EXPECTED.len()), (821, 498));
    assert_eq!(
        (
            USE_INPUT.len(),
            USE_FIRST.len(),
            USE_MIDDLE.len(),
            USE_LAST.len(),
            USE_ALL.len(),
        ),
        (198, 185, 175, 185, 139)
    );

    assert!(!ITEM_EXPECTED.contains("dead_"));
    assert!(MACRO_EXPECTED.contains("sibling_dependency"));
    assert!(!MACRO_EXPECTED.contains("fn dead()"));
    assert!(MACRO_INPUT.contains("dead_program!()"));
    assert!(MACRO_INPUT.contains("dead_generated"));
    assert!(!MACRO_EXPECTED.contains("dead_program"));
    assert!(!MACRO_EXPECTED.contains("dead_generated"));
    assert!(!MEMBER_EXPECTED.contains("unused_"));
    assert!(!MEMBER_EXPECTED.contains("dead_"));

    for source in [USE_INPUT, USE_FIRST, USE_MIDDLE, USE_LAST, USE_ALL] {
        assert!(source.starts_with(&[0xef, 0xbb, 0xbf]));
        assert_crlf_only(source);
        std::str::from_utf8(source).expect("the byte oracle must remain UTF-8");
    }
    assert!(contains(USE_FIRST, "/* 二 */".as_bytes()));
    assert!(!contains(USE_MIDDLE, "/* 二 */".as_bytes()));
    assert!(contains(USE_LAST, "/* 二 */".as_bytes()));
    assert!(!contains(USE_ALL, "/* 二 */".as_bytes()));
}

#[test]
fn source_inventory_contains_every_handwritten_retention_unit() {
    assert_inventory_units(&inspect_inventory(ITEM_INPUT), ITEM_RETAINED);
    assert_inventory_units(&inspect_inventory(MACRO_INPUT), MACRO_RETAINED);
    #[cfg(rust_item_dependencies_patched)]
    assert_inventory_units(
        &inspect_inventory(DIRECT_MACRO_INPUT),
        DIRECT_MACRO_RETAINED,
    );
    assert_inventory_units(&inspect_inventory(MEMBER_INPUT), MEMBER_RETAINED);
    let use_source = std::str::from_utf8(USE_INPUT).expect("the use fixture must be UTF-8");
    assert_inventory_units(&inspect_inventory(use_source), USE_LEAVES);
    #[cfg(rust_item_dependencies_patched)]
    assert_inventory_units(
        &inspect_inventory(SYSROOT_MACRO_INPUT),
        SYSROOT_MACRO_RETAINED,
    );
}

#[test]
fn use_leaf_matrix_rewrites_exact_original_bytes() {
    let source = std::str::from_utf8(USE_INPUT).expect("the use fixture must be UTF-8");
    let inventory = inspect_inventory(source);
    for (removed, expected) in [
        (&[(128, 140)][..], USE_FIRST),
        (&[(152, 163)][..], USE_MIDDLE),
        (&[(164, 176)][..], USE_LAST),
        (&[(128, 140), (152, 163), (164, 176)][..], USE_ALL),
    ] {
        let retained = retained_except_ranges(&inventory, removed);
        let first = rewrite_source(&inventory, &retained).expect("use rewrite must be complete");
        let second =
            rewrite_source(&inventory, &retained).expect("use rewrite must be deterministic");
        assert_eq!(first, second);
        assert_eq!(first.source.as_bytes(), expected);
        assert_piece_map(&inventory, &first);
    }
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn compiler_retention_rewrites_the_handwritten_fixtures_exactly() {
    for (input, expected, expected_units) in [
        (ITEM_INPUT, ITEM_EXPECTED, ITEM_RETAINED),
        (MACRO_INPUT, MACRO_EXPECTED, MACRO_RETAINED),
        (
            DIRECT_MACRO_INPUT,
            DIRECT_MACRO_EXPECTED,
            DIRECT_MACRO_RETAINED,
        ),
        (MEMBER_INPUT, MEMBER_EXPECTED, MEMBER_RETAINED),
    ] {
        let reduced = inspect_reduction(input);
        assert_eq!(reduced.rewrite.source, expected);
        assert_piece_map(&reduced.source, &reduced.rewrite);
        assert_retained_units(&reduced, expected_units);
    }
    for (input, expected) in [(USE_RESOLUTION_INPUT, USE_RESOLUTION_EXPECTED)] {
        let reduced = inspect_reduction(input);
        assert_eq!(reduced.rewrite.source, expected);
        assert_piece_map(&reduced.source, &reduced.rewrite);
    }
    let sysroot = inspect_reduction(SYSROOT_MACRO_INPUT);
    assert_eq!(sysroot.rewrite.source, SYSROOT_MACRO_EXPECTED);
    assert_piece_map(&sysroot.source, &sysroot.rewrite);
    assert_retained_units(&sysroot, SYSROOT_MACRO_RETAINED);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn empty_use_item_is_a_valid_deletion_unit() {
    let first = inspect_reduction("use {};fn main(){}");
    assert_eq!(
        source_units_of_kind(&first.source, WrittenUnitKind::UseItem),
        BTreeSet::from(["use {};".to_owned()]),
    );
    assert!(
        source_units_of_kind(&first.source, WrittenUnitKind::UseLeaf).is_empty(),
        "an empty use tree must not invent an import leaf"
    );
    assert_eq!(
        source_units_of_kind(&first.source, WrittenUnitKind::Item),
        BTreeSet::from(["fn main(){}".to_owned()]),
    );
    assert_eq!(
        retained_units_of_kind(&first, WrittenUnitKind::Item),
        BTreeSet::from(["fn main(){}".to_owned()]),
    );
    assert_eq!(first.rewrite.source, "fn main(){}");
    assert_piece_map(&first.source, &first.rewrite);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn selected_empty_trait_impl_shell_survives_unused_inherent_impl() {
    let reduced = inspect_reduction(IMPL_SHELL_INPUT);

    assert_eq!(reduced.rewrite.source, IMPL_SHELL_EXPECTED);
    assert_piece_map(&reduced.source, &reduced.rewrite);
    assert!(!reduced.rewrite.source.contains("impl Used"));
    assert!(reduced.rewrite.source.contains("unsafe trait Marker {}"));
    assert!(
        reduced
            .rewrite
            .source
            .contains("unsafe impl Marker for Used {}")
    );

    let reparsed = inspect_inventory(&reduced.rewrite.source);
    assert_eq!(reparsed.original.as_ref(), reduced.rewrite.source.as_str());
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn must_implement_one_of_accepts_a_macro_generated_impl_member() {
    let reduced = inspect_reduction(MACRO_IMPL_MEMBER_INPUT);

    assert_eq!(reduced.rewrite.source, MACRO_IMPL_MEMBER_EXPECTED);
    assert_piece_map(&reduced.source, &reduced.rewrite);
    assert_eq!(
        source_units_of_kind(&reduced.source, WrittenUnitKind::MacroInvocation),
        BTreeSet::from(["implement_read!();".to_owned()]),
    );
    assert_eq!(
        retained_units_of_kind(&reduced, WrittenUnitKind::MacroInvocation),
        BTreeSet::from(["implement_read!();".to_owned()]),
    );
    assert!(reduced.rewrite.source.contains("impl std::io::Read"));
    assert!(!reduced.rewrite.source.contains("fn dead()"));

    let second = inspect_reduction(&reduced.rewrite.source);
    assert_eq!(second.rewrite.source, reduced.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn macro_fixed_points_are_byte_idempotent() {
    for input in [MACRO_INPUT, DIRECT_MACRO_INPUT, SYSROOT_MACRO_INPUT] {
        let first = inspect_reduction(input);
        let second = inspect_reduction(&first.rewrite.source);
        assert_eq!(second.rewrite.source, first.rewrite.source);
        assert_piece_map(&second.source, &second.rewrite);
    }
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_method_keeps_the_required_impl_shell() {
    let first = inspect_reduction(GENERATED_SIBLING_IMPL_INPUT);

    assert_eq!(first.rewrite.source, GENERATED_SIBLING_IMPL_INPUT);
    assert_retained_units(&first, GENERATED_SIBLING_IMPL_RETAINED);
    assert_piece_map(&first.source, &first.rewrite);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_keeps_default_blanket_and_nested_local_impls() {
    for (case, source) in [
        ("default method", GENERATED_SIBLING_DEFAULT_IMPL_INPUT),
        ("blanket impl", GENERATED_SIBLING_BLANKET_IMPL_INPUT),
        ("nested obligation", GENERATED_SIBLING_NESTED_IMPL_INPUT),
    ] {
        let first = inspect_reduction(source);
        assert_eq!(first.rewrite.source, source, "{case}");
        assert_piece_map(&first.source, &first.rewrite);

        let second = inspect_reduction(&first.rewrite.source);
        assert_eq!(second.rewrite.source, first.rewrite.source, "{case}");
    }
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_where_clause_keeps_the_required_impl() {
    assert_generated_sibling_unchanged(GENERATED_SIBLING_WHERE_CLAUSE_INPUT);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_associated_const_signature_keeps_the_required_impl() {
    assert_generated_sibling_unchanged(GENERATED_SIBLING_ASSOC_CONST_SIGNATURE_INPUT);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_associated_type_signature_keeps_the_required_impl() {
    assert_generated_sibling_unchanged(GENERATED_SIBLING_ASSOC_TYPE_SIGNATURE_INPUT);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_overloaded_autoderef_keeps_the_required_impls() {
    assert_generated_sibling_unchanged(GENERATED_SIBLING_OVERLOADED_AUTODEREF_INPUT);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_autoderef_keeps_the_nested_bound_impl() {
    let first = inspect_reduction(GENERATED_SIBLING_NESTED_AUTODEREF_INPUT);

    assert_eq!(
        first.rewrite.source,
        GENERATED_SIBLING_NESTED_AUTODEREF_EXPECTED
    );
    assert_piece_map(&first.source, &first.rewrite);
    assert!(!first.rewrite.source.contains("struct Dead"));

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generic_user_defined_and_param_selections_retain_different_impls() {
    let blanket = inspect_reduction(GENERATED_SIBLING_GENERIC_BLANKET_INPUT);
    assert_eq!(
        blanket.rewrite.source,
        GENERATED_SIBLING_GENERIC_BLANKET_EXPECTED
    );
    assert_piece_map(&blanket.source, &blanket.rewrite);
    let blanket_again = inspect_reduction(&blanket.rewrite.source);
    assert_eq!(blanket_again.rewrite.source, blanket.rewrite.source);

    let parameter = inspect_reduction(GENERATED_SIBLING_PARAM_INPUT);
    assert_eq!(parameter.rewrite.source, GENERATED_SIBLING_PARAM_EXPECTED);
    assert_piece_map(&parameter.source, &parameter.rewrite);
    let parameter_again = inspect_reduction(&parameter.rewrite.source);
    assert_eq!(parameter_again.rewrite.source, parameter.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_signature_well_formedness_keeps_the_selected_impl() {
    let first = inspect_reduction(GENERATED_SIBLING_SIGNATURE_WF_INPUT);

    assert_eq!(
        first.rewrite.source,
        GENERATED_SIBLING_SIGNATURE_WF_EXPECTED
    );
    assert_piece_map(&first.source, &first.rewrite);
    assert!(!first.rewrite.source.contains("struct Dead"));

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_signature_well_formedness_covers_defaults_and_supertraits() {
    let first = inspect_reduction(GENERATED_SIBLING_SIGNATURE_WF_FORMS_INPUT);

    assert_eq!(
        first.rewrite.source,
        GENERATED_SIBLING_SIGNATURE_WF_FORMS_EXPECTED
    );
    assert_piece_map(&first.source, &first.rewrite);
    assert!(first.rewrite.source.contains("impl B for S"));
    assert!(!first.rewrite.source.contains("struct Dead"));

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_external_default_override_retains_only_the_selected_member() {
    let first = inspect_reduction(GENERATED_SIBLING_EXTERNAL_DEFAULT_OVERRIDE_INPUT);

    assert_eq!(
        first.rewrite.source,
        GENERATED_SIBLING_EXTERNAL_DEFAULT_OVERRIDE_EXPECTED
    );
    assert_piece_map(&first.source, &first.rewrite);
    assert_eq!(
        retained_units_of_kind(&first, WrittenUnitKind::ImplMember),
        BTreeSet::from([
            "fn read(&mut self,_:&mut[u8])->std::io::Result<usize>{Ok(0)}".to_owned(),
            "fn read_to_end(&mut self,_:&mut Vec<u8>)->std::io::Result<usize>{Ok(1)}".to_owned(),
        ])
    );
    let impl_shell = first
        .source
        .units
        .iter()
        .find(|unit| {
            unit.kind == WrittenUnitKind::Item
                && first.source.original
                    [unit.full_range.start as usize..unit.full_range.end as usize]
                    .starts_with("impl std::io::Read for Reader")
        })
        .expect("the external trait impl must have one handwritten shell");
    assert!(first.retention.retained_units.contains(&impl_shell.id));

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_copy_keeps_nested_manual_copy_coherence() {
    let first = inspect_reduction(GENERATED_SIBLING_NESTED_COPY_INPUT);

    assert_eq!(first.rewrite.source, GENERATED_SIBLING_NESTED_COPY_EXPECTED);
    assert_piece_map(&first.source, &first.rewrite);
    assert_retained_units(&first, GENERATED_SIBLING_NESTED_COPY_RETAINED);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
    assert_piece_map(&second.source, &second.rewrite);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn ordinary_copy_decision_keeps_manual_copy_implementation() {
    let first = inspect_reduction(ORDINARY_COPY_MOVE_INPUT);

    assert_eq!(first.rewrite.source, ORDINARY_COPY_MOVE_EXPECTED);
    assert_piece_map(&first.source, &first.rewrite);
    assert_retained_units(&first, ORDINARY_COPY_MOVE_RETAINED);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
    assert_piece_map(&second.source, &second.rewrite);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn generated_sibling_adt_keeps_its_exact_drop_implementation() {
    let first = inspect_reduction(GENERATED_SIBLING_DROP_INPUT);

    assert_eq!(first.rewrite.source, GENERATED_SIBLING_DROP_EXPECTED);
    assert_piece_map(&first.source, &first.rewrite);
    assert_eq!(
        retained_units_of_kind(&first, WrittenUnitKind::ImplMember),
        BTreeSet::from(["fn drop(&mut self){}".to_owned()])
    );
    assert!(!first.rewrite.source.contains("struct Dead"));
    assert_compiles(&first.rewrite.source);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
    assert_piece_map(&second.source, &second.rewrite);
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn dead_top_level_macro_does_not_follow_crate_expansion_use() {
    let reduced = inspect_reduction(DIRECT_MACRO_INPUT);
    let expected_expansions = BTreeSet::from([ByteRange { start: 43, end: 60 }]);

    assert_eq!(reduced.rewrite.source, DIRECT_MACRO_EXPECTED);
    assert_retained_units(&reduced, DIRECT_MACRO_RETAINED);
    assert_eq!(
        written_expansion_ranges(
            &reduced.retention.main_semantic,
            &reduced.graph,
            &reduced.source,
        ),
        expected_expansions
    );
    assert_eq!(
        written_expansion_ranges(
            &reduced.retention.compile_required,
            &reduced.graph,
            &reduced.source,
        ),
        expected_expansions
    );
    assert!(!reduced.rewrite.source.contains("macro_rules! dead"));
    assert!(!reduced.rewrite.source.contains("dead!()"));
    assert!(reduced.rewrite.source.contains("println!(\"kept\")"));
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn semantic_and_compile_closures_are_not_conflated() {
    let item = inspect_reduction(ITEM_INPUT);
    let expected_item = BTreeSet::from([
        "<crate>".to_owned(),
        "kept".to_owned(),
        "kept::entry".to_owned(),
        "kept::helper".to_owned(),
        "main".to_owned(),
    ]);
    assert_eq!(
        local_definitions(&item.retention.main_semantic, &item.graph.definitions),
        expected_item
    );
    assert_eq!(
        local_definitions(&item.retention.compile_required, &item.graph.definitions),
        expected_item
    );
    assert_eq!(
        injected_definitions(&item.retention.main_semantic, &item.graph.definitions),
        BTreeSet::new()
    );

    let generated = inspect_reduction(MACRO_INPUT);
    assert_eq!(
        local_definitions(
            &generated.retention.main_semantic,
            &generated.graph.definitions
        ),
        BTreeSet::from([
            "<crate>".to_owned(),
            "program".to_owned(),
            "main".to_owned(),
            "needed".to_owned(),
        ])
    );
    assert_eq!(
        local_definitions(
            &generated.retention.compile_required,
            &generated.graph.definitions
        ),
        BTreeSet::from([
            "<crate>".to_owned(),
            "program".to_owned(),
            "main".to_owned(),
            "needed".to_owned(),
            "sibling".to_owned(),
            "sibling_dependency".to_owned(),
        ])
    );
    let expected_expansions = BTreeSet::from([ByteRange {
        start: 130,
        end: 141,
    }]);
    assert_eq!(
        written_expansion_ranges(
            &generated.retention.main_semantic,
            &generated.graph,
            &generated.source,
        ),
        expected_expansions
    );
    assert_eq!(
        written_expansion_ranges(
            &generated.retention.compile_required,
            &generated.graph,
            &generated.source,
        ),
        expected_expansions
    );
    assert_eq!(
        injected_definitions(
            &generated.retention.main_semantic,
            &generated.graph.definitions
        ),
        BTreeSet::new()
    );
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn retained_use_leaves_keep_their_exact_resolution_targets() {
    let reduced = inspect_reduction(USE_RESOLUTION_INPUT);
    assert_eq!(reduced.rewrite.source, USE_RESOLUTION_EXPECTED);
    let expected = BTreeSet::from([
        ("*".to_owned(), "catalog".to_owned()),
        ("Named as Renamed".to_owned(), "catalog::Named".to_owned()),
        (
            "nested as nested_alias".to_owned(),
            "catalog::inner::nested".to_owned(),
        ),
        ("self as namespace".to_owned(), "catalog".to_owned()),
    ]);
    assert_eq!(
        import_resolution_projection(
            USE_RESOLUTION_INPUT,
            &reduced.graph.definitions,
            Some(&reduced.retention.retained_units),
        ),
        expected
    );
    let reduced_graph = inspect_definitions(USE_RESOLUTION_EXPECTED);
    assert_eq!(
        import_resolution_projection(USE_RESOLUTION_EXPECTED, &reduced_graph, None),
        expected
    );
}

#[test]
#[cfg(rust_item_dependencies_patched)]
fn trait_signature_retains_the_exact_associated_type_target() {
    let reduced = inspect_reduction(MEMBER_INPUT);
    let graph = &reduced.graph.definitions;
    let trait_run = definition_id(graph, "Service::run");
    let trait_output = definition_id(graph, "Service::Output");
    let impl_run = definition_id(graph, "run");
    let impl_output = definition_id(graph, "Output");

    assert_eq!(
        graph
            .edges
            .iter()
            .filter(|edge| {
                edge.from == trait_run && edge.to == DefinitionTarget::Local(trait_output)
            })
            .map(|edge| (edge.kind, edge.sites.clone()))
            .collect::<Vec<_>>(),
        vec![(
            DefinitionDependencyKind::ReturnType,
            vec![ByteRange {
                start: 118,
                end: 124,
            }],
        )]
    );
    assert!(
        graph.edges.iter().all(|edge| {
            edge.from != impl_run || edge.to != DefinitionTarget::Local(impl_output)
        })
    );
}

fn assert_inventory_units(inventory: &SourceInventory, expected: &[UnitRef]) {
    let actual = inventory
        .units
        .iter()
        .map(|unit| UnitRef {
            kind: unit.kind,
            range: unit.full_range,
        })
        .collect::<Vec<_>>();
    for expected in expected {
        assert!(
            actual.contains(expected),
            "missing handwritten source unit {expected:?}; actual={actual:#?}"
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
fn assert_retained_units(reduction: &super::InspectedReduction, expected: &[UnitRef]) {
    let actual = reduction
        .retention
        .retained_units
        .iter()
        .map(|unit| {
            let unit = &reduction.source.units[unit.0 as usize];
            UnitRef {
                kind: unit.kind,
                range: unit.full_range,
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

#[cfg(rust_item_dependencies_patched)]
fn retained_units_of_kind(
    reduction: &super::InspectedReduction,
    kind: WrittenUnitKind,
) -> BTreeSet<String> {
    reduction
        .retention
        .retained_units
        .iter()
        .filter_map(|unit| {
            let unit = &reduction.source.units[unit.0 as usize];
            (unit.kind == kind).then(|| {
                reduction.source.original
                    [unit.full_range.start as usize..unit.full_range.end as usize]
                    .to_owned()
            })
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn source_units_of_kind(source: &SourceInventory, kind: WrittenUnitKind) -> BTreeSet<String> {
    source
        .units
        .iter()
        .filter(|unit| unit.kind == kind)
        .map(|unit| {
            source.original[unit.full_range.start as usize..unit.full_range.end as usize].to_owned()
        })
        .collect()
}

fn assert_crlf_only(source: &[u8]) {
    assert!(source.windows(2).any(|bytes| bytes == b"\r\n"));
    for (index, byte) in source.iter().copied().enumerate() {
        if byte == b'\n' {
            assert!(index > 0 && source[index - 1] == b'\r');
        }
    }
}

fn retained_except_ranges(
    inventory: &SourceInventory,
    removed: &[(u32, u32)],
) -> BTreeSet<crate::source::SourceUnitId> {
    inventory
        .units
        .iter()
        .filter(|unit| !removed.contains(&(unit.full_range.start, unit.full_range.end)))
        .map(|unit| unit.id)
        .collect()
}

fn assert_piece_map(inventory: &SourceInventory, rewrite: &SourceRewrite) {
    let mut cursor = 0_u32;
    let mut previous_original_end = 0_u32;
    for piece in &rewrite.pieces {
        assert_eq!(piece.output_range.start, cursor);
        assert!(piece.original_range.start >= previous_original_end);
        assert_eq!(piece.output_range.len(), piece.original_range.len());
        assert_eq!(
            &rewrite.source[piece.output_range.start as usize..piece.output_range.end as usize],
            &inventory.original
                [piece.original_range.start as usize..piece.original_range.end as usize]
        );
        cursor = piece.output_range.end;
        previous_original_end = piece.original_range.end;
    }
    assert_eq!(cursor as usize, rewrite.source.len());
}

#[cfg(rust_item_dependencies_patched)]
fn local_definitions(nodes: &BTreeSet<GraphNode>, graph: &DefinitionGraph) -> BTreeSet<String> {
    nodes
        .iter()
        .filter_map(|node| match node {
            GraphNode::Definition(definition) => {
                let definition = &graph.definitions[definition.0 as usize];
                matches!(
                    definition.origin,
                    DefinitionOrigin::Written { .. } | DefinitionOrigin::Expanded { .. }
                )
                .then(|| definition_path(&definition.key))
            }
            GraphNode::ExternalDefinition(_)
            | GraphNode::Expansion(_)
            | GraphNode::Proof(_)
            | GraphNode::Mono(_) => None,
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn injected_definitions(nodes: &BTreeSet<GraphNode>, graph: &DefinitionGraph) -> BTreeSet<String> {
    nodes
        .iter()
        .filter_map(|node| match node {
            GraphNode::Definition(definition) => {
                let definition = &graph.definitions[definition.0 as usize];
                matches!(definition.origin, DefinitionOrigin::Injected { .. })
                    .then(|| definition_path(&definition.key))
            }
            GraphNode::ExternalDefinition(_)
            | GraphNode::Expansion(_)
            | GraphNode::Proof(_)
            | GraphNode::Mono(_) => None,
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn written_expansion_ranges(
    nodes: &BTreeSet<GraphNode>,
    graph: &DependencyGraph,
    source: &SourceInventory,
) -> BTreeSet<ByteRange> {
    nodes
        .iter()
        .filter_map(|node| match node {
            GraphNode::Expansion(expansion) => graph.expansions[expansion.0 as usize]
                .written_invocation
                .map(|unit| source.units[unit.0 as usize].full_range),
            GraphNode::Definition(_)
            | GraphNode::ExternalDefinition(_)
            | GraphNode::Proof(_)
            | GraphNode::Mono(_) => None,
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn definition_path(key: &DefinitionKey) -> String {
    let path = key
        .0
        .iter()
        .filter_map(|part| part.name.as_deref())
        .collect::<Vec<_>>()
        .join("::");
    if path.is_empty() {
        "<crate>".to_owned()
    } else {
        path
    }
}

#[cfg(rust_item_dependencies_patched)]
fn definition_id(graph: &DefinitionGraph, path: &str) -> DefinitionId {
    let matches = graph
        .definitions
        .iter()
        .filter(|definition| definition_path(&definition.key) == path)
        .map(|definition| definition.id)
        .collect::<Vec<_>>();
    let [definition] = matches.as_slice() else {
        panic!("expected one definition for {path}, got {matches:?}");
    };
    *definition
}

#[cfg(rust_item_dependencies_patched)]
fn import_resolution_projection(
    source: &str,
    graph: &DefinitionGraph,
    retained: Option<&BTreeSet<crate::source::SourceUnitId>>,
) -> BTreeSet<(String, String)> {
    graph
        .definitions
        .iter()
        .filter_map(|definition| {
            let DefinitionOrigin::Written {
                unit,
                unit_range,
                unit_kind: WrittenUnitKind::UseLeaf,
                ..
            } = definition.origin
            else {
                return None;
            };
            if retained.is_some_and(|retained| !retained.contains(&unit)) {
                return None;
            }
            let leaf = source[unit_range.start as usize..unit_range.end as usize].to_owned();
            let targets = graph
                .edges
                .iter()
                .filter(|edge| {
                    edge.from == definition.id
                        && matches!(
                            edge.kind,
                            DefinitionDependencyKind::TypePath
                                | DefinitionDependencyKind::ValuePath
                        )
                })
                .map(|edge| match edge.to {
                    DefinitionTarget::Local(target) => {
                        definition_path(&graph.definitions[target.0 as usize].key)
                    }
                    DefinitionTarget::External(target) => {
                        graph.external_definitions[target.0 as usize].path.clone()
                    }
                })
                .collect::<Vec<_>>();
            Some(
                targets
                    .into_iter()
                    .map(|target| (leaf.clone(), target))
                    .collect::<Vec<_>>(),
            )
        })
        .flatten()
        .collect()
}

fn contains(source: &[u8], needle: &[u8]) -> bool {
    source
        .windows(needle.len())
        .any(|candidate| candidate == needle)
}

fn inspect_inventory(source: &str) -> SourceInventory {
    let (sysroot, target) = compiler_context();
    inspect_source(
        &SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2024,
            target,
        },
        &sysroot,
    )
    .expect("a retention fixture must have a complete source inventory")
}

#[cfg(rust_item_dependencies_patched)]
fn inspect_definitions(source: &str) -> DefinitionGraph {
    let (sysroot, target) = compiler_context();
    inspect_source_with_definitions(
        &SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2024,
            target,
        },
        &sysroot,
    )
    .expect("the reduced use fixture must retain resolution observations")
    .definitions
}

#[cfg(rust_item_dependencies_patched)]
fn assert_generated_sibling_unchanged(source: &str) {
    let first = inspect_reduction(source);
    assert_eq!(first.rewrite.source, source);
    assert_piece_map(&first.source, &first.rewrite);

    let second = inspect_reduction(&first.rewrite.source);
    assert_eq!(second.rewrite.source, first.rewrite.source);
}

#[cfg(rust_item_dependencies_patched)]
fn inspect_reduction(source: &str) -> super::InspectedReduction {
    let (sysroot, target) = compiler_context();
    inspect_source_with_reduction(
        &SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2024,
            target,
        },
        &sysroot,
    )
    .expect("the fixture must produce a complete reduction")
}

fn compiler_context() -> (PathBuf, String) {
    let rustc = env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC");
    let sysroot = rustc_output(rustc, &["--print", "sysroot"]);
    let version = rustc_output(rustc, &["-Vv"]);
    let target = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc -Vv must report a host")
        .to_owned();
    (PathBuf::from(sysroot.trim()), target)
}

fn rustc_output(rustc: &str, arguments: &[&str]) -> String {
    let output = Command::new(rustc)
        .args(arguments)
        .output()
        .expect("rustc query must start");
    assert!(output.status.success(), "rustc query failed");
    String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
}

#[cfg(rust_item_dependencies_patched)]
fn assert_compiles(source: &str) {
    let mut child = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .args([
            "--edition=2024",
            "--crate-name=drop_retention",
            "--emit=metadata=-",
            "-",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the retained source compiler must start");
    let mut stdin = child.stdin.take().expect("rustc stdin must be piped");
    stdin
        .write_all(source.as_bytes())
        .expect("the retained source must reach rustc");
    drop(stdin);
    let output = child
        .wait_with_output()
        .expect("the retained source compiler must finish");
    assert!(
        output.status.success(),
        "retained source failed to compile: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
