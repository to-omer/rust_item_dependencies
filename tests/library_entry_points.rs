#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use std::collections::BTreeSet;
#[cfg(rust_item_dependencies_patched)]
use std::path::{Path, PathBuf};
#[cfg(rust_item_dependencies_patched)]
use std::process::{Command, Output};
#[cfg(rust_item_dependencies_patched)]
use std::sync::OnceLock;
#[cfg(rust_item_dependencies_patched)]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::dependency_graph::RootReason;
#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::{
    AnalysisError, Analyzer, Edition, EntryPoint, EntryPointError, SourceInput,
};

#[cfg(rust_item_dependencies_patched)]
#[test]
fn library_configuration_failures_are_typed() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();

    let invalid_name = SourceInput::library(
        "pub fn entry() {}\n",
        Edition::Rust2024,
        target.clone(),
        "invalid-name",
    )
    .with_entry_point(EntryPoint::new("invalid-name::entry"));
    assert_eq!(
        analyzer.analyze(&invalid_name).unwrap_err(),
        AnalysisError::InvalidCrateName {
            name: "invalid-name".to_owned(),
        }
    );

    let missing_entry = SourceInput::library(
        "pub fn entry() {}\n",
        Edition::Rust2024,
        target.clone(),
        "typed_errors",
    );
    assert_eq!(
        analyzer.analyze(&missing_entry).unwrap_err(),
        AnalysisError::MissingLibraryEntryPoint
    );

    let source = concat!(
        "pub fn entry() {}\n",
        "pub struct Unsupported;\n",
        "unsafe extern \"C\" {\n",
        "    pub fn foreign_function();\n",
        "    pub static foreign_static: u8;\n",
        "}\n",
    );
    let cases = [
        ("entry", EntryPointError::InvalidPath),
        ("another_crate::entry", EntryPointError::WrongCrate),
        ("typed_errors::missing", EntryPointError::NotFound),
        (
            "typed_errors::Unsupported",
            EntryPointError::UnsupportedItem,
        ),
        (
            "typed_errors::foreign_function",
            EntryPointError::UnsupportedItem,
        ),
        (
            "typed_errors::foreign_static",
            EntryPointError::UnsupportedItem,
        ),
    ];
    for (path, reason) in cases {
        let input = SourceInput::library(source, Edition::Rust2024, target.clone(), "typed_errors")
            .with_entry_point(EntryPoint::new(path));
        assert_eq!(
            analyzer.analyze(&input).unwrap_err(),
            AnalysisError::InvalidEntryPoint {
                path: path.to_owned(),
                reason,
            },
            "{path}"
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn multiple_function_and_static_entries_remove_unrelated_items() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = concat!(
        "pub fn rid_function() -> u32 { rid_helper() }\n",
        "fn rid_helper() -> u32 { 7 }\n",
        "pub static rid_static: u32 = 9;\n",
        "pub fn rid_dead_function() -> u32 { 0 }\n",
        "pub static rid_dead_static: u32 = 0;\n",
    );
    let input = library_input(source, "multiple_roots")
        .with_entry_point(EntryPoint::new("multiple_roots::rid_static"))
        .with_entry_point(EntryPoint::new("multiple_roots::rid_function"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("multiple explicit roots must be reducible");
    assert_eq!(
        rid_lines(verified.reduced_source()),
        BTreeSet::from([
            "fn rid_helper() -> u32 { 7 }",
            "pub fn rid_function() -> u32 { rid_helper() }",
            "pub static rid_static: u32 = 9;",
        ])
    );
    assert_fixed_point(&analyzer, &input, verified.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_no_std_library_preserves_core_semantics_for_a_std_downstream() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = r#"#![no_std]

fn helper() -> u8 { 2 }

pub fn entry(value: u8) -> u8 { value.saturating_add(helper()) }

fn unused() -> u8 { 0 }
"#;
    let expected = r#"#![no_std]

fn helper() -> u8 { 2 }

pub fn entry(value: u8) -> u8 { value.saturating_add(helper()) }


"#;
    let input = SourceInput::library(source, Edition::Rust2024, target.clone(), "no_std_library")
        .with_entry_point(EntryPoint::new("no_std_library::entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("the no_std library must preserve its explicit entry and core dependencies");
    assert_eq!(verified.reduced_source(), expected);
    assert_fixed_point(&analyzer, &input, expected);

    let downstream = concat!(
        "use no_std_library::entry;\n",
        "fn main() { println!(\"{}\", entry(5)); }\n",
    );
    let directory = TestDirectory::new("no-std-library");
    let original = compile_library_and_run_downstream(
        directory.path(),
        "original",
        "no_std_library",
        source,
        downstream,
        &target,
    );
    let reduced = compile_library_and_run_downstream(
        directory.path(),
        "reduced",
        "no_std_library",
        expected,
        downstream,
        &target,
    );
    assert!(original.status.success(), "original run: {original:?}");
    assert_eq!(original.stdout, b"7\n");
    assert!(original.stderr.is_empty(), "original run: {original:?}");
    assert_eq!(reduced.status, original.status);
    assert_eq!(reduced.stdout, original.stdout);
    assert_eq!(reduced.stderr, original.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn an_unused_alloc_import_preserves_the_downstream_allocator_requirement() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = "#![no_std]\nextern crate alloc;\npub fn entry() {}\n";
    let input = SourceInput::library(
        source,
        Edition::Rust2024,
        target.clone(),
        "allocator_requirement",
    )
    .with_entry_point(EntryPoint::new("allocator_requirement::entry"));

    let reduction = analyzer
        .reduce(&input)
        .expect("the public reduction path must preserve external compiler requirements");
    assert!(reduction.reduced_source().contains("extern crate alloc;"));
    assert_fixed_point(&analyzer, &input, reduction.reduced_source());

    let directory = TestDirectory::new("allocator-requirement");
    let original = compile_library(
        directory.path(),
        "original",
        "allocator_requirement",
        source,
        &target,
    );
    let reduced = compile_library(
        directory.path(),
        "reduced",
        "allocator_requirement",
        reduction.reduced_source(),
        &target,
    );
    let control = compile_library(
        directory.path(),
        "control",
        "allocator_requirement",
        "#![no_std]\npub fn entry() {}\n",
        &target,
    );

    let original_downstream =
        compile_no_std_allocator_downstream(directory.path(), "original", &original, &target);
    let reduced_downstream =
        compile_no_std_allocator_downstream(directory.path(), "reduced", &reduced, &target);
    let control_downstream =
        compile_no_std_allocator_downstream(directory.path(), "control", &control, &target);
    assert!(!original_downstream.status.success());
    assert_eq!(reduced_downstream.status, original_downstream.status);
    assert!(
        String::from_utf8_lossy(&original_downstream.stderr)
            .contains("no global memory allocator found")
    );
    assert!(
        String::from_utf8_lossy(&reduced_downstream.stderr)
            .contains("no global memory allocator found")
    );
    assert!(
        control_downstream.status.success(),
        "control downstream failed:\n{}",
        String::from_utf8_lossy(&control_downstream.stderr)
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_macro_generated_panic_handler_remains_an_external_symbol_root() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = r#"#![no_std]

macro_rules! define_panic_handler {
    () => {
        #[panic_handler]
        fn panic(_: &core::panic::PanicInfo<'_>) -> ! { runtime() }
    };
}

define_panic_handler!();

fn runtime() -> ! { loop {} }

pub fn entry() -> u8 { 7 }

fn unused() {}
"#;
    let expected = r#"#![no_std]

macro_rules! define_panic_handler {
    () => {
        #[panic_handler]
        fn panic(_: &core::panic::PanicInfo<'_>) -> ! { runtime() }
    };
}

define_panic_handler!();

fn runtime() -> ! { loop {} }

pub fn entry() -> u8 { 7 }


"#;
    let input = SourceInput::library(
        source,
        Edition::Rust2024,
        target.clone(),
        "panic_handler_library",
    )
    .with_entry_point(EntryPoint::new("panic_handler_library::entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("the generated panic handler must be retained as a compiler root");
    assert_eq!(verified.reduced_source(), expected);
    assert_eq!(
        verified
            .original_analysis()
            .roots()
            .iter()
            .filter(|root| root.reason == RootReason::ExternalSymbol)
            .count(),
        1
    );
    assert_fixed_point(&analyzer, &input, expected);

    let directory = TestDirectory::new("panic-handler-library");
    let _ = compile_library(
        directory.path(),
        "original",
        "panic_handler_library",
        source,
        &target,
    );
    let _ = compile_library(
        directory.path(),
        "reduced",
        "panic_handler_library",
        expected,
        &target,
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn explicit_reexport_paths_keep_their_complete_alias_chains_only() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = concat!(
        "mod rid_direct_source {\n",
        "    pub fn rid_direct_target() -> u32 { 1 }\n",
        "    pub fn rid_direct_dead() -> u32 { 0 }\n",
        "}\n",
        "pub use rid_direct_source::{\n",
        "    rid_direct_target as rid_direct_api,\n",
        "    rid_direct_dead as rid_direct_dead_api,\n",
        "};\n",
        "\n",
        "mod rid_chain_source {\n",
        "    pub fn rid_chain_target() -> u32 { 2 }\n",
        "    pub fn rid_chain_dead() -> u32 { 0 }\n",
        "}\n",
        "mod rid_chain_middle {\n",
        "    pub use super::rid_chain_source::rid_chain_target as rid_chain_step;\n",
        "    pub use super::rid_chain_source::rid_chain_dead as rid_chain_dead_step;\n",
        "}\n",
        "pub use rid_chain_middle::rid_chain_step as rid_chain_api;\n",
        "pub use rid_chain_middle::rid_chain_dead_step as rid_chain_dead_api;\n",
        "\n",
        "mod rid_module_source {\n",
        "    pub mod rid_nested {\n",
        "        pub fn rid_module_target() -> u32 { 3 }\n",
        "        pub fn rid_module_dead() -> u32 { 0 }\n",
        "    }\n",
        "}\n",
        "pub use rid_module_source::rid_nested as rid_module_alias;\n",
        "\n",
        "mod rid_glob_source {\n",
        "    pub fn rid_glob_target() -> u32 { 4 }\n",
        "    pub fn rid_glob_dead() -> u32 { 0 }\n",
        "}\n",
        "pub use rid_glob_source::*;\n",
    );
    let input = library_input(source, "reexports")
        .with_entry_point(EntryPoint::new("reexports::rid_direct_api"))
        .with_entry_point(EntryPoint::new("reexports::rid_chain_api"))
        .with_entry_point(EntryPoint::new(
            "reexports::rid_module_alias::rid_module_target",
        ))
        .with_entry_point(EntryPoint::new("reexports::rid_glob_target"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("all supported reexport shapes must be reducible");
    assert_eq!(
        rid_lines(verified.reduced_source()),
        BTreeSet::from([
            "mod rid_chain_middle {",
            "mod rid_chain_source {",
            "mod rid_direct_source {",
            "mod rid_glob_source {",
            "mod rid_module_source {",
            "pub fn rid_chain_target() -> u32 { 2 }",
            "pub fn rid_direct_target() -> u32 { 1 }",
            "pub fn rid_glob_target() -> u32 { 4 }",
            "pub fn rid_module_target() -> u32 { 3 }",
            "pub mod rid_nested {",
            "pub use rid_chain_middle::rid_chain_step as rid_chain_api;",
            "pub use rid_direct_source::{",
            "rid_direct_target as rid_direct_api,",
            "pub use rid_glob_source::*;",
            "pub use rid_module_source::rid_nested as rid_module_alias;",
            "pub use super::rid_chain_source::rid_chain_target as rid_chain_step;",
        ])
    );
    assert_fixed_point(&analyzer, &input, verified.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_generic_definition_entry_preserves_downstream_trait_selection() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "pub struct Marker;\n",
        "pub trait Local {\n",
        "    type Output;\n",
        "    const VALUE: u8;\n",
        "    fn defaulted() -> u8 { 3 }\n",
        "    fn overridden() -> u8 { 4 }\n",
        "}\n",
        "impl<T> Local for T {\n",
        "    type Output = Marker;\n",
        "    const VALUE: u8 = 7;\n",
        "    fn overridden() -> u8 { 9 }\n",
        "}\n",
        "pub trait Unrelated { fn unused() -> u8 { 5 } }\n",
        "impl Unrelated for Marker {}\n",
        "impl Marker { pub fn unused_inherent() -> u8 { 6 } }\n",
        "pub fn entry<T: Local>() {}\n",
        "pub fn const_entry<const N: usize>() -> usize { N }\n",
        "pub fn unrelated() -> u8 { 0 }\n",
    );
    let input = SourceInput::library(
        source,
        Edition::Rust2024,
        target.clone(),
        "generic_definition",
    )
    .with_entry_point(EntryPoint::new("generic_definition::entry"))
    .with_entry_point(EntryPoint::new("generic_definition::const_entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("a generic definition root must be reducible without a concrete instance");
    assert_eq!(
        generic_contract_lines(verified.reduced_source()),
        BTreeSet::from([
            "const VALUE: u8 = 7;",
            "const VALUE: u8;",
            "fn defaulted() -> u8 { 3 }",
            "fn overridden() -> u8 { 4 }",
            "fn overridden() -> u8 { 9 }",
            "impl Marker { pub fn unused_inherent() -> u8 { 6 } }",
            "impl<T> Local for T {",
            "impl Unrelated for Marker {}",
            "pub fn const_entry<const N: usize>() -> usize { N }",
            "pub fn entry<T: Local>() {}",
            "pub struct Marker;",
            "pub trait Local {",
            "pub trait Unrelated { fn unused() -> u8 { 5 } }",
            "type Output = Marker;",
            "type Output;",
        ])
    );
    assert_fixed_point(&analyzer, &input, verified.reduced_source());

    let downstream = concat!(
        "use generic_definition::{const_entry, entry, Local, Marker};\n",
        "fn main() {\n",
        "    entry::<u8>();\n",
        "    let _: <u8 as Local>::Output = Marker;\n",
        "    println!(\"{}:{}:{}:{}\", <u8 as Local>::VALUE, <u8 as Local>::defaulted(), <u8 as Local>::overridden(), const_entry::<11>());\n",
        "}\n",
    );
    let directory = TestDirectory::new("generic-definition-downstream");
    let original = compile_library_and_run_downstream(
        directory.path(),
        "original",
        "generic_definition",
        source,
        downstream,
        &target,
    );
    let reduced = compile_library_and_run_downstream(
        directory.path(),
        "reduced",
        "generic_definition",
        verified.reduced_source(),
        downstream,
        &target,
    );
    assert!(original.status.success(), "original run: {original:?}");
    assert_eq!(original.stdout, b"7:3:9:11\n");
    assert!(original.stderr.is_empty(), "original run: {original:?}");
    assert_eq!(reduced.status, original.status);
    assert_eq!(reduced.stdout, original.stdout);
    assert_eq!(reduced.stderr, original.stderr);

    let directory_path = directory.path().to_owned();
    drop(directory);
    assert!(
        !directory_path.exists(),
        "temporary artifacts were not removed: {}",
        directory_path.display()
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn downstream_codegen_assembly_preserves_the_active_library_source() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let cases = [
        (
            "generic_assembly",
            concat!(
                "pub fn entry<T>() { unsafe { core::arch::asm!(\"\"); } }\n",
                "fn unused() {}\n",
            ),
            concat!(
                "use generic_assembly::entry;\n",
                "fn main() { entry::<u8>(); println!(\"ok\"); }\n",
            ),
        ),
        (
            "default_method_assembly",
            concat!(
                "pub trait AssemblyDefault {\n",
                "    fn run() { unsafe { core::arch::asm!(\"\"); } }\n",
                "}\n",
                "pub fn entry<T: AssemblyDefault>() {}\n",
                "fn unused() {}\n",
            ),
            concat!(
                "use default_method_assembly::{entry, AssemblyDefault};\n",
                "struct Downstream;\n",
                "impl AssemblyDefault for Downstream {}\n",
                "fn main() { entry::<Downstream>(); Downstream::run(); println!(\"ok\"); }\n",
            ),
        ),
    ];

    for (crate_name, source, downstream) in cases {
        let input = library_input(source, crate_name)
            .with_entry_point(EntryPoint::new(format!("{crate_name}::entry")));
        let verified = analyzer
            .reduce_and_verify(&input)
            .unwrap_or_else(|error| panic!("{crate_name}: {error:?}"));
        assert_eq!(verified.reduced_source(), source, "{crate_name}");
        assert_fixed_point(&analyzer, &input, source);

        let directory = TestDirectory::new(crate_name);
        let original = compile_library_and_run_downstream(
            directory.path(),
            "original",
            crate_name,
            source,
            downstream,
            &target,
        );
        let reduced = compile_library_and_run_downstream(
            directory.path(),
            "reduced",
            crate_name,
            verified.reduced_source(),
            downstream,
            &target,
        );
        assert!(original.status.success(), "{crate_name}: {original:?}");
        assert_eq!(original.stdout, b"ok\n", "{crate_name}");
        assert!(original.stderr.is_empty(), "{crate_name}: {original:?}");
        assert_eq!(reduced.status, original.status, "{crate_name}");
        assert_eq!(reduced.stdout, original.stdout, "{crate_name}");
        assert_eq!(reduced.stderr, original.stderr, "{crate_name}");
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_local_type_in_an_entry_signature_preserves_its_downstream_value_semantics() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "pub struct Value(pub *const u8);\n",
        "unsafe impl Send for Value {}\n",
        "impl Copy for Value {}\n",
        "impl Clone for Value { fn clone(&self) -> Self { *self } }\n",
        "pub fn entry() -> Value { Value(std::ptr::null()) }\n",
        "pub fn unrelated() {}\n",
    );
    let input = SourceInput::library(source, Edition::Rust2024, target.clone(), "exposed_value")
        .with_entry_point(EntryPoint::new("exposed_value::entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("an exposed local type must retain downstream-selected implementations");
    assert_eq!(
        exposed_value_contract_lines(verified.reduced_source()),
        BTreeSet::from([
            "impl Clone for Value { fn clone(&self) -> Self { *self } }",
            "impl Copy for Value {}",
            "pub fn entry() -> Value { Value(std::ptr::null()) }",
            "pub struct Value(pub *const u8);",
            "unsafe impl Send for Value {}",
        ])
    );
    assert_fixed_point(&analyzer, &input, verified.reduced_source());

    let downstream = concat!(
        "use exposed_value::entry;\n",
        "fn require_send<T: Send>(_: T) {}\n",
        "fn main() {\n",
        "    let value = entry();\n",
        "    let copied = value;\n",
        "    require_send(value);\n",
        "    println!(\"{}\", copied.0.is_null());\n",
        "}\n",
    );
    let directory = TestDirectory::new("exposed-value-downstream");
    let original = compile_library_and_run_downstream(
        directory.path(),
        "original",
        "exposed_value",
        source,
        downstream,
        &target,
    );
    let reduced = compile_library_and_run_downstream(
        directory.path(),
        "reduced",
        "exposed_value",
        verified.reduced_source(),
        downstream,
        &target,
    );
    assert!(original.status.success(), "original run: {original:?}");
    assert_eq!(original.stdout, b"true\n");
    assert!(original.stderr.is_empty(), "original run: {original:?}");
    assert_eq!(reduced.status, original.status);
    assert_eq!(reduced.stdout, original.stdout);
    assert_eq!(reduced.stderr, original.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn derived_impls_follow_the_same_downstream_selection_contract() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "#[derive(Clone, Debug)]\n",
        "pub struct DerivedValue(pub u8);\n",
        "pub fn entry() -> DerivedValue { DerivedValue(7) }\n",
        "pub fn unrelated() {}\n",
    );
    let input = SourceInput::library(source, Edition::Rust2024, target.clone(), "derived_value")
        .with_entry_point(EntryPoint::new("derived_value::entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("derive-generated impls on an exposed type must remain available downstream");
    assert!(
        verified
            .reduced_source()
            .contains("#[derive(Clone, Debug)]")
    );
    assert!(
        verified
            .reduced_source()
            .contains("pub struct DerivedValue(pub u8);")
    );
    assert!(!verified.reduced_source().contains("unrelated"));
    assert_fixed_point(&analyzer, &input, verified.reduced_source());

    let private_source = concat!(
        "#[derive(Clone)]\n",
        "struct Private;\n",
        "pub fn entry() { let _ = Private; }\n",
    );
    let private_input = SourceInput::library(
        private_source,
        Edition::Rust2024,
        target.clone(),
        "private_derive",
    )
    .with_entry_point(EntryPoint::new("private_derive::entry"));
    let private_verified = analyzer
        .reduce_and_verify(&private_input)
        .expect("an unused derive on a private entry dependency must be removable");
    assert!(!private_verified.reduced_source().contains("derive"));
    assert!(
        private_verified
            .reduced_source()
            .contains("struct Private;")
    );
    assert_fixed_point(&analyzer, &private_input, private_verified.reduced_source());

    let downstream = concat!(
        "use derived_value::entry;\n",
        "fn main() {\n",
        "    let value = entry();\n",
        "    println!(\"{:?}:{}\", value.clone(), value.0);\n",
        "}\n",
    );
    let directory = TestDirectory::new("derived-value-downstream");
    let original = compile_library_and_run_downstream(
        directory.path(),
        "original",
        "derived_value",
        source,
        downstream,
        &target,
    );
    let reduced = compile_library_and_run_downstream(
        directory.path(),
        "reduced",
        "derived_value",
        verified.reduced_source(),
        downstream,
        &target,
    );
    assert!(original.status.success(), "original run: {original:?}");
    assert_eq!(original.stdout, b"DerivedValue(7):7\n");
    assert!(original.stderr.is_empty(), "original run: {original:?}");
    assert_eq!(reduced.status, original.status);
    assert_eq!(reduced.stdout, original.stdout);
    assert_eq!(reduced.stderr, original.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn entry_type_surfaces_and_bounds_preserve_downstream_trait_semantics() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let cases = [
        (
            "projected_entry",
            concat!(
                "pub struct Hidden(pub *const u8);\n",
                "unsafe impl Send for Hidden {}\n",
                "pub trait Local { type Assoc; }\n",
                "impl Local for u8 { type Assoc = Hidden; }\n",
                "pub fn entry() -> <u8 as Local>::Assoc { Hidden(std::ptr::null()) }\n",
                "pub fn unrelated() {}\n",
            ),
            "entry",
            "entry()",
            "unsafe impl Send for Hidden {}",
        ),
        (
            "opaque_entry",
            concat!(
                "pub struct Hidden(pub *const u8);\n",
                "unsafe impl Send for Hidden {}\n",
                "pub fn entry() -> impl Sized { Hidden(std::ptr::null()) }\n",
                "pub fn unrelated() {}\n",
            ),
            "entry",
            "entry()",
            "unsafe impl Send for Hidden {}",
        ),
        (
            "async_entry",
            concat!(
                "pub struct Hidden(pub *const u8);\n",
                "unsafe impl Send for Hidden {}\n",
                "pub async fn entry() {\n",
                "    let value = Hidden(std::ptr::null());\n",
                "    std::future::ready(()).await;\n",
                "    std::hint::black_box(value);\n",
                "}\n",
                "pub fn unrelated() {}\n",
            ),
            "entry",
            "entry()",
            "unsafe impl Send for Hidden {}",
        ),
        (
            "static_entry",
            concat!(
                "pub struct Hidden(pub *const u8);\n",
                "unsafe impl Send for Hidden {}\n",
                "unsafe impl Sync for Hidden {}\n",
                "impl Clone for Hidden { fn clone(&self) -> Self { Hidden(self.0) } }\n",
                "impl Copy for Hidden {}\n",
                "pub static ENTRY: Hidden = Hidden(std::ptr::null());\n",
                "pub fn unrelated() {}\n",
            ),
            "ENTRY",
            "ENTRY",
            "unsafe impl Send for Hidden {}",
        ),
        (
            "bounded_entry",
            concat!(
                "pub struct LocalType;\n",
                "pub trait LocalTrait {}\n",
                "impl LocalTrait for LocalType {}\n",
                "pub struct IrrelevantType;\n",
                "pub trait IrrelevantTrait {}\n",
                "impl IrrelevantTrait for IrrelevantType {}\n",
                "pub fn entry() where LocalType: LocalTrait {}\n",
                "pub fn unrelated() {}\n",
            ),
            "entry",
            "entry()",
            "impl LocalTrait for LocalType {}",
        ),
    ];

    for (crate_name, source, entry_name, entry_expression, retained_fragment) in cases {
        let input = SourceInput::library(source, Edition::Rust2024, target.clone(), crate_name)
            .with_entry_point(EntryPoint::new(format!("{crate_name}::{entry_name}")));
        let verified = analyzer
            .reduce_and_verify(&input)
            .expect("the exposed type must retain downstream-selected implementations");
        assert!(
            verified.reduced_source().contains(retained_fragment),
            "{crate_name}: {}",
            verified.reduced_source()
        );
        assert!(!verified.reduced_source().contains("pub fn unrelated"));
        assert!(!verified.reduced_source().contains("IrrelevantTrait"));
        assert_fixed_point(&analyzer, &input, verified.reduced_source());

        let downstream = format!(
            "use {crate_name}::{entry_name};\nfn require_send<T: Send>(_: T) {{}}\nfn main() {{ require_send({entry_expression}); println!(\"ok\"); }}\n"
        );
        let directory = TestDirectory::new(crate_name);
        let original = compile_library_and_run_downstream(
            directory.path(),
            "original",
            crate_name,
            source,
            &downstream,
            &target,
        );
        let reduced = compile_library_and_run_downstream(
            directory.path(),
            "reduced",
            crate_name,
            verified.reduced_source(),
            &downstream,
            &target,
        );
        assert!(original.status.success(), "{crate_name}: {original:?}");
        assert_eq!(original.stdout, b"ok\n", "{crate_name}");
        assert!(original.stderr.is_empty(), "{crate_name}: {original:?}");
        assert_eq!(reduced.status, original.status, "{crate_name}");
        assert_eq!(reduced.stdout, original.stdout, "{crate_name}");
        assert_eq!(reduced.stderr, original.stderr, "{crate_name}");
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_binary_can_add_an_explicit_entry_without_losing_main() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = concat!(
        "fn main() { println!(\"main\"); }\n",
        "pub fn rid_exported() -> u8 { 7 }\n",
        "fn rid_dead() -> u8 { 0 }\n",
    );
    let input = SourceInput::binary(source, Edition::Rust2024, host_target())
        .with_crate_name("binary_entries")
        .with_entry_point(EntryPoint::new("binary_entries::rid_exported"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("main and the additional entry must share the root model");
    assert_eq!(
        rid_lines(verified.reduced_source()),
        BTreeSet::from(["pub fn rid_exported() -> u8 { 7 }"])
    );
    assert!(verified.reduced_source().contains("fn main()"));
    assert_fixed_point(&analyzer, &input, verified.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn external_only_entry_types_do_not_retain_unrelated_trait_implementations() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = concat!(
        "trait UnusedLocal { fn unused_value() -> u8 { 0 } }\n",
        "impl<T> UnusedLocal for T {}\n",
        "pub fn lifetime_entry<'a>(value: &'a u8) -> &'a u8 { value }\n",
        "pub fn array_entry() -> [u8; 1 + 1] { [0; 1 + 1] }\n",
        "pub struct LocalType;\n",
        "pub fn outlives_entry() where LocalType: 'static {}\n",
    );
    let input = library_input(source, "lifetime_definition")
        .with_entry_point(EntryPoint::new("lifetime_definition::lifetime_entry"))
        .with_entry_point(EntryPoint::new("lifetime_definition::array_entry"))
        .with_entry_point(EntryPoint::new("lifetime_definition::outlives_entry"));

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("external-only types must use ordinary mono roots");
    assert_eq!(
        external_type_contract_lines(verified.reduced_source()),
        BTreeSet::from([
            "pub fn array_entry() -> [u8; 1 + 1] { [0; 1 + 1] }",
            "pub fn lifetime_entry<'a>(value: &'a u8) -> &'a u8 { value }",
            "pub fn outlives_entry() where LocalType: 'static {}",
        ])
    );
    assert_fixed_point(&analyzer, &input, verified.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn recipe_normalizes_entries_and_identifies_the_library_contract() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = "pub fn first() {}\npub fn second() {}\nfn main() {}\n";
    let ordered = SourceInput::library(source, Edition::Rust2024, target.clone(), "recipe")
        .with_entry_point(EntryPoint::new("recipe::first"))
        .with_entry_point(EntryPoint::new("recipe::second"));
    let reordered_with_duplicate =
        SourceInput::library(source, Edition::Rust2024, target.clone(), "recipe")
            .with_entry_point(EntryPoint::new("recipe::second"))
            .with_entry_point(EntryPoint::new("recipe::first"))
            .with_entry_point(EntryPoint::new("recipe::second"));
    let one_entry = SourceInput::library(source, Edition::Rust2024, target.clone(), "recipe")
        .with_entry_point(EntryPoint::new("recipe::first"));
    let renamed = SourceInput::library(source, Edition::Rust2024, target.clone(), "renamed_recipe")
        .with_entry_point(EntryPoint::new("renamed_recipe::first"))
        .with_entry_point(EntryPoint::new("renamed_recipe::second"));
    let binary = SourceInput::binary(source, Edition::Rust2024, target)
        .with_crate_name("recipe")
        .with_entry_point(EntryPoint::new("recipe::first"))
        .with_entry_point(EntryPoint::new("recipe::second"));

    let ordered_recipe = analyzer
        .analyze(&ordered)
        .expect("the library must compile")
        .recipe();
    assert_eq!(
        analyzer
            .analyze(&reordered_with_duplicate)
            .expect("entry order and duplicates must not affect compilation")
            .recipe(),
        ordered_recipe
    );
    assert_ne!(
        analyzer
            .analyze(&one_entry)
            .expect("a smaller entry set must compile")
            .recipe(),
        ordered_recipe
    );
    assert_ne!(
        analyzer
            .analyze(&renamed)
            .expect("the renamed library must compile")
            .recipe(),
        ordered_recipe
    );
    assert_ne!(
        analyzer
            .analyze(&binary)
            .expect("the binary input must compile")
            .recipe(),
        ordered_recipe
    );
}

#[cfg(rust_item_dependencies_patched)]
fn library_input(source: &str, crate_name: &str) -> SourceInput {
    SourceInput::library(source, Edition::Rust2024, host_target(), crate_name)
}

#[cfg(rust_item_dependencies_patched)]
fn assert_fixed_point(analyzer: &Analyzer, input: &SourceInput, reduced_source: &str) {
    let mut reduced_input = input.clone();
    reduced_input.source = reduced_source.to_owned();
    let fixed = analyzer
        .reduce_and_verify(&reduced_input)
        .expect("an already reduced library must remain reducible");
    assert_eq!(fixed.reduced_source(), reduced_source);
}

#[cfg(rust_item_dependencies_patched)]
fn rid_lines(source: &str) -> BTreeSet<&str> {
    source
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("rid_"))
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn generic_contract_lines(source: &str) -> BTreeSet<&str> {
    source
        .lines()
        .map(str::trim)
        .filter(|line| {
            line.starts_with("pub trait Local")
                || line.starts_with("pub struct Marker")
                || line.starts_with("type Output")
                || line.starts_with("const VALUE")
                || line.starts_with("fn defaulted")
                || line.starts_with("fn overridden")
                || line.starts_with("impl<T> Local")
                || line.starts_with("pub trait Unrelated")
                || line.starts_with("impl Unrelated")
                || line.starts_with("impl Marker")
                || line.starts_with("fn unused")
                || line.starts_with("pub fn const_entry")
                || line.starts_with("pub fn entry")
                || line.starts_with("pub fn unrelated")
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn external_type_contract_lines(source: &str) -> BTreeSet<&str> {
    source
        .lines()
        .map(str::trim)
        .filter(|line| {
            line.starts_with("trait UnusedLocal")
                || line.starts_with("impl<T> UnusedLocal")
                || line.starts_with("pub fn array_entry")
                || line.starts_with("pub fn lifetime_entry")
                || line.starts_with("pub fn outlives_entry")
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn exposed_value_contract_lines(source: &str) -> BTreeSet<&str> {
    source
        .lines()
        .map(str::trim)
        .filter(|line| {
            line.starts_with("pub struct Value")
                || line.starts_with("unsafe impl Send for Value")
                || line.starts_with("impl Copy for Value")
                || line.starts_with("impl Clone for Value")
                || line.starts_with("pub fn entry")
                || line.starts_with("pub fn unrelated")
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn compile_library_and_run_downstream(
    root: &Path,
    variant: &str,
    crate_name: &str,
    library_source: &str,
    downstream_source: &str,
    target: &str,
) -> Output {
    let library_artifact = compile_library(root, variant, crate_name, library_source, target);
    let directory = root.join(variant);
    let downstream_path = directory.join("downstream.rs");
    let executable = directory.join(format!("downstream{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(&downstream_path, downstream_source)
        .expect("the downstream source must be writable");
    let compilation = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg(&downstream_path)
        .args([
            "--crate-name",
            "downstream",
            "--crate-type=bin",
            "--edition=2024",
            "--target",
            target,
            "-Awarnings",
            "--extern",
        ])
        .arg(format!("{crate_name}={}", library_artifact.display()))
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("the downstream compiler must start");
    assert!(
        compilation.status.success(),
        "{variant} downstream compilation failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    Command::new(executable)
        .output()
        .expect("the downstream executable must start")
}

#[cfg(rust_item_dependencies_patched)]
fn compile_library(
    root: &Path,
    variant: &str,
    crate_name: &str,
    source: &str,
    target: &str,
) -> PathBuf {
    let directory = root.join(variant);
    std::fs::create_dir(&directory).expect("the variant directory must be writable");
    let source_path = directory.join("library.rs");
    let artifact = directory.join(format!("lib{crate_name}.rlib"));
    std::fs::write(&source_path, source).expect("the library source must be writable");

    let compilation = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg(&source_path)
        .args([
            "--crate-name",
            crate_name,
            "--crate-type=rlib",
            "--edition=2024",
            "--target",
            target,
            "-Awarnings",
            "-o",
        ])
        .arg(&artifact)
        .output()
        .expect("the library compiler must start");
    assert!(
        compilation.status.success(),
        "{variant} library compilation failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    artifact
}

#[cfg(rust_item_dependencies_patched)]
fn compile_no_std_allocator_downstream(
    root: &Path,
    variant: &str,
    library: &Path,
    target: &str,
) -> Output {
    let directory = root.join(variant);
    let source = directory.join("allocator-downstream.rs");
    let metadata = directory.join("allocator-downstream.rmeta");
    std::fs::write(
        &source,
        concat!(
            "#![no_std]\n",
            "#![no_main]\n",
            "extern crate allocator_requirement;\n",
            "#[panic_handler]\n",
            "fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }\n",
            "#[unsafe(no_mangle)]\n",
            "pub extern \"C\" fn _start() -> ! {\n",
            "    allocator_requirement::entry();\n",
            "    loop {}\n",
            "}\n",
        ),
    )
    .expect("the allocator downstream source must be writable");
    Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg(&source)
        .args([
            "--crate-name",
            "allocator_downstream",
            "--crate-type=bin",
            "--edition=2024",
            "--target",
            target,
            "-Cpanic=abort",
            "--emit=metadata",
            "--extern",
        ])
        .arg(format!("allocator_requirement={}", library.display()))
        .args(["-Awarnings", "-o"])
        .arg(metadata)
        .output()
        .expect("the allocator downstream compiler must finish")
}

#[cfg(rust_item_dependencies_patched)]
struct TestDirectory {
    path: PathBuf,
}

#[cfg(rust_item_dependencies_patched)]
impl TestDirectory {
    fn new(label: &str) -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);

        let parent = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("target")
            .join("test-artifacts")
            .join("library-entry-points");
        std::fs::create_dir_all(&parent).expect("the test artifact directory must be writable");
        loop {
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let path = parent.join(format!("{label}-{}-{id}", std::process::id()));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self { path },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => panic!("cannot create {}: {error}", path.display()),
            }
        }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

#[cfg(rust_item_dependencies_patched)]
impl Drop for TestDirectory {
    fn drop(&mut self) {
        if let Err(error) = std::fs::remove_dir_all(&self.path) {
            if error.kind() != std::io::ErrorKind::NotFound {
                eprintln!("cannot clean up {}: {error}", self.path.display());
            }
        }
    }
}

#[cfg(rust_item_dependencies_patched)]
fn host_target() -> String {
    static TARGET: OnceLock<String> = OnceLock::new();
    TARGET
        .get_or_init(|| {
            let output = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
                .arg("-Vv")
                .output()
                .expect("rustc -Vv must start");
            assert!(output.status.success(), "rustc -Vv failed: {output:?}");
            String::from_utf8(output.stdout)
                .expect("rustc -Vv output must be UTF-8")
                .lines()
                .find_map(|line| line.strip_prefix("host: "))
                .expect("rustc -Vv must report its host")
                .to_owned()
        })
        .clone()
}
