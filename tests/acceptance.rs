#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::{AnalysisError, Analyzer, Edition, SourceInput, VerifiedReduction};

#[cfg(rust_item_dependencies_patched)]
const CASES: &[(&str, &str, &str)] = &[
    (
        "nested items",
        include_str!("fixtures/retention/item_nested_module.input.rs"),
        include_str!("fixtures/retention/item_nested_module.expected.rs"),
    ),
    (
        "resolved use leaves",
        include_str!("fixtures/retention/use_resolution.input.rs"),
        include_str!("fixtures/retention/use_resolution.expected.rs"),
    ),
    (
        "trait and impl members",
        include_str!("fixtures/retention/trait_impl_members.input.rs"),
        include_str!("fixtures/retention/trait_impl_members.expected.rs"),
    ),
    (
        "selected impl shell",
        include_str!("fixtures/retention/impl_shells.input.rs"),
        include_str!("fixtures/retention/impl_shells.expected.rs"),
    ),
    (
        "local macro fixed point",
        include_str!("fixtures/retention/macro_fixed_point.input.rs"),
        include_str!("fixtures/retention/macro_fixed_point.expected.rs"),
    ),
    (
        "sysroot macro fixed point",
        include_str!("fixtures/retention/sysroot_macro_fixed_point.input.rs"),
        include_str!("fixtures/retention/sysroot_macro_fixed_point.expected.rs"),
    ),
    (
        "direct macro retention",
        include_str!("fixtures/retention/direct_macro_retention.input.rs"),
        include_str!("fixtures/retention/direct_macro_retention.expected.rs"),
    ),
    (
        "macro generated impl member",
        include_str!("fixtures/retention/macro_generated_impl_member.input.rs"),
        include_str!("fixtures/retention/macro_generated_impl_member.expected.rs"),
    ),
];

#[cfg(rust_item_dependencies_patched)]
#[test]
fn complex_reductions_match_handwritten_sources() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();

    for &(case, source, expected) in CASES {
        let verified = analyzer
            .reduce_and_verify(&input(source, &target))
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert_verified(case, source, expected, &verified);
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_complex_macro_reduction_is_deterministic_and_byte_idempotent() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let (_, source, expected) = CASES
        .iter()
        .find(|(case, _, _)| *case == "sysroot macro fixed point")
        .unwrap();

    let first = analyzer.reduce_and_verify(&input(source, &target)).unwrap();
    let second = analyzer.reduce_and_verify(&input(source, &target)).unwrap();
    assert_eq!(second, first);

    let fixed = analyzer
        .reduce_and_verify(&input(first.reduced_source(), &target))
        .unwrap();
    assert_eq!(fixed.reduced_source(), *expected);
    assert_eq!(fixed.reduced_source(), first.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn external_symbol_roots_preserve_linked_entry_points() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = include_str!("fixtures/retention/external_symbol_roots.input.rs");
    let expected = include_str!("fixtures/retention/external_symbol_roots.expected.rs");

    let verified = analyzer
        .reduce_and_verify(&input(source, &target))
        .expect("external symbols must be retained as compiler roots");
    assert_verified("external symbol roots", source, expected, &verified);

    let fixed = analyzer
        .reduce_and_verify(&input(expected, &target))
        .expect("external symbol roots must be byte-idempotent");
    assert_eq!(fixed.reduced_source(), expected);

    let original_output = compile_and_run(source, &target, "external_symbols_original");
    let reduced_output = compile_and_run(expected, &target, "external_symbols_reduced");
    assert!(original_output.status.success());
    assert_eq!(original_output.stdout, b"10\n");
    assert!(original_output.stderr.is_empty());
    assert_eq!(reduced_output.status, original_output.status);
    assert_eq!(reduced_output.stdout, original_output.stdout);
    assert_eq!(reduced_output.stderr, original_output.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_global_allocator_and_its_generated_entry_points_survive_reduction() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "#[global_allocator]\n",
        "static ALLOCATOR: std::alloc::System = std::alloc::System;\n",
        "\n",
        "fn unused() {}\n",
        "\n",
        "fn main() { println!(\"{}\", Box::new(7)); }\n",
    );
    let expected = concat!(
        "#[global_allocator]\n",
        "static ALLOCATOR: std::alloc::System = std::alloc::System;\n",
        "\n",
        "\n",
        "\n",
        "fn main() { println!(\"{}\", Box::new(7)); }\n",
    );

    let verified = analyzer
        .reduce_and_verify(&input(source, &target))
        .expect("a global allocator must be retained through its generated entry points");
    assert_verified("global allocator", source, expected, &verified);

    let fixed = analyzer
        .reduce_and_verify(&input(expected, &target))
        .expect("a reduced global allocator must remain byte-idempotent");
    assert_eq!(fixed.reduced_source(), expected);

    let original_output = compile_and_run(source, &target, "global_allocator_original");
    let reduced_output = compile_and_run(expected, &target, "global_allocator_reduced");
    assert!(original_output.status.success());
    assert_eq!(original_output.stdout, b"7\n");
    assert!(original_output.stderr.is_empty());
    assert_eq!(reduced_output.status, original_output.status);
    assert_eq!(reduced_output.stdout, original_output.stdout);
    assert_eq!(reduced_output.stderr, original_output.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn foreign_items_are_reduced_independently_and_preserve_linked_behavior() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = include_str!("fixtures/retention/foreign_function_blocks.input.rs");
    let expected = include_str!("fixtures/retention/foreign_function_blocks.expected.rs");

    for (edition_name, edition) in [
        ("2015", Edition::Rust2015),
        ("2018", Edition::Rust2018),
        ("2021", Edition::Rust2021),
        ("2024", Edition::Rust2024),
    ] {
        let verified = analyzer
            .reduce_and_verify(&input_with_edition(source, &target, edition))
            .unwrap_or_else(|error| panic!("Rust {edition_name}: {error:?}"));
        assert_verified(
            &format!("foreign items in Rust {edition_name}"),
            source,
            expected,
            &verified,
        );

        let fixed = analyzer
            .reduce_and_verify(&input_with_edition(expected, &target, edition))
            .unwrap_or_else(|error| panic!("Rust {edition_name} fixed point: {error:?}"));
        assert_eq!(fixed.reduced_source(), expected, "Rust {edition_name}");
    }

    let original_output = compile_and_run(source, &target, "foreign_block_original");
    let reduced_output = compile_and_run(expected, &target, "foreign_block_reduced");
    assert!(original_output.status.success());
    assert_eq!(original_output.stdout, b"7\n");
    assert!(original_output.stderr.is_empty());
    assert_eq!(reduced_output.status, original_output.status);
    assert_eq!(reduced_output.stdout, original_output.stdout);
    assert_eq!(reduced_output.stderr, original_output.stderr);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_macro_generated_foreign_function_block_is_reducible() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "macro_rules! foreign {\n",
        "    () => {\n",
        "        unsafe extern \"C\" {\n",
        "            fn abs(value: core::ffi::c_int) -> core::ffi::c_int;\n",
        "        }\n",
        "    };\n",
        "}\n",
        "foreign!();\n",
        "fn unused_local() {}\n",
        "fn main() { println!(\"{}\", unsafe { abs(-7) }); }\n",
    );
    let expected = concat!(
        "macro_rules! foreign {\n",
        "    () => {\n",
        "        unsafe extern \"C\" {\n",
        "            fn abs(value: core::ffi::c_int) -> core::ffi::c_int;\n",
        "        }\n",
        "    };\n",
        "}\n",
        "foreign!();\n",
        "\n",
        "fn main() { println!(\"{}\", unsafe { abs(-7) }); }\n",
    );

    let verified = analyzer
        .reduce_and_verify(&input(source, &target))
        .expect("a generated foreign function declaration must be reducible");

    assert_verified(
        "generated foreign function block",
        source,
        expected,
        &verified,
    );

    let fixed = analyzer
        .reduce_and_verify(&input(expected, &target))
        .expect("a reduced generated foreign block must remain reducible");
    assert_eq!(fixed.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn supported_ffi_constructs_follow_the_same_reduction_rules_as_rust_items() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let cases = [
        (
            "foreign static declarations",
            concat!(
                "unsafe extern \"C\" {\n",
                "    static USED: i32;\n",
                "    static UNUSED: i32;\n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    let _ = unsafe { USED };\n",
                "}\n",
            ),
            concat!(
                "unsafe extern \"C\" {\n",
                "    static USED: i32;\n",
                "    \n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    let _ = unsafe { USED };\n",
                "}\n",
            ),
        ),
        (
            "foreign item macro invocations",
            concat!(
                "macro_rules! used_declaration {\n",
                "    () => {\n",
                "        fn used();\n",
                "    };\n",
                "}\n",
                "\n",
                "macro_rules! unused_declaration {\n",
                "    () => {\n",
                "        fn unused();\n",
                "    };\n",
                "}\n",
                "\n",
                "unsafe extern \"C\" {\n",
                "    used_declaration!();\n",
                "    unused_declaration!();\n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    unsafe { used() }\n",
                "}\n",
            ),
            concat!(
                "macro_rules! used_declaration {\n",
                "    () => {\n",
                "        fn used();\n",
                "    };\n",
                "}\n",
                "\n",
                "\n",
                "\n",
                "unsafe extern \"C\" {\n",
                "    used_declaration!();\n",
                "    \n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    unsafe { used() }\n",
                "}\n",
            ),
        ),
        (
            "non-Rust ABI definitions and function pointers",
            concat!(
                "extern \"C\" fn used(value: i32) -> i32 {\n",
                "    value + 1\n",
                "}\n",
                "\n",
                "#[cfg_attr(target_vendor = \"apple\", unsafe(link_section = \"__TEXT,__text\"))]\n",
                "#[cfg_attr(target_os = \"windows\", unsafe(link_section = \".text$rid\"))]\n",
                "#[cfg_attr(not(any(target_vendor = \"apple\", target_os = \"windows\")), unsafe(link_section = \".text.rid\"))]\n",
                "extern \"C\" fn unused() -> i32 {\n",
                "    0\n",
                "}\n",
                "\n",
                "fn call(function: extern \"C\" fn(i32) -> i32) -> i32 {\n",
                "    function(1)\n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    assert_eq!(call(used), 2);\n",
                "}\n",
            ),
            concat!(
                "extern \"C\" fn used(value: i32) -> i32 {\n",
                "    value + 1\n",
                "}\n",
                "\n",
                "\n",
                "\n",
                "fn call(function: extern \"C\" fn(i32) -> i32) -> i32 {\n",
                "    function(1)\n",
                "}\n",
                "\n",
                "fn main() {\n",
                "    assert_eq!(call(used), 2);\n",
                "}\n",
            ),
        ),
    ];

    for (case, source, expected) in cases {
        let verified = analyzer
            .reduce_and_verify(&input(source, &target))
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert_verified(case, source, expected, &verified);

        let fixed = analyzer
            .reduce_and_verify(&input(expected, &target))
            .unwrap_or_else(|error| panic!("{case} fixed point: {error:?}"));
        assert_eq!(fixed.reduced_source(), expected, "{case}");
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn a_used_constructor_static_runs_before_main_after_reduction() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = r#"static INITIALIZED: core::sync::atomic::AtomicBool =
    core::sync::atomic::AtomicBool::new(false);

extern "C" fn initialize() {
    INITIALIZED.store(true, core::sync::atomic::Ordering::Relaxed);
}

fn unused() {}

#[cfg_attr(
    any(
        target_os = "android",
        target_os = "dragonfly",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "illumos",
        target_os = "linux",
        target_os = "netbsd",
        target_os = "nto",
        target_os = "qnx",
        target_os = "openbsd",
        target_os = "fuchsia",
        target_os = "managarm",
    ),
    unsafe(link_section = ".init_array")
)]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__mod_init_func,mod_init_funcs"))]
#[cfg_attr(target_os = "windows", unsafe(link_section = ".CRT$XCU"))]
#[used]
static INITIALIZER: extern "C" fn() = initialize;

fn main() {
    assert!(INITIALIZED.load(core::sync::atomic::Ordering::Relaxed));
    println!("initialized");
}
"#;
    let expected = r#"static INITIALIZED: core::sync::atomic::AtomicBool =
    core::sync::atomic::AtomicBool::new(false);

extern "C" fn initialize() {
    INITIALIZED.store(true, core::sync::atomic::Ordering::Relaxed);
}



#[cfg_attr(
    any(
        target_os = "android",
        target_os = "dragonfly",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "illumos",
        target_os = "linux",
        target_os = "netbsd",
        target_os = "nto",
        target_os = "qnx",
        target_os = "openbsd",
        target_os = "fuchsia",
        target_os = "managarm",
    ),
    unsafe(link_section = ".init_array")
)]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__mod_init_func,mod_init_funcs"))]
#[cfg_attr(target_os = "windows", unsafe(link_section = ".CRT$XCU"))]
#[used]
static INITIALIZER: extern "C" fn() = initialize;

fn main() {
    assert!(INITIALIZED.load(core::sync::atomic::Ordering::Relaxed));
    println!("initialized");
}
"#;

    let verified = analyzer
        .reduce_and_verify(&input(source, &target))
        .expect("a used constructor static must be reducible");
    assert_verified("used constructor static", source, expected, &verified);

    let fixed = analyzer
        .reduce_and_verify(&input(expected, &target))
        .expect("a reduced constructor static must remain reducible");
    assert_eq!(fixed.reduced_source(), expected);

    let original_output = compile_and_run(source, &target, "constructor_static_original");
    let reduced_output = compile_and_run(
        verified.reduced_source(),
        &target,
        "constructor_static_reduced",
    );
    assert!(original_output.status.success());
    assert_eq!(original_output.stdout, b"initialized\n");
    assert!(original_output.stderr.is_empty());
    assert_eq!(reduced_output.status, original_output.status);
    assert_eq!(reduced_output.stdout, original_output.stdout);
    assert_eq!(reduced_output.stderr, original_output.stderr);
}

#[cfg(all(rust_item_dependencies_patched, target_arch = "x86_64"))]
#[test]
fn x86_sysroot_sources_are_not_treated_as_user_inputs() {
    let cases = [
        (
            "x86 feature detection",
            concat!(
                "fn unused() {}\n",
                "fn main() {\n",
                "    let _ = std::is_x86_feature_detected!(\"avx2\");\n",
                "}\n",
            ),
            concat!(
                "\n",
                "fn main() {\n",
                "    let _ = std::is_x86_feature_detected!(\"avx2\");\n",
                "}\n",
            ),
        ),
        (
            "x86 intrinsic",
            concat!(
                "fn unused() {}\n",
                "fn main() {\n",
                "    unsafe { core::arch::x86_64::_mm_pause() };\n",
                "}\n",
            ),
            concat!(
                "\n",
                "fn main() {\n",
                "    unsafe { core::arch::x86_64::_mm_pause() };\n",
                "}\n",
            ),
        ),
    ];
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();

    for (case, source, expected) in cases {
        let verified = analyzer
            .reduce_and_verify(&input(source, &target))
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert_verified(case, source, expected, &verified);

        let fixed = analyzer
            .reduce_and_verify(&input(verified.reduced_source(), &target))
            .unwrap_or_else(|error| panic!("{case} fixed point: {error:?}"));
        assert_eq!(fixed.reduced_source(), expected, "{case}");
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn builtin_test_attributes_are_accepted_and_their_unreachable_items_are_removed() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let cases = [
        (
            "written and cfg_attr test attributes",
            "use std::prelude::v1::test as renamed_test;#[test]fn test_only(){}#[renamed_test]fn renamed_test_only(){}#[cfg_attr(all(),test)]fn cfg_test_only(){macro_rules! local{()=>{1}}let _=local!();}#[cfg_attr(all(),derive(Clone))]struct Live;fn main(){let _=Live.clone();}",
            "#[cfg_attr(all(),derive(Clone))]struct Live;fn main(){let _=Live.clone();}",
        ),
        (
            "generated test attribute",
            "macro_rules! tests{()=>{#[test]fn generated_test(){macro_rules! local{()=>{1}}let _=local!();}}}tests!();fn main(){}",
            "fn main(){}",
        ),
        (
            "test attribute on a macro invocation",
            "macro_rules! item{()=>{fn generated(){}}}#[test]item!();fn main(){}",
            "fn main(){}",
        ),
    ];

    for (case, source, expected) in cases {
        let verified = analyzer
            .reduce_and_verify(&input(source, &target))
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert_verified(case, source, expected, &verified);

        let fixed = analyzer
            .reduce_and_verify(&input(verified.reduced_source(), &target))
            .unwrap_or_else(|error| panic!("{case} fixed point: {error:?}"));
        assert_eq!(fixed.reduced_source(), verified.reduced_source(), "{case}");
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn an_edition_error_is_reported_before_the_recovery_ast_is_inspected() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = concat!(
        "macro_rules! array {\n",
        "    ([|$item:pat| $expression:expr]) => {};\n",
        "}\n",
        "fn main() {}\n",
    );
    let error = analyzer
        .analyze(&SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        })
        .unwrap_err();
    let AnalysisError::OriginalCompilationFailed(diagnostics) = error else {
        panic!("unexpected parser-error result: {error:?}");
    };
    let start = source.find("$item:pat|").unwrap() + "$item:pat".len();
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .range
            .is_some_and(|range| range.start as usize == start && range.end as usize == start + 1)
    }));
}

#[cfg(rust_item_dependencies_patched)]
fn assert_verified(case: &str, original: &str, expected: &str, verified: &VerifiedReduction) {
    assert_eq!(verified.reduced_source(), expected, "{case}");
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash(),
        "{case}"
    );
    assert_eq!(
        verified
            .pieces()
            .iter()
            .map(|piece| {
                &original[piece.original_range.start as usize..piece.original_range.end as usize]
            })
            .collect::<String>(),
        expected,
        "{case}"
    );
}

#[cfg(rust_item_dependencies_patched)]
fn compile_and_run(source: &str, target: &str, crate_name: &str) -> std::process::Output {
    use std::process::Command;

    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("acceptance")
        .join("linked-programs");
    std::fs::create_dir_all(&directory).expect("the acceptance output directory must be writable");
    let source_path = directory.join(format!("{crate_name}.rs"));
    std::fs::write(&source_path, source).expect("the acceptance source must be writable");
    let executable = directory.join(format!("{crate_name}{}", std::env::consts::EXE_SUFFIX));
    let compiled = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg(source_path)
        .args(["--crate-name", crate_name, "--crate-type=bin"])
        .arg("--edition=2024")
        .args(["--target", target, "-Awarnings", "-o"])
        .arg(&executable)
        .output()
        .expect("the acceptance compiler must finish");
    assert!(
        compiled.status.success(),
        "linking {crate_name} failed:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    Command::new(executable)
        .output()
        .expect("the linked acceptance program must start")
}

#[cfg(rust_item_dependencies_patched)]
fn input(source: &str, target: &str) -> SourceInput {
    input_with_edition(source, target, Edition::Rust2024)
}

#[cfg(rust_item_dependencies_patched)]
fn input_with_edition(source: &str, target: &str, edition: Edition) -> SourceInput {
    SourceInput {
        source: source.to_owned(),
        edition,
        target: target.to_owned(),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn host_target() -> String {
    let output = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("-Vv")
        .output()
        .expect("rustc -Vv must start");
    assert!(output.status.success());
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .unwrap()
        .to_owned()
}
