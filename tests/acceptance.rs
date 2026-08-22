#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::{
    AnalysisError, Analyzer, Edition, SourceInput, UnsupportedReason, VerifiedReduction,
};

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
fn an_external_proc_macro_is_rejected_at_the_written_attribute() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = include_str!("fixtures/acceptance/external_proc_macro.input.rs");
    let error = analyzer
        .analyze(&SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2018,
            target: host_target(),
        })
        .unwrap_err();
    let AnalysisError::UnsupportedInput {
        reason: UnsupportedReason::ProcMacro,
        range: Some(range),
    } = error
    else {
        panic!("unexpected external proc-macro result: {error:?}");
    };
    assert_eq!(
        &source[range.start as usize..range.end as usize],
        "#[fastout]"
    );
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
fn input(source: &str, target: &str) -> SourceInput {
    SourceInput {
        source: source.to_owned(),
        edition: Edition::Rust2024,
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
