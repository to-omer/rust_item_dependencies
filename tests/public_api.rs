#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::error::DiagnosticLevel;
use rust_item_dependencies::{AnalysisError, Analyzer};
#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::{CompilationOptions, Edition, OptimizationLevel, SourceInput};

#[cfg(not(rust_item_dependencies_patched))]
#[test]
fn stock_compiler_is_not_accepted_as_an_analyzer_artifact() {
    assert!(matches!(
        Analyzer::new(),
        Err(AnalysisError::CompilerArtifactMismatch)
    ));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn high_level_reduction_removes_dead_code_and_reaches_a_fixed_point() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "struct Kept(u32);\n",
        "fn dead() {}\n",
        "fn value(value: Kept) -> u32 { value.0 }\n",
        "fn main() { let _ = value(Kept(1)); }\n",
    );
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, target.clone());

    let reduction = analyzer
        .reduce(&input)
        .expect("the reduced compiler decisions must match");
    assert!(!reduction.reduced_source().contains("fn dead"));
    assert!(reduction.reduced_source().contains("fn main"));

    let second = analyzer
        .reduce(&SourceInput::binary(
            reduction.reduced_source().to_owned(),
            Edition::Rust2024,
            target,
        ))
        .expect("an already reduced source must remain byte-identical");
    assert_eq!(second.reduced_source(), reduction.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn compilation_options_are_accepted_by_the_high_level_api() {
    let analyzer = Analyzer::new_with_options(
        CompilationOptions::new()
            .with_cfg("ONLINE_JUDGE")
            .with_optimization_level(OptimizationLevel::O2),
    )
    .expect("valid compilation options must be accepted");
    let input = SourceInput::binary(
        concat!(
            "#[cfg(ONLINE_JUDGE)] fn value() -> u32 { 1 }\n",
            "#[cfg(not(ONLINE_JUDGE))] fn value() -> u32 { 2 }\n",
            "fn dead() {}\n",
            "fn main() { assert_eq!(value(), 1); }\n",
        )
        .to_owned(),
        Edition::Rust2024,
        host_target(),
    );

    let reduction = analyzer
        .reduce(&input)
        .expect("the configured source must be reducible");
    assert!(!reduction.reduced_source().contains("fn dead"));
    assert!(reduction.reduced_source().contains("assert_eq!"));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn no_effect_cfg_attrs_are_removed() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = "#[cfg_attr(any(),allow(dead_code))]fn main(){}";
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let reduction = analyzer
        .reduce(&input)
        .expect("removing the attribute must preserve compiler decisions");
    assert_eq!(reduction.reduced_source(), "fn main(){}");
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn binary_exported_macros_remove_unselected_rules_and_dead_selected_components() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = include_str!("fixtures/compiler/macro_rule_reduction.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_reduction.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, target.clone());

    let reduction = analyzer
        .reduce(&input)
        .expect("binary-local exported macros must be reducible");
    assert_eq!(reduction.reduced_source(), expected);
    assert!(reduction.reduced_source().len() < source.len());
    assert!(!reduction.reduced_source().contains("selected_dead_local"));
    assert!(!reduction.reduced_source().contains("selected_dead_item"));
    assert!(reduction.reduced_source().contains("fn value"));

    let second = analyzer
        .reduce(&SourceInput::binary(
            expected.to_owned(),
            Edition::Rust2024,
            target,
        ))
        .expect("a reduced macro rule inventory must be byte-idempotent");
    assert_eq!(second.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn unreachable_macro_expansions_and_their_selected_rules_are_removed_together() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = include_str!("fixtures/compiler/macro_rule_expansion_retention.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_expansion_retention.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, target.clone());

    let reduction = analyzer
        .reduce(&input)
        .expect("an unreachable expansion and its private rule must be removed together");
    assert_eq!(reduction.reduced_source(), expected);

    let second = analyzer
        .reduce(&SourceInput::binary(
            reduction.reduced_source().to_owned(),
            Edition::Rust2024,
            target,
        ))
        .expect("the first reduction must already be a fixed point");
    assert_eq!(second.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn same_rule_expansion_subtrees_stabilize_repeated_identity() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = include_str!("fixtures/compiler/macro_rule_expansion_identity.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_expansion_identity.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, target.clone());

    let reduction = analyzer
        .reduce(&input)
        .expect("deleting leading rules must not reorder repeated semantic expansions");
    assert_eq!(reduction.reduced_source(), expected);

    let second = analyzer
        .reduce(&SourceInput::binary(
            expected.to_owned(),
            Edition::Rust2024,
            target,
        ))
        .expect("an already reduced same-rule fixture must remain byte-identical");
    assert_eq!(second.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn runtime_location_changes_do_not_change_the_decision_snapshot() {
    let analyzer = Analyzer::new().unwrap();
    let source = concat!(
        "fn dead() {\n",
        "    let _ = 0;\n",
        "}\n",
        "#[track_caller] fn caller() -> (&'static str, u32, u32, u32) {\n",
        "    let location = std::panic::Location::caller();\n",
        "    (file!(), line!(), column!(), location.line())\n",
        "}\n",
        "fn main() { let _ = caller(); }\n",
    );
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target())
        .with_source_paths("original.rs", "reduced.rs");

    let reduction = analyzer.reduce(&input).unwrap();
    assert!(!reduction.reduced_source().contains("fn dead"));
    let line_number = |text: &str| {
        text[..text.find("line!()").unwrap()]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1
    };
    assert_ne!(line_number(source), line_number(reduction.reduced_source()));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn virtual_source_paths_determine_compiler_decisions() {
    let analyzer = Analyzer::new().unwrap();
    let target = host_target();
    let source = include_str!("fixtures/compiler/source_filename.rs");
    for (name, kept, removed) in [
        ("main.rs", "true", "false"),
        ("virtual.rs", "false", "true"),
    ] {
        let input =
            SourceInput::binary(source, Edition::Rust2024, &target).with_source_paths(name, name);
        let reduction = analyzer.reduce(&input).unwrap();
        assert!(
            reduction
                .reduced_source()
                .contains(&format!("impl Pick for Flag<{kept}>"))
        );
        assert!(
            !reduction
                .reduced_source()
                .contains(&format!("impl Pick for Flag<{removed}>"))
        );
        let second = analyzer
            .reduce(
                &SourceInput::binary(reduction.reduced_source(), Edition::Rust2024, &target)
                    .with_source_paths(name, name),
            )
            .unwrap();
        assert_eq!(second.reduced_source(), reduction.reduced_source());
    }

    let source = source.replace(
        "fn main() {",
        "fn main() { let _ = (<Flag<true> as Pick>::value, <Flag<false> as Pick>::value);",
    );
    let input = SourceInput::binary(source, Edition::Rust2024, target)
        .with_source_paths("main.rs", "virtual.rs");
    assert!(matches!(
        analyzer.reduce(&input),
        Err(AnalysisError::DecisionMismatch(_))
    ));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn named_source_diagnostics_survive_parsing_and_offset_normalization() {
    let analyzer = Analyzer::new().unwrap();
    let target = host_target();
    for (body, marker) in [
        ("fn main() { let broken: = 0; }\n", "="),
        ("fn main() { let _: u32 = \"型エラー\"; }\n", "\"型エラー\""),
    ] {
        for source in [
            format!("// 日本語\n{body}"),
            format!("\u{feff}// 日本語\r\n{}", body.replace('\n', "\r\n")),
        ] {
            let input = SourceInput::binary(&source, Edition::Rust2024, &target)
                .with_source_paths("virtual/input.rs", "virtual/output.rs");
            let result = analyzer.reduce(&input);
            let Err(AnalysisError::OriginalCompilationFailed(diagnostics)) = result else {
                panic!("expected original diagnostics: {result:?}");
            };
            assert!(
                diagnostics
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.range.is_some_and(|range| &source
                        [range.start as usize..range.end as usize]
                        == marker)),
                "{diagnostics:?}"
            );
        }
    }
}

#[cfg(all(rust_item_dependencies_patched, unix))]
#[test]
fn non_utf8_virtual_source_paths_are_kept_as_paths() {
    use std::os::unix::ffi::OsStringExt;

    let analyzer = Analyzer::new().unwrap();
    let target = host_target();
    let original =
        std::path::PathBuf::from(std::ffi::OsString::from_vec(b"named-\xff.rs".to_vec()));
    let reduced =
        std::path::PathBuf::from(std::ffi::OsString::from_vec(b"output-\xfe.rs".to_vec()));
    let input = SourceInput::binary(
        include_str!("fixtures/compiler/source_filename.rs"),
        Edition::Rust2024,
        &target,
    )
    .with_source_paths(&original, &reduced);
    let reduction = analyzer.reduce(&input).unwrap();
    assert!(
        reduction
            .reduced_source()
            .contains("impl Pick for Flag<false>")
    );
    assert!(
        !reduction
            .reduced_source()
            .contains("impl Pick for Flag<true>")
    );
    let second = analyzer
        .reduce(
            &SourceInput::binary(reduction.reduced_source(), Edition::Rust2024, target)
                .with_source_paths(&reduced, &reduced),
        )
        .unwrap();
    assert_eq!(second.reduced_source(), reduction.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn compiler_decision_changes_caused_by_line_are_rejected() {
    let analyzer = Analyzer::new().unwrap();
    let input = SourceInput::binary(
        concat!(
            "trait Pick { fn value() -> u32; }\n",
            "struct Line<const N: u32>;\n",
            "macro_rules! impls { () => { impl Pick for Line<6> { fn value()->u32{6} } impl Pick for Line<8> { fn value()->u32{8} } }; }\n",
            "impls!();\n",
            "fn dead() {\n",
            "    let _ = 0;\n",
            "}\n",
            "fn main() { let _ = (<Line<6> as Pick>::value, <Line<8> as Pick>::value); let _ = <Line<{ line!() }> as Pick>::value(); }\n",
        )
        .to_owned(),
        Edition::Rust2024,
        host_target(),
    );

    let result = analyzer.reduce(&input);
    let Err(AnalysisError::DecisionMismatch(difference)) = result else {
        panic!("expected a compiler-decision mismatch: {result:?}");
    };
    assert_eq!(difference.differences().len(), 1);
    assert!(!difference.differences()[0].original.is_empty());
    assert!(!difference.differences()[0].reduced.is_empty());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn deleted_nested_use_prefix_is_not_a_compiler_decision_mismatch() {
    let analyzer = Analyzer::new().unwrap();
    let input = SourceInput::binary(
        concat!(
            "use std::{fmt::{Debug}, marker::{PhantomData}, collections::HashMap};\n",
            "fn main() { let _: PhantomData<u8> = PhantomData; }\n",
        )
        .to_owned(),
        Edition::Rust2024,
        host_target(),
    );

    let reduction = analyzer
        .reduce(&input)
        .expect("deleting an unused nested import must preserve compiler decisions");
    assert!(!reduction.reduced_source().contains("fmt::{Debug}"));
    assert!(!reduction.reduced_source().contains("collections::HashMap"));
    assert!(reduction.reduced_source().contains("marker::{PhantomData}"));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn original_compiler_diagnostics_are_owned_and_source_anchored() {
    let analyzer = Analyzer::new().unwrap();
    let source = "\u{feff}// 日本語\r\nfn main() { let value: u32 = \"not a number\"; let flag: bool = 0; }\r\n";
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let AnalysisError::OriginalCompilationFailed(diagnostics) =
        analyzer.reduce(&input).unwrap_err()
    else {
        panic!("invalid source must return its compiler diagnostics");
    };
    assert!(!diagnostics.diagnostics().is_empty());
    assert!(diagnostics.diagnostics().iter().all(|diagnostic| {
        !diagnostic.message.is_empty()
            && diagnostic
                .range
                .is_none_or(|range| range.start <= range.end && range.end as usize <= source.len())
    }));
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic.range.is_some_and(|range| {
            &source[range.start as usize..range.end as usize] == "\"not a number\""
        })
    }));
    assert_eq!(
        diagnostics
            .diagnostics()
            .iter()
            .filter(|diagnostic| {
                diagnostic.level == DiagnosticLevel::Error
                    && diagnostic.message == "mismatched types"
            })
            .count(),
        2,
    );
    for (message, text) in [
        ("expected `u32`, found `&str`", "\"not a number\""),
        ("expected due to this", "u32"),
        ("expected `bool`, found integer", "0"),
    ] {
        assert!(
            diagnostics.diagnostics().iter().any(|diagnostic| {
                diagnostic.level == DiagnosticLevel::Note
                    && diagnostic.message == message
                    && diagnostic.range.is_some_and(|range| {
                        &source[range.start as usize..range.end as usize] == text
                    })
            }),
            "missing {message}: {diagnostics:?}"
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn compiler_notes_and_suggestion_help_reach_the_public_api() {
    let analyzer = Analyzer::new().unwrap();
    let cases = [
        (
            "trait Mark {}\nfn need<T: Mark>(_: T) {}\nfn main() { need(1u8); }\n",
            "required by a bound in `need`",
            DiagnosticLevel::Note,
            "Mark",
            "T: ",
        ),
        (
            "trait Mark {}\nfn need<T: Mark>(_: T) {}\nfn main() { need(1u8); }\n",
            "this trait has no implementations, consider adding one",
            DiagnosticLevel::Help,
            "trait Mark",
            "",
        ),
        (
            "fn consume(_: &str) {}\nfn main() { let value = String::new(); consume(value); }\n",
            "consider borrowing here",
            DiagnosticLevel::Help,
            "",
            "consume(",
        ),
    ];
    for (source, message, level, text, prefix) in cases {
        let input = SourceInput::binary(source, Edition::Rust2024, host_target());
        let AnalysisError::OriginalCompilationFailed(diagnostics) =
            analyzer.reduce(&input).unwrap_err()
        else {
            panic!("invalid input must return compiler diagnostics");
        };
        let position = source.rfind(&format!("{prefix}{text}")).unwrap() + prefix.len();
        assert!(
            diagnostics.diagnostics().iter().any(|diagnostic| {
                diagnostic.level == level
                    && diagnostic.message == message
                    && diagnostic.range
                        == Some(rust_item_dependencies::ByteRange {
                            start: position as u32,
                            end: (position + text.len()) as u32,
                        })
            }),
            "missing {message}: {diagnostics:?}"
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn deny_by_default_lints_reject_the_original_source() {
    let analyzer = Analyzer::new().unwrap();
    let source = "fn main() { let value: u8 = 256; println!(\"{value}\"); }\n";
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let AnalysisError::OriginalCompilationFailed(diagnostics) =
        analyzer.reduce(&input).unwrap_err()
    else {
        panic!("a deny-by-default lint must reject the original source");
    };
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .range
            .is_some_and(|range| &source[range.start as usize..range.end as usize] == "256")
    }));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn reduction_rejects_new_unfulfilled_lint_expectations() {
    let analyzer = Analyzer::new().unwrap();
    let source = concat!(
        "#![deny(unfulfilled_lint_expectations)]\n",
        "#[expect(unused_imports)]\n",
        "use std::fmt::{Debug, Display};\n",
        "fn main() { let _: &dyn Debug = &0; }\n",
    );
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let AnalysisError::ReducedCompilationFailed(diagnostics) = analyzer.reduce(&input).unwrap_err()
    else {
        panic!("the reduced source must be compiled before it is returned");
    };
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("lint expectation is unfulfilled")
    }));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn reduced_compiler_diagnostics_use_original_source_coordinates() {
    let analyzer = Analyzer::new().unwrap();
    let source = concat!(
        "trait Pick {}\n",
        "struct Line<const N: u32>;\n",
        "impl Pick for Line<8> {}\n",
        "fn dead() {\n",
        "    let _ = 0;\n",
        "}\n",
        "fn require<T: Pick>() {}\n",
        "fn main() { require::<Line<{ line!() }>>(); }\n",
    );
    let source = format!("\u{feff}{}", source.replace('\n', "\r\n"));
    let input = SourceInput::binary(&source, Edition::Rust2024, host_target())
        .with_source_paths("virtual/input.rs", "virtual/output.rs");

    let AnalysisError::ReducedCompilationFailed(diagnostics) = analyzer.reduce(&input).unwrap_err()
    else {
        panic!("the location-dependent reduced source must fail compilation");
    };
    let main_start = source.find("fn main").unwrap() as u32;
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .range
            .is_some_and(|range| range.start >= main_start && range.end as usize <= source.len())
    }));
    let bound = source.find("T: Pick").unwrap() + "T: ".len();
    assert!(
        diagnostics.diagnostics().iter().any(|diagnostic| {
            diagnostic.level == DiagnosticLevel::Note
                && diagnostic.message == "required by a bound in `require`"
                && diagnostic.range
                    == Some(rust_item_dependencies::ByteRange {
                        start: bound as u32,
                        end: (bound + "Pick".len()) as u32,
                    })
        }),
        "{diagnostics:?}"
    );
}

#[cfg(rust_item_dependencies_patched)]
fn host_target() -> String {
    let target = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .args(["-Vv"])
        .output()
        .expect("rustc -Vv must start");
    assert!(target.status.success());
    String::from_utf8(target.stdout)
        .unwrap()
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .unwrap()
        .to_owned()
}
