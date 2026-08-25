#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::dependency_graph::{
    DependencyKind, ExpansionKind, GraphNode, ProofNodeKind, ProofRelationKind, RootReason,
};
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
fn analysis_and_verified_reduction_are_owned_read_only_results() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let target = host_target();
    let source = concat!(
        "#[doc = \"rust-item-dependencies:tag=kept\"]\n",
        "struct Kept(u32);\n",
        "#[doc = \"rust-item-dependencies:tag=dead\"]\n",
        "fn dead() {}\n",
        "fn value(value: Kept) -> u32 { value.0 }\n",
        "fn main() { let _ = value(Kept(1)); }\n",
    );
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, target);

    let analysis = analyzer.analyze(&input).expect("analysis must succeed");
    assert!(analysis.tags().contains("kept"));
    assert!(!analysis.tags().contains("dead"));
    assert!(!analysis.removed_source_units().is_empty());
    assert_eq!(analysis.source_digest().len(), 32);
    assert_eq!(analysis.graph().roots, analysis.roots());
    assert!(
        analysis
            .retained_source_units()
            .is_disjoint(analysis.removed_source_units())
    );
    assert_eq!(
        analysis.retained_source_units().len() + analysis.removed_source_units().len(),
        analysis.source_units().len()
    );
    let main = analysis
        .roots()
        .iter()
        .find(|root| root.reason == RootReason::Main)
        .expect("a binary analysis must expose its main root");
    assert!(analysis.graph().outgoing(main.node).next().is_some());
    assert_eq!(analyzer.analyze(&input).unwrap(), analysis);

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("the reduced compiler decisions must match");
    assert!(!verified.reduced_source().contains("fn dead"));
    assert!(verified.reduced_source().contains("fn main"));
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash()
    );
    assert_eq!(
        verified.original_analysis().source_digest(),
        analysis.source_digest()
    );
    assert_eq!(verified.original_analysis().recipe(), analysis.recipe());
    assert_eq!(
        verified.pieces().last().unwrap().output_range.end as usize,
        verified.reduced_source().len()
    );
    let rebuilt = verified
        .pieces()
        .iter()
        .map(|piece| {
            &source[piece.original_range.start as usize..piece.original_range.end as usize]
        })
        .collect::<String>();
    assert_eq!(rebuilt, verified.reduced_source());

    let second = analyzer
        .reduce_and_verify(&SourceInput::binary(
            verified.reduced_source().to_owned(),
            input.edition,
            input.target.clone(),
        ))
        .expect("an already reduced source must remain byte-identical");
    assert_eq!(second.reduced_source(), verified.reduced_source());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn compiler_recipe_identifies_normalized_compilation_options_but_not_source_text() {
    let target = host_target();
    let input = SourceInput::binary(
        "fn unused() {}\nfn main() {}\n".to_owned(),
        Edition::Rust2024,
        target.clone(),
    );
    let reordered_options = CompilationOptions::new()
        .with_optimization_level(OptimizationLevel::O2)
        .with_cfg("SECOND")
        .with_cfg("ONLINE_JUDGE");
    let ordered_analysis = Analyzer::new_with_options(
        CompilationOptions::new()
            .with_cfg("ONLINE_JUDGE")
            .with_cfg("SECOND")
            .with_cfg("ONLINE_JUDGE")
            .with_optimization_level(OptimizationLevel::O2),
    )
    .expect("valid compilation options must be accepted")
    .analyze(&input)
    .expect("the first source must compile");
    let reordered_analyzer = Analyzer::new_with_options(reordered_options)
        .expect("the reordered compilation options must be accepted");
    let reordered_analysis = reordered_analyzer
        .analyze(&input)
        .expect("the first source must compile with reordered options");

    assert_eq!(reordered_analysis.recipe(), ordered_analysis.recipe());
    assert_eq!(
        reordered_analysis.source_digest(),
        ordered_analysis.source_digest()
    );

    let other_source = SourceInput::binary(
        "fn main() { let _ = 1_u32; }\n".to_owned(),
        Edition::Rust2024,
        target,
    );
    let other_source_analysis = reordered_analyzer
        .analyze(&other_source)
        .expect("the second source must compile with the same options");
    assert_eq!(other_source_analysis.recipe(), ordered_analysis.recipe());
    assert_ne!(
        other_source_analysis.source_digest(),
        ordered_analysis.source_digest()
    );

    let different_cfg = Analyzer::new_with_options(
        CompilationOptions::new()
            .with_optimization_level(OptimizationLevel::O2)
            .with_cfg("ONLINE_JUDGE"),
    )
    .expect("a different valid cfg set must be accepted")
    .analyze(&input)
    .expect("the first source must compile with a different cfg set");
    assert_ne!(different_cfg.recipe(), ordered_analysis.recipe());

    let different_optimization = Analyzer::new_with_options(
        CompilationOptions::new()
            .with_optimization_level(OptimizationLevel::O3)
            .with_cfg("SECOND")
            .with_cfg("ONLINE_JUDGE"),
    )
    .expect("a different optimization level must be accepted")
    .analyze(&input)
    .expect("the first source must compile with a different optimization level");
    assert_ne!(different_optimization.recipe(), ordered_analysis.recipe());
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn unselected_macro_rules_are_physically_removed_and_idempotent() {
    use rust_item_dependencies::source::WrittenUnitKind;

    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = include_str!("fixtures/compiler/macro_rule_reduction.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_reduction.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("unused macro rules must preserve compiler decisions");
    assert_eq!(verified.reduced_source(), expected);
    assert!(verified.reduced_source().len() < source.len());
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash()
    );

    let analysis = verified.original_analysis();
    assert_eq!(
        analysis
            .source_units()
            .iter()
            .filter(|unit| unit.kind == WrittenUnitKind::MacroDefinition)
            .count(),
        3,
        "a macro definition forwarded through an expansion must not become a written source unit"
    );
    let rules = analysis
        .source_units()
        .iter()
        .filter(|unit| unit.kind == WrittenUnitKind::MacroRule)
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 6);
    assert!(rules.iter().all(|rule| {
        rule.parent.is_some_and(|parent| {
            analysis.source_units()[parent.0 as usize].kind == WrittenUnitKind::MacroDefinition
        })
    }));
    let removed = rules
        .iter()
        .filter(|rule| analysis.removed_source_units().contains(&rule.id))
        .map(|rule| &source[rule.full_range.start as usize..rule.full_range.end as usize])
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        removed,
        std::collections::BTreeSet::from([
            concat!(
                "(@unused) => {\n",
                "        compile_error!(\"an unselected rule must be removable\");\n",
                "    };"
            ),
            concat!(
                "(@unused) => {\n",
                "        compile_error!(\"removing a leading rule changes raw indices\");\n",
                "    };"
            ),
        ])
    );
    assert_eq!(
        rules
            .iter()
            .filter(|rule| analysis.retained_source_units().contains(&rule.id))
            .count(),
        4
    );
    assert_eq!(
        verified
            .pieces()
            .iter()
            .map(|piece| {
                &source[piece.original_range.start as usize..piece.original_range.end as usize]
            })
            .collect::<String>(),
        expected
    );

    let second = analyzer
        .reduce_and_verify(&SourceInput::binary(
            expected.to_owned(),
            input.edition,
            input.target,
        ))
        .expect("a reduced macro rule inventory must be byte-idempotent");
    assert_eq!(second.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn unreachable_macro_expansions_and_their_selected_rules_are_removed_together() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = include_str!("fixtures/compiler/macro_rule_expansion_retention.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_expansion_retention.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("an unreachable expansion and its private rule must be removed together");
    assert_eq!(verified.reduced_source(), expected);

    let second = analyzer
        .reduce_and_verify(&SourceInput::binary(
            verified.reduced_source().to_owned(),
            input.edition,
            input.target,
        ))
        .expect("the first reduction must already be a fixed point");
    assert_eq!(second.reduced_source(), expected);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn same_rule_expansion_subtrees_stabilize_repeated_identity() {
    use rust_item_dependencies::source::WrittenUnitKind;

    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let source = include_str!("fixtures/compiler/macro_rule_expansion_identity.rs");
    let expected = include_str!("fixtures/compiler/macro_rule_expansion_identity.expected.rs");
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("deleting leading rules must not reorder repeated semantic expansions");
    assert_eq!(verified.reduced_source(), expected);
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash()
    );
    let analysis = verified.original_analysis();
    let removed = analysis
        .source_units()
        .iter()
        .filter(|unit| {
            unit.kind == WrittenUnitKind::MacroRule
                && analysis.removed_source_units().contains(&unit.id)
        })
        .map(|unit| &source[unit.full_range.start as usize..unit.full_range.end as usize])
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        removed,
        std::collections::BTreeSet::from(["( unused ) => { } ;"])
    );

    let mut selected_rules = std::collections::BTreeMap::<&str, usize>::new();
    for expansion in &analysis.graph().expansions {
        let part = expansion
            .key
            .0
            .last()
            .expect("an expansion key must be nonempty");
        if !matches!(
            &part.kind,
            ExpansionKind::Macro { name, .. } if name == "m"
        ) {
            continue;
        }
        let range = part
            .selected_macro_rule
            .expect("every fixture expansion must select a written macro rule");
        *selected_rules
            .entry(&source[range.start as usize..range.end as usize])
            .or_default() += 1;
    }
    assert_eq!(
        selected_rules,
        std::collections::BTreeMap::from([
            (
                "( ( $ ( $ t : tt ) ,* ) ) => { ( $ ( m ! ( same $ t ) ) ,* ) } ;",
                1,
            ),
            ("( same $ t : tt ) => { m ! ( $ t ) } ;", 2),
            ("( wrap ) => { m ! ( base ) } ;", 1),
            ("( base ) => { 0usize } ;", 2),
        ])
    );

    let second = analyzer
        .reduce_and_verify(&SourceInput::binary(
            expected.to_owned(),
            input.edition,
            input.target,
        ))
        .expect("an already reduced same-rule fixture must remain byte-identical");
    assert_eq!(second.reduced_source(), expected);
    assert_eq!(
        second.verification().original_snapshot_hash(),
        second.verification().reduced_snapshot_hash()
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn fulfillment_dependencies_are_canonical_across_codegen_queries() {
    let analyzer = Analyzer::new().expect("the qualified compiler artifact must be accepted");
    let input = SourceInput::binary(
        include_str!("fixtures/compiler/fulfillment_order.rs").to_owned(),
        Edition::Rust2024,
        host_target(),
    );

    let analysis = analyzer
        .analyze(&input)
        .expect("reordered fulfillment dependencies must merge");
    assert_eq!(analyzer.analyze(&input).unwrap(), analysis);
    let graph = analysis.graph();
    let candidates = graph
        .proofs
        .iter()
        .filter(|proof| {
            matches!(
                &proof.kind,
                ProofNodeKind::Obligation {
                    fulfillment_nested: Some(nested),
                    ..
                } if nested.len() == 8
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(candidates.len(), 4);
    for owner in candidates {
        let ProofNodeKind::Obligation {
            fulfillment_nested: Some(nested),
            ..
        } = &owner.kind
        else {
            unreachable!()
        };
        assert!(nested.windows(2).all(|pair| {
            graph.proofs[pair[0].0 as usize].key < graph.proofs[pair[1].0 as usize].key
        }));

        let mut relations = graph
            .edges
            .iter()
            .filter_map(|edge| match &edge.kind {
                DependencyKind::ProofRelation {
                    relation: ProofRelationKind::FulfillmentNested,
                    ordinal,
                } if edge.from == GraphNode::Proof(owner.id) => Some((*ordinal, edge.to)),
                _ => None,
            })
            .collect::<Vec<_>>();
        relations.sort_by_key(|(ordinal, _)| *ordinal);
        assert_eq!(
            relations,
            nested
                .iter()
                .enumerate()
                .map(|(ordinal, &target)| {
                    (u32::try_from(ordinal).unwrap(), GraphNode::Proof(target))
                })
                .collect::<Vec<_>>()
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn runtime_location_changes_do_not_change_the_decision_snapshot() {
    let analyzer = Analyzer::new().unwrap();
    let input = SourceInput::binary(
        concat!(
            "fn dead() {}\n",
            "#[track_caller] fn caller() -> (&'static str, u32, u32, u32) {\n",
            "    let location = std::panic::Location::caller();\n",
            "    (file!(), line!(), column!(), location.line())\n",
            "}\n",
            "fn main() { let _ = caller(); }\n",
        )
        .to_owned(),
        Edition::Rust2024,
        host_target(),
    );

    let verified = analyzer.reduce_and_verify(&input).unwrap();
    assert!(!verified.reduced_source().contains("fn dead"));
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash()
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn compiler_decision_changes_caused_by_line_are_rejected() {
    let analyzer = Analyzer::new().unwrap();
    let input = SourceInput::binary(concat!(
            "trait Pick { fn value() -> u32; }\n",
            "struct Line<const N: u32>;\n",
            "macro_rules! impls { () => { impl Pick for Line<6> { fn value()->u32{6} } impl Pick for Line<8> { fn value()->u32{8} } }; }\n",
            "impls!();\n",
            "fn dead() {\n",
            "    let _ = 0;\n",
            "}\n",
            "fn main() { let _ = <Line<{ line!() }> as Pick>::value(); }\n",
        )
        .to_owned(), Edition::Rust2024, host_target());

    let result = analyzer.reduce_and_verify(&input);
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

    let verified = analyzer
        .reduce_and_verify(&input)
        .expect("deleting an unused nested import must preserve compiler decisions");
    assert!(!verified.reduced_source().contains("fmt::{Debug}"));
    assert!(!verified.reduced_source().contains("collections::HashMap"));
    assert!(verified.reduced_source().contains("marker::{PhantomData}"));
    assert_eq!(
        verified.verification().original_snapshot_hash(),
        verified.verification().reduced_snapshot_hash()
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn empty_tag_is_a_typed_error() {
    let analyzer = Analyzer::new().unwrap();
    let source = "#[doc = \"rust-item-dependencies:tag=\"]\nfn main() {}\n";
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let error = analyzer.analyze(&input).unwrap_err();
    let AnalysisError::InvalidTag { range } = error else {
        panic!("unexpected error: {error:?}");
    };
    assert_eq!(
        &source[range.start as usize..range.end as usize],
        "#[doc = \"rust-item-dependencies:tag=\"]"
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn original_compiler_diagnostics_are_owned_and_source_anchored() {
    let analyzer = Analyzer::new().unwrap();
    let source = "fn main() { let value: u32 = \"not a number\"; }\n";
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let AnalysisError::OriginalCompilationFailed(diagnostics) =
        analyzer.analyze(&input).unwrap_err()
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

    analyzer
        .analyze(&input)
        .expect("the original source fulfills its lint expectation");
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
    let input = SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target());

    let AnalysisError::ReducedCompilationFailed(diagnostics) =
        analyzer.reduce_and_verify(&input).unwrap_err()
    else {
        panic!("the location-dependent reduced source must fail compilation");
    };
    let main_start = source.find("fn main").unwrap() as u32;
    assert!(diagnostics.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .range
            .is_some_and(|range| range.start >= main_start && range.end as usize <= source.len())
    }));
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn tags_follow_expanded_definitions_and_semantic_reachability() {
    let analyzer = Analyzer::new().unwrap();
    let input = SourceInput::binary(concat!(
            "#![doc = \"rust-item-dependencies:tag=inner-is-ignored\"]\n",
            "macro_rules! tagged { () => { #[doc = concat!(\"rust-item-dependencies:\", \"tag=generated\")] struct Generated; }; }\n",
            "tagged!();\n",
            "///rust-item-dependencies:tag=sugared\n",
            "#[doc = \"rust-item-dependencies:tag=sugared\"]\n",
            "fn use_generated(_: Generated) {}\n",
            "#[doc = \"rust-item-dependencies:tag=dead\"] fn dead() {}\n",
            "fn main() { use_generated(Generated); }\n",
        )
        .to_owned(), Edition::Rust2024, host_target());

    let analysis = analyzer.analyze(&input).unwrap();
    assert_eq!(
        analysis.tags(),
        &std::collections::BTreeSet::from(["generated".to_owned(), "sugared".to_owned()])
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
