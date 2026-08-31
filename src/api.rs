//! Public source reduction API.

use std::path::PathBuf;
#[cfg(all(test, rust_item_dependencies_patched))]
use std::process::Command;
use std::sync::Arc;

use crate::artifact::compiler_sysroot;
use crate::error::{
    AnalysisError, CompilerFailure, DecisionDifference, Diagnostic, DiagnosticBundle,
    DiagnosticLevel, ObservationGap, SnapshotDiff as PublicSnapshotDiff, SourceRewriteViolation,
};
use crate::input::{
    CompilationContext, InputError, InspectedDependencies, InspectedReduction,
    PreparedCompilationOptions,
    inspect_source_with_dependencies_at_original_coordinates_and_identity_in_context,
    inspect_source_with_reduction_in_context,
};
use crate::retention::external_compiler_outcome_difference;
use crate::rewrite::SourceRewriteError;
use crate::snapshot::{CompilerDecisionSnapshot, SnapshotDiff, SnapshotError};

pub use crate::input::{CompilationOptions, Edition, EntryPoint, OptimizationLevel, SourceInput};

#[derive(Clone, Debug)]
pub struct Analyzer {
    sysroot: PathBuf,
    compilation: Arc<PreparedCompilationOptions>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reduction {
    reduced_source: String,
}

impl Analyzer {
    pub fn new() -> Result<Self, AnalysisError> {
        Self::new_with_options(CompilationOptions::default())
    }

    pub fn new_with_options(options: CompilationOptions) -> Result<Self, AnalysisError> {
        artifact_context(options)
    }

    pub fn reduce(&self, input: &SourceInput) -> Result<Reduction, AnalysisError> {
        let context = self.compilation_context(input)?;
        let inspected = inspect_source_with_reduction_in_context(input.source(), &context)
            .map_err(|error| analysis_error(error, CompilationPhase::Original))?;
        let original_snapshot = CompilerDecisionSnapshot::original(
            &inspected.graph,
            &inspected.source,
            &inspected.retention,
            &inspected.rewrite,
        )
        .map_err(snapshot_error)?;

        let reduced = self.inspect_reduced(&context, &inspected)?;
        let reduced_outputless = reduced
            .complete_source_outputless_macro_expansions
            .as_ref()
            .ok_or_else(|| {
                analysis_error(
                    InputError::CompilerProtocolFailure,
                    CompilationPhase::Reduced,
                )
            })?;
        let reduced_snapshot = CompilerDecisionSnapshot::reduced_excluding_outputless_macros(
            &reduced.graph,
            reduced_outputless,
        )
        .map_err(snapshot_error)?;
        if let Some(difference) = original_snapshot.first_difference(&reduced_snapshot) {
            return Err(AnalysisError::DecisionMismatch(snapshot_difference(
                difference,
            )));
        }
        Ok(Reduction {
            reduced_source: inspected.rewrite.source,
        })
    }

    fn inspect_reduced(
        &self,
        context: &CompilationContext<'_>,
        original: &InspectedReduction,
    ) -> Result<InspectedDependencies, AnalysisError> {
        let reduced =
            inspect_source_with_dependencies_at_original_coordinates_and_identity_in_context(
                &original.rewrite.source,
                context,
                &original.rewrite,
                &original.definition_identity_universe,
            )
            .map_err(|error| analysis_error(error, CompilationPhase::Reduced))?;
        if let Some(difference) = external_compiler_outcome_difference(
            &original.external_compiler,
            &reduced.external_compiler,
        ) {
            return Err(AnalysisError::DecisionMismatch(PublicSnapshotDiff::new(
                vec![DecisionDifference {
                    kind: difference.kind().to_owned(),
                    original: difference.original(),
                    reduced: difference.reduced(),
                    range: None,
                }],
            )));
        }
        Ok(reduced)
    }

    fn compilation_context<'a>(
        &'a self,
        input: &'a SourceInput,
    ) -> Result<CompilationContext<'a>, AnalysisError> {
        CompilationContext::new(input, &self.compilation, &self.sysroot)
            .map_err(|error| analysis_error(error, CompilationPhase::Original))
    }
}

impl Reduction {
    pub fn reduced_source(&self) -> &str {
        &self.reduced_source
    }
}

fn artifact_context(options: CompilationOptions) -> Result<Analyzer, AnalysisError> {
    let compilation = PreparedCompilationOptions::prepare(options)?;
    let sysroot = compiler_sysroot().map_err(|_| AnalysisError::CompilerArtifactMismatch)?;
    Ok(Analyzer {
        sysroot,
        compilation: Arc::new(compilation),
    })
}

#[derive(Clone, Copy)]
enum CompilationPhase {
    Original,
    Reduced,
}

fn analysis_error(error: InputError, phase: CompilationPhase) -> AnalysisError {
    match error {
        InputError::InvalidCrateName { name } => AnalysisError::InvalidCrateName { name },
        InputError::MissingLibraryEntryPoint => AnalysisError::MissingLibraryEntryPoint,
        InputError::InvalidEntryPoint { path, reason } => {
            AnalysisError::InvalidEntryPoint { path, reason }
        }
        InputError::UnsupportedInput { reason, range } => {
            AnalysisError::UnsupportedInput { reason, range }
        }
        InputError::Dependency(crate::input::DependencyError::Retention(
            crate::retention::RetentionError::UnsupportedExternalNativeLink,
        )) => AnalysisError::UnsupportedInput {
            reason: crate::error::UnsupportedReason::ExternalNativeLink,
            range: None,
        },
        InputError::OriginalCompilationFailed(diagnostics) => {
            let diagnostics = DiagnosticBundle::new(
                diagnostics
                    .into_iter()
                    .map(|diagnostic| Diagnostic {
                        level: DiagnosticLevel::Error,
                        message: diagnostic.message,
                        range: diagnostic.range,
                    })
                    .collect(),
            );
            match phase {
                CompilationPhase::Original => AnalysisError::OriginalCompilationFailed(diagnostics),
                CompilationPhase::Reduced => AnalysisError::ReducedCompilationFailed(diagnostics),
            }
        }
        InputError::CompilerIce => AnalysisError::CompilerFailure(CompilerFailure::Ice),
        InputError::CompilerProtocolFailure => {
            AnalysisError::CompilerFailure(CompilerFailure::DriverProtocol)
        }
        InputError::Rewrite(error) => rewrite_error(error),
        other => AnalysisError::IncompleteObservation(ObservationGap {
            phase: match phase {
                CompilationPhase::Original => "original analysis",
                CompilationPhase::Reduced => "reduced analysis",
            }
            .to_owned(),
            fact: format!("{other:?}"),
            range: None,
        }),
    }
}

fn rewrite_error(error: SourceRewriteError) -> AnalysisError {
    AnalysisError::SourceRewriteInvariantViolation(SourceRewriteViolation {
        message: format!("{error:?}"),
        range: None,
    })
}

fn snapshot_error(error: SnapshotError) -> AnalysisError {
    AnalysisError::IncompleteObservation(ObservationGap {
        phase: "decision snapshot".to_owned(),
        fact: format!("{error:?}"),
        range: None,
    })
}

fn snapshot_difference(difference: SnapshotDiff) -> PublicSnapshotDiff {
    let (kind, original, reduced) = match difference {
        SnapshotDiff::Root { original, reduced } => (
            "compiler decision root".to_owned(),
            format!("{original:?}"),
            format!("{reduced:?}"),
        ),
        SnapshotDiff::Node {
            key,
            original,
            reduced,
        } => (
            format!("compiler decision node {key:?}"),
            format!("{original:?}"),
            format!("{reduced:?}"),
        ),
        SnapshotDiff::Edge { original, reduced } => (
            "compiler dependency edge".to_owned(),
            format!("{original:?}"),
            format!("{reduced:?}"),
        ),
    };
    PublicSnapshotDiff::new(vec![DecisionDifference {
        kind,
        original,
        reduced,
        range: None,
    }])
}

#[cfg(all(test, rust_item_dependencies_patched))]
fn host_target() -> String {
    let version = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("-Vv")
        .output()
        .unwrap();
    String::from_utf8(version.stdout)
        .unwrap()
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .unwrap()
        .to_owned()
}

#[cfg(test)]
mod compilation_options_tests {
    use super::*;

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn new_with_options_accepts_supported_cfg_names_and_duplicates() {
        let ordered = [
            "ONLINE_JUDGE",
            "日本語",
            "panic",
            "target_arch",
            "target_feature",
            "test",
        ]
        .into_iter()
        .fold(CompilationOptions::new(), CompilationOptions::with_cfg);
        let reordered_with_duplicate = [
            "test",
            "target_feature",
            "ONLINE_JUDGE",
            "panic",
            "日本語",
            "target_arch",
            "ONLINE_JUDGE",
        ]
        .into_iter()
        .fold(CompilationOptions::new(), CompilationOptions::with_cfg);
        let input = SourceInput::binary(
            concat!(
                "#[cfg(all(ONLINE_JUDGE, 日本語, panic, target_arch, target_feature, test))]\n",
                "fn selected() {}\n",
                "fn main() { selected(); }\n",
            ),
            Edition::Rust2024,
            host_target(),
        );

        let ordered =
            Analyzer::new_with_options(ordered).and_then(|analyzer| analyzer.reduce(&input));
        let reordered = Analyzer::new_with_options(reordered_with_duplicate)
            .and_then(|analyzer| analyzer.reduce(&input));

        assert!(ordered.is_ok(), "{ordered:?}");
        assert_eq!(reordered, ordered);
    }

    #[test]
    fn new_with_options_rejects_non_identifiers_and_raw_incompatible_names() {
        for name in [
            "",
            "r#ONLINE_JUDGE",
            "ONLINE-JUDGE",
            "feature=\"judge\"",
            "_",
            "Self",
            "crate",
            "self",
            "super",
        ] {
            assert_invalid_options(name);
        }
    }

    #[test]
    fn new_with_options_rejects_builtin_cfg_names() {
        for name in [
            "overflow_checks",
            "debug_assertions",
            "ub_checks",
            "contract_checks",
            "sanitize",
            "sanitizer_cfi_generalize_pointers",
            "sanitizer_cfi_normalize_integers",
            "proc_macro",
            "unix",
            "windows",
            "target_abi",
            "target_env",
            "target_vendor",
            "target_has_threads",
            "target_has_reliable_f16",
            "target_has_reliable_f16_math",
            "target_has_reliable_f128",
            "target_has_reliable_f128_math",
            "target_thread_local",
            "fmt_debug",
        ] {
            assert_invalid_options(name);
        }
    }

    #[test]
    fn builtin_cfg_is_rejected_before_an_input_lint_can_allow_the_rustc_flag() {
        let input = SourceInput::binary(
            "#![allow(explicit_builtin_cfgs_in_flags)]\nfn main() {}\n".to_owned(),
            Edition::Rust2024,
            "unused-before-compilation".to_owned(),
        );

        let result =
            Analyzer::new_with_options(CompilationOptions::new().with_cfg("debug_assertions"))
                .and_then(|analyzer| analyzer.reduce(&input));

        assert_eq!(
            result,
            Err(AnalysisError::InvalidCfgName {
                name: "debug_assertions".to_owned()
            })
        );
    }

    fn assert_invalid_options(name: &str) {
        let result = Analyzer::new_with_options(CompilationOptions::new().with_cfg(name));
        let error = result.expect_err("an invalid cfg name must be rejected");

        assert_eq!(
            error,
            AnalysisError::InvalidCfgName {
                name: name.to_owned()
            }
        );
        assert_eq!(error.to_string(), "an explicit cfg name is invalid");
    }
}

#[cfg(test)]
mod error_mapping_tests {
    use super::*;

    #[test]
    fn compiler_failure_causes_remain_distinct() {
        assert_eq!(
            analysis_error(InputError::CompilerIce, CompilationPhase::Original),
            AnalysisError::CompilerFailure(CompilerFailure::Ice)
        );
        assert_eq!(
            analysis_error(
                InputError::CompilerProtocolFailure,
                CompilationPhase::Original,
            ),
            AnalysisError::CompilerFailure(CompilerFailure::DriverProtocol)
        );
    }
}

#[cfg(all(test, rust_item_dependencies_patched))]
mod tests {
    use super::*;

    #[test]
    fn plain_cfg_names_activate_plain_source_predicates() {
        let target = host_target();
        let analyzer = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_cfg("ONLINE_JUDGE")
                .with_cfg("日本語")
                .with_cfg("macro_rules"),
        )
        .unwrap();
        let input = SourceInput::binary(
            concat!(
                "#[cfg(all(ONLINE_JUDGE, 日本語, macro_rules))]\n",
                "fn selected() {}\n",
                "fn main() { selected(); }\n",
            )
            .to_owned(),
            Edition::Rust2024,
            target,
        );

        let result = analyzer.reduce(&input);

        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn keyword_cfg_names_activate_raw_source_predicates_in_every_edition() {
        let target = host_target();
        let options = [
            "fn", "true", "abstract", "async", "await", "dyn", "try", "gen",
        ]
        .into_iter()
        .fold(CompilationOptions::new(), CompilationOptions::with_cfg);
        let analyzer = Analyzer::new_with_options(options).unwrap();
        for edition in [
            Edition::Rust2015,
            Edition::Rust2018,
            Edition::Rust2021,
            Edition::Rust2024,
        ] {
            let input = SourceInput::binary(
                concat!(
                    "#[cfg(all(r#fn, r#true, r#abstract, r#async, r#await, r#dyn, r#try, r#gen))]\n",
                    "fn selected() {}\n",
                    "fn main() { selected(); }\n",
                )
                .to_owned(),
                edition,
                target.clone(),
            );

            let result = analyzer.reduce(&input);

            assert!(result.is_ok(), "{edition:?}: {result:?}");
        }
    }

    #[test]
    fn reduction_compiles_the_original_and_reduced_sources_once_each() {
        crate::input::reset_inspection_count();
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput::binary(
            "fn dead() {}\nfn main() {}\n".to_owned(),
            Edition::Rust2024,
            host_target(),
        );

        let reduction = analyzer.reduce(&input).unwrap();
        assert_eq!(reduction.reduced_source(), "\nfn main() {}\n");
        assert_eq!(crate::input::inspection_count(), 2);
    }

    #[test]
    fn public_reduction_rejects_an_external_compiler_outcome_change() {
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput::library(
            "#![no_std]\nextern crate alloc;\npub fn entry() {}\n".to_owned(),
            Edition::Rust2024,
            host_target(),
            "external_outcome".to_owned(),
        )
        .with_entry_point(EntryPoint::new("external_outcome::entry"));

        let error = crate::retention::with_one_omitted_external_compiler_metadata_fact(|| {
            analyzer.reduce(&input)
        })
        .expect_err("the public reduction path must compare external compiler outcomes");
        let AnalysisError::DecisionMismatch(difference) = error else {
            panic!("unexpected error: {error:?}")
        };
        assert_eq!(difference.differences().len(), 1);
        assert_eq!(
            difference.differences()[0].kind,
            "external_compiler_metadata"
        );
    }

    #[test]
    fn reduction_does_not_write_compiler_artifacts_to_the_current_directory() {
        const CHILD_DIRECTORY: &str = "RUST_ITEM_DEPENDENCIES_CWD_TEST_DIRECTORY";
        const TEST_NAME: &str =
            "api::tests::reduction_does_not_write_compiler_artifacts_to_the_current_directory";

        if let Some(directory) = std::env::var_os(CHILD_DIRECTORY) {
            std::env::set_current_dir(&directory).unwrap();
            let analyzer = Analyzer::new().unwrap();
            analyzer
                .reduce(&SourceInput::binary(
                    "fn dead() {}\nfn main() {}\n".to_owned(),
                    Edition::Rust2024,
                    host_target(),
                ))
                .unwrap();
            assert_eq!(std::fs::read_dir(directory).unwrap().count(), 0);
            return;
        }

        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "rust-item-dependencies-cwd-test-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap();
        let output = Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg(TEST_NAME)
            .arg("--nocapture")
            .env(CHILD_DIRECTORY, &directory)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "child test failed:\n{}\n{}",
            stdout,
            stderr
        );
        assert!(
            stdout.contains("1 passed"),
            "child test did not run:\n{stdout}"
        );
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 0);
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn a_missing_selected_impl_fact_cannot_produce_an_analysis() {
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput::binary(
            concat!(
                "trait Value { fn value(&self) -> u32; }\n",
                "struct Selected;\n",
                "impl Value for Selected { fn value(&self) -> u32 { 1 } }\n",
                "fn main() { let _ = Selected.value(); }\n",
            )
            .to_owned(),
            Edition::Rust2024,
            host_target(),
        );

        let result = crate::input::with_one_missing_selected_impl_fact(input.source(), || {
            analyzer.reduce(&input)
        });
        let Err(AnalysisError::IncompleteObservation(gap)) = result else {
            panic!("a missing dependency fact must not produce a successful analysis")
        };
        assert_eq!(gap.phase, "original analysis");
        assert_eq!(gap.fact, "Dependency(Graph(InvalidProof))");
        assert_eq!(gap.range, None);
    }

    #[test]
    fn a_missing_macro_rule_selection_stops_before_reduced_compilation() {
        crate::input::reset_inspection_count();
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput::binary(
            concat!(
                "#[macro_export]\n",
                "macro_rules! exported { () => { fn main() {} }; }\n",
                "exported!();\n",
            )
            .to_owned(),
            Edition::Rust2024,
            host_target(),
        );

        let result = crate::input::with_one_missing_macro_rule_selection(input.source(), || {
            analyzer.reduce(&input)
        });
        let Err(AnalysisError::IncompleteObservation(gap)) = result else {
            panic!("a missing macro rule selection must not produce a reduction")
        };
        assert_eq!(gap.phase, "original analysis");
        assert_eq!(gap.fact, "Source(IncompleteMacroRuleObservation)");
        assert_eq!(gap.range, None);
        assert_eq!(crate::input::inspection_count(), 1);
    }

    #[test]
    fn reduced_analysis_rejects_nonempty_macro_output_marked_outputless() {
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput::binary(
            concat!(
                "macro_rules! marker { ($($name:ident),*) => { () }; }\n",
                "fn dead() {}\n",
                "fn main() { marker!(first, second); }\n",
            )
            .to_owned(),
            Edition::Rust2024,
            host_target(),
        );
        let reduced_source = analyzer.reduce(&input).unwrap().reduced_source().to_owned();

        let result =
            crate::input::with_one_nonempty_macro_marked_outputless(&reduced_source, || {
                analyzer.reduce(&input)
            });

        let Err(AnalysisError::IncompleteObservation(gap)) = result else {
            panic!("inconsistent reduced output coverage must not produce a reduction")
        };
        assert_eq!(gap.phase, "reduced analysis");
        assert_eq!(gap.fact, "Dependency(Retention(InvalidConstraint))");
        assert_eq!(gap.range, None);
    }
}
