//! Public, read-only source analysis and source reduction API.

use std::collections::BTreeSet;
use std::path::PathBuf;
#[cfg(all(test, rust_item_dependencies_patched))]
use std::process::Command;

use crate::artifact::compiler_artifact;
use crate::dependency_graph::{DependencyGraph, GraphNode, RootRecord};
use crate::digest::sha256;
use crate::error::{
    AnalysisError, CompilerFailure, DecisionDifference, Diagnostic, DiagnosticBundle,
    DiagnosticLevel, ObservationGap, SnapshotDiff as PublicSnapshotDiff, SourceRewriteViolation,
};
use crate::graph::DefinitionId;
use crate::input::{
    InputError, InspectedReduction, inspect_source,
    inspect_source_with_dependencies_at_original_coordinates, inspect_source_with_reduction,
};
use crate::rewrite::{SourcePiece, SourceRewriteError};
use crate::snapshot::{CompilerDecisionSnapshot, SnapshotDiff, SnapshotError};
use crate::source::{SourceUnitId, WrittenUnit};
use crate::tags::TagError;

pub use crate::input::{Edition, SourceInput};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CompilerRecipeIdentity(pub [u8; 32]);

#[derive(Clone, Debug)]
pub struct Analyzer {
    sysroot: PathBuf,
    artifact_digest: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Analysis {
    recipe: CompilerRecipeIdentity,
    source_digest: [u8; 32],
    graph: DependencyGraph,
    source_units: Vec<WrittenUnit>,
    semantic_definitions: BTreeSet<DefinitionId>,
    retained_source_units: BTreeSet<SourceUnitId>,
    removed_source_units: BTreeSet<SourceUnitId>,
    tags: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reduction {
    original: Analysis,
    reduced_source: String,
    reduced_source_digest: [u8; 32],
    pieces: Vec<SourcePiece>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[doc(hidden)]
pub struct VerifiedReduction {
    reduction: Reduction,
    verification: VerificationSummary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[doc(hidden)]
pub struct VerificationSummary {
    original_snapshot_hash: [u8; 32],
    reduced_snapshot_hash: [u8; 32],
}

impl Analyzer {
    pub fn new() -> Result<Self, AnalysisError> {
        artifact_context()
    }

    pub fn analyze(&self, input: &SourceInput) -> Result<Analysis, AnalysisError> {
        let inspected = inspect_source_with_reduction(input, &self.sysroot)
            .map_err(|error| analysis_error(error, CompilationPhase::Original))?;
        Ok(self.analysis(input, &inspected))
    }

    pub fn reduce(&self, input: &SourceInput) -> Result<Reduction, AnalysisError> {
        let inspected = inspect_source_with_reduction(input, &self.sysroot)
            .map_err(|error| analysis_error(error, CompilationPhase::Original))?;
        inspect_source(
            &SourceInput {
                source: inspected.rewrite.source.clone(),
                edition: input.edition,
                target: input.target.clone(),
            },
            &self.sysroot,
        )
        .map_err(|error| analysis_error(error, CompilationPhase::Reduced))?;
        Ok(self.reduction(input, &inspected))
    }

    #[doc(hidden)]
    pub fn reduce_and_verify(
        &self,
        input: &SourceInput,
    ) -> Result<VerifiedReduction, AnalysisError> {
        let inspected = inspect_source_with_reduction(input, &self.sysroot)
            .map_err(|error| analysis_error(error, CompilationPhase::Original))?;
        let original_snapshot = CompilerDecisionSnapshot::original(
            &inspected.graph,
            &inspected.source,
            &inspected.retention,
            &inspected.rewrite,
        )
        .map_err(snapshot_error)?;

        let reduced_input = SourceInput {
            source: inspected.rewrite.source.clone(),
            edition: input.edition,
            target: input.target.clone(),
        };
        let reduced = inspect_source_with_dependencies_at_original_coordinates(
            &reduced_input,
            &self.sysroot,
            &inspected.rewrite,
        )
        .map_err(|error| analysis_error(error, CompilationPhase::Reduced))?;
        let reduced_snapshot =
            CompilerDecisionSnapshot::reduced(&reduced.graph).map_err(snapshot_error)?;
        if let Some(difference) = original_snapshot.first_difference(&reduced_snapshot) {
            return Err(AnalysisError::DecisionMismatch(snapshot_difference(
                difference,
            )));
        }

        let original_snapshot_hash = original_snapshot.hash();
        let reduced_snapshot_hash = reduced_snapshot.hash();
        debug_assert_eq!(original_snapshot_hash, reduced_snapshot_hash);
        Ok(VerifiedReduction {
            reduction: self.reduction(input, &inspected),
            verification: VerificationSummary {
                original_snapshot_hash,
                reduced_snapshot_hash,
            },
        })
    }

    fn reduction(&self, input: &SourceInput, inspected: &InspectedReduction) -> Reduction {
        Reduction {
            original: self.analysis(input, inspected),
            reduced_source_digest: sha256(inspected.rewrite.source.as_bytes()),
            reduced_source: inspected.rewrite.source.clone(),
            pieces: inspected.rewrite.pieces.clone(),
        }
    }

    fn analysis(&self, input: &SourceInput, inspected: &InspectedReduction) -> Analysis {
        let semantic_definitions = inspected
            .retention
            .main_semantic
            .iter()
            .filter_map(|node| match node {
                GraphNode::Definition(definition) => Some(*definition),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let all_source_units = inspected
            .source
            .units
            .iter()
            .map(|unit| unit.id)
            .collect::<BTreeSet<_>>();
        let removed_source_units = all_source_units
            .difference(&inspected.retention.retained_units)
            .copied()
            .collect();
        let tags = semantic_definitions
            .iter()
            .filter_map(|definition| inspected.tags.get(definition))
            .flatten()
            .cloned()
            .collect();
        Analysis {
            recipe: recipe_identity(self.artifact_digest, input),
            source_digest: sha256(input.source.as_bytes()),
            graph: inspected.graph.clone(),
            source_units: inspected.source.units.clone(),
            semantic_definitions,
            retained_source_units: inspected.retention.retained_units.clone(),
            removed_source_units,
            tags,
        }
    }
}

impl Analysis {
    pub fn recipe(&self) -> CompilerRecipeIdentity {
        self.recipe
    }

    pub fn source_digest(&self) -> [u8; 32] {
        self.source_digest
    }

    pub fn graph(&self) -> &DependencyGraph {
        &self.graph
    }

    pub fn main_definition(&self) -> DefinitionId {
        self.graph.main_definition
    }

    pub fn main_instance(&self) -> crate::dependency_graph::MonoId {
        self.graph.main_instance
    }

    pub fn compiler_required_roots(&self) -> &[RootRecord] {
        &self.graph.compiler_required_roots
    }

    pub fn semantic_definitions(&self) -> &BTreeSet<DefinitionId> {
        &self.semantic_definitions
    }

    pub fn source_units(&self) -> &[WrittenUnit] {
        &self.source_units
    }

    pub fn retained_source_units(&self) -> &BTreeSet<SourceUnitId> {
        &self.retained_source_units
    }

    pub fn removed_source_units(&self) -> &BTreeSet<SourceUnitId> {
        &self.removed_source_units
    }

    pub fn tags(&self) -> &BTreeSet<String> {
        &self.tags
    }
}

impl Reduction {
    pub fn original_analysis(&self) -> &Analysis {
        &self.original
    }

    pub fn reduced_source(&self) -> &str {
        &self.reduced_source
    }

    pub fn reduced_source_digest(&self) -> [u8; 32] {
        self.reduced_source_digest
    }

    pub fn pieces(&self) -> &[SourcePiece] {
        &self.pieces
    }
}

impl VerifiedReduction {
    pub fn original_analysis(&self) -> &Analysis {
        self.reduction.original_analysis()
    }

    pub fn reduced_source(&self) -> &str {
        self.reduction.reduced_source()
    }

    pub fn reduced_source_digest(&self) -> [u8; 32] {
        self.reduction.reduced_source_digest()
    }

    pub fn pieces(&self) -> &[SourcePiece] {
        self.reduction.pieces()
    }

    pub fn verification(&self) -> &VerificationSummary {
        &self.verification
    }
}

impl VerificationSummary {
    pub fn original_snapshot_hash(&self) -> [u8; 32] {
        self.original_snapshot_hash
    }

    pub fn reduced_snapshot_hash(&self) -> [u8; 32] {
        self.reduced_snapshot_hash
    }
}

fn artifact_context() -> Result<Analyzer, AnalysisError> {
    let artifact = compiler_artifact().map_err(|_| AnalysisError::CompilerArtifactMismatch)?;
    Ok(Analyzer {
        sysroot: artifact.sysroot,
        artifact_digest: artifact.identity,
    })
}

fn recipe_identity(artifact: [u8; 32], input: &SourceInput) -> CompilerRecipeIdentity {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"rust-item-dependencies-recipe-v1\0");
    bytes.extend_from_slice(&artifact);
    bytes.push(input.edition as u8);
    bytes.extend_from_slice(&(input.target.len() as u64).to_le_bytes());
    bytes.extend_from_slice(input.target.as_bytes());
    CompilerRecipeIdentity(sha256(bytes))
}

#[derive(Clone, Copy)]
enum CompilationPhase {
    Original,
    Reduced,
}

fn analysis_error(error: InputError, phase: CompilationPhase) -> AnalysisError {
    match error {
        InputError::UnsupportedInput { reason, range } => {
            AnalysisError::UnsupportedInput { reason, range }
        }
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
        InputError::Tag(TagError::InvalidTag(range)) => AnalysisError::InvalidTag { range },
        InputError::Tag(TagError::InvalidSource) => {
            AnalysisError::IncompleteObservation(ObservationGap {
                phase: "tag collection".to_owned(),
                fact: "definition source origin".to_owned(),
                range: None,
            })
        }
        InputError::Dependency(crate::input::DependencyError::Tag(TagError::InvalidTag(range))) => {
            AnalysisError::InvalidTag { range }
        }
        InputError::Dependency(crate::input::DependencyError::Tag(TagError::InvalidSource)) => {
            AnalysisError::IncompleteObservation(ObservationGap {
                phase: "tag collection".to_owned(),
                fact: "definition source origin".to_owned(),
                range: None,
            })
        }
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
        SnapshotDiff::MainDefinition { original, reduced } => (
            "main definition".to_owned(),
            format!("{original:?}"),
            format!("{reduced:?}"),
        ),
        SnapshotDiff::MainInstance { original, reduced } => (
            "main instance".to_owned(),
            format!("{original:?}"),
            format!("{reduced:?}"),
        ),
        SnapshotDiff::CompilerRequiredRoot { original, reduced } => (
            "compiler-required root".to_owned(),
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

    #[test]
    fn verified_reduction_runs_original_and_reduced_compilers_once_each() {
        crate::input::reset_inspection_count();
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput {
            source: "fn dead() {}\nfn main() {}\n".to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        };

        analyzer.reduce_and_verify(&input).unwrap();
        assert_eq!(crate::input::inspection_count(), 2);
    }

    #[test]
    fn reduction_compiles_the_original_and_reduced_sources_once_each() {
        crate::input::reset_inspection_count();
        let analyzer = Analyzer::new().unwrap();
        let input = SourceInput {
            source: "fn dead() {}\nfn main() {}\n".to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        };

        let reduction = analyzer.reduce(&input).unwrap();
        assert_eq!(reduction.reduced_source(), "\nfn main() {}\n");
        assert_eq!(crate::input::inspection_count(), 2);
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
                .reduce(&SourceInput {
                    source: "fn dead() {}\nfn main() {}\n".to_owned(),
                    edition: Edition::Rust2024,
                    target: host_target(),
                })
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
        let input = SourceInput {
            source: concat!(
                "trait Value { fn value(&self) -> u32; }\n",
                "struct Selected;\n",
                "impl Value for Selected { fn value(&self) -> u32 { 1 } }\n",
                "fn main() { let _ = Selected.value(); }\n",
            )
            .to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        };

        let result = crate::input::with_one_missing_selected_impl_fact(&input.source, || {
            analyzer.analyze(&input)
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
        let input = SourceInput {
            source: include_str!("../tests/fixtures/compiler/macro_rule_reduction.rs").to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        };

        let result = crate::input::with_one_missing_macro_rule_selection(&input.source, || {
            analyzer.reduce_and_verify(&input)
        });
        let Err(AnalysisError::IncompleteObservation(gap)) = result else {
            panic!("a missing macro rule selection must not produce a verified reduction")
        };
        assert_eq!(gap.phase, "original analysis");
        assert_eq!(gap.fact, "Source(IncompleteMacroRuleObservation)");
        assert_eq!(gap.range, None);
        assert_eq!(crate::input::inspection_count(), 1);
    }
}
