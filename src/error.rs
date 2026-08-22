//! Owned public failures returned by the analyzer.

use std::fmt;
use std::io;
use std::path::PathBuf;

use crate::source::{ByteRange, SourceUnitId};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum UnsupportedReason {
    UnstableLanguageFeature,
    AdditionalSourceFile,
    ExternalCompileTimeResource,
    ExternalDependency,
    ProcMacro,
    NoStdOrNoMain,
    Assembly,
    NativeLinkOrCustomRuntime,
    UnsupportedTarget,
    MissingMain,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AnalysisError {
    InvalidCfgName {
        name: String,
    },
    InvalidExternalCrateName {
        name: String,
    },
    ConflictingExternalCrate {
        name: String,
        first_path: PathBuf,
        second_path: PathBuf,
    },
    ExternalCrateArtifactUnreadable {
        path: PathBuf,
        error: io::ErrorKind,
    },
    UnsupportedExternalCrateArtifact {
        path: PathBuf,
    },
    ConflictingExternalCrateArtifactName {
        file_name: String,
        first_path: PathBuf,
        second_path: PathBuf,
    },
    ExternalCrateSnapshotFailure {
        path: PathBuf,
        error: io::ErrorKind,
    },
    UnsupportedInput {
        reason: UnsupportedReason,
        range: Option<ByteRange>,
    },
    InvalidTag {
        range: ByteRange,
    },
    OriginalCompilationFailed(DiagnosticBundle),
    CompilerArtifactMismatch,
    UnsupportedCompilerRevision,
    IncompleteObservation(ObservationGap),
    AmbiguousSourceOrigin,
    UneditableSourceUnit(SourceUnitId),
    SourceRewriteInvariantViolation(SourceRewriteViolation),
    ReducedCompilationFailed(DiagnosticBundle),
    DecisionMismatch(SnapshotDiff),
    CompilerFailure(CompilerFailure),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DiagnosticBundle {
    diagnostics: Vec<Diagnostic>,
}

impl DiagnosticBundle {
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub(crate) fn new(diagnostics: Vec<Diagnostic>) -> Self {
        Self { diagnostics }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Note,
    Help,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationGap {
    pub phase: String,
    pub fact: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceRewriteViolation {
    pub message: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SnapshotDiff {
    differences: Vec<DecisionDifference>,
}

impl SnapshotDiff {
    pub fn differences(&self) -> &[DecisionDifference] {
        &self.differences
    }

    pub(crate) fn new(differences: Vec<DecisionDifference>) -> Self {
        Self { differences }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecisionDifference {
    pub kind: String,
    pub original: String,
    pub reduced: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum CompilerFailure {
    Ice,
    DriverProtocol,
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::InvalidCfgName { .. } => "an explicit cfg name is invalid",
            Self::InvalidExternalCrateName { .. } => "an external crate name is invalid",
            Self::ConflictingExternalCrate { .. } => {
                "an external crate name refers to conflicting artifacts"
            }
            Self::ExternalCrateArtifactUnreadable { .. } => {
                "an external crate artifact could not be read"
            }
            Self::UnsupportedExternalCrateArtifact { .. } => {
                "an external crate artifact format is not supported"
            }
            Self::ConflictingExternalCrateArtifactName { .. } => {
                "external crate artifacts have a conflicting file name"
            }
            Self::ExternalCrateSnapshotFailure { .. } => {
                "the external crate snapshot could not be prepared"
            }
            Self::UnsupportedInput { .. } => "the input is outside the supported source boundary",
            Self::InvalidTag { .. } => "a dependency tag has an empty name",
            Self::OriginalCompilationFailed(_) => "the original source did not compile",
            Self::CompilerArtifactMismatch => {
                "the configured compiler is not compatible with this build"
            }
            Self::UnsupportedCompilerRevision => "the compiler revision is not supported",
            Self::IncompleteObservation(_) => "a required compiler observation is incomplete",
            Self::AmbiguousSourceOrigin => "a compiler fact has no unique source origin",
            Self::UneditableSourceUnit(_) => "a required source unit cannot be edited safely",
            Self::SourceRewriteInvariantViolation(_) => "the source rewrite violated an invariant",
            Self::ReducedCompilationFailed(_) => "the reduced source did not compile",
            Self::DecisionMismatch(_) => "the reduced compiler decisions differ from the original",
            Self::CompilerFailure(_) => "the compiler driver failed",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for AnalysisError {}
