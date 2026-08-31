//! Owned public failures returned by the analyzer.

use std::fmt;
use std::io;
use std::path::PathBuf;

use crate::source::ByteRange;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum UnsupportedReason {
    UnstableLanguageFeature,
    AdditionalSourceFile,
    ExternalCompileTimeResource,
    ExternalDependency,
    ProcMacro,
    NativeLinkOrCustomRuntime,
    ExternalNativeLink,
    UnsupportedTarget,
    MissingMain,
    MissingTargetEntry,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum EntryPointError {
    InvalidPath,
    WrongCrate,
    NotFound,
    UnsupportedItem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AnalysisError {
    InvalidCrateName {
        name: String,
    },
    MissingLibraryEntryPoint,
    InvalidEntryPoint {
        path: String,
        reason: EntryPointError,
    },
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
    InvalidProcMacroExecutionArtifact {
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
    OriginalCompilationFailed(DiagnosticBundle),
    CompilerArtifactMismatch,
    IncompleteObservation(ObservationGap),
    SourceRewriteInvariantViolation(SourceRewriteViolation),
    ReducedCompilationFailed(DiagnosticBundle),
    DecisionMismatch(SnapshotDiff),
    CompilerFailure(CompilerFailure),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
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
#[non_exhaustive]
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
#[non_exhaustive]
pub struct ObservationGap {
    pub phase: String,
    pub fact: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct SourceRewriteViolation {
    pub message: String,
    pub range: Option<ByteRange>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
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
#[non_exhaustive]
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
            Self::InvalidCrateName { .. } => "the crate name is invalid",
            Self::MissingLibraryEntryPoint => "a library input requires at least one entry point",
            Self::InvalidEntryPoint { .. } => "an explicit entry point is invalid",
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
            Self::InvalidProcMacroExecutionArtifact { .. } => {
                "a procedural macro execution permission does not refer to a declared host dynamic library"
            }
            Self::ConflictingExternalCrateArtifactName { .. } => {
                "external crate artifacts have a conflicting file name"
            }
            Self::ExternalCrateSnapshotFailure { .. } => {
                "the external crate snapshot could not be prepared"
            }
            Self::UnsupportedInput { .. } => "the input is outside the supported source boundary",
            Self::OriginalCompilationFailed(_) => "the original source did not compile",
            Self::CompilerArtifactMismatch => {
                "the configured compiler is not compatible with this build"
            }
            Self::IncompleteObservation(_) => "a required compiler observation is incomplete",
            Self::SourceRewriteInvariantViolation(_) => "the source rewrite violated an invariant",
            Self::ReducedCompilationFailed(_) => "the reduced source did not compile",
            Self::DecisionMismatch(_) => "the reduced compiler decisions differ from the original",
            Self::CompilerFailure(_) => "the compiler driver failed",
        };
        formatter.write_str(message)
    }
}

impl fmt::Display for EntryPointError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::InvalidPath => "the path is not a fully qualified Rust item path",
            Self::WrongCrate => "the path starts with a different crate name",
            Self::NotFound => "the path does not resolve to an item",
            Self::UnsupportedItem => "the path does not name a free function or static item",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for AnalysisError {}
