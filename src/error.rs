//! Owned public failures returned by the analyzer.

use std::fmt;

use crate::input::UnsupportedReason;
use crate::source::{ByteRange, SourceUnitId};

#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AnalysisError {
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
