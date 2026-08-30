#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_expand;
extern crate rustc_feature;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_lexer;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

mod api;
#[allow(dead_code)]
pub(crate) mod artifact;
#[allow(dead_code)]
pub mod compiler_terms;
#[allow(dead_code)]
pub(crate) mod definitions;
#[allow(dead_code)]
pub mod dependency_graph;
#[allow(dead_code)]
pub(crate) mod digest;
#[allow(dead_code)]
pub mod error;
#[allow(dead_code)]
pub(crate) mod expansions;
#[allow(dead_code)]
pub(crate) mod external;
#[allow(dead_code)]
pub mod graph;
#[allow(dead_code)]
pub(crate) mod input;
#[allow(dead_code)]
pub(crate) mod macro_output;
#[allow(dead_code)]
pub(crate) mod monomorphization;
pub mod qualification;
#[allow(dead_code)]
pub(crate) mod retention;
#[allow(dead_code)]
pub(crate) mod rewrite;
#[allow(dead_code)]
pub(crate) mod selection;
#[allow(dead_code)]
pub(crate) mod snapshot;
#[allow(dead_code)]
pub mod source;
#[allow(dead_code)]
pub(crate) mod tags;

pub use api::{
    Analysis, Analyzer, CompilationOptions, CompilerRecipeIdentity, CrateType, Edition, EntryPoint,
    OptimizationLevel, Reduction, SourceInput, VerificationSummary, VerifiedReduction,
};
pub use error::{AnalysisError, EntryPointError, UnsupportedReason};
pub use rewrite::SourcePiece;
