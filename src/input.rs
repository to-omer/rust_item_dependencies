//! Validation and compiler entry point for a single in-memory Rust source.

#[cfg(test)]
use std::cell::Cell;
use std::collections::BTreeSet;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use rustc_ast as ast;
use rustc_ast::visit::{self, AssocCtxt, Visitor};
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::emitter::Emitter;
use rustc_errors::formatting::format_diag_messages;
use rustc_errors::{DiagInner, E0463, E0554, E0658, ErrCode, Level};
use rustc_expand::config::{StripUnconfigured, features, pre_configure_attrs};
use rustc_feature::{Features, UnstableFeatures};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CRATE_DEF_ID, LocalDefId};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::metadata::Reexport;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::MacroImplementationKind;
use rustc_middle::ty::{self, GenericArgKind, TyCtxt};
use rustc_session::config::Input;
use rustc_span::source_map::{FileLoader, SourceMap};
use rustc_span::{FileName, RealFileName, Span, Symbol, sym};
use rustc_target::spec::TARGETS;

use crate::definitions::{
    DefinitionError, collect_definition_graph, collect_definitions, normalize_definition_key,
};
use crate::dependency_graph::{
    AllocationPathSite, DependencyEdge, DependencyGraph, DependencyGraphError, ExpansionNode,
    GraphNode, MonoKey, MonoNode, ObservationSite, RootReason, RootRecord,
    is_downstream_selection_candidate,
};
#[cfg(all(test, rust_item_dependencies_patched))]
use crate::dependency_graph::{DependencyKind, EvidenceOrigin, ProofRelationKind};
use crate::error::{AnalysisError, EntryPointError, UnsupportedReason};
use crate::expansions::{CollectedExpansions, ExpansionError, collect_expansions};
use crate::external::{ExternalCrate, PreparedExternalCrates, prepare_external_crates};
use crate::graph::{DefinitionGraph, DefinitionKind, DefinitionOrigin};
use crate::monomorphization::{
    CollectedMonomorphization, MonomorphizationError, collect_monomorphization,
};
use crate::retention::{
    Retention, RetentionError, SourceConstraints, collect_macro_rule_expansion_constraints,
    collect_source_constraints, compute_retention,
};
use crate::rewrite::{SourceRewrite, SourceRewriteError, rewrite_source};
use crate::source::{
    ByteRange, OriginalOffsetMap, SourceError, SourceInventory, collect_source, original_span_range,
};
#[cfg(rust_item_dependencies_patched)]
use crate::source::{refine_attribute_macros_from_compiler, refine_macro_rules_from_compiler};
use crate::tags::{DefinitionTags, TagError, collect_definition_tags};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Edition {
    Rust2015,
    Rust2018,
    Rust2021,
    Rust2024,
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum CrateType {
    #[default]
    Binary,
    Library,
}

impl CrateType {
    fn compiler_argument(self) -> &'static str {
        match self {
            Self::Binary => "bin",
            Self::Library => "rlib",
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EntryPoint(String);

impl EntryPoint {
    pub fn new(path: impl Into<String>) -> Self {
        Self(path.into())
    }

    pub fn path(&self) -> &str {
        &self.0
    }
}

impl Edition {
    fn as_str(self) -> &'static str {
        match self {
            Self::Rust2015 => "2015",
            Self::Rust2018 => "2018",
            Self::Rust2021 => "2021",
            Self::Rust2024 => "2024",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum OptimizationLevel {
    #[default]
    O0,
    O1,
    O2,
    O3,
    Size,
    SizeMin,
}

impl OptimizationLevel {
    fn as_str(self) -> &'static str {
        match self {
            Self::O0 => "0",
            Self::O1 => "1",
            Self::O2 => "2",
            Self::O3 => "3",
            Self::Size => "s",
            Self::SizeMin => "z",
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CompilationOptions {
    optimization_level: OptimizationLevel,
    explicit_cfgs: BTreeSet<String>,
    external_crates: BTreeSet<ExternalCrate>,
    dependency_artifacts: BTreeSet<PathBuf>,
    allowed_proc_macro_artifacts: BTreeSet<PathBuf>,
}

#[derive(Debug)]
pub(crate) struct PreparedCompilationOptions {
    optimization_level: OptimizationLevel,
    explicit_cfgs: BTreeSet<String>,
    external_crates: PreparedExternalCrates,
}

impl PreparedCompilationOptions {
    fn new(options: CompilationOptions, external_crates: PreparedExternalCrates) -> Self {
        Self {
            optimization_level: options.optimization_level,
            explicit_cfgs: options.explicit_cfgs,
            external_crates,
        }
    }

    pub(crate) fn prepare(options: CompilationOptions) -> Result<Self, AnalysisError> {
        options.validate()?;
        let external_crates = prepare_external_crates(
            options.external_crates(),
            options.dependency_artifacts(),
            options.allowed_proc_macro_artifacts(),
        )?;
        Ok(Self::new(options, external_crates))
    }

    #[cfg(test)]
    fn empty() -> Self {
        Self::new(
            CompilationOptions::default(),
            PreparedExternalCrates::default(),
        )
    }
}

// rustc cannot parse these semantic names as raw cfgspec identifiers.
const RAW_INCOMPATIBLE_CFG_NAMES: &[&str] = &["_", "Self", "crate", "self", "super"];

// Mirrors the `(name, None)` arms in rustc_session::config::cfg::disallow_cfgs.
const DISALLOWED_BUILTIN_CFG_NAMES: &[&str] = &[
    "contract_checks",
    "debug_assertions",
    "fmt_debug",
    "overflow_checks",
    "proc_macro",
    "sanitize",
    "sanitizer_cfi_generalize_pointers",
    "sanitizer_cfi_normalize_integers",
    "target_abi",
    "target_env",
    "target_has_reliable_f128",
    "target_has_reliable_f128_math",
    "target_has_reliable_f16",
    "target_has_reliable_f16_math",
    "target_has_threads",
    "target_thread_local",
    "target_vendor",
    "ub_checks",
    "unix",
    "windows",
];

impl CompilationOptions {
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_optimization_level(mut self, optimization_level: OptimizationLevel) -> Self {
        self.optimization_level = optimization_level;
        self
    }

    #[must_use]
    pub fn with_cfg(mut self, name: impl Into<String>) -> Self {
        self.explicit_cfgs.insert(name.into());
        self
    }

    #[must_use]
    pub fn with_external_crate(
        mut self,
        extern_name: impl Into<String>,
        artifact: impl Into<PathBuf>,
    ) -> Self {
        self.external_crates
            .insert(ExternalCrate::new(extern_name, artifact));
        self
    }

    #[must_use]
    pub fn with_dependency_artifact(mut self, artifact: impl Into<PathBuf>) -> Self {
        self.dependency_artifacts.insert(artifact.into());
        self
    }

    #[must_use]
    pub fn allow_proc_macro_execution(mut self, artifact: impl Into<PathBuf>) -> Self {
        self.allowed_proc_macro_artifacts.insert(artifact.into());
        self
    }

    pub fn optimization_level(&self) -> OptimizationLevel {
        self.optimization_level
    }

    pub fn cfgs(&self) -> impl Iterator<Item = &str> {
        self.explicit_cfgs.iter().map(String::as_str)
    }

    pub(crate) fn external_crates(&self) -> impl Iterator<Item = &ExternalCrate> {
        self.external_crates.iter()
    }

    pub(crate) fn dependency_artifacts(&self) -> impl Iterator<Item = &Path> {
        self.dependency_artifacts.iter().map(PathBuf::as_path)
    }

    pub(crate) fn allowed_proc_macro_artifacts(&self) -> impl Iterator<Item = &Path> {
        self.allowed_proc_macro_artifacts
            .iter()
            .map(PathBuf::as_path)
    }

    pub(crate) fn validate(&self) -> Result<(), AnalysisError> {
        let invalid = self.cfgs().find(|name| {
            !rustc_lexer::is_ident(name)
                || RAW_INCOMPATIBLE_CFG_NAMES.contains(name)
                || DISALLOWED_BUILTIN_CFG_NAMES.contains(name)
        });
        match invalid {
            Some(name) => Err(AnalysisError::InvalidCfgName {
                name: name.to_owned(),
            }),
            None => Ok(()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceInput {
    pub source: String,
    pub edition: Edition,
    pub target: String,
    pub crate_type: CrateType,
    pub crate_name: String,
    pub entry_points: Vec<EntryPoint>,
}

impl SourceInput {
    pub fn binary(source: impl Into<String>, edition: Edition, target: impl Into<String>) -> Self {
        Self {
            source: source.into(),
            edition,
            target: target.into(),
            crate_type: CrateType::Binary,
            crate_name: "main".to_owned(),
            entry_points: Vec::new(),
        }
    }

    pub fn library(
        source: impl Into<String>,
        edition: Edition,
        target: impl Into<String>,
        crate_name: impl Into<String>,
    ) -> Self {
        Self {
            source: source.into(),
            edition,
            target: target.into(),
            crate_type: CrateType::Library,
            crate_name: crate_name.into(),
            entry_points: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_crate_name(mut self, crate_name: impl Into<String>) -> Self {
        self.crate_name = crate_name.into();
        self
    }

    #[must_use]
    pub fn with_entry_point(mut self, entry_point: EntryPoint) -> Self {
        self.entry_points.push(entry_point);
        self
    }
}

pub(crate) struct CompilationContext<'a> {
    input: &'a SourceInput,
    compilation: &'a PreparedCompilationOptions,
    sysroot: &'a Path,
}

impl<'a> CompilationContext<'a> {
    pub(crate) fn new(
        input: &'a SourceInput,
        compilation: &'a PreparedCompilationOptions,
        sysroot: &'a Path,
    ) -> Self {
        Self {
            input,
            compilation,
            sysroot,
        }
    }

    pub(crate) fn edition_argument(&self) -> &'static str {
        self.input.edition.as_str()
    }

    pub(crate) fn target(&self) -> &str {
        &self.input.target
    }

    pub(crate) fn crate_type(&self) -> CrateType {
        self.input.crate_type
    }

    pub(crate) fn crate_type_argument(&self) -> &'static str {
        self.input.crate_type.compiler_argument()
    }

    pub(crate) fn crate_name(&self) -> &str {
        &self.input.crate_name
    }

    pub(crate) fn entry_points(&self) -> impl Iterator<Item = &EntryPoint> {
        self.input.entry_points.iter()
    }

    pub(crate) fn optimization_level_argument(&self) -> &'static str {
        self.compilation.optimization_level.as_str()
    }

    pub(crate) fn cfgs(&self) -> impl Iterator<Item = &str> {
        self.compilation.explicit_cfgs.iter().map(String::as_str)
    }

    pub(crate) fn external_crates(&self) -> &PreparedExternalCrates {
        &self.compilation.external_crates
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum InputError {
    InvalidCrateName {
        name: String,
    },
    MissingLibraryEntryPoint,
    InvalidEntryPoint {
        path: String,
        reason: EntryPointError,
    },
    UnsupportedInput {
        reason: UnsupportedReason,
        range: Option<ByteRange>,
    },
    OriginalCompilationFailed(Vec<CompilerDiagnostic>),
    CompilerIce,
    CompilerProtocolFailure,
    Source(SourceError),
    Definition(DefinitionError),
    Dependency(DependencyError),
    Rewrite(SourceRewriteError),
    Tag(TagError),
}

#[derive(Clone, Debug)]
pub(crate) struct ResolvedEntryPoint {
    pub(crate) definition: LocalDefId,
    pub(crate) reexports: Vec<LocalDefId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DependencyError {
    Definition(DefinitionError),
    Expansion(ExpansionError),
    Monomorphization(MonomorphizationError),
    Retention(RetentionError),
    Graph(DependencyGraphError),
    Tag(TagError),
    Rewrite(SourceRewriteError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompilerDiagnostic {
    pub message: String,
    pub range: Option<ByteRange>,
}

impl From<SourceError> for InputError {
    fn from(error: SourceError) -> Self {
        Self::Source(error)
    }
}

impl From<DefinitionError> for InputError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

impl From<DependencyError> for InputError {
    fn from(error: DependencyError) -> Self {
        Self::Dependency(error)
    }
}

impl From<DefinitionError> for DependencyError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

impl From<ExpansionError> for DependencyError {
    fn from(error: ExpansionError) -> Self {
        Self::Expansion(error)
    }
}

impl From<MonomorphizationError> for DependencyError {
    fn from(error: MonomorphizationError) -> Self {
        Self::Monomorphization(error)
    }
}

impl From<DependencyGraphError> for DependencyError {
    fn from(error: DependencyGraphError) -> Self {
        Self::Graph(error)
    }
}

impl From<RetentionError> for DependencyError {
    fn from(error: RetentionError) -> Self {
        Self::Retention(error)
    }
}

impl From<SourceRewriteError> for DependencyError {
    fn from(error: SourceRewriteError) -> Self {
        Self::Rewrite(error)
    }
}

impl From<RetentionError> for InputError {
    fn from(error: RetentionError) -> Self {
        Self::Dependency(DependencyError::Retention(error))
    }
}

impl From<SourceRewriteError> for InputError {
    fn from(error: SourceRewriteError) -> Self {
        Self::Rewrite(error)
    }
}

impl From<TagError> for InputError {
    fn from(error: TagError) -> Self {
        Self::Tag(error)
    }
}

impl From<TagError> for DependencyError {
    fn from(error: TagError) -> Self {
        Self::Tag(error)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InspectedSource {
    pub source: SourceInventory,
    pub definitions: DefinitionGraph,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InspectedDependencies {
    pub source: SourceInventory,
    pub graph: DependencyGraph,
    pub constraints: SourceConstraints,
    pub tags: DefinitionTags,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InspectedReduction {
    pub source: SourceInventory,
    pub graph: DependencyGraph,
    pub constraints: SourceConstraints,
    pub retention: Retention,
    pub rewrite: SourceRewrite,
    pub tags: DefinitionTags,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CollectionMode {
    Source,
    Definitions,
    Dependencies,
}

#[cfg(test)]
thread_local! {
    static INSPECTION_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[cfg(all(test, rust_item_dependencies_patched))]
static OMIT_ONE_SELECTED_IMPL_FACT_FROM: Mutex<Option<String>> = Mutex::new(None);

#[cfg(all(test, rust_item_dependencies_patched))]
static OMIT_ONE_MACRO_RULE_SELECTION_FROM: Mutex<Option<String>> = Mutex::new(None);

#[cfg(test)]
pub(crate) fn reset_inspection_count() {
    INSPECTION_COUNT.set(0);
}

#[cfg(test)]
pub(crate) fn inspection_count() -> usize {
    INSPECTION_COUNT.get()
}

#[cfg(all(test, rust_item_dependencies_patched))]
pub(crate) fn with_one_missing_selected_impl_fact<T>(source: &str, f: impl FnOnce() -> T) -> T {
    let mut request = OMIT_ONE_SELECTED_IMPL_FACT_FROM
        .lock()
        .expect("fact omission mutex is poisoned");
    assert!(request.is_none(), "fact omission must not be nested");
    *request = Some(source.to_owned());
    drop(request);

    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            *OMIT_ONE_SELECTED_IMPL_FACT_FROM
                .lock()
                .expect("fact omission mutex is poisoned") = None;
        }
    }
    let _reset = Reset;
    f()
}

#[cfg(all(test, rust_item_dependencies_patched))]
pub(crate) fn with_one_missing_macro_rule_selection<T>(source: &str, f: impl FnOnce() -> T) -> T {
    let mut request = OMIT_ONE_MACRO_RULE_SELECTION_FROM
        .lock()
        .expect("macro rule selection omission mutex is poisoned");
    assert!(request.is_none(), "selection omission must not be nested");
    *request = Some(source.to_owned());
    drop(request);

    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            *OMIT_ONE_MACRO_RULE_SELECTION_FROM
                .lock()
                .expect("macro rule selection omission mutex is poisoned") = None;
        }
    }
    let _reset = Reset;
    f()
}

#[cfg(test)]
pub(crate) fn inspect_source(
    input: &SourceInput,
    sysroot: &Path,
) -> Result<SourceInventory, InputError> {
    let compilation = PreparedCompilationOptions::empty();
    let context = CompilationContext::new(input, &compilation, sysroot);
    inspect_source_in_context(&input.source, &context)
}

pub(crate) fn inspect_source_in_context(
    source: &str,
    context: &CompilationContext<'_>,
) -> Result<SourceInventory, InputError> {
    run_inspection(source, context, CollectionMode::Source, None)
        .map(|inspection| inspection.source)
}

#[cfg(test)]
pub(crate) fn inspect_source_with_definitions(
    input: &SourceInput,
    sysroot: &Path,
) -> Result<InspectedSource, InputError> {
    let compilation = PreparedCompilationOptions::empty();
    let context = CompilationContext::new(input, &compilation, sysroot);
    inspect_source_with_definitions_in_context(&input.source, &context)
}

#[cfg(test)]
fn inspect_source_with_definitions_in_context(
    source: &str,
    context: &CompilationContext<'_>,
) -> Result<InspectedSource, InputError> {
    let inspection = run_inspection(source, context, CollectionMode::Definitions, None)?;
    Ok(InspectedSource {
        source: inspection.source,
        definitions: inspection
            .definitions
            .ok_or(InputError::CompilerProtocolFailure)?,
    })
}

#[cfg(test)]
pub(crate) fn inspect_source_with_dependencies(
    input: &SourceInput,
    sysroot: &Path,
) -> Result<InspectedDependencies, InputError> {
    let compilation = PreparedCompilationOptions::empty();
    let context = CompilationContext::new(input, &compilation, sysroot);
    inspect_source_with_dependencies_inner(&input.source, &context, None)
}

/// Inspects a rewritten source while expressing every compiler-decision
/// identity and source observation in the coordinates of its original source.
/// `coordinates` must be the piece map that produced `input.source`.
#[cfg(test)]
pub(crate) fn inspect_source_with_dependencies_at_original_coordinates(
    input: &SourceInput,
    sysroot: &Path,
    coordinates: &SourceRewrite,
) -> Result<InspectedDependencies, InputError> {
    let compilation = PreparedCompilationOptions::empty();
    let context = CompilationContext::new(input, &compilation, sysroot);
    inspect_source_with_dependencies_at_original_coordinates_in_context(
        &input.source,
        &context,
        coordinates,
    )
}

pub(crate) fn inspect_source_with_dependencies_at_original_coordinates_in_context(
    source: &str,
    context: &CompilationContext<'_>,
    coordinates: &SourceRewrite,
) -> Result<InspectedDependencies, InputError> {
    inspect_source_with_dependencies_inner(source, context, Some(coordinates))
}

fn inspect_source_with_dependencies_inner(
    source: &str,
    context: &CompilationContext<'_>,
    coordinates: Option<&SourceRewrite>,
) -> Result<InspectedDependencies, InputError> {
    if let Some(coordinates) = coordinates {
        if coordinates.source != source {
            return Err(InputError::Rewrite(SourceRewriteError::InvalidInventory));
        }
        coordinates.original_crate_range(ByteRange {
            start: 0,
            end: u32::try_from(source.len())
                .map_err(|_| InputError::Rewrite(SourceRewriteError::InvalidInventory))?,
        })?;
    }
    let inspection = run_inspection(source, context, CollectionMode::Dependencies, coordinates)?;
    let dependencies = inspection
        .dependencies
        .ok_or(InputError::CompilerProtocolFailure)?;
    Ok(InspectedDependencies {
        source: inspection.source,
        graph: dependencies.graph,
        constraints: dependencies.constraints,
        tags: dependencies.tags,
    })
}

#[cfg(test)]
pub(crate) fn inspect_source_with_reduction(
    input: &SourceInput,
    sysroot: &Path,
) -> Result<InspectedReduction, InputError> {
    let compilation = PreparedCompilationOptions::empty();
    let context = CompilationContext::new(input, &compilation, sysroot);
    inspect_source_with_reduction_in_context(&input.source, &context)
}

pub(crate) fn inspect_source_with_reduction_in_context(
    source: &str,
    context: &CompilationContext<'_>,
) -> Result<InspectedReduction, InputError> {
    let inspected = inspect_source_with_dependencies_inner(source, context, None)?;
    let retention = compute_retention(&inspected.source, &inspected.graph, &inspected.constraints)?;
    let rewrite = rewrite_source(&inspected.source, &retention.retained_units)?;
    Ok(InspectedReduction {
        source: inspected.source,
        graph: inspected.graph,
        constraints: inspected.constraints,
        retention,
        rewrite,
        tags: inspected.tags,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CollectedDependencies {
    graph: DependencyGraph,
    constraints: SourceConstraints,
    tags: DefinitionTags,
}

struct CompilerInspection {
    source: SourceInventory,
    definitions: Option<DefinitionGraph>,
    dependencies: Option<CollectedDependencies>,
}

fn run_inspection(
    source: &str,
    context: &CompilationContext<'_>,
    collection_mode: CollectionMode,
    coordinates: Option<&SourceRewrite>,
) -> Result<CompilerInspection, InputError> {
    #[cfg(test)]
    INSPECTION_COUNT.set(INSPECTION_COUNT.get() + 1);
    validate_crate_configuration(context)?;
    validate_target(context.sysroot, context.target())?;

    let result = Arc::new(Mutex::new(None));
    let diagnostics = Arc::new(Mutex::new(DiagnosticState::default()));
    let denied_file = Arc::new(Mutex::new(None));
    let expansion_complete = Arc::new(AtomicBool::new(false));
    #[cfg(rust_item_dependencies_patched)]
    let denied_resources = Arc::new(Mutex::new(Vec::new()));
    #[cfg(rust_item_dependencies_patched)]
    let denied_proc_macro = Arc::new(Mutex::new(None));
    let original = Arc::<str>::from(source);
    let (_, offsets) = OriginalOffsetMap::from_source(&original)?;
    let mut callbacks = InputCallbacks {
        original: Arc::clone(&original),
        offsets,
        working_directory: PathBuf::new(),
        denied_file: Arc::clone(&denied_file),
        expansion_complete: Arc::clone(&expansion_complete),
        diagnostics: Arc::clone(&diagnostics),
        #[cfg(rust_item_dependencies_patched)]
        denied_resources: Arc::clone(&denied_resources),
        #[cfg(rust_item_dependencies_patched)]
        denied_proc_macro: Arc::clone(&denied_proc_macro),
        #[cfg(rust_item_dependencies_patched)]
        allowed_proc_macro_artifacts: context
            .external_crates()
            .proc_macro_execution_artifacts()
            .iter()
            .map(|artifact| artifact.artifact().to_owned())
            .collect(),
        result: Arc::clone(&result),
        inventory: None,
        collection_mode,
        coordinates: coordinates.cloned(),
        direct_external_crates: context
            .external_crates()
            .direct()
            .iter()
            .map(|external| external.extern_name().to_owned())
            .collect(),
        crate_type: context.crate_type(),
        crate_name: context.crate_name().to_owned(),
        entry_points: context.entry_points().cloned().collect(),
    };

    let arguments = compiler_arguments(context);
    let _ =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut callbacks));

    if let Some(result) = result
        .lock()
        .expect("source inspection result mutex is poisoned")
        .take()
    {
        return result.map_err(|error| map_input_error(error, coordinates));
    }

    let diagnostics = diagnostics
        .lock()
        .expect("diagnostic state mutex is poisoned");
    #[cfg(rust_item_dependencies_patched)]
    {
        let mut resources = denied_resources
            .lock()
            .expect("external resource mutex is poisoned")
            .clone();
        resources.sort();
        resources.dedup();
        if let Some(span) = resources.first().copied() {
            let range = original_diagnostic_range(&diagnostics, &callbacks.offsets, span)?;
            return Err(map_input_error(
                InputError::UnsupportedInput {
                    reason: UnsupportedReason::ExternalCompileTimeResource,
                    range: Some(range),
                },
                coordinates,
            ));
        }
    }

    #[cfg(rust_item_dependencies_patched)]
    if let Some(denied) = *denied_proc_macro
        .lock()
        .expect("denied procedural macro mutex is poisoned")
    {
        let range = diagnostics
            .errors
            .iter()
            .skip(denied.diagnostic_index)
            .filter_map(|diagnostic| diagnostic.normalized_range)
            .min()
            .map(|range| callbacks.offsets.original_range(range))
            .transpose()?;
        return Err(map_input_error(
            InputError::UnsupportedInput {
                reason: denied.reason,
                range,
            },
            coordinates,
        ));
    }

    if let Some(diagnostic) = diagnostics
        .errors
        .iter()
        .find(|diagnostic| matches!(diagnostic.code, Some(E0554 | E0658)))
    {
        let range = diagnostic
            .normalized_range
            .ok_or(InputError::Source(SourceError::InvalidSpan))?;
        return Err(map_input_error(
            InputError::UnsupportedInput {
                reason: UnsupportedReason::UnstableLanguageFeature,
                range: Some(callbacks.offsets.original_range(range)?),
            },
            coordinates,
        ));
    }

    if let Some(diagnostic) = diagnostics
        .errors
        .iter()
        .find(|diagnostic| diagnostic.code == Some(E0463))
    {
        let range = diagnostic
            .normalized_range
            .ok_or(InputError::Source(SourceError::InvalidSpan))?;
        return Err(map_input_error(
            InputError::UnsupportedInput {
                reason: UnsupportedReason::ExternalDependency,
                range: Some(callbacks.offsets.original_range(range)?),
            },
            coordinates,
        ));
    }

    if let Some(denied) = *denied_file.lock().expect("denied file mutex is poisoned") {
        let range = diagnostics
            .errors
            .iter()
            .skip(denied.diagnostic_index)
            .filter_map(|diagnostic| diagnostic.normalized_range)
            .min()
            .ok_or(InputError::Source(SourceError::InvalidSpan))?;
        return Err(map_input_error(
            InputError::UnsupportedInput {
                reason: denied.reason,
                range: Some(callbacks.offsets.original_range(range)?),
            },
            coordinates,
        ));
    }

    if diagnostics
        .errors
        .iter()
        .any(|diagnostic| diagnostic.compiler_bug)
    {
        Err(InputError::CompilerIce)
    } else if !diagnostics.errors.is_empty() {
        let diagnostics = diagnostics
            .errors
            .iter()
            .map(|diagnostic| {
                Ok(CompilerDiagnostic {
                    message: diagnostic.message.clone(),
                    range: diagnostic
                        .normalized_range
                        .map(|range| callbacks.offsets.original_range(range))
                        .transpose()?,
                })
            })
            .collect::<Result<_, SourceError>>()?;
        Err(map_input_error(
            InputError::OriginalCompilationFailed(diagnostics),
            coordinates,
        ))
    } else {
        Err(InputError::CompilerProtocolFailure)
    }
}

fn map_input_error(error: InputError, coordinates: Option<&SourceRewrite>) -> InputError {
    let Some(coordinates) = coordinates else {
        return error;
    };
    let map = |range: ByteRange| coordinates.original_range(range);
    match error {
        error @ (InputError::InvalidCrateName { .. }
        | InputError::MissingLibraryEntryPoint
        | InputError::InvalidEntryPoint { .. }) => error,
        InputError::UnsupportedInput { reason, range } => match range.map(map).transpose() {
            Ok(range) => InputError::UnsupportedInput { reason, range },
            Err(error) => InputError::Rewrite(error),
        },
        InputError::OriginalCompilationFailed(mut diagnostics) => {
            for diagnostic in &mut diagnostics {
                if let Some(range) = diagnostic.range {
                    match map(range) {
                        Ok(range) => diagnostic.range = Some(range),
                        Err(error) => return InputError::Rewrite(error),
                    }
                }
            }
            InputError::OriginalCompilationFailed(diagnostics)
        }
        InputError::Tag(TagError::InvalidTag(range)) => match map(range) {
            Ok(range) => InputError::Tag(TagError::InvalidTag(range)),
            Err(error) => InputError::Rewrite(error),
        },
        InputError::Dependency(DependencyError::Tag(TagError::InvalidTag(range))) => {
            match map(range) {
                Ok(range) => {
                    InputError::Dependency(DependencyError::Tag(TagError::InvalidTag(range)))
                }
                Err(error) => InputError::Rewrite(error),
            }
        }
        error => error,
    }
}

fn compiler_arguments(context: &CompilationContext<'_>) -> Vec<String> {
    let mut arguments = vec![
        "rust-item-dependencies".to_owned(),
        "main.rs".to_owned(),
        format!("--crate-name={}", context.crate_name()),
        format!("--crate-type={}", context.crate_type_argument()),
        format!("--edition={}", context.edition_argument()),
        format!("--target={}", context.target()),
        format!("-Copt-level={}", context.optimization_level_argument()),
        "--sysroot".to_owned(),
        context.sysroot.to_string_lossy().into_owned(),
        "--emit=metadata=-".to_owned(),
    ];
    arguments.extend(context.cfgs().map(|cfg| format!("--cfg=r#{cfg}")));
    for external in context.external_crates().direct() {
        arguments.push("--extern".to_owned());
        arguments.push(format!(
            "{}={}",
            external.extern_name(),
            external.artifact_argument()
        ));
    }
    if let Some(directory) = context.external_crates().search_directory() {
        arguments.push("-L".to_owned());
        arguments.push(format!("dependency={directory}"));
        arguments.push("-L".to_owned());
        arguments.push(format!("crate={directory}"));
    }
    arguments
}

fn validate_crate_configuration(context: &CompilationContext<'_>) -> Result<(), InputError> {
    let crate_name = context.crate_name();
    if crate_name.is_empty()
        || crate_name
            .chars()
            .any(|character| !character.is_alphanumeric() && character != '_')
    {
        return Err(InputError::InvalidCrateName {
            name: crate_name.to_owned(),
        });
    }
    if context.crate_type() == CrateType::Library && context.entry_points().next().is_none() {
        return Err(InputError::MissingLibraryEntryPoint);
    }
    Ok(())
}

fn validate_target(sysroot: &Path, target: &str) -> Result<(), InputError> {
    if !TARGETS.contains(&target) {
        return Err(InputError::UnsupportedInput {
            reason: UnsupportedReason::UnsupportedTarget,
            range: None,
        });
    }
    let installed = rustc_session::filesearch::make_target_lib_path(sysroot, target);
    let has_std = installed
        .read_dir()
        .ok()
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .filter_map(|entry| entry.file_name().into_string().ok())
        .any(|name| name.starts_with("libstd-") && name.ends_with(".rlib"));
    if !has_std {
        return Err(InputError::UnsupportedInput {
            reason: UnsupportedReason::UnsupportedTarget,
            range: None,
        });
    }
    Ok(())
}

struct InputCallbacks {
    original: Arc<str>,
    offsets: OriginalOffsetMap,
    working_directory: PathBuf,
    denied_file: Arc<Mutex<Option<DeniedFile>>>,
    expansion_complete: Arc<AtomicBool>,
    diagnostics: Arc<Mutex<DiagnosticState>>,
    #[cfg(rust_item_dependencies_patched)]
    denied_resources: Arc<Mutex<Vec<Span>>>,
    #[cfg(rust_item_dependencies_patched)]
    denied_proc_macro: Arc<Mutex<Option<DeniedFile>>>,
    #[cfg(rust_item_dependencies_patched)]
    allowed_proc_macro_artifacts: BTreeSet<PathBuf>,
    result: Arc<Mutex<Option<Result<CompilerInspection, InputError>>>>,
    inventory: Option<SourceInventory>,
    collection_mode: CollectionMode,
    coordinates: Option<SourceRewrite>,
    direct_external_crates: BTreeSet<String>,
    crate_type: CrateType,
    crate_name: String,
    entry_points: Vec<EntryPoint>,
}

impl InputCallbacks {
    fn finish(&self, result: Result<CompilerInspection, InputError>) -> Compilation {
        *self
            .result
            .lock()
            .expect("source inspection result mutex is poisoned") = Some(result);
        Compilation::Stop
    }

    fn compiler_has_errors(&self) -> bool {
        !self
            .diagnostics
            .lock()
            .expect("diagnostic state mutex is poisoned")
            .errors
            .is_empty()
    }
}

fn resolve_entry_points(
    tcx: TyCtxt<'_>,
    crate_name: &str,
    entry_points: &[EntryPoint],
) -> Result<Vec<ResolvedEntryPoint>, InputError> {
    let mut resolved = Vec::new();
    let paths = entry_points
        .iter()
        .map(EntryPoint::path)
        .collect::<BTreeSet<_>>();
    for path in paths {
        let segments = parse_entry_point_path(tcx, crate_name, path).map_err(|reason| {
            InputError::InvalidEntryPoint {
                path: path.to_owned(),
                reason,
            }
        })?;
        let mut module = CRATE_DEF_ID;
        let mut reexports = Vec::new();
        let mut definition = None;

        for (index, name) in segments.iter().copied().enumerate() {
            let last = index + 1 == segments.len();
            let named = tcx
                .module_children_local(module)
                .iter()
                .filter(|child| child.ident.name == name)
                .collect::<Vec<_>>();
            let candidates = named
                .iter()
                .copied()
                .filter_map(|child| match child.res {
                    Res::Def(DefKind::Mod, target) if !last => {
                        target.as_local().map(|target| (child, target))
                    }
                    Res::Def(DefKind::Fn | DefKind::Static { .. }, target) if last => target
                        .as_local()
                        .filter(|target| is_free_entry_item(tcx, *target))
                        .map(|target| (child, target)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let (child, target) = match candidates.as_slice() {
                [(child, target)] => (*child, *target),
                [] if named.is_empty() => {
                    return Err(InputError::InvalidEntryPoint {
                        path: path.to_owned(),
                        reason: EntryPointError::NotFound,
                    });
                }
                _ => {
                    return Err(InputError::InvalidEntryPoint {
                        path: path.to_owned(),
                        reason: EntryPointError::UnsupportedItem,
                    });
                }
            };
            for step in &child.reexport_chain {
                let reexport = match *step {
                    Reexport::Single(definition)
                    | Reexport::Glob(definition)
                    | Reexport::ExternCrate(definition) => definition.as_local(),
                    Reexport::MacroUse | Reexport::MacroExport => None,
                }
                .ok_or_else(|| InputError::InvalidEntryPoint {
                    path: path.to_owned(),
                    reason: EntryPointError::UnsupportedItem,
                })?;
                if !reexports.contains(&reexport) {
                    reexports.push(reexport);
                }
            }
            if last {
                definition = Some(target);
            } else {
                module = target;
            }
        }

        resolved.push(ResolvedEntryPoint {
            definition: definition.ok_or_else(|| InputError::InvalidEntryPoint {
                path: path.to_owned(),
                reason: EntryPointError::NotFound,
            })?,
            reexports,
        });
    }
    Ok(resolved)
}

fn is_free_entry_item(tcx: TyCtxt<'_>, definition: LocalDefId) -> bool {
    matches!(
        tcx.hir_node_by_def_id(definition),
        hir::Node::Item(hir::Item {
            kind: hir::ItemKind::Fn { .. } | hir::ItemKind::Static(..),
            ..
        })
    )
}

fn parse_entry_point_path(
    tcx: TyCtxt<'_>,
    crate_name: &str,
    path: &str,
) -> Result<Vec<Symbol>, EntryPointError> {
    let segments = path.split("::").collect::<Vec<_>>();
    if segments.len() < 2 || segments.iter().any(|segment| segment.is_empty()) {
        return Err(EntryPointError::InvalidPath);
    }
    if segments[0] != crate_name {
        return Err(EntryPointError::WrongCrate);
    }
    segments[1..]
        .iter()
        .map(|segment| {
            let (name, raw) = segment
                .strip_prefix("r#")
                .map_or((*segment, false), |name| (name, true));
            if !rustc_lexer::is_ident(name) {
                return Err(EntryPointError::InvalidPath);
            }
            let symbol = Symbol::intern(name);
            if raw {
                if !symbol.can_be_raw() {
                    return Err(EntryPointError::InvalidPath);
                }
            } else if symbol.is_reserved(|| tcx.sess.edition()) {
                return Err(EntryPointError::InvalidPath);
            }
            Ok(symbol)
        })
        .collect()
}

impl Callbacks for InputCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.opts.unstable_features = UnstableFeatures::Disallow;
        let name = config
            .opts
            .file_path_mapping()
            .to_real_filename(&RealFileName::empty(), Path::new("main.rs"));
        config.input = Input::Str {
            name: FileName::Real(name),
            input: self.original.to_string(),
        };
        config.file_loader = Some(Box::new(DenyExternalFiles {
            working_directory: self.working_directory.clone(),
            denied_file: Arc::clone(&self.denied_file),
            expansion_complete: Arc::clone(&self.expansion_complete),
            diagnostics: Arc::clone(&self.diagnostics),
        }));
        let diagnostics = Arc::clone(&self.diagnostics);
        config.psess_created = Some(Box::new(move |parse_session| {
            let source_map = parse_session.clone_source_map();
            parse_session.dcx().set_emitter(Box::new(CapturingEmitter {
                source_map,
                diagnostics,
            }));
        }));

        #[cfg(rust_item_dependencies_patched)]
        {
            let denied_resources = Arc::clone(&self.denied_resources);
            config.external_resource_guard =
                Some(rustc_driver::ExternalResourceGuard::new(move |resource| {
                    let span = resource.span.source_callsite();
                    denied_resources
                        .lock()
                        .expect("external resource mutex is poisoned")
                        .push(span);
                }));

            let allowed = self.allowed_proc_macro_artifacts.clone();
            let denied_proc_macro = Arc::clone(&self.denied_proc_macro);
            let diagnostics = Arc::clone(&self.diagnostics);
            config.proc_macro_load_guard =
                Some(rustc_driver::ProcMacroLoadGuard::new(move |artifact| {
                    if allowed.contains(artifact) {
                        return true;
                    }
                    let diagnostic_index = diagnostics
                        .lock()
                        .expect("diagnostic state mutex is poisoned")
                        .errors
                        .len();
                    if diagnostic_index == 0 {
                        let mut denied = denied_proc_macro
                            .lock()
                            .expect("denied procedural macro mutex is poisoned");
                        if denied.is_none() {
                            *denied = Some(DeniedFile {
                                reason: UnsupportedReason::ProcMacro,
                                diagnostic_index,
                            });
                        }
                    }
                    false
                }));
        }
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        krate: &mut ast::Crate,
    ) -> Compilation {
        if self.compiler_has_errors() {
            return Compilation::Stop;
        }
        self.diagnostics
            .lock()
            .expect("diagnostic state mutex is poisoned")
            .main_start = Some(
            compiler
                .sess
                .source_map()
                .lookup_source_file(krate.spans.inner_span.lo())
                .start_pos
                .0,
        );
        let inventory = match collect_source(compiler, krate, Arc::clone(&self.original)) {
            Ok(inventory) => inventory,
            Err(error) => return self.finish(Err(error.into())),
        };
        if let Err(error) =
            validate_unexpanded(compiler, krate, &inventory, &self.direct_external_crates)
        {
            return self.finish(Err(error));
        }
        self.inventory = Some(inventory);
        Compilation::Continue
    }

    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if self.compiler_has_errors() {
            return Compilation::Stop;
        }
        self.expansion_complete.store(true, Ordering::Relaxed);
        #[cfg(rust_item_dependencies_patched)]
        if let Some(error) = validate_attribute_expansions(tcx, &self.offsets) {
            return self.finish(Err(error));
        }
        {
            let (_, krate) = tcx.resolver_for_lowering();
            let krate = krate.borrow();
            if let Err(error) = validate_expanded(
                compiler,
                &krate,
                self.inventory
                    .as_ref()
                    .expect("source inventory must be collected before expansion"),
                &self.direct_external_crates,
            ) {
                return self.finish(Err(error));
            }
            #[cfg(rust_item_dependencies_patched)]
            if let Err(error) = refine_attribute_macros_from_compiler(
                compiler,
                tcx,
                &krate,
                self.inventory
                    .as_mut()
                    .expect("source inventory must survive through expansion"),
            ) {
                return self.finish(Err(error.into()));
            }
        }
        #[cfg(rust_item_dependencies_patched)]
        {
            #[cfg(test)]
            let omit_one_selection = {
                let mut request = OMIT_ONE_MACRO_RULE_SELECTION_FROM
                    .lock()
                    .expect("macro rule selection omission mutex is poisoned");
                if request.as_deref()
                    == Some(
                        self.inventory
                            .as_ref()
                            .expect("source inventory must survive through expansion")
                            .original
                            .as_ref(),
                    )
                {
                    request.take();
                    true
                } else {
                    false
                }
            };
            #[cfg(not(test))]
            let omit_one_selection = false;
            if let Err(error) = refine_macro_rules_from_compiler(
                compiler,
                tcx,
                self.inventory
                    .as_mut()
                    .expect("source inventory must survive through expansion"),
                omit_one_selection,
            ) {
                return self.finish(Err(error.into()));
            }
        }
        tcx.ensure_ok().early_lint_checks(());
        if self.crate_type == CrateType::Binary && tcx.entry_fn(()).is_none() {
            return self.finish(Err(InputError::UnsupportedInput {
                reason: UnsupportedReason::MissingMain,
                range: None,
            }));
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        if self.crate_type == CrateType::Binary && tcx.entry_fn(()).is_none() {
            return self.finish(Err(InputError::UnsupportedInput {
                reason: UnsupportedReason::MissingMain,
                range: None,
            }));
        }
        let entry_points = match resolve_entry_points(tcx, &self.crate_name, &self.entry_points) {
            Ok(entry_points) => entry_points,
            Err(error) => return self.finish(Err(error)),
        };
        let inventory = self
            .inventory
            .as_ref()
            .expect("source inventory must survive through analysis");
        let (definitions, dependencies) = match self.collection_mode {
            CollectionMode::Source => (None, None),
            CollectionMode::Definitions => match collect_definition_graph(compiler, tcx, inventory)
            {
                Ok(definitions) => (Some(definitions), None),
                Err(error) => return self.finish(Err(error.into())),
            },
            CollectionMode::Dependencies => {
                match collect_dependency_graph(
                    compiler,
                    tcx,
                    inventory,
                    self.coordinates.as_ref(),
                    self.crate_type,
                    &entry_points,
                ) {
                    Ok(dependencies) => (None, Some(dependencies)),
                    Err(error) => return self.finish(Err(error.into())),
                }
            }
        };
        let source = self
            .inventory
            .take()
            .expect("source inventory must survive through analysis");
        self.finish(Ok(CompilerInspection {
            source,
            definitions,
            dependencies,
        }))
    }
}

fn collect_dependency_graph(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    coordinates: Option<&SourceRewrite>,
    crate_type: CrateType,
    entry_points: &[ResolvedEntryPoint],
) -> Result<CollectedDependencies, DependencyError> {
    let mut definitions = collect_definitions(compiler, tcx, source)?;
    let tags = collect_definition_tags(compiler, tcx, source, &definitions)?;
    // Source constraints join HIR definitions to the rewritten inventory, so
    // they must be collected before any identity is moved to original-source
    // coordinates. Preserve the established query order for original-source
    // analysis, where no coordinate switch is needed.
    let constraints = coordinates
        .map(|_| collect_source_constraints(tcx, source, &definitions))
        .transpose()?;
    if let Some(coordinates) = coordinates {
        definitions.normalize_identity_keys(coordinates)?;
    }
    let CollectedExpansions {
        nodes: mut expansions,
        mut edges,
    } = collect_expansions(compiler, tcx, source, &mut definitions)?;
    let needs_downstream_selection = if crate_type == CrateType::Library {
        entry_points.iter().try_fold(false, |needed, entry| {
            if needed {
                Ok(true)
            } else {
                entry_requires_downstream_selection(tcx, &definitions, entry.definition)
            }
        })?
    } else {
        false
    };
    let CollectedMonomorphization {
        proofs,
        mut mono_nodes,
        edges: mono_edges,
        mut roots,
    } = collect_monomorphization(
        compiler,
        tcx,
        source,
        &mut definitions,
        crate_type,
        entry_points,
    )?;
    if needs_downstream_selection {
        roots.extend(downstream_selection_roots(&definitions.graph));
        roots.sort();
        roots.dedup();
    }
    let mut constraints =
        constraints.map_or_else(|| collect_source_constraints(tcx, source, &definitions), Ok)?;
    collect_macro_rule_expansion_constraints(
        source,
        &definitions.graph,
        &expansions,
        &mut constraints,
    )?;
    edges.extend(mono_edges);
    #[cfg(all(test, rust_item_dependencies_patched))]
    let omit_selected_impl = {
        let mut request = OMIT_ONE_SELECTED_IMPL_FACT_FROM
            .lock()
            .expect("fact omission mutex is poisoned");
        if request.as_deref() == Some(source.original.as_ref()) {
            request.take();
            true
        } else {
            false
        }
    };
    #[cfg(all(test, rust_item_dependencies_patched))]
    if omit_selected_impl {
        let fact = edges
            .iter()
            .position(|edge| {
                edge.evidence == EvidenceOrigin::PatchedObserver
                    && matches!(
                        edge.kind,
                        DependencyKind::ProofRelation {
                            relation: ProofRelationKind::SelectedImpl,
                            ..
                        }
                    )
            })
            .expect("the mutation fixture must observe a selected implementation");
        edges.remove(fact);
    }
    if let Some(coordinates) = coordinates {
        normalize_definition_graph(&mut definitions.graph, coordinates)?;
        normalize_expansion_ranges(&mut expansions, coordinates)?;
        normalize_mono_ranges(&mut mono_nodes, coordinates)?;
        normalize_observation_ranges(&mut edges, coordinates)?;
    }
    let graph = DependencyGraph::new(
        definitions.graph,
        expansions,
        proofs,
        mono_nodes,
        edges,
        roots,
    )?;
    Ok(CollectedDependencies {
        graph,
        constraints,
        tags,
    })
}

fn entry_requires_downstream_selection(
    tcx: TyCtxt<'_>,
    definitions: &crate::definitions::CollectedDefinitions,
    entry: LocalDefId,
) -> Result<bool, DefinitionError> {
    if matches!(tcx.def_kind(entry), DefKind::Fn)
        && tcx.generics_of(entry).requires_monomorphization(tcx)
    {
        return Ok(true);
    }

    let entry_definition = definitions
        .definition_id(entry)
        .ok_or(DefinitionError::IncompleteDefinition)?;
    match definitions.graph.definitions[entry_definition.0 as usize].kind {
        DefinitionKind::Function => {
            let signature = tcx.fn_sig(entry).instantiate_identity().skip_norm_wip();
            Ok(signature
                .inputs_and_output()
                .skip_binder()
                .iter()
                .any(type_exposes_local_definition))
        }
        DefinitionKind::Static => Ok(type_exposes_local_definition(
            tcx.type_of(entry).instantiate_identity().skip_norm_wip(),
        )),
        _ => Ok(false),
    }
}

fn type_exposes_local_definition(value: ty::Ty<'_>) -> bool {
    value.walk().any(|argument| {
        let GenericArgKind::Type(value) = argument.kind() else {
            return false;
        };
        match *value.kind() {
            ty::Adt(definition, _) => definition.did().is_local(),
            ty::Foreign(definition)
            | ty::FnDef(definition, _)
            | ty::Closure(definition, _)
            | ty::CoroutineClosure(definition, _)
            | ty::Coroutine(definition, _)
            | ty::CoroutineWitness(definition, _) => definition.is_local(),
            ty::Alias(_, alias) => match alias.kind {
                ty::AliasTyKind::Projection { def_id }
                | ty::AliasTyKind::Inherent { def_id }
                | ty::AliasTyKind::Opaque { def_id }
                | ty::AliasTyKind::Free { def_id } => def_id.is_local(),
            },
            ty::Dynamic(predicates, ..) => {
                predicates
                    .iter()
                    .any(|predicate| match predicate.skip_binder() {
                        ty::ExistentialPredicate::Trait(reference) => reference.def_id.is_local(),
                        ty::ExistentialPredicate::Projection(projection) => {
                            projection.def_id.is_local()
                        }
                        ty::ExistentialPredicate::AutoTrait(definition) => definition.is_local(),
                    })
            }
            _ => false,
        }
    })
}

fn downstream_selection_roots(graph: &DefinitionGraph) -> Vec<RootRecord> {
    graph
        .definitions
        .iter()
        .filter(|definition| is_downstream_selection_candidate(graph, definition.id))
        .map(|definition| RootRecord {
            node: GraphNode::Definition(definition.id),
            reason: RootReason::DownstreamSelection,
        })
        .collect()
}

fn normalize_definition_graph(
    graph: &mut DefinitionGraph,
    coordinates: &SourceRewrite,
) -> Result<(), DependencyError> {
    let mut definitions = graph.definitions.clone();
    for definition in &mut definitions {
        normalize_definition_key(&mut definition.key, coordinates)?;
        match &mut definition.origin {
            DefinitionOrigin::Written {
                unit_range, anchor, ..
            } => {
                if definition.kind == DefinitionKind::Crate {
                    *unit_range = coordinates.original_crate_range(*unit_range)?;
                    *anchor = coordinates.original_crate_range(*anchor)?;
                } else {
                    *unit_range = coordinates.original_range(*unit_range)?;
                    *anchor = coordinates.original_range(*anchor)?;
                }
            }
            DefinitionOrigin::Expanded {
                invocation_range, ..
            } => {
                *invocation_range = coordinates.original_range(*invocation_range)?;
            }
            DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => {}
        }
    }
    let mut edges = graph.edges.clone();
    for edge in &mut edges {
        for site in &mut edge.sites {
            *site = coordinates.original_range(*site)?;
        }
    }
    *graph = DefinitionGraph::new(definitions, graph.external_definitions.clone(), edges)
        .map_err(DefinitionError::from)?;
    Ok(())
}

fn normalize_expansion_ranges(
    expansions: &mut [ExpansionNode],
    coordinates: &SourceRewrite,
) -> Result<(), SourceRewriteError> {
    for expansion in expansions {
        for part in &mut expansion.key.0 {
            for range in [
                &mut part.invocation_range,
                &mut part.node_range,
                &mut part.target_range,
                &mut part.selected_macro_rule,
            ]
            .into_iter()
            .flatten()
            {
                *range = coordinates.original_range(*range)?;
            }
        }
    }
    Ok(())
}

fn normalize_mono_ranges(
    nodes: &mut [MonoNode],
    coordinates: &SourceRewrite,
) -> Result<(), SourceRewriteError> {
    for node in nodes {
        let MonoKey::Allocation(allocation) = &mut node.key else {
            continue;
        };
        for part in &mut allocation.path {
            if let AllocationPathSite::Source(range) = &mut part.site {
                *range = coordinates.original_range(*range)?;
            }
        }
    }
    Ok(())
}

fn normalize_observation_ranges(
    edges: &mut [DependencyEdge],
    coordinates: &SourceRewrite,
) -> Result<(), SourceRewriteError> {
    for edge in edges {
        for site in &mut edge.sites {
            if let ObservationSite::Source(range) = site {
                *range = coordinates.original_range(*range)?;
            }
        }
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn validate_attribute_expansions(
    tcx: TyCtxt<'_>,
    offsets: &OriginalOffsetMap,
) -> Option<InputError> {
    use rustc_span::hygiene::{ExpnKind, MacroKind};

    let rejected = tcx
        .resolutions(())
        .macro_invocation_origins
        .items()
        .filter_map(|(&expansion, origin)| {
            let ExpnKind::Macro(MacroKind::Attr, name) = expansion.expn_data().kind else {
                return None;
            };
            let canonical_name = if origin.implementation_kind == MacroImplementationKind::Builtin {
                expansion
                    .expn_data()
                    .macro_def_id
                    .map_or(name, |definition| tcx.item_name(definition))
            } else {
                name
            };
            let reason =
                unsupported_resolved_attribute(origin.implementation_kind, canonical_name)?;
            let raw = expansion.expn_data().call_site;
            let source_map = tcx.sess.source_map();
            let range = original_diagnostic_range_from_span(source_map, offsets, raw);
            Some((range.ok(), reason))
        })
        .min();
    rejected.map(|(range, reason)| match range {
        Some(range) => InputError::UnsupportedInput {
            reason,
            range: Some(range),
        },
        None => InputError::Source(SourceError::InvalidSpan),
    })
}

#[cfg(rust_item_dependencies_patched)]
fn unsupported_resolved_attribute(
    implementation: MacroImplementationKind,
    canonical_name: Symbol,
) -> Option<UnsupportedReason> {
    match implementation {
        MacroImplementationKind::Builtin => unsupported_attribute_symbol(canonical_name),
        _ => None,
    }
}

fn validate_unexpanded(
    compiler: &Compiler,
    krate: &ast::Crate,
    inventory: &SourceInventory,
    direct_external_crates: &BTreeSet<String>,
) -> Result<(), InputError> {
    let configured_attrs = pre_configure_attrs(&compiler.sess, &krate.attrs);
    if let Some(attribute) = configured_attrs
        .iter()
        .find(|attribute| attribute.has_name(sym::feature))
    {
        return Err(unsupported(
            compiler,
            inventory,
            UnsupportedReason::UnstableLanguageFeature,
            attribute.span,
        ));
    }
    let crate_name = compiler
        .sess
        .opts
        .crate_name
        .as_deref()
        .ok_or(InputError::CompilerProtocolFailure)?;
    let features = features(
        &compiler.sess,
        &configured_attrs,
        Symbol::intern(crate_name),
    );
    if let Some((_, span)) = features
        .enabled_features_iter_stable_order()
        .min_by_key(|(_, span)| (span.lo(), span.hi()))
    {
        return Err(unsupported(
            compiler,
            inventory,
            UnsupportedReason::UnstableLanguageFeature,
            span,
        ));
    }

    let root_active = inventory
        .units
        .first()
        .is_some_and(|unit| unit.cfg_state == crate::source::CfgState::Active);
    let mut validator = UnexpandedValidator {
        compiler,
        inventory,
        features,
        active_stack: vec![root_active],
        direct_external_crates,
        errors: Vec::new(),
    };
    if root_active {
        validator.validate_attributes(&configured_attrs);
    }
    validator.visit_crate(krate);
    validator.finish()
}

struct UnexpandedValidator<'a> {
    compiler: &'a Compiler,
    inventory: &'a SourceInventory,
    features: Features,
    active_stack: Vec<bool>,
    direct_external_crates: &'a BTreeSet<String>,
    errors: Vec<InputError>,
}

impl UnexpandedValidator<'_> {
    fn current_active(&self) -> bool {
        *self
            .active_stack
            .last()
            .expect("crate cfg state must exist")
    }

    fn configured<T: ast::HasTokens + Clone>(&self, node: &T) -> Option<T> {
        if !self.current_active() {
            return None;
        }
        StripUnconfigured {
            sess: &self.compiler.sess,
            features: Some(&self.features),
            config_tokens: false,
            lint_node_id: ast::CRATE_NODE_ID,
        }
        .configure(node.clone())
    }

    fn reject(&mut self, reason: UnsupportedReason, span: Span) {
        self.errors
            .push(unsupported(self.compiler, self.inventory, reason, span));
    }

    fn validate_attributes(&mut self, attributes: &[ast::Attribute]) {
        for attribute in attributes {
            if let Some(reason) = unsupported_attribute_reason(attribute) {
                self.reject(reason, attribute.span);
            }
        }
    }

    fn finish(mut self) -> Result<(), InputError> {
        self.errors.sort_by_key(|error| match error {
            InputError::UnsupportedInput { reason, range } => {
                (range.map_or(u32::MAX, |range| range.start), *reason)
            }
            _ => (u32::MAX, UnsupportedReason::MissingMain),
        });
        self.errors.into_iter().next().map_or(Ok(()), Err)
    }
}

impl<'ast> Visitor<'ast> for UnexpandedValidator<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let Some(configured) = self.configured(item) else {
            self.active_stack.push(false);
            visit::walk_item(self, item);
            self.active_stack.pop();
            return;
        };
        self.validate_attributes(&configured.attrs);
        match &configured.kind {
            ast::ItemKind::Mod(_, _, ast::ModKind::Unloaded) => {
                self.reject(UnsupportedReason::AdditionalSourceFile, item.span)
            }
            ast::ItemKind::GlobalAsm(_) => self.reject(UnsupportedReason::Assembly, item.span),
            ast::ItemKind::ExternCrate(original, identifier) => {
                let name = original.unwrap_or(identifier.name);
                if !supported_external_crate(name, self.direct_external_crates) {
                    self.reject(external_crate_reason(name), item.span);
                }
            }
            _ => {}
        }

        self.active_stack.push(true);
        visit::walk_item(self, item);
        self.active_stack.pop();
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: AssocCtxt) {
        let Some(configured) = self.configured(item) else {
            self.active_stack.push(false);
            visit::walk_assoc_item(self, item, context);
            self.active_stack.pop();
            return;
        };
        self.validate_attributes(&configured.attrs);
        self.active_stack.push(true);
        visit::walk_assoc_item(self, item, context);
        self.active_stack.pop();
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        let Some(configured) = self.configured(item) else {
            self.active_stack.push(false);
            visit::walk_item(self, item);
            self.active_stack.pop();
            return;
        };
        self.validate_attributes(&configured.attrs);
        self.active_stack.push(true);
        visit::walk_item(self, item);
        self.active_stack.pop();
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let active = self.configured(expression).is_some();
        if active && matches!(expression.kind, ast::ExprKind::InlineAsm(_)) {
            self.reject(UnsupportedReason::Assembly, expression.span);
        }
        self.active_stack.push(active);
        visit::walk_expr(self, expression);
        self.active_stack.pop();
    }

    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        let active = self.configured(statement).is_some();
        self.active_stack.push(active);
        visit::walk_stmt(self, statement);
        self.active_stack.pop();
    }

    fn visit_arm(&mut self, arm: &'ast ast::Arm) {
        let active = self.configured(arm).is_some();
        self.active_stack.push(active);
        visit::walk_arm(self, arm);
        self.active_stack.pop();
    }

    fn visit_expr_field(&mut self, field: &'ast ast::ExprField) {
        let active = self.configured(field).is_some();
        self.active_stack.push(active);
        visit::walk_expr_field(self, field);
        self.active_stack.pop();
    }

    fn visit_field_def(&mut self, field: &'ast ast::FieldDef) {
        let active = self.configured(field).is_some();
        self.active_stack.push(active);
        visit::walk_field_def(self, field);
        self.active_stack.pop();
    }

    fn visit_generic_param(&mut self, parameter: &'ast ast::GenericParam) {
        let active = self.configured(parameter).is_some();
        self.active_stack.push(active);
        visit::walk_generic_param(self, parameter);
        self.active_stack.pop();
    }

    fn visit_param(&mut self, parameter: &'ast ast::Param) {
        let active = self.configured(parameter).is_some();
        self.active_stack.push(active);
        visit::walk_param(self, parameter);
        self.active_stack.pop();
    }

    fn visit_pat_field(&mut self, field: &'ast ast::PatField) {
        let active = self.configured(field).is_some();
        self.active_stack.push(active);
        visit::walk_pat_field(self, field);
        self.active_stack.pop();
    }

    fn visit_variant(&mut self, variant: &'ast ast::Variant) {
        let active = self.configured(variant).is_some();
        self.active_stack.push(active);
        visit::walk_variant(self, variant);
        self.active_stack.pop();
    }

    fn visit_where_predicate(&mut self, predicate: &'ast ast::WherePredicate) {
        let active = self.configured(predicate).is_some();
        self.active_stack.push(active);
        visit::walk_where_predicate(self, predicate);
        self.active_stack.pop();
    }
}

fn validate_expanded(
    compiler: &Compiler,
    krate: &ast::Crate,
    inventory: &SourceInventory,
    direct_external_crates: &BTreeSet<String>,
) -> Result<(), InputError> {
    let mut validator = ExpandedValidator {
        compiler,
        inventory,
        direct_external_crates,
        errors: Vec::new(),
    };
    validator.visit_crate(krate);
    validator.errors.sort_by_key(|error| match error {
        InputError::UnsupportedInput { reason, range } => {
            (range.map_or(u32::MAX, |range| range.start), *reason)
        }
        _ => (u32::MAX, UnsupportedReason::MissingMain),
    });
    validator.errors.into_iter().next().map_or(Ok(()), Err)
}

struct ExpandedValidator<'a> {
    compiler: &'a Compiler,
    inventory: &'a SourceInventory,
    direct_external_crates: &'a BTreeSet<String>,
    errors: Vec<InputError>,
}

impl ExpandedValidator<'_> {
    fn reject(&mut self, reason: UnsupportedReason, span: Span) {
        self.errors.push(unsupported(
            self.compiler,
            self.inventory,
            reason,
            span.source_callsite(),
        ));
    }

    fn validate_attributes(&mut self, attributes: &[ast::Attribute]) {
        for attribute in attributes {
            if let Some(reason) = unsupported_attribute_reason(attribute) {
                self.reject(reason, attribute.span);
            }
        }
    }
}

impl<'ast> Visitor<'ast> for ExpandedValidator<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        self.validate_attributes(&item.attrs);
        match &item.kind {
            ast::ItemKind::GlobalAsm(_) => self.reject(UnsupportedReason::Assembly, item.span),
            ast::ItemKind::ExternCrate(original, identifier) => {
                let name = original.unwrap_or(identifier.name);
                let reason = external_crate_reason(name);
                let provided_by_external_macro = reason == UnsupportedReason::ExternalDependency
                    && item.span.in_external_macro(self.compiler.sess.source_map());
                if !supported_external_crate(name, self.direct_external_crates)
                    && !provided_by_external_macro
                {
                    self.reject(reason, item.span);
                }
            }
            _ => {}
        }
        visit::walk_item(self, item);
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: AssocCtxt) {
        self.validate_attributes(&item.attrs);
        visit::walk_assoc_item(self, item, context);
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        self.validate_attributes(&item.attrs);
        visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        if matches!(expression.kind, ast::ExprKind::InlineAsm(_)) {
            self.reject(UnsupportedReason::Assembly, expression.span);
        }
        visit::walk_expr(self, expression);
    }
}

fn unsupported_attribute_reason(attribute: &ast::Attribute) -> Option<UnsupportedReason> {
    if attribute.has_name(sym::no_std) || attribute.has_name(sym::no_main) {
        Some(UnsupportedReason::NoStdOrNoMain)
    } else if attribute.has_name(sym::path) {
        Some(UnsupportedReason::AdditionalSourceFile)
    } else if attribute.has_name(sym::proc_macro)
        || attribute.has_name(sym::proc_macro_attribute)
        || attribute.has_name(sym::proc_macro_derive)
    {
        Some(UnsupportedReason::ProcMacro)
    } else if attribute.has_name(sym::panic_handler)
        || attribute.has_name(sym::alloc_error_handler)
        || attribute.has_name(sym::crate_name)
        || attribute.has_name(sym::crate_type)
        || attribute.has_name(sym::no_builtins)
        || attribute.has_name(sym::no_link)
        || attribute.has_name(sym::windows_subsystem)
        || attribute.has_name(sym::link)
    {
        Some(UnsupportedReason::NativeLinkOrCustomRuntime)
    } else {
        None
    }
}

fn unsupported_attribute_symbol(name: Symbol) -> Option<UnsupportedReason> {
    matches!(
        name,
        sym::panic_handler | sym::alloc_error_handler | sym::no_link | sym::link
    )
    .then_some(UnsupportedReason::NativeLinkOrCustomRuntime)
}

fn external_crate_reason(name: Symbol) -> UnsupportedReason {
    if name.as_str() == "proc_macro" {
        UnsupportedReason::ProcMacro
    } else {
        UnsupportedReason::ExternalDependency
    }
}

fn supported_external_crate(name: Symbol, direct_external_crates: &BTreeSet<String>) -> bool {
    supported_external_crate_name(name.as_str(), direct_external_crates)
}

fn supported_external_crate_name(name: &str, direct_external_crates: &BTreeSet<String>) -> bool {
    matches!(name, "std" | "core" | "alloc" | "self") || direct_external_crates.contains(name)
}

fn unsupported(
    compiler: &Compiler,
    inventory: &SourceInventory,
    reason: UnsupportedReason,
    span: Span,
) -> InputError {
    match original_span_range(compiler, &inventory.offsets, span) {
        Ok(range) => InputError::UnsupportedInput {
            reason,
            range: Some(range),
        },
        Err(error) => InputError::Source(error),
    }
}

#[derive(Clone, Debug)]
struct ObservedDiagnostic {
    code: Option<ErrCode>,
    normalized_range: Option<ByteRange>,
    compiler_bug: bool,
    message: String,
}

#[derive(Default)]
struct DiagnosticState {
    main_start: Option<u32>,
    errors: Vec<ObservedDiagnostic>,
}

struct CapturingEmitter {
    source_map: Arc<SourceMap>,
    diagnostics: Arc<Mutex<DiagnosticState>>,
}

impl Emitter for CapturingEmitter {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if !diagnostic.is_error() {
            return;
        }
        let normalized_range = diagnostic
            .span
            .primary_span()
            .and_then(|span| normalized_span_range(&self.source_map, span.source_callsite()));
        self.diagnostics
            .lock()
            .expect("diagnostic state mutex is poisoned")
            .errors
            .push(ObservedDiagnostic {
                message: format_diag_messages(&diagnostic.messages, &diagnostic.args).into_owned(),
                code: diagnostic.code,
                normalized_range,
                compiler_bug: matches!(diagnostic.level(), Level::Bug | Level::DelayedBug),
            });
    }

    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

fn normalized_span_range(source_map: &SourceMap, span: Span) -> Option<ByteRange> {
    if span.is_dummy() {
        return None;
    }
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    (start.sf.start_pos == end.sf.start_pos && start.sf.name.short().to_string() == "main.rs")
        .then_some(ByteRange {
            start: start.pos.0,
            end: end.pos.0,
        })
}

fn original_diagnostic_range(
    diagnostics: &DiagnosticState,
    offsets: &OriginalOffsetMap,
    span: Span,
) -> Result<ByteRange, InputError> {
    let start = diagnostics
        .main_start
        .ok_or(InputError::Source(SourceError::InvalidSpan))?;
    let span = span.source_callsite();
    if span.is_dummy() {
        return Err(InputError::Source(SourceError::InvalidSpan));
    }
    let normalized = ByteRange {
        start: span
            .lo()
            .0
            .checked_sub(start)
            .ok_or(InputError::Source(SourceError::InvalidSpan))?,
        end: span
            .hi()
            .0
            .checked_sub(start)
            .ok_or(InputError::Source(SourceError::InvalidSpan))?,
    };
    Ok(offsets.original_range(normalized)?)
}

#[cfg(rust_item_dependencies_patched)]
fn original_diagnostic_range_from_span(
    source_map: &SourceMap,
    offsets: &OriginalOffsetMap,
    span: Span,
) -> Result<ByteRange, InputError> {
    let normalized = normalized_span_range(source_map, span.source_callsite())
        .ok_or(InputError::Source(SourceError::InvalidSpan))?;
    Ok(offsets.original_range(normalized)?)
}

struct DenyExternalFiles {
    working_directory: PathBuf,
    denied_file: Arc<Mutex<Option<DeniedFile>>>,
    expansion_complete: Arc<AtomicBool>,
    diagnostics: Arc<Mutex<DiagnosticState>>,
}

#[derive(Clone, Copy)]
struct DeniedFile {
    reason: UnsupportedReason,
    diagnostic_index: usize,
}

impl DenyExternalFiles {
    fn deny(&self, reason: UnsupportedReason) {
        if self.expansion_complete.load(Ordering::Relaxed) {
            return;
        }
        let diagnostic_index = self
            .diagnostics
            .lock()
            .expect("diagnostic state mutex is poisoned")
            .errors
            .len();
        if diagnostic_index != 0 {
            return;
        }
        let mut denied = self
            .denied_file
            .lock()
            .expect("denied file mutex is poisoned");
        if denied.is_none() {
            *denied = Some(DeniedFile {
                reason,
                diagnostic_index,
            });
        }
    }
}

impl FileLoader for DenyExternalFiles {
    fn file_exists(&self, _path: &Path) -> bool {
        self.deny(UnsupportedReason::AdditionalSourceFile);
        false
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        self.deny(UnsupportedReason::AdditionalSourceFile);
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("external source is disabled: {}", path.display()),
        ))
    }

    #[cfg(rust_item_dependencies_patched)]
    fn read_imported_source_file(&self, path: &Path) -> io::Result<String> {
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("imported source is unavailable: {}", path.display()),
        ))
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        self.deny(UnsupportedReason::ExternalCompileTimeResource);
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("external source is disabled: {}", path.display()),
        ))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        Ok(self.working_directory.clone())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    #[cfg(rust_item_dependencies_patched)]
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::sync::atomic::AtomicBool;
    use std::sync::{Arc, Mutex};

    #[cfg(rust_item_dependencies_patched)]
    use super::FileLoader;
    #[cfg(not(rust_item_dependencies_patched))]
    use super::inspect_source_with_dependencies;
    use super::{
        DenyExternalFiles, DiagnosticState, Edition, InputError, ObservedDiagnostic, SourceInput,
        UnsupportedReason, inspect_source, inspect_source_with_definitions,
        supported_external_crate_name,
    };
    #[cfg(not(rust_item_dependencies_patched))]
    use crate::definitions::DefinitionError;
    use crate::source::{ByteRange, CfgState, PieceKind, WrittenUnitKind};

    const INVENTORY_SOURCE: &str = concat!(
        "\u{feff}// 先頭\r\n",
        "#[allow(dead_code)]\r\n",
        "mod 内 {\r\n",
        "    use crate::{\r\n",
        "        helper as 一, // leaf 一\r\n",
        "        nested::{first, /* 間 */ second},\r\n",
        "    };\r\n",
        "\r\n",
        "    macro_rules! pair { () => { fn a() {} fn b() {} }; }\r\n",
        "    pair!();\r\n",
        "    #[cfg(any())]\r\n",
        "    pair!();\r\n",
        "\r\n",
        "    /// 文書\r\n",
        "    #[inline]\r\n",
        "    fn local() { fn nested_item() {} }\r\n",
        "}\r\n",
        "fn helper() {}\r\n",
        "mod nested { pub fn first() {} pub fn second() {} }\r\n",
        "#[derive(Clone, Copy)]\r\n",
        "struct Stamp;\r\n",
        "fn main() {}\r\n",
        "// 末尾\r\n",
    );

    #[test]
    #[cfg(rust_item_dependencies_patched)]
    fn definition_collection_accepts_resolved_local_and_external_paths() {
        let (sysroot, target) = compiler_context();
        let result = inspect_source_with_definitions(
            &SourceInput::binary(
                include_str!("../tests/fixtures/definitions/path_resolution.rs").to_owned(),
                Edition::Rust2024,
                target,
            ),
            &sysroot,
        );
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    #[cfg(not(rust_item_dependencies_patched))]
    fn definition_collection_requires_import_provenance() {
        let (sysroot, target) = compiler_context();
        let result = inspect_source_with_definitions(
            &SourceInput::binary(
                include_str!("../tests/fixtures/definitions/path_resolution.rs").to_owned(),
                Edition::Rust2024,
                target,
            ),
            &sysroot,
        );
        assert_eq!(
            result,
            Err(InputError::Definition(
                DefinitionError::IncompleteImportDependency
            ))
        );
    }

    #[test]
    #[cfg(not(rust_item_dependencies_patched))]
    fn dependency_collection_fails_without_complete_compiler_observation() {
        let (sysroot, target) = compiler_context();
        let result = inspect_source_with_dependencies(
            &SourceInput::binary("fn main() {}\n".to_owned(), Edition::Rust2024, target),
            &sysroot,
        );
        assert!(
            matches!(result, Err(InputError::Dependency(_))),
            "{result:?}"
        );
    }

    #[test]
    fn inventory_preserves_written_ranges_hierarchy_and_groups() {
        assert_eq!(INVENTORY_SOURCE.len(), 468);
        let inventory = inspect(INVENTORY_SOURCE).unwrap();
        let projection = inventory
            .units
            .iter()
            .map(|unit| {
                (
                    unit.kind,
                    unit.full_range,
                    unit.parent
                        .map(|parent| inventory.units[parent.0 as usize].full_range),
                    unit.cfg_state,
                )
            })
            .collect::<Vec<_>>();

        use CfgState::{Active, Inactive};
        #[cfg(rust_item_dependencies_patched)]
        use WrittenUnitKind::MacroRule;
        use WrittenUnitKind::{
            CrateRoot, InlineModule, Item, MacroDefinition, MacroInvocation, NestedItem, UseItem,
            UseLeaf,
        };
        assert_eq!(
            projection,
            vec![
                (CrateRoot, range(0, 468), None, Active),
                (InlineModule, range(14, 333), Some(range(0, 468)), Active),
                (UseItem, range(50, 150), Some(range(14, 333)), Active),
                (UseLeaf, range(72, 85), Some(range(50, 150)), Active),
                (UseLeaf, range(117, 122), Some(range(50, 150)), Active),
                (UseLeaf, range(134, 140), Some(range(50, 150)), Active),
                (
                    MacroDefinition,
                    range(158, 210),
                    Some(range(14, 333)),
                    Active
                ),
                #[cfg(rust_item_dependencies_patched)]
                (MacroRule, range(178, 208), Some(range(158, 210)), Active),
                (
                    MacroInvocation,
                    range(216, 224),
                    Some(range(14, 333)),
                    Active
                ),
                (
                    MacroInvocation,
                    range(230, 257),
                    Some(range(14, 333)),
                    Inactive
                ),
                (Item, range(265, 330), Some(range(14, 333)), Active),
                (NestedItem, range(309, 328), Some(range(265, 330)), Active),
                (Item, range(335, 349), Some(range(0, 468)), Active),
                (InlineModule, range(351, 402), Some(range(0, 468)), Active),
                (Item, range(364, 381), Some(range(351, 402)), Active),
                (Item, range(382, 400), Some(range(351, 402)), Active),
                (Item, range(404, 441), Some(range(0, 468)), Active),
                (
                    MacroInvocation,
                    range(404, 426),
                    Some(range(404, 441)),
                    Active
                ),
                (Item, range(443, 455), Some(range(0, 468)), Active),
            ]
        );

        let stamp = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == range(404, 441))
            .unwrap();
        let derive = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == range(404, 426))
            .unwrap();
        assert_eq!(stamp.atomic_group, derive.atomic_group);

        let pair_groups = inventory
            .units
            .iter()
            .filter(|unit| {
                matches!(
                    unit.full_range,
                    ByteRange { start: 216, .. } | ByteRange { start: 230, .. }
                )
            })
            .map(|unit| unit.atomic_group)
            .collect::<Vec<_>>();
        assert_eq!(pair_groups.len(), 2);
        assert_ne!(pair_groups[0], pair_groups[1]);

        for comment in [
            range(3, 12),
            range(87, 98),
            range(124, 133),
            range(457, 466),
        ] {
            let piece = inventory
                .pieces
                .iter()
                .find(|piece| piece.range == comment)
                .expect("the comment must have one lexical piece");
            assert_eq!(piece.kind, PieceKind::Trivia);
            assert_ne!(inventory.units[piece.owner.0 as usize].kind, UseLeaf);
        }

        for (piece_range, expected_owner) in [
            (range(0, 3), range(0, 468)),
            (range(3, 12), range(0, 468)),
            (range(72, 78), range(72, 85)),
            (range(85, 86), range(50, 150)),
            (range(87, 98), range(50, 150)),
            (range(124, 133), range(50, 150)),
            (range(404, 405), range(404, 426)),
            (range(426, 428), range(404, 441)),
            (range(428, 434), range(404, 441)),
            (range(457, 466), range(0, 468)),
        ] {
            let piece = inventory
                .pieces
                .iter()
                .find(|piece| piece.range == piece_range)
                .expect("the byte range must have one lexical owner");
            assert_eq!(
                inventory.units[piece.owner.0 as usize].full_range,
                expected_owner
            );
        }

        assert_eq!(inventory, inspect(INVENTORY_SOURCE).unwrap());
    }

    #[test]
    fn inactive_parent_state_propagates_to_every_nested_unit() {
        let source = concat!(
            "#[cfg(any())]\n",
            "mod hidden {\n",
            "    fn child() { fn nested() {} }\n",
            "    mod external;\n",
            "}\n",
            "fn main() {}\n",
        );
        assert_eq!(source.len(), 94);
        let inventory = inspect(source).unwrap();
        use CfgState::{Active, Inactive};
        use WrittenUnitKind::{CrateRoot, InlineModule, Item, NestedItem};
        assert_eq!(
            inventory
                .units
                .iter()
                .map(|unit| {
                    (
                        unit.kind,
                        unit.full_range,
                        unit.parent
                            .map(|parent| inventory.units[parent.0 as usize].full_range),
                        unit.cfg_state,
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                (CrateRoot, range(0, 94), None, Active),
                (InlineModule, range(0, 80), Some(range(0, 94)), Inactive),
                (Item, range(31, 60), Some(range(0, 80)), Inactive),
                (NestedItem, range(44, 58), Some(range(31, 60)), Inactive),
                (Item, range(65, 78), Some(range(0, 80)), Inactive),
                (Item, range(81, 93), Some(range(0, 94)), Active),
            ]
        );
    }

    #[test]
    fn trait_impl_and_body_units_keep_their_exact_parents() {
        let source = concat!(
            "trait Service {\n",
            "    #[cfg(any())]\n",
            "    fn hidden();\n",
            "    fn required();\n",
            "}\n",
            "impl Service for () {\n",
            "    #[cfg(any())]\n",
            "    fn hidden() {}\n",
            "    fn required() { fn local() {} }\n",
            "}\n",
            "fn main() {}\n",
        );
        assert_eq!(source.len(), 182);
        let inventory = inspect(source).unwrap();
        use CfgState::{Active, Inactive};
        use WrittenUnitKind::{CrateRoot, ImplMember, Item, NestedItem, TraitMember};
        assert_eq!(
            inventory
                .units
                .iter()
                .map(|unit| {
                    (
                        unit.kind,
                        unit.full_range,
                        unit.parent
                            .map(|parent| inventory.units[parent.0 as usize].full_range),
                        unit.cfg_state,
                        unit.same_role_ordinal,
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                (CrateRoot, range(0, 182), None, Active, 0),
                (Item, range(0, 71), Some(range(0, 182)), Active, 0),
                (TraitMember, range(20, 50), Some(range(0, 71)), Inactive, 0),
                (TraitMember, range(55, 69), Some(range(0, 71)), Active, 1),
                (Item, range(72, 168), Some(range(0, 182)), Active, 1),
                (
                    ImplMember,
                    range(98, 130),
                    Some(range(72, 168)),
                    Inactive,
                    0
                ),
                (ImplMember, range(135, 166), Some(range(72, 168)), Active, 1),
                (
                    NestedItem,
                    range(151, 164),
                    Some(range(135, 166)),
                    Active,
                    0
                ),
                (Item, range(169, 181), Some(range(0, 182)), Active, 2),
            ]
        );
    }

    #[test]
    fn active_cfg_attr_derive_has_one_written_anchor() {
        let source = concat!(
            "#[cfg_attr(all(), derive(Clone))]\n",
            "struct Active;\n",
            "#[cfg_attr(any(), derive(Clone))]\n",
            "struct Disabled;\n",
            "fn main() {}\n",
        );
        let inventory = inspect(source).unwrap();
        let anchors = inventory
            .units
            .iter()
            .filter(|unit| unit.kind == WrittenUnitKind::MacroInvocation)
            .collect::<Vec<_>>();
        assert_eq!(anchors.len(), 1);
        let expected = "#[cfg_attr(all(), derive(Clone))]";
        assert_eq!(anchors[0].full_range, range(0, expected.len() as u32));
        let target = &inventory.units[anchors[0].parent.unwrap().0 as usize];
        assert_eq!(target.kind, WrittenUnitKind::Item);
        assert_eq!(anchors[0].atomic_group, target.atomic_group);
    }

    #[test]
    fn derive_helper_attributes_are_not_mistaken_for_attribute_macros() {
        let source = concat!(
            "#[cfg_attr(all(), derive(Default))]\n",
            "enum Choice { #[default] First, Second }\n",
            "fn main() { let _ = Choice::default(); }\n",
        );
        assert!(inspect(source).is_ok());
    }

    #[test]
    fn macro_in_active_cfg_attr_value_is_inventoried_once() {
        let source = concat!(
            "#[cfg_attr(all(), doc = concat!(\"hello\", \" world\"))]\n",
            "struct Active;\n",
            "#[cfg_attr(any(), doc = concat!(\"ignored\"))]\n",
            "struct Disabled;\n",
            "fn main() {}\n",
        );
        let inventory = inspect(source).unwrap();
        let macros = inventory
            .units
            .iter()
            .filter(|unit| unit.kind == WrittenUnitKind::MacroInvocation)
            .collect::<Vec<_>>();
        assert_eq!(macros.len(), 1);
        let snippet = "concat!(\"hello\", \" world\")";
        let start = source.find(snippet).unwrap() as u32;
        assert_eq!(
            macros[0].full_range,
            range(start, start + snippet.len() as u32)
        );
        let target = &inventory.units[macros[0].parent.unwrap().0 as usize];
        assert_eq!(target.kind, WrittenUnitKind::Item);
        assert_eq!(macros[0].atomic_group, target.atomic_group);
    }

    #[test]
    fn macro_in_nested_item_cfg_attr_belongs_to_the_nested_item() {
        let source = concat!(
            "fn main() {\n",
            "    #[cfg_attr(all(), doc = concat!(\"nested\"))]\n",
            "    struct Nested;\n",
            "}\n",
        );
        let inventory = inspect(source).unwrap();
        let snippet = "concat!(\"nested\")";
        let start = source.find(snippet).unwrap() as u32;
        let invocation = inventory
            .units
            .iter()
            .find(|unit| {
                unit.kind == WrittenUnitKind::MacroInvocation
                    && unit.full_range == range(start, start + snippet.len() as u32)
            })
            .expect("the attribute macro must be inventoried");
        let parent = &inventory.units[invocation.parent.unwrap().0 as usize];
        assert_eq!(parent.kind, WrittenUnitKind::NestedItem);
        assert_eq!(invocation.atomic_group, parent.atomic_group);
    }

    #[test]
    fn expression_and_statement_macros_share_the_enclosing_item_group() {
        let source = "fn main() {\n    let _ = stringify!(x);\n    println!();\n}\n";
        assert_eq!(source.len(), 57);
        let inventory = inspect(source).unwrap();
        let main = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == range(0, 56))
            .unwrap();
        let macros = inventory
            .units
            .iter()
            .filter(|unit| unit.kind == WrittenUnitKind::MacroInvocation)
            .collect::<Vec<_>>();
        assert_eq!(
            macros
                .iter()
                .map(|unit| (unit.full_range, unit.parent, unit.same_role_ordinal))
                .collect::<Vec<_>>(),
            vec![
                (range(24, 37), Some(main.id), 0),
                (range(43, 54), Some(main.id), 1),
            ]
        );
        assert!(
            macros
                .iter()
                .all(|unit| unit.atomic_group == main.atomic_group)
        );
    }

    #[test]
    fn macro_under_an_inactive_statement_keeps_the_inactive_state() {
        let source = concat!(
            "fn main() {\n",
            "    #[cfg(any())]\n",
            "    let _ = stringify!(x);\n",
            "}\n",
        );
        let inventory = inspect(source).unwrap();
        let snippet = "stringify!(x)";
        let start = source.find(snippet).unwrap() as u32;
        let invocation = inventory
            .units
            .iter()
            .find(|unit| {
                unit.kind == WrittenUnitKind::MacroInvocation
                    && unit.full_range == range(start, start + snippet.len() as u32)
            })
            .expect("the inactive macro must remain in the written inventory");
        assert_eq!(invocation.cfg_state, CfgState::Inactive);
        let parent = &inventory.units[invocation.parent.unwrap().0 as usize];
        assert_eq!(parent.kind, WrittenUnitKind::Item);
        assert_eq!(invocation.atomic_group, parent.atomic_group);
    }

    #[test]
    fn glob_and_self_imports_are_distinct_use_leaves() {
        let source = concat!(
            "mod nested { pub fn first() {} }\n",
            "use crate::nested::{self as alias, *};\n",
            "fn main() { alias::first(); first(); }\n",
        );
        assert_eq!(source.len(), 111);
        let inventory = inspect(source).unwrap();
        let use_item = inventory
            .units
            .iter()
            .find(|unit| unit.full_range == range(33, 71))
            .unwrap();
        let leaves = inventory
            .units
            .iter()
            .filter(|unit| unit.kind == WrittenUnitKind::UseLeaf)
            .collect::<Vec<_>>();
        assert_eq!(
            leaves
                .iter()
                .map(|unit| (unit.full_range, unit.parent, unit.same_role_ordinal))
                .collect::<Vec<_>>(),
            vec![
                (range(53, 66), Some(use_item.id), 0),
                (range(68, 69), Some(use_item.id), 1),
            ]
        );
        assert_ne!(leaves[0].atomic_group, leaves[1].atomic_group);
    }

    #[test]
    fn active_unsupported_inputs_have_typed_reasons_and_original_ranges() {
        assert_unsupported(
            "#![feature(async_await)]\nfn main() {}\n",
            UnsupportedReason::UnstableLanguageFeature,
            "#![feature(async_await)]",
        );
        assert_unsupported(
            "#![cfg_attr(all(), feature(rustc_attrs))]\nfn main() {}\n",
            UnsupportedReason::UnstableLanguageFeature,
            "feature(rustc_attrs)",
        );
        assert_unsupported(
            "fn main() { let _ = try { 1 }; }\n",
            UnsupportedReason::UnstableLanguageFeature,
            "try { 1 }",
        );
        assert_unsupported(
            "#[linkage = \"external\"] static EXTERNAL: i32 = 0;\nfn main() {}\n",
            UnsupportedReason::UnstableLanguageFeature,
            "linkage",
        );
        assert_unsupported(
            "\u{feff}// 注\r\nmod external;\r\nfn main() {}\r\n",
            UnsupportedReason::AdditionalSourceFile,
            "mod external;",
        );
        assert_unsupported(
            "#[path = \"external.rs\"] mod external;\nfn main() {}\n",
            UnsupportedReason::AdditionalSourceFile,
            "#[path = \"external.rs\"]",
        );
        assert_unsupported(
            "#![no_main]\nfn main() {}\n",
            UnsupportedReason::NoStdOrNoMain,
            "#![no_main]",
        );
        assert_unsupported(
            "#![no_std]\nfn main() {}\n",
            UnsupportedReason::NoStdOrNoMain,
            "#![no_std]",
        );
        assert_unsupported(
            "fn main() { unsafe { core::arch::asm!(\"\"); } }\n",
            UnsupportedReason::Assembly,
            "core::arch::asm!(\"\")",
        );
        assert_unsupported(
            "extern crate unavailable;\nfn main() {}\n",
            UnsupportedReason::ExternalDependency,
            "extern crate unavailable;",
        );
        assert_unsupported(
            "extern crate proc_macro;\nfn main() {}\n",
            UnsupportedReason::ProcMacro,
            "extern crate proc_macro;",
        );
        assert_unsupported(
            "#[proc_macro]\npub fn generated() {}\nfn main() {}\n",
            UnsupportedReason::ProcMacro,
            "#[proc_macro]",
        );
        for (source, snippet) in [
            (
                "#![crate_name = \"other\"]\nfn main() {}\n",
                "#![crate_name = \"other\"]",
            ),
            (
                "#![crate_type = \"lib\"]\nfn main() {}\n",
                "#![crate_type = \"lib\"]",
            ),
            ("#![no_builtins]\nfn main() {}\n", "#![no_builtins]"),
            (
                "#[no_link]\nextern crate std;\nfn main() {}\n",
                "#[no_link]",
            ),
            (
                "#![windows_subsystem = \"windows\"]\nfn main() {}\n",
                "#![windows_subsystem = \"windows\"]",
            ),
            (
                "#[link(name = \"native\")] unsafe extern \"C\" { fn foreign(); }\nfn main() {}\n",
                "#[link(name = \"native\")]",
            ),
        ] {
            assert_unsupported(
                source,
                UnsupportedReason::NativeLinkOrCustomRuntime,
                snippet,
            );
        }

        let (sysroot, target) = compiler_context();
        assert_eq!(
            inspect_source(
                &SourceInput::binary(
                    "fn main() {}\n".to_owned(),
                    Edition::Rust2024,
                    "not-a-rust-target".to_owned()
                ),
                &sysroot,
            ),
            Err(InputError::UnsupportedInput {
                reason: UnsupportedReason::UnsupportedTarget,
                range: None,
            })
        );
        assert!(!target.is_empty());
        assert_eq!(
            inspect_source(
                &SourceInput::binary(
                    "fn main() {}\n".to_owned(),
                    Edition::Rust2024,
                    "thumbv7em-none-eabi".to_owned()
                ),
                &sysroot,
            ),
            Err(InputError::UnsupportedInput {
                reason: UnsupportedReason::UnsupportedTarget,
                range: None,
            })
        );
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn resolved_attribute_validation_does_not_reject_permitted_proc_macros() {
        use rustc_middle::ty::MacroImplementationKind;
        use rustc_span::sym;

        assert_eq!(
            super::unsupported_resolved_attribute(
                MacroImplementationKind::Builtin,
                sym::global_allocator,
            ),
            None
        );
        assert_eq!(
            super::unsupported_resolved_attribute(MacroImplementationKind::Builtin, sym::test),
            None
        );
        assert_eq!(
            super::unsupported_resolved_attribute(MacroImplementationKind::Procedural, sym::test,),
            None
        );
        assert!(
            inspect(concat!(
                "use std::prelude::v1::global_allocator as ga;\n",
                "#[ga]\n",
                "static A: std::alloc::System = std::alloc::System;\n",
                "fn main() {}\n",
            ))
            .is_ok()
        );
    }

    #[test]
    fn foreign_items_follow_edition_cfg_and_source_unit_rules() {
        let legacy = "extern \"C\" { fn foreign(); }\nfn main() {}\n";
        for edition in [Edition::Rust2015, Edition::Rust2018, Edition::Rust2021] {
            assert!(inspect_edition(legacy, edition).is_ok(), "{edition:?}");
        }

        let source = concat!(
            "unsafe extern \"C\" {\n",
            "    #[link_name = \"abs\"]\n",
            "    fn renamed(value: core::ffi::c_int) -> core::ffi::c_int;\n",
            "    static FOREIGN: i32;\n",
            "    #[cfg(any())] static INACTIVE: i32;\n",
            "}\n",
            "type Callback = extern \"C\" fn(i32) -> i32;\n",
            "extern \"C\" fn identity(value: i32) -> i32 { value }\n",
            "fn main() { let _: Callback = identity; }\n",
        );
        let inventory = inspect(source).unwrap();
        let foreign_block = inventory
            .units
            .iter()
            .find(|unit| {
                unit.kind == WrittenUnitKind::Item
                    && source[unit.full_range.start as usize..unit.full_range.end as usize]
                        == source[..source.find("\ntype Callback").unwrap()]
            })
            .expect("the foreign block must be an item");
        let expected = [
            (
                "#[link_name = \"abs\"]\n    fn renamed(value: core::ffi::c_int) -> core::ffi::c_int;",
                CfgState::Active,
            ),
            ("static FOREIGN: i32;", CfgState::Active),
            ("#[cfg(any())] static INACTIVE: i32;", CfgState::Inactive),
        ];
        let foreign_items = expected
            .iter()
            .map(|(snippet, state)| {
                let start = source.find(snippet).unwrap() as u32;
                inventory
                    .units
                    .iter()
                    .find(|unit| {
                        unit.kind == WrittenUnitKind::Item
                            && unit.full_range == range(start, start + snippet.len() as u32)
                    })
                    .map(|unit| (unit, state))
                    .expect("every foreign item must have its own source unit")
            })
            .collect::<Vec<_>>();
        for (unit, state) in &foreign_items {
            assert_eq!(unit.parent, Some(foreign_block.id));
            assert_eq!(unit.cfg_state, **state);
        }
        assert_eq!(
            foreign_items
                .iter()
                .map(|(unit, _)| unit.atomic_group)
                .collect::<BTreeSet<_>>()
                .len(),
            foreign_items.len()
        );
    }

    #[test]
    fn a_macro_call_inside_a_foreign_block_is_an_independent_source_unit() {
        let source = concat!(
            "macro_rules! declaration { () => { fn foreign(); } }\n",
            "unsafe extern \"C\" { declaration!(); }\n",
            "fn main() {}\n",
        );
        let inventory = inspect(source).unwrap();
        let snippet = "declaration!();";
        let start = source.find(snippet).unwrap() as u32;
        let invocation = inventory
            .units
            .iter()
            .find(|unit| {
                unit.kind == WrittenUnitKind::MacroInvocation
                    && unit.full_range == range(start, start + snippet.len() as u32)
            })
            .expect("the foreign item macro must have its own source unit");
        let parent = &inventory.units[invocation.parent.unwrap().0 as usize];
        assert_eq!(parent.kind, WrittenUnitKind::Item);
        assert_ne!(invocation.atomic_group, parent.atomic_group);
    }

    #[test]
    fn inactive_and_shadowed_constructs_do_not_trigger_guards() {
        let source = concat!(
            "#![cfg_attr(any(), feature(rustc_attrs))]\n",
            "#[cfg(any())] mod external;\n",
            "#[cfg(any())] #[rust_item_dependencies_unknown_attribute] fn ignored() {}\n",
            "#[cfg(any())] unsafe extern \"C\" { fn foreign(); }\n",
            "#[cfg(any())] const DATA: &str = include_str!(\"missing.txt\");\n",
            "struct Ignored { #[cfg(any())] callback: extern \"C\" fn() }\n",
            "macro_rules! include_str { () => { \"local\" }; }\n",
            "macro_rules! env { () => { \"local\" }; }\n",
            "macro_rules! asm { () => { 1_u8 }; }\n",
            "macro_rules! make_main { () => { fn main() {\n",
            "    let _ = (include_str!(), env!(), asm!());\n",
            "} }; }\n",
            "make_main!();\n",
        );
        let inventory = inspect(source).unwrap();
        assert_eq!(inventory.original.as_ref(), source);
        let inactive_start = source.find("#[cfg(any())] mod external;").unwrap() as u32;
        assert!(inventory.units.iter().any(|unit| {
            unit.cfg_state == CfgState::Inactive
                && unit.full_range
                    == range(
                        inactive_start,
                        inactive_start + "#[cfg(any())] mod external;".len() as u32,
                    )
        }));
    }

    #[test]
    fn stable_sysroot_macros_are_not_rejected_for_internal_expansions() {
        let source = concat!(
            "thread_local! { static CELL: std::cell::Cell<u32> = ",
            "const { std::cell::Cell::new(0) }; }\n",
            "fn main() { let _ = vec![1_u8]; println!(\"{}\", line!()); ",
            "CELL.with(|cell| cell.set(1)); }\n",
        );
        assert!(inspect(source).is_ok());
    }

    #[test]
    fn editions_are_forwarded_to_the_compiler_without_aliasing() {
        let async_name = "fn async() {} fn main() { async(); }\n";
        assert!(inspect_edition(async_name, Edition::Rust2015).is_ok());
        for edition in [Edition::Rust2018, Edition::Rust2021, Edition::Rust2024] {
            assert!(matches!(
                inspect_edition(async_name, edition),
                Err(InputError::OriginalCompilationFailed(_))
            ));
        }

        let array_iteration = "fn main() { [1].into_iter().for_each(|_: &i32| {}); }\n";
        for edition in [Edition::Rust2015, Edition::Rust2018] {
            assert!(inspect_edition(array_iteration, edition).is_ok());
        }
        for edition in [Edition::Rust2021, Edition::Rust2024] {
            assert!(matches!(
                inspect_edition(array_iteration, edition),
                Err(InputError::OriginalCompilationFailed(_))
            ));
        }

        let gen_name = "fn gen() {} fn main() { gen(); }\n";
        for edition in [Edition::Rust2015, Edition::Rust2018, Edition::Rust2021] {
            assert!(inspect_edition(gen_name, edition).is_ok());
        }
        assert!(matches!(
            inspect_edition(gen_name, Edition::Rust2024),
            Err(InputError::OriginalCompilationFailed(_))
        ));
    }

    #[test]
    fn compiler_errors_and_missing_entry_are_not_reported_as_unsupported_syntax() {
        assert!(matches!(
            inspect("fn main() { let _: u8 = \"not a number\"; }\n"),
            Err(InputError::OriginalCompilationFailed(_))
        ));
        assert!(matches!(
            inspect("#[unsafe(no_mangle)] extern \"C\" fn generic<T>() {}\nfn main() {}\n"),
            Err(InputError::OriginalCompilationFailed(_))
        ));
        assert_eq!(
            inspect("fn helper() {}\n"),
            Err(InputError::UnsupportedInput {
                reason: UnsupportedReason::MissingMain,
                range: None,
            })
        );
    }

    #[test]
    fn parser_errors_are_reported_before_inspecting_the_recovery_ast() {
        let source = concat!(
            "macro_rules! array {\n",
            "    ([|$i:pat| $e:expr]) => {};\n",
            "}\n",
            "fn main() {}\n",
        );
        assert!(inspect_edition(source, Edition::Rust2018).is_ok());

        let Err(InputError::OriginalCompilationFailed(diagnostics)) =
            inspect_edition(source, Edition::Rust2024)
        else {
            panic!("the edition error must remain a compiler diagnostic");
        };
        assert!(diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("`$i:pat` is followed by `|`")
                && diagnostic
                    .range
                    .is_some_and(|range| &source[range.start as usize..range.end as usize] == "|")
        }));
    }

    #[test]
    fn file_denials_after_compiler_errors_do_not_mask_the_diagnostic() {
        let diagnostics = Arc::new(Mutex::new(DiagnosticState::default()));
        let denied_file = Arc::new(Mutex::new(None));
        let loader = DenyExternalFiles {
            working_directory: PathBuf::new(),
            denied_file: Arc::clone(&denied_file),
            expansion_complete: Arc::new(AtomicBool::new(false)),
            diagnostics: Arc::clone(&diagnostics),
        };

        loader.deny(UnsupportedReason::AdditionalSourceFile);
        diagnostics
            .lock()
            .expect("diagnostic state mutex is poisoned")
            .errors
            .push(ObservedDiagnostic {
                code: None,
                normalized_range: Some(range(0, 1)),
                compiler_bug: false,
                message: "sentinel compiler error".to_owned(),
            });
        loader.deny(UnsupportedReason::ExternalCompileTimeResource);
        let denied = denied_file
            .lock()
            .expect("denied file mutex is poisoned")
            .expect("a pre-error denial must be preserved");
        assert_eq!(denied.reason, UnsupportedReason::AdditionalSourceFile);
        assert_eq!(denied.diagnostic_index, 0);

        *denied_file.lock().expect("denied file mutex is poisoned") = None;
        loader.deny(UnsupportedReason::AdditionalSourceFile);
        assert!(
            denied_file
                .lock()
                .expect("denied file mutex is poisoned")
                .is_none()
        );
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn in_memory_loader_does_not_classify_imported_source_hydration_as_user_input() {
        let denied_file = Arc::new(Mutex::new(None));
        let loader = DenyExternalFiles {
            working_directory: PathBuf::new(),
            denied_file: Arc::clone(&denied_file),
            expansion_complete: Arc::new(AtomicBool::new(false)),
            diagnostics: Arc::new(Mutex::new(DiagnosticState::default())),
        };

        let error = loader
            .read_imported_source_file(Path::new("dependency.rs"))
            .expect_err("imported source hydration must remain unavailable");

        assert_eq!(error.kind(), std::io::ErrorKind::NotFound);
        assert!(
            denied_file
                .lock()
                .expect("denied file mutex is poisoned")
                .is_none()
        );
    }

    #[test]
    fn unresolved_macro_syntax_is_an_original_compilation_failure() {
        for (source, expected) in [
            (
                "use unavailable::input;\nfn main() { input!(); }\n",
                "unavailable",
            ),
            (
                "#[rust_item_dependencies_unknown_attribute]\nfn main() {}\n",
                "rust_item_dependencies_unknown_attribute",
            ),
        ] {
            let Err(InputError::OriginalCompilationFailed(diagnostics)) =
                inspect_edition(source, Edition::Rust2018)
            else {
                panic!("unresolved macro syntax must remain a compiler diagnostic");
            };
            assert!(diagnostics.iter().any(|diagnostic| {
                diagnostic.range.is_some_and(|range| {
                    &source[range.start as usize..range.end as usize] == expected
                })
            }));
        }
    }

    #[test]
    fn in_memory_source_input_rejects_source_inclusion_at_the_written_site() {
        for (source, snippet) in [
            (
                "fn main() { include!(\"missing-source.rs\"); }\n",
                "include!(\"missing-source.rs\")",
            ),
            (
                concat!(
                    "macro_rules! source { () => { include!(\"missing.rs\"); }; }\n",
                    "source!();\n",
                    "fn main() {}\n",
                ),
                "source!()",
            ),
            (
                concat!(
                    "macro_rules! module { () => { #[path = \"missing.rs\"] mod child; }; }\n",
                    "module!();\n",
                    "fn main() {}\n",
                ),
                "module!()",
            ),
            (
                concat!(
                    "macro_rules! source { () => { ",
                    "include!(\"tests/fixtures/compiler/external_source.rs\"); }; }\n",
                    "source!();\n",
                    "fn main() { marker(); }\n",
                ),
                "source!()",
            ),
            (
                concat!(
                    "macro_rules! module { () => { ",
                    "#[path = \"tests/fixtures/compiler/external_source.rs\"] mod child; }; }\n",
                    "module!();\n",
                    "fn main() { child::marker(); }\n",
                ),
                "module!()",
            ),
        ] {
            assert_unsupported(source, UnsupportedReason::AdditionalSourceFile, snippet);
        }
    }

    #[test]
    fn expanded_assembly_and_native_linkage_are_rejected_at_the_written_invocation() {
        assert_unsupported(
            concat!(
                "macro_rules! assembly { () => { core::arch::global_asm!(\"\"); }; }\n",
                "assembly!();\n",
                "fn main() {}\n",
            ),
            UnsupportedReason::Assembly,
            "assembly!()",
        );
        assert_unsupported(
            concat!(
                "macro_rules! linkage { () => { #[no_link] extern crate std; }; }\n",
                "linkage!();\n",
                "fn main() {}\n",
            ),
            UnsupportedReason::NativeLinkOrCustomRuntime,
            "linkage!()",
        );
    }

    #[test]
    fn generated_external_crate_is_classified_from_the_compiler_diagnostic() {
        for source in [
            concat!(
                "macro_rules! dependency { () => { extern crate unavailable; }; }\n",
                "dependency!();\n",
                "fn main() {}\n",
            ),
            concat!(
                "\u{feff}// 日本語\r\n",
                "macro_rules! dependency { () => { extern crate unavailable; }; }\r\n",
                "dependency!();\r\n",
                "fn main() {}\r\n",
            ),
        ] {
            assert_unsupported(
                source,
                UnsupportedReason::ExternalDependency,
                "dependency!()",
            );
        }
    }

    #[test]
    fn external_crate_allowlist_contains_only_builtins_and_direct_dependencies() {
        let direct = BTreeSet::from(["configured".to_owned()]);

        for name in ["std", "core", "alloc", "self", "configured"] {
            assert!(supported_external_crate_name(name, &direct), "{name}");
        }
        assert!(!supported_external_crate_name("dependency_only", &direct));
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn actual_compile_time_resource_access_is_rejected_at_the_invocation() {
        for (source, snippet) in [
            (
                "fn main() { let _ = include_str!(\"missing-resource.txt\"); }\n",
                "include_str!(\"missing-resource.txt\")",
            ),
            (
                "fn main() { let _ = include_bytes!(\"missing-resource.bin\"); }\n",
                "include_bytes!(\"missing-resource.bin\")",
            ),
            (
                "fn main() { let _ = env!(\"RUST_ITEM_DEPENDENCIES_MISSING_ENV\"); }\n",
                "env!(\"RUST_ITEM_DEPENDENCIES_MISSING_ENV\")",
            ),
            (
                "fn main() { let _ = option_env!(\"RUST_ITEM_DEPENDENCIES_MISSING_ENV\"); }\n",
                "option_env!(\"RUST_ITEM_DEPENDENCIES_MISSING_ENV\")",
            ),
            ("fn main() { let _ = env!(\"PATH\"); }\n", "env!(\"PATH\")"),
            (
                "fn main() { let _ = option_env!(\"PATH\"); }\n",
                "option_env!(\"PATH\")",
            ),
            (
                "\u{feff}// 注\r\nfn main() {\r\n    let _ = include_str!(\"欠.txt\");\r\n}\r\n",
                "include_str!(\"欠.txt\")",
            ),
            (
                concat!(
                    "macro_rules! load { () => { include_str!(\"missing-resource.txt\") }; }\n",
                    "fn main() { let _ = load!(); }\n",
                ),
                "load!()",
            ),
            (
                concat!(
                    "macro_rules! read { () => { env!(\"PATH\") }; }\n",
                    "fn main() { let _ = read!(); }\n",
                ),
                "read!()",
            ),
        ] {
            assert_unsupported(
                source,
                UnsupportedReason::ExternalCompileTimeResource,
                snippet,
            );
        }
    }

    fn range(start: u32, end: u32) -> ByteRange {
        ByteRange { start, end }
    }

    fn assert_unsupported(source: &str, reason: UnsupportedReason, snippet: &str) {
        let start = source
            .find(snippet)
            .expect("the expected source snippet must exist") as u32;
        let expected = ByteRange {
            start,
            end: start + snippet.len() as u32,
        };
        assert_eq!(
            inspect(source),
            Err(InputError::UnsupportedInput {
                reason,
                range: Some(expected),
            })
        );
    }

    fn inspect(source: &str) -> Result<crate::source::SourceInventory, super::InputError> {
        inspect_edition(source, Edition::Rust2024)
    }

    fn inspect_edition(
        source: &str,
        edition: Edition,
    ) -> Result<crate::source::SourceInventory, super::InputError> {
        let (sysroot, target) = compiler_context();
        inspect_source(
            &SourceInput::binary(source.to_owned(), edition, target),
            &sysroot,
        )
    }

    fn compiler_context() -> (PathBuf, String) {
        let rustc = env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC");
        let sysroot = rustc_output(rustc, &["--print", "sysroot"]);
        let version = rustc_output(rustc, &["-Vv"]);
        let target = version
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .expect("rustc -Vv must report a host")
            .to_owned();
        (PathBuf::from(sysroot.trim()), target)
    }

    fn rustc_output(rustc: &str, arguments: &[&str]) -> String {
        let output = Command::new(rustc)
            .args(arguments)
            .output()
            .expect("rustc query must start");
        assert!(output.status.success(), "rustc query failed");
        String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
    }
}

#[cfg(all(test, rust_item_dependencies_patched))]
#[path = "input/dependency_tests.rs"]
mod dependency_tests;

#[cfg(test)]
#[path = "input/retention_tests.rs"]
mod retention_tests;
