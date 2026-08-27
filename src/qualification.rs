//! Probes for validating the pinned compiler integration.
//!
//! These records contain only the facts needed to validate the compiler
//! boundary. They are not stable graph identities or part of the public graph
//! model.

#[cfg(rust_item_dependencies_patched)]
use std::collections::BTreeMap;
#[cfg(any(rust_item_dependencies_patched, test))]
use std::collections::BTreeSet;
#[cfg(rust_item_dependencies_patched)]
use std::collections::HashSet;
use std::io;
use std::path::{Path, PathBuf};
#[cfg(rust_item_dependencies_patched)]
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fingerprint::Fingerprint;
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_driver::{Callbacks, Compilation};
use rustc_feature::UnstableFeatures;
#[cfg(rust_item_dependencies_patched)]
use rustc_hir::HirId;
#[cfg(rust_item_dependencies_patched)]
use rustc_hir::def::DefKind;
use rustc_interface::interface::{Compiler, Config};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::metadata::Reexport;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mir;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mir::interpret::GlobalId;
use rustc_middle::mono::{CollectionMode, MonoItem};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mono::{
    MonoProof, MonoProofUse, MonoSuccessors, MonoTraceCollection, MonoTraceNode, MonoTraceRoot,
    MonoTraceSite, MonoUseCause,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::traits::{CodegenSelectionProof, CodegenSpecializationNode, ImplSource};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::adjustment::PointerCoercion;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{self, TypeVisitableExt, Unnormalized};
use rustc_middle::ty::{Instance, TyCtxt};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::Span;
#[cfg(rust_item_dependencies_patched)]
use rustc_span::def_id::LocalDefId;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::hygiene::ExpnId;
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::ExpnKind;
use rustc_span::source_map::FileLoader;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProbeConfig {
    pub sysroot: PathBuf,
    pub target: String,
    pub edition: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionProbe {
    pub path: String,
    pub kind: String,
    pub expansion: Option<ExpansionProbe>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpansionProbe {
    pub kind: String,
    pub macro_definition: Option<String>,
    pub call_site: (u32, u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonoChildProbe {
    pub collection: ProbeCollection,
    pub kind: String,
    pub definition: String,
    pub instance: Option<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LocalProofDefinitionProbe {
    pub path: String,
    pub source_range: (u32, u32),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoProofOriginProbe {
    CompilerObservation,
    SupertraitConstraint,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoUseCauseProbe {
    DirectCall,
    FunctionPointer,
    ClosureFunctionPointer,
    InlineAsmSymbol,
    StaticReference,
    ThreadLocalReference,
    DropGlue,
    VTableConstruction,
    VTableMethod,
    VTableDrop,
    SupertraitVTable,
    ConstAllocation,
    AllocationReference,
    ThreadLocalShim,
    CompilerRequirement,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoSiteProbe {
    Source((u32, u32)),
    ExternalSource(String),
    AllocationOffset(u64),
    VTableSlot(u64),
    CompilerGenerated,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MonoNodeProbe {
    pub kind: String,
    pub definition: Option<String>,
    pub instance: Option<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoProofKindProbe {
    TraitSelection {
        trait_definition: String,
        arguments: Vec<String>,
    },
    AssociatedItem {
        item: String,
        arguments: Vec<String>,
        raw_instance: String,
        codegen_instance: String,
    },
    Projection {
        item: String,
        arguments: Vec<String>,
        expected: String,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MonoProofProbe {
    pub origin: MonoProofOriginProbe,
    pub from: MonoNodeProbe,
    pub kind: MonoProofKindProbe,
    pub cause: MonoUseCauseProbe,
    pub collection: ProbeCollection,
    pub site: MonoSiteProbe,
    pub local_impls: Vec<LocalProofDefinitionProbe>,
    pub local_leaves: Vec<LocalProofDefinitionProbe>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ConstIdentityProbe {
    pub definition: String,
    pub arguments: Vec<String>,
    pub instance: String,
    pub promoted: Option<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RequiredConstUseProbe {
    pub owner: String,
    pub request_definition: String,
    pub request_arguments: Vec<String>,
    pub target: ConstIdentityProbe,
    pub collection: ProbeCollection,
    pub site: MonoSiteProbe,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ConstTraitFunctionUseProbe {
    pub body: ConstIdentityProbe,
    pub item: String,
    pub arguments: Vec<String>,
    pub raw_instance: String,
    pub codegen_instance: String,
    pub collection: ProbeCollection,
    pub site: MonoSiteProbe,
    pub local_impls: Vec<LocalProofDefinitionProbe>,
    pub local_leaves: Vec<LocalProofDefinitionProbe>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedImportUseProbe {
    pub owner: String,
    pub path_range: (u32, u32),
    pub segment_range: (u32, u32),
    pub namespace: String,
    pub target: String,
    pub import_chain: Vec<ResolvedImportStepProbe>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ResolvedImportStepProbe {
    pub kind: ImportKindProbe,
    pub definition: Option<String>,
    pub source_range: Option<(u32, u32)>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ImportKindProbe {
    Single,
    Glob,
    ExternCrate,
    MacroUse,
    MacroExport,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelectedTraitImportProbe {
    pub owner: String,
    pub site_range: (u32, u32),
    pub selected_item: String,
    pub import_chain: Vec<ImportLeafProbe>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypeckImplDependencyProbe {
    pub source_owner: String,
    pub source_range: (u32, u32),
    pub implementation: String,
    pub associated_item: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExpansionKeyProbe(pub u64);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExpansionKindProbe {
    Macro(String),
    AstPass(String),
    Desugaring(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MacroInvocationProbe {
    pub expansion: ExpansionKeyProbe,
    /// Expansion containing the AST fragment in which this invocation was discovered.
    pub discovered_in: Option<ExpansionKeyProbe>,
    pub discovered_in_kind: Option<ExpansionKindProbe>,
    /// Semantic expansion parent from stock `ExpnData`.
    pub parent: Option<ExpansionKeyProbe>,
    /// Expansion context carried by stock `ExpnData::call_site`.
    pub source_call_parent: Option<ExpansionKeyProbe>,
    pub kind: String,
    pub fragment_kind: String,
    pub implementation_kind: String,
    pub macro_definition: Option<String>,
    /// Present only for an invocation written directly in `main.rs`.
    pub written_invocation_range: Option<(u32, u32)>,
    /// Exact written AST node, including a trailing semicolon when present.
    /// Outer attributes and comments belong to the source inventory rather than this record.
    pub written_node_range: Option<(u32, u32)>,
    /// Raw node range when its span points into logical `main.rs`, including forwarded tokens.
    pub source_node_range: Option<(u32, u32)>,
    /// Attribute or derive target written in `main.rs`.
    pub written_target_range: Option<(u32, u32)>,
    /// Local definitions directly generated by this expansion.
    pub generated_definitions: Vec<String>,
    /// Final local import/re-export paths selected for this invocation.
    pub resolved_import_uses: Vec<MacroResolvedImportUseProbe>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MacroResolvedImportUseProbe {
    pub path_range: Option<(u32, u32)>,
    pub segment_range: Option<(u32, u32)>,
    pub namespace: String,
    pub target: String,
    pub import_chain: Vec<ResolvedImportStepProbe>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ImportLeafProbe {
    pub definition: String,
    pub source_range: (u32, u32),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProbeCollection {
    Used,
    Mentioned,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QualificationReport {
    pub entry_definition: String,
    pub definitions: Vec<DefinitionProbe>,
    pub main_children: Vec<MonoChildProbe>,
    pub mono_proofs: Vec<MonoProofProbe>,
    pub required_const_uses: Vec<RequiredConstUseProbe>,
    pub const_trait_function_uses: Vec<ConstTraitFunctionUseProbe>,
    pub resolved_import_uses: Vec<ResolvedImportUseProbe>,
    pub selected_trait_imports: Vec<SelectedTraitImportProbe>,
    pub typeck_impl_dependencies: Vec<TypeckImplDependencyProbe>,
    pub macro_invocations: Vec<MacroInvocationProbe>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProbeError {
    CompilationDidNotReachAnalysis,
    CompilationDidNotComplete,
    ExternalSourceAccess(Vec<PathBuf>),
    ExternalResourceAccess(Vec<DeniedResourceProbe>),
    MissingEntryPoint,
    MonoCollectionFailed,
    MonoObservationIncomplete,
    MonoObservationCacheMismatch,
    MonoProofIncomplete,
    MonoProofCacheMismatch,
    MonoProofConflict,
    RequiredConstTraversalIncomplete,
    RequiredConstCycle,
    ImportProvenanceIncomplete,
    ImportProvenanceCacheMismatch,
    TypeckImplDependenciesIncomplete,
    ExpansionOriginIncomplete,
    ExpansionOriginCacheMismatch,
    MacroImportProvenanceIncomplete,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeniedResourceProbe {
    Environment,
    OptionalEnvironment,
}

/// Runs the pinned compiler over one in-memory `main.rs`.
///
/// Compilation stops after analysis because none of the inspected facts require code generation.
/// Display strings are suitable for qualification assertions, not as stable graph identities.
pub fn probe_source(source: &str, probe: &ProbeConfig) -> Result<QualificationReport, ProbeError> {
    let result = Arc::new(Mutex::new(None));
    let denied_source_paths = Arc::new(Mutex::new(Vec::new()));
    #[cfg(rust_item_dependencies_patched)]
    let denied_resources = Arc::new(Mutex::new(Vec::new()));
    let mut callbacks = ProbeCallbacks {
        source: Arc::<str>::from(source),
        working_directory: std::env::current_dir()
            .expect("compiler qualification requires a current directory"),
        denied_source_paths: Arc::clone(&denied_source_paths),
        #[cfg(rust_item_dependencies_patched)]
        denied_resources: Arc::clone(&denied_resources),
        result: Arc::clone(&result),
        continue_after_analysis: false,
        #[cfg(rust_item_dependencies_patched)]
        require_cached_typeck_root: false,
    };

    let args = probe_arguments(probe);

    let _compiler_status =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callbacks));

    let compiler_result = result
        .lock()
        .expect("qualification result mutex is poisoned")
        .take();
    if let Some(compiler_result) = compiler_result {
        return compiler_result;
    }

    let mut denied_source_paths = denied_source_paths
        .lock()
        .expect("denied source path mutex is poisoned")
        .clone();
    denied_source_paths.sort();
    denied_source_paths.dedup();
    if denied_source_paths.is_empty() {
        #[cfg(rust_item_dependencies_patched)]
        {
            let mut denied_resources = denied_resources
                .lock()
                .expect("denied resource mutex is poisoned")
                .clone();
            denied_resources.sort();
            denied_resources.dedup();
            if !denied_resources.is_empty() {
                return Err(ProbeError::ExternalResourceAccess(denied_resources));
            }
        }
        return Err(ProbeError::CompilationDidNotReachAnalysis);
    }

    Err(ProbeError::ExternalSourceAccess(denied_source_paths))
}

fn probe_arguments(probe: &ProbeConfig) -> Vec<String> {
    vec![
        "rust-item-dependencies-compiler-qualification".to_owned(),
        "main.rs".to_owned(),
        "--crate-name=rust_item_dependencies_compiler_qualification".to_owned(),
        "--crate-type=bin".to_owned(),
        format!("--edition={}", probe.edition),
        format!("--target={}", probe.target),
        "--sysroot".to_owned(),
        probe.sysroot.to_string_lossy().into_owned(),
        "--emit=metadata=-".to_owned(),
    ]
}

struct ProbeCallbacks {
    source: Arc<str>,
    working_directory: PathBuf,
    denied_source_paths: Arc<Mutex<Vec<PathBuf>>>,
    #[cfg(rust_item_dependencies_patched)]
    denied_resources: Arc<Mutex<Vec<DeniedResourceProbe>>>,
    result: Arc<Mutex<Option<Result<QualificationReport, ProbeError>>>>,
    continue_after_analysis: bool,
    #[cfg(rust_item_dependencies_patched)]
    require_cached_typeck_root: bool,
}

impl Callbacks for ProbeCallbacks {
    fn config(&mut self, config: &mut Config) {
        // The analyzer runs on nightly, but accepted user input is stable-only.
        // Force feature gating independently of the tool process environment.
        config.opts.unstable_features = UnstableFeatures::Disallow;
        config.file_loader = Some(Box::new(SingleSourceLoader {
            source: Arc::clone(&self.source),
            working_directory: self.working_directory.clone(),
            denied_source_paths: Arc::clone(&self.denied_source_paths),
        }));

        #[cfg(rust_item_dependencies_patched)]
        if self.require_cached_typeck_root {
            config.override_queries = Some(|_, providers| {
                providers.queries.typeck_root = cached_typeck_root_only;
            });
        }

        #[cfg(rust_item_dependencies_patched)]
        {
            let denied_resources = Arc::clone(&self.denied_resources);
            config.external_resource_guard = Some(rustc_driver::ExternalResourceGuard::new(
                move |resource_use| {
                    let kind = match resource_use.kind {
                        rustc_driver::ExternalResourceKind::Environment => {
                            DeniedResourceProbe::Environment
                        }
                        rustc_driver::ExternalResourceKind::OptionalEnvironment => {
                            DeniedResourceProbe::OptionalEnvironment
                        }
                    };
                    denied_resources
                        .lock()
                        .expect("denied resource mutex is poisoned")
                        .push(kind);
                },
            ));
        }
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        *self
            .result
            .lock()
            .expect("qualification result mutex is poisoned") = Some(collect_report(tcx));
        if self.continue_after_analysis {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

#[cfg(rust_item_dependencies_patched)]
fn cached_typeck_root_only<'tcx>(
    _tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
) -> &'tcx rustc_middle::ty::TypeckResults<'tcx> {
    panic!("typeck_root({definition:?}) was recomputed instead of restored from disk cache")
}

/// Verifies that type-checking observations survive rustc's on-disk query cache.
/// This validates the compiler boundary and is not part of the graph API.
#[doc(hidden)]
#[cfg(rust_item_dependencies_patched)]
pub fn probe_incremental_import_cache(
    source: &str,
    probe: &ProbeConfig,
) -> Result<(QualificationReport, QualificationReport), ProbeError> {
    let temporary_directory = QualificationTempDirectory::create();
    let output = temporary_directory.path().join("fixture.rmeta");

    let seed = run_incremental_import_probe(
        source,
        probe,
        temporary_directory.path(),
        &output,
        "not-loaded",
        false,
    )?;
    let loaded = run_incremental_import_probe(
        source,
        probe,
        temporary_directory.path(),
        &output,
        "loaded",
        true,
    )?;

    Ok((seed, loaded))
}

#[cfg(rust_item_dependencies_patched)]
fn run_incremental_import_probe(
    source: &str,
    probe: &ProbeConfig,
    incremental_directory: &Path,
    output: &Path,
    expected_incremental_state: &str,
    require_cached_typeck_root: bool,
) -> Result<QualificationReport, ProbeError> {
    let result = Arc::new(Mutex::new(None));
    let denied_source_paths = Arc::new(Mutex::new(Vec::new()));
    let denied_resources = Arc::new(Mutex::new(Vec::new()));
    let mut callbacks = ProbeCallbacks {
        source: Arc::<str>::from(source),
        working_directory: std::env::current_dir()
            .expect("compiler qualification requires a current directory"),
        denied_source_paths: Arc::clone(&denied_source_paths),
        denied_resources: Arc::clone(&denied_resources),
        result: Arc::clone(&result),
        continue_after_analysis: true,
        require_cached_typeck_root,
    };
    let mut args = probe_arguments(probe);
    args.extend([
        format!("-Cincremental={}", incremental_directory.display()),
        format!("-Zassert-incr-state={expected_incremental_state}"),
        "-Zincremental-verify-ich".to_owned(),
        "-o".to_owned(),
        output.to_string_lossy().into_owned(),
    ]);

    let compiler_status =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callbacks));
    if compiler_status.is_err() {
        return Err(ProbeError::CompilationDidNotComplete);
    }

    result
        .lock()
        .expect("qualification result mutex is poisoned")
        .take()
        .ok_or(ProbeError::CompilationDidNotReachAnalysis)?
}

#[cfg(rust_item_dependencies_patched)]
struct QualificationTempDirectory(PathBuf);

#[cfg(rust_item_dependencies_patched)]
impl QualificationTempDirectory {
    fn create() -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);

        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "rust-item-dependencies-compiler-qualification-{}-{id}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap_or_else(|error| {
            panic!(
                "cannot create compiler qualification directory {}: {error}",
                path.display()
            )
        });
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

#[cfg(rust_item_dependencies_patched)]
impl Drop for QualificationTempDirectory {
    fn drop(&mut self) {
        if let Err(error) = std::fs::remove_dir_all(&self.0) {
            eprintln!(
                "cannot remove compiler qualification directory {}: {error}",
                self.0.display()
            );
        }
    }
}

fn collect_report(tcx: TyCtxt<'_>) -> Result<QualificationReport, ProbeError> {
    let (entry_definition, _) = tcx.entry_fn(()).ok_or(ProbeError::MissingEntryPoint)?;

    let mut definitions = tcx
        .iter_local_def_id()
        .map(|definition| {
            let expansion_id = tcx.expn_that_defined(definition.to_def_id());
            let expansion = (expansion_id != ExpnId::root()).then(|| {
                let data = expansion_id.expn_data();
                ExpansionProbe {
                    kind: data.kind.descr(),
                    macro_definition: data.macro_def_id.map(|id| display_def_path(tcx, id)),
                    call_site: (data.call_site.lo().0, data.call_site.hi().0),
                }
            });

            DefinitionProbe {
                path: display_def_path(tcx, definition.to_def_id()),
                kind: format!("{:?}", tcx.def_kind(definition)),
                expansion,
            }
        })
        .collect::<Vec<_>>();
    definitions.sort_by(|left, right| left.path.cmp(&right.path).then(left.kind.cmp(&right.kind)));

    let main_instance = Instance::mono(tcx, entry_definition);
    let (used, mentioned) = tcx
        .items_of_instance((main_instance, CollectionMode::UsedItems))
        .map_err(|_| ProbeError::MonoCollectionFailed)?;

    let mut main_children = used
        .iter()
        .map(|item| mono_child(tcx, ProbeCollection::Used, item.node))
        .chain(
            mentioned
                .iter()
                .map(|item| mono_child(tcx, ProbeCollection::Mentioned, item.node)),
        )
        .collect::<Vec<_>>();
    main_children.sort_by(|left, right| {
        left.definition
            .cmp(&right.definition)
            .then(left.kind.cmp(&right.kind))
            .then(left.instance.cmp(&right.instance))
            .then((left.collection as u8).cmp(&(right.collection as u8)))
    });

    #[cfg(rust_item_dependencies_patched)]
    let (mono_proofs, required_const_uses, const_trait_function_uses) = {
        let (cold_proofs, cold_consts, cold_functions) =
            collect_mono_qualification(tcx, main_instance)?;
        let (warm_proofs, warm_consts, warm_functions) =
            collect_mono_qualification(tcx, main_instance)?;
        if cold_proofs != warm_proofs {
            return Err(ProbeError::MonoProofCacheMismatch);
        }
        if cold_consts != warm_consts || cold_functions != warm_functions {
            return Err(ProbeError::MonoObservationCacheMismatch);
        }
        (cold_proofs, cold_consts, cold_functions)
    };
    #[cfg(not(rust_item_dependencies_patched))]
    let (mono_proofs, required_const_uses, const_trait_function_uses) =
        (Vec::new(), Vec::new(), Vec::new());

    let import_provenance = collect_import_provenance(tcx)?;
    #[cfg(rust_item_dependencies_patched)]
    {
        let memory_warm = collect_import_provenance(tcx)?;
        if import_provenance != memory_warm {
            return Err(ProbeError::ImportProvenanceCacheMismatch);
        }
    }
    let (resolved_import_uses, selected_trait_imports) = import_provenance;
    #[cfg(rust_item_dependencies_patched)]
    let typeck_impl_dependencies = collect_typeck_impl_dependencies(tcx)?;
    #[cfg(not(rust_item_dependencies_patched))]
    let typeck_impl_dependencies = Vec::new();
    let macro_invocations = collect_macro_invocations(tcx)?;
    #[cfg(rust_item_dependencies_patched)]
    if macro_invocations != collect_macro_invocations(tcx)? {
        return Err(ProbeError::ExpansionOriginCacheMismatch);
    }

    Ok(QualificationReport {
        entry_definition: display_def_path(tcx, entry_definition),
        definitions,
        main_children,
        mono_proofs,
        required_const_uses,
        const_trait_function_uses,
        resolved_import_uses,
        selected_trait_imports,
        typeck_impl_dependencies,
        macro_invocations,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn collect_mono_qualification<'tcx>(
    tcx: TyCtxt<'tcx>,
    entry: Instance<'tcx>,
) -> Result<
    (
        Vec<MonoProofProbe>,
        Vec<RequiredConstUseProbe>,
        Vec<ConstTraitFunctionUseProbe>,
    ),
    ProbeError,
> {
    let mut collector = MonoQualificationCollector {
        tcx,
        mono_active: HashSet::new(),
        mono_done: HashSet::new(),
        const_active: HashSet::new(),
        const_done: HashSet::new(),
        supertrait_active: Vec::new(),
        mono_proofs: Vec::new(),
        required_const_uses: Vec::new(),
        const_trait_function_uses: Vec::new(),
    };
    collector.visit_mono(MonoTraceRoot::Fn(entry), CollectionMode::UsedItems)?;
    for item_id in tcx.hir_free_items() {
        if tcx.def_kind(item_id.owner_id) == DefKind::GlobalAsm {
            let item = tcx.hir_item(item_id);
            collector.visit_mono(
                MonoTraceRoot::GlobalAsm {
                    item_id,
                    trigger_span: item.span,
                },
                CollectionMode::UsedItems,
            )?;
        }
    }
    Ok((
        collector.mono_proofs,
        collector.required_const_uses,
        collector.const_trait_function_uses,
    ))
}

#[cfg(rust_item_dependencies_patched)]
struct MonoQualificationCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    mono_active: HashSet<(MonoTraceRoot<'tcx>, CollectionMode)>,
    mono_done: HashSet<(MonoTraceRoot<'tcx>, CollectionMode)>,
    const_active: HashSet<(GlobalId<'tcx>, CollectionMode)>,
    const_done: HashSet<(GlobalId<'tcx>, CollectionMode)>,
    supertrait_active: Vec<ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>>,
    mono_proofs: Vec<MonoProofProbe>,
    required_const_uses: Vec<RequiredConstUseProbe>,
    const_trait_function_uses: Vec<ConstTraitFunctionUseProbe>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct RequiredConstTarget<'tcx> {
    global_id: GlobalId<'tcx>,
    site: Span,
    associated_key: Option<ty::PseudoCanonicalInput<'tcx, (DefId, ty::GenericArgsRef<'tcx>)>>,
}

#[cfg(rust_item_dependencies_patched)]
impl<'tcx> MonoQualificationCollector<'tcx> {
    fn visit_mono(
        &mut self,
        root: MonoTraceRoot<'tcx>,
        mode: CollectionMode,
    ) -> Result<(), ProbeError> {
        let visit_key = (root, mode);
        if self.mono_done.contains(&visit_key) || !self.mono_active.insert(visit_key) {
            return Ok(());
        }

        let successors = self
            .tcx
            .mono_successors(visit_key)
            .map_err(|_| ProbeError::MonoCollectionFailed)?;
        let warm = self
            .tcx
            .mono_successors(visit_key)
            .map_err(|_| ProbeError::MonoCollectionFailed)?;
        if !std::ptr::eq(successors, warm) {
            return Err(ProbeError::MonoObservationCacheMismatch);
        }
        self.validate_stock_endpoints(root, mode, successors)?;

        for proof in successors
            .proof_uses
            .iter()
            .filter(|proof| proof.collection == MonoTraceCollection::Used)
        {
            self.record_mono_proof(*proof)?;
        }
        for item in successors.used {
            self.visit_mono_item(item.node, item.span, CollectionMode::UsedItems)?;
        }

        let (owner, instance_and_body) = match root {
            MonoTraceRoot::Fn(instance) => (
                MonoTraceNode::Item(MonoItem::Fn(instance)),
                Some((instance, self.tcx.instance_mir(instance.def))),
            ),
            MonoTraceRoot::Static { def_id, .. } => {
                let instance = Instance::mono(self.tcx, def_id);
                (
                    MonoTraceNode::Item(MonoItem::Static(def_id)),
                    Some((instance, self.tcx.instance_mir(instance.def))),
                )
            }
            MonoTraceRoot::GlobalAsm { item_id, .. } => {
                (MonoTraceNode::Item(MonoItem::GlobalAsm(item_id)), None)
            }
        };
        let collection = probe_collection_for_mode(mode);
        let targets = instance_and_body.map_or(Ok(Vec::new()), |(instance, body)| {
            self.required_const_targets(&format!("{owner:?}"), instance, body, collection)
        })?;
        self.validate_associated_const_observations(owner, successors, &targets)?;
        for target in targets {
            self.visit_const(target.global_id, mode)?;
        }

        for proof in successors
            .proof_uses
            .iter()
            .filter(|proof| proof.collection == MonoTraceCollection::Mentioned)
        {
            self.record_mono_proof(*proof)?;
        }
        for item in successors.mentioned {
            self.visit_mono_item(item.node, item.span, CollectionMode::MentionedItems)?;
        }

        self.mono_active.remove(&visit_key);
        self.mono_done.insert(visit_key);
        Ok(())
    }

    fn visit_mono_item(
        &mut self,
        item: MonoItem<'tcx>,
        span: Span,
        mode: CollectionMode,
    ) -> Result<(), ProbeError> {
        match item {
            MonoItem::Fn(instance) => self.visit_mono(MonoTraceRoot::Fn(instance), mode),
            MonoItem::Static(def_id) => self.visit_mono(
                MonoTraceRoot::Static {
                    def_id,
                    trigger_span: span,
                },
                mode,
            ),
            MonoItem::GlobalAsm(item_id) => self.visit_mono(
                MonoTraceRoot::GlobalAsm {
                    item_id,
                    trigger_span: span,
                },
                mode,
            ),
        }
    }

    fn validate_stock_endpoints(
        &self,
        root: MonoTraceRoot<'tcx>,
        mode: CollectionMode,
        successors: &MonoSuccessors<'tcx>,
    ) -> Result<(), ProbeError> {
        let MonoTraceRoot::Fn(instance) = root else {
            return Ok(());
        };
        let (used, mentioned) = self
            .tcx
            .items_of_instance((instance, mode))
            .map_err(|_| ProbeError::MonoCollectionFailed)?;
        if successors.used != used || successors.mentioned != mentioned {
            return Err(ProbeError::MonoObservationIncomplete);
        }
        Ok(())
    }
}

#[cfg(rust_item_dependencies_patched)]
impl<'tcx> MonoQualificationCollector<'tcx> {
    fn record_mono_proof(&mut self, proof_use: MonoProofUse<'tcx>) -> Result<(), ProbeError> {
        let from = mono_node(self.tcx, proof_use.from);
        let cause = mono_cause(proof_use.cause);
        let collection = mono_collection(proof_use.collection);
        let site = mono_site(self.tcx, proof_use.site)?;

        match proof_use.proof {
            MonoProof::TraitSelection { proof_key } => {
                if !matches!(
                    proof_use.cause,
                    MonoUseCause::VTableConstruction | MonoUseCause::SupertraitVTable
                ) || (proof_use.cause == MonoUseCause::SupertraitVTable
                    && (!matches!(proof_use.from, MonoTraceNode::VTable { .. })
                        || !matches!(proof_use.site, MonoTraceSite::VTableSlot(_))))
                {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                let selection = self.checked_selection_proof(proof_key)?;
                let (local_impls, local_leaves) =
                    selection_local_dependencies(self.tcx, selection)?;
                self.insert_mono_proof(MonoProofProbe {
                    origin: MonoProofOriginProbe::CompilerObservation,
                    from: from.clone(),
                    kind: MonoProofKindProbe::TraitSelection {
                        trait_definition: display_def_path(self.tcx, proof_key.value.def_id),
                        arguments: generic_arguments(proof_key.value.args),
                    },
                    cause,
                    collection,
                    site: site.clone(),
                    local_impls,
                    local_leaves,
                })?;
                if proof_use.cause == MonoUseCause::VTableConstruction {
                    self.record_supertrait_proofs(proof_key, from, cause, collection, site)?;
                }
            }
            MonoProof::AssociatedItem {
                selection_key,
                request,
                raw_instance,
                codegen_instance,
            } => {
                let (expected_key, selection, expected_raw) =
                    self.checked_associated_request(request)?;
                if selection_key != expected_key || raw_instance != expected_raw {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                self.validate_codegen_instance(proof_use, request, raw_instance, codegen_instance)?;
                let (mut local_impls, mut local_leaves) =
                    selection_local_dependencies(self.tcx, selection)?;
                self.extend_associated_dependencies(
                    request,
                    selection,
                    raw_instance,
                    &mut local_impls,
                    &mut local_leaves,
                )?;
                local_impls.sort();
                local_impls.dedup();
                local_leaves.sort();
                local_leaves.dedup();
                self.insert_mono_proof(MonoProofProbe {
                    origin: MonoProofOriginProbe::CompilerObservation,
                    from: from.clone(),
                    kind: MonoProofKindProbe::AssociatedItem {
                        item: display_def_path(self.tcx, request.value.0),
                        arguments: generic_arguments(request.value.1),
                        raw_instance: format!("{raw_instance:?}"),
                        codegen_instance: format!("{codegen_instance:?}"),
                    },
                    cause,
                    collection,
                    site: site.clone(),
                    local_impls,
                    local_leaves,
                })?;
                self.record_supertrait_proofs(selection_key, from, cause, collection, site)?;
            }
            MonoProof::Projection {
                proof_key,
                expected,
            } => {
                if proof_use.cause != MonoUseCause::VTableConstruction
                    || !matches!(proof_key.value.kind, ty::AliasTermKind::ProjectionTy { .. })
                    || proof_key.value.args.type_at(0).has_non_region_param()
                {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                let projection = self.checked_projection_proof(proof_key)?;
                if projection.normalized_term != expected {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                let (local_impls, local_leaves) =
                    trace_local_dependencies(self.tcx, &projection.trace)?;
                let item = match proof_key.value.kind {
                    ty::AliasTermKind::ProjectionTy { def_id } => def_id,
                    _ => return Err(ProbeError::MonoProofIncomplete),
                };
                self.insert_mono_proof(MonoProofProbe {
                    origin: MonoProofOriginProbe::CompilerObservation,
                    from,
                    kind: MonoProofKindProbe::Projection {
                        item: display_def_path(self.tcx, item),
                        arguments: generic_arguments(proof_key.value.args),
                        expected: format!("{expected:?}"),
                    },
                    cause,
                    collection,
                    site,
                    local_impls,
                    local_leaves,
                })?;
            }
        }
        Ok(())
    }

    fn checked_associated_request(
        &self,
        request: ty::PseudoCanonicalInput<'tcx, (DefId, ty::GenericArgsRef<'tcx>)>,
    ) -> Result<
        (
            ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
            &'tcx CodegenSelectionProof<'tcx>,
            Instance<'tcx>,
        ),
        ProbeError,
    > {
        if request.typing_env != ty::TypingEnv::fully_monomorphized()
            || !matches!(
                self.tcx.def_kind(request.value.0),
                DefKind::AssocFn | DefKind::AssocConst { .. }
            )
            || request.value.1.has_non_region_param()
            || request.value.1.has_non_region_infer()
        {
            return Err(ProbeError::MonoProofIncomplete);
        }
        let trait_id = self
            .tcx
            .trait_of_assoc(request.value.0)
            .ok_or(ProbeError::MonoProofIncomplete)?;
        let receiver_arguments = self
            .tcx
            .try_normalize_erasing_regions(
                request.typing_env,
                Unnormalized::new_wip(request.value.1),
            )
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        let selection_key = request.typing_env.as_query_input(ty::TraitRef::from_assoc(
            self.tcx,
            trait_id,
            receiver_arguments,
        ));
        let selection = self.checked_selection_proof(selection_key)?;
        let raw_instance = self
            .tcx
            .resolve_instance_raw(request)
            .map_err(|_| ProbeError::MonoProofIncomplete)?
            .ok_or(ProbeError::MonoProofIncomplete)?;
        Ok((selection_key, selection, raw_instance))
    }

    fn extend_associated_dependencies(
        &self,
        request: ty::PseudoCanonicalInput<'tcx, (DefId, ty::GenericArgsRef<'tcx>)>,
        selection: &CodegenSelectionProof<'tcx>,
        raw_instance: Instance<'tcx>,
        implementations: &mut Vec<LocalProofDefinitionProbe>,
        leaves: &mut Vec<LocalProofDefinitionProbe>,
    ) -> Result<(), ProbeError> {
        match &selection.top_source {
            ImplSource::UserDefined(_) => {
                let proof = self.checked_associated_item_proof(request)?;
                let (selection_key, _, _) = self.checked_associated_request(request)?;
                if proof.selection_key != selection_key
                    || proof.source != selection.top_source
                    || proof.final_instance != raw_instance
                {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                if let Some(leaf) = local_proof_definition(self.tcx, proof.leaf_item)? {
                    leaves.push(leaf);
                }
                for node in &proof.ancestor_path {
                    if let CodegenSpecializationNode::Impl(definition) = *node
                        && let Some(implementation) = local_proof_definition(self.tcx, definition)?
                    {
                        implementations.push(implementation);
                    }
                }
            }
            ImplSource::Builtin(..) | ImplSource::Param(_) => {
                if self.tcx.codegen_associated_item_proof(request).is_ok() {
                    return Err(ProbeError::MonoProofIncomplete);
                }
            }
        }
        Ok(())
    }

    fn validate_codegen_instance(
        &self,
        proof_use: MonoProofUse<'tcx>,
        request: ty::PseudoCanonicalInput<'tcx, (DefId, ty::GenericArgsRef<'tcx>)>,
        raw_instance: Instance<'tcx>,
        codegen_instance: Instance<'tcx>,
    ) -> Result<(), ProbeError> {
        match proof_use.cause {
            MonoUseCause::DirectCall if codegen_instance == raw_instance => Ok(()),
            MonoUseCause::FunctionPointer | MonoUseCause::InlineAsmSymbol => {
                let expected = if proof_use.collection == MonoTraceCollection::Used {
                    Instance::resolve_for_fn_ptr(
                        self.tcx,
                        request.typing_env,
                        request.value.0,
                        request.value.1,
                    )
                    .ok_or(ProbeError::MonoProofIncomplete)?
                } else {
                    raw_instance
                };
                (codegen_instance == expected)
                    .then_some(())
                    .ok_or(ProbeError::MonoProofIncomplete)
            }
            MonoUseCause::VTableMethod => {
                let MonoTraceNode::VTable {
                    trait_ref: Some(trait_ref),
                    ..
                } = proof_use.from
                else {
                    return Err(ProbeError::MonoProofIncomplete);
                };
                let MonoTraceSite::VTableSlot(slot) = proof_use.site else {
                    return Err(ProbeError::MonoProofIncomplete);
                };
                let cold = self
                    .tcx
                    .codegen_vtable_method_witnesses(trait_ref)
                    .map_err(|_| ProbeError::MonoProofIncomplete)?;
                let warm = self
                    .tcx
                    .codegen_vtable_method_witnesses(trait_ref)
                    .map_err(|_| ProbeError::MonoProofIncomplete)?;
                if !std::ptr::eq(cold, warm) {
                    return Err(ProbeError::MonoProofCacheMismatch);
                }
                let witness = cold
                    .iter()
                    .find(|witness| witness.slot == slot)
                    .ok_or(ProbeError::MonoProofIncomplete)?;
                if witness.request != request || witness.codegen_instance != codegen_instance {
                    return Err(ProbeError::MonoProofIncomplete);
                }
                Ok(())
            }
            _ => Err(ProbeError::MonoProofIncomplete),
        }
    }

    fn checked_selection_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
    ) -> Result<&'tcx CodegenSelectionProof<'tcx>, ProbeError> {
        let cold = self
            .tcx
            .codegen_selection_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        let warm = self
            .tcx
            .codegen_selection_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        if !std::ptr::eq(cold, warm) {
            return Err(ProbeError::MonoProofCacheMismatch);
        }
        let stock = self
            .tcx
            .codegen_select_candidate(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        if cold.top_source != *stock {
            return Err(ProbeError::MonoProofIncomplete);
        }
        Ok(cold)
    }

    fn checked_projection_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, ty::AliasTerm<'tcx>>,
    ) -> Result<&'tcx rustc_middle::traits::CodegenProjectionProof<'tcx>, ProbeError> {
        let cold = self
            .tcx
            .codegen_projection_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        let warm = self
            .tcx
            .codegen_projection_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        if !std::ptr::eq(cold, warm) {
            return Err(ProbeError::MonoProofCacheMismatch);
        }
        let stock = self
            .tcx
            .try_normalize_generic_arg_after_erasing_regions(
                key.typing_env
                    .as_query_input(key.value.to_term(self.tcx, ty::IsRigid::No).into_arg()),
            )
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        let stock = match stock.kind() {
            ty::GenericArgKind::Type(value) => value.into(),
            ty::GenericArgKind::Const(value) => value.into(),
            ty::GenericArgKind::Lifetime(_) => return Err(ProbeError::MonoProofIncomplete),
        };
        if cold.normalized_term != stock {
            return Err(ProbeError::MonoProofIncomplete);
        }
        Ok(cold)
    }

    fn checked_associated_item_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, (DefId, ty::GenericArgsRef<'tcx>)>,
    ) -> Result<&'tcx rustc_middle::traits::CodegenAssociatedItemProof<'tcx>, ProbeError> {
        let cold = self
            .tcx
            .codegen_associated_item_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        let warm = self
            .tcx
            .codegen_associated_item_proof(key)
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        if !std::ptr::eq(cold, warm) {
            return Err(ProbeError::MonoProofCacheMismatch);
        }
        Ok(cold)
    }

    fn insert_mono_proof(&mut self, proof: MonoProofProbe) -> Result<(), ProbeError> {
        if let Some(existing) = self
            .mono_proofs
            .iter()
            .find(|existing| mono_proof_identity_matches(existing, &proof))
        {
            if existing == &proof {
                return Ok(());
            }
            return Err(ProbeError::MonoProofConflict);
        }
        self.mono_proofs.push(proof);
        Ok(())
    }

    fn record_supertrait_proofs(
        &mut self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
        from: MonoNodeProbe,
        cause: MonoUseCauseProbe,
        collection: ProbeCollection,
        site: MonoSiteProbe,
    ) -> Result<(), ProbeError> {
        let selection = self.checked_selection_proof(key)?;
        let ImplSource::UserDefined(selected) = &selection.top_source else {
            return Ok(());
        };
        let selected_trait_ref = self
            .tcx
            .impl_trait_ref(selected.impl_def_id)
            .instantiate(self.tcx, selected.args)
            .skip_norm_wip();
        let selected_trait_ref = self
            .tcx
            .try_normalize_erasing_regions(
                key.typing_env,
                Unnormalized::new_wip(selected_trait_ref),
            )
            .map_err(|_| ProbeError::MonoProofIncomplete)?;
        if selected_trait_ref != key.value {
            return Err(ProbeError::MonoProofIncomplete);
        }
        if self.supertrait_active.contains(&key) {
            return Err(ProbeError::MonoProofIncomplete);
        }
        self.supertrait_active.push(key);

        for (clause, _) in self
            .tcx
            .explicit_super_clauses_of(selected_trait_ref.def_id)
            .iter_identity_copied()
            .map(Unnormalized::skip_norm_wip)
        {
            let Some(predicate) = clause
                .instantiate_supertrait(self.tcx, ty::Binder::dummy(selected_trait_ref))
                .as_trait_clause()
            else {
                // Associated-type bindings are projection clauses. Their
                // codegen projection proofs are recorded independently.
                continue;
            };
            let predicate = self.tcx.instantiate_bound_regions_with_erased(predicate);
            let predicate = self
                .tcx
                .try_normalize_erasing_regions(key.typing_env, Unnormalized::new_wip(predicate))
                .map_err(|_| ProbeError::MonoProofIncomplete)?;
            let super_key = self
                .tcx
                .erase_and_anonymize_regions(key.typing_env.as_query_input(predicate.trait_ref));
            let super_selection = self.checked_selection_proof(super_key)?;
            let (local_impls, local_leaves) =
                selection_local_dependencies(self.tcx, super_selection)?;
            self.insert_mono_proof(MonoProofProbe {
                origin: MonoProofOriginProbe::SupertraitConstraint,
                from: from.clone(),
                kind: MonoProofKindProbe::TraitSelection {
                    trait_definition: display_def_path(self.tcx, super_key.value.def_id),
                    arguments: generic_arguments(super_key.value.args),
                },
                cause,
                collection,
                site: site.clone(),
                local_impls,
                local_leaves,
            })?;
            self.record_supertrait_proofs(
                super_key,
                from.clone(),
                cause,
                collection,
                site.clone(),
            )?;
        }

        self.supertrait_active.pop();
        Ok(())
    }
}

#[cfg(rust_item_dependencies_patched)]
fn mono_proof_identity_matches(left: &MonoProofProbe, right: &MonoProofProbe) -> bool {
    if left.origin != right.origin
        || left.from != right.from
        || left.cause != right.cause
        || left.collection != right.collection
        || left.site != right.site
    {
        return false;
    }
    match (&left.kind, &right.kind) {
        (
            MonoProofKindProbe::TraitSelection {
                trait_definition: left_definition,
                arguments: left_arguments,
            },
            MonoProofKindProbe::TraitSelection {
                trait_definition: right_definition,
                arguments: right_arguments,
            },
        ) => left_definition == right_definition && left_arguments == right_arguments,
        (
            MonoProofKindProbe::AssociatedItem {
                item: left_item,
                arguments: left_arguments,
                ..
            },
            MonoProofKindProbe::AssociatedItem {
                item: right_item,
                arguments: right_arguments,
                ..
            },
        ) => left_item == right_item && left_arguments == right_arguments,
        (
            MonoProofKindProbe::Projection {
                item: left_item,
                arguments: left_arguments,
                ..
            },
            MonoProofKindProbe::Projection {
                item: right_item,
                arguments: right_arguments,
                ..
            },
        ) => left_item == right_item && left_arguments == right_arguments,
        _ => false,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn selection_local_dependencies(
    tcx: TyCtxt<'_>,
    proof: &CodegenSelectionProof<'_>,
) -> Result<
    (
        Vec<LocalProofDefinitionProbe>,
        Vec<LocalProofDefinitionProbe>,
    ),
    ProbeError,
> {
    let (mut implementations, leaves) = trace_local_dependencies(tcx, &proof.trace)?;
    append_impl_source(tcx, &proof.top_source, &mut implementations)?;
    implementations.sort();
    implementations.dedup();
    Ok((implementations, leaves))
}

#[cfg(rust_item_dependencies_patched)]
fn trace_local_dependencies(
    tcx: TyCtxt<'_>,
    trace: &rustc_middle::traits::CodegenSolverTrace<'_>,
) -> Result<
    (
        Vec<LocalProofDefinitionProbe>,
        Vec<LocalProofDefinitionProbe>,
    ),
    ProbeError,
> {
    let mut implementations = Vec::new();
    let mut leaves = Vec::new();
    for selection in &trace.trait_selections {
        append_impl_source(tcx, &selection.source, &mut implementations)?;
    }
    for projection in &trace.projections {
        if let Some(item) = projection.selected_projection_item
            && let Some(item) = local_proof_definition(tcx, item)?
        {
            leaves.push(item);
        }
    }
    implementations.sort();
    implementations.dedup();
    leaves.sort();
    leaves.dedup();
    Ok((implementations, leaves))
}

#[cfg(rust_item_dependencies_patched)]
fn append_impl_source(
    tcx: TyCtxt<'_>,
    source: &ImplSource<'_, ()>,
    implementations: &mut Vec<LocalProofDefinitionProbe>,
) -> Result<(), ProbeError> {
    if let ImplSource::UserDefined(data) = source
        && let Some(implementation) = local_proof_definition(tcx, data.impl_def_id)?
    {
        implementations.push(implementation);
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn local_proof_definition(
    tcx: TyCtxt<'_>,
    definition: DefId,
) -> Result<Option<LocalProofDefinitionProbe>, ProbeError> {
    if !definition.is_local() {
        return Ok(None);
    }
    Ok(Some(LocalProofDefinitionProbe {
        path: display_def_path(tcx, definition),
        source_range: mono_source_range(tcx, tcx.def_span(definition))?,
    }))
}

#[cfg(rust_item_dependencies_patched)]
fn generic_arguments(arguments: ty::GenericArgsRef<'_>) -> Vec<String> {
    arguments
        .iter()
        .map(|argument| format!("{argument:?}"))
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn const_identity(tcx: TyCtxt<'_>, global_id: GlobalId<'_>) -> ConstIdentityProbe {
    ConstIdentityProbe {
        definition: display_def_path(tcx, global_id.instance.def_id()),
        arguments: generic_arguments(global_id.instance.args),
        instance: format!("{:?}", global_id.instance),
        promoted: global_id.promoted.map(|promoted| format!("{promoted:?}")),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn probe_collection_for_mode(mode: CollectionMode) -> ProbeCollection {
    match mode {
        CollectionMode::UsedItems => ProbeCollection::Used,
        CollectionMode::MentionedItems => ProbeCollection::Mentioned,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn mono_collection(collection: MonoTraceCollection) -> ProbeCollection {
    match collection {
        MonoTraceCollection::Used => ProbeCollection::Used,
        MonoTraceCollection::Mentioned => ProbeCollection::Mentioned,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn mono_cause(cause: MonoUseCause) -> MonoUseCauseProbe {
    match cause {
        MonoUseCause::DirectCall => MonoUseCauseProbe::DirectCall,
        MonoUseCause::FunctionPointer => MonoUseCauseProbe::FunctionPointer,
        MonoUseCause::ClosureFunctionPointer => MonoUseCauseProbe::ClosureFunctionPointer,
        MonoUseCause::InlineAsmSymbol => MonoUseCauseProbe::InlineAsmSymbol,
        MonoUseCause::StaticReference => MonoUseCauseProbe::StaticReference,
        MonoUseCause::ThreadLocalReference => MonoUseCauseProbe::ThreadLocalReference,
        MonoUseCause::DropGlue => MonoUseCauseProbe::DropGlue,
        MonoUseCause::VTableConstruction => MonoUseCauseProbe::VTableConstruction,
        MonoUseCause::VTableMethod => MonoUseCauseProbe::VTableMethod,
        MonoUseCause::VTableDrop => MonoUseCauseProbe::VTableDrop,
        MonoUseCause::SupertraitVTable => MonoUseCauseProbe::SupertraitVTable,
        MonoUseCause::ConstAllocation => MonoUseCauseProbe::ConstAllocation,
        MonoUseCause::AllocationReference => MonoUseCauseProbe::AllocationReference,
        MonoUseCause::ThreadLocalShim => MonoUseCauseProbe::ThreadLocalShim,
        MonoUseCause::CompilerRequirement => MonoUseCauseProbe::CompilerRequirement,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn mono_site(tcx: TyCtxt<'_>, site: MonoTraceSite) -> Result<MonoSiteProbe, ProbeError> {
    Ok(match site {
        MonoTraceSite::Source(span) => span_site(tcx, span)?,
        MonoTraceSite::AllocationOffset(offset) => MonoSiteProbe::AllocationOffset(offset),
        MonoTraceSite::VTableSlot(slot) => MonoSiteProbe::VTableSlot(slot),
        MonoTraceSite::CompilerGenerated => MonoSiteProbe::CompilerGenerated,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn span_site(tcx: TyCtxt<'_>, span: Span) -> Result<MonoSiteProbe, ProbeError> {
    if span.is_dummy() {
        return Ok(MonoSiteProbe::CompilerGenerated);
    }
    let source_map = tcx.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos {
        return Err(ProbeError::MonoProofIncomplete);
    }
    if start.sf.name.short().to_string() == "main.rs" {
        Ok(MonoSiteProbe::Source((start.pos.0, end.pos.0)))
    } else {
        Ok(MonoSiteProbe::ExternalSource(
            source_map.span_to_diagnostic_string(span),
        ))
    }
}

#[cfg(rust_item_dependencies_patched)]
fn mono_node(tcx: TyCtxt<'_>, node: MonoTraceNode<'_>) -> MonoNodeProbe {
    match node {
        MonoTraceNode::Item(MonoItem::Fn(instance)) => MonoNodeProbe {
            kind: "Function".to_owned(),
            definition: Some(display_def_path(tcx, instance.def_id())),
            instance: Some(format!("{instance:?}")),
        },
        MonoTraceNode::Item(MonoItem::Static(definition)) => MonoNodeProbe {
            kind: "Static".to_owned(),
            definition: Some(display_def_path(tcx, definition)),
            instance: None,
        },
        MonoTraceNode::Item(MonoItem::GlobalAsm(item)) => MonoNodeProbe {
            kind: "GlobalAsm".to_owned(),
            definition: Some(display_def_path(tcx, item.owner_id.to_def_id())),
            instance: None,
        },
        MonoTraceNode::Allocation(allocation) => MonoNodeProbe {
            kind: "Allocation".to_owned(),
            definition: None,
            instance: Some(tcx.with_stable_hashing_context(|mut context| {
                let mut hasher = StableHasher::new();
                allocation.stable_hash(&mut context, &mut hasher);
                fingerprint_identity(hasher.finish::<Fingerprint>())
            })),
        },
        MonoTraceNode::VTable {
            concrete_ty,
            trait_ref,
        } => MonoNodeProbe {
            kind: "VTable".to_owned(),
            definition: trait_ref.map(|trait_ref| display_def_path(tcx, trait_ref.def_id)),
            instance: Some(format!("({concrete_ty:?}, {trait_ref:?})")),
        },
    }
}

#[cfg(rust_item_dependencies_patched)]
fn fingerprint_identity(fingerprint: Fingerprint) -> String {
    let (first, second) = fingerprint.split();
    format!("{:016x}{:016x}", first.as_u64(), second.as_u64())
}

#[cfg(rust_item_dependencies_patched)]
fn mono_source_range(tcx: TyCtxt<'_>, span: Span) -> Result<(u32, u32), ProbeError> {
    if span.is_dummy() {
        return Err(ProbeError::MonoProofIncomplete);
    }
    let source_map = tcx.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos || start.sf.name.short().to_string() != "main.rs" {
        return Err(ProbeError::MonoProofIncomplete);
    }
    Ok((start.pos.0, end.pos.0))
}

#[cfg(rust_item_dependencies_patched)]
impl<'tcx> MonoQualificationCollector<'tcx> {
    fn required_const_targets(
        &mut self,
        owner: &str,
        instance: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        collection: ProbeCollection,
    ) -> Result<Vec<RequiredConstTarget<'tcx>>, ProbeError> {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut targets = Vec::new();

        for operand in body.required_consts() {
            let constant = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    ty::EarlyBinder::bind(self.tcx, operand.const_),
                )
                .map_err(|_| ProbeError::RequiredConstTraversalIncomplete)?;
            let mir::Const::Unevaluated(unevaluated, _) = constant else {
                if matches!(constant, mir::Const::Ty(_, value) if value.try_to_value().is_some()) {
                    continue;
                }
                return Err(ProbeError::RequiredConstTraversalIncomplete);
            };
            let target_instance =
                Instance::try_resolve(self.tcx, typing_env, unevaluated.def, unevaluated.args)
                    .map_err(|_| ProbeError::RequiredConstTraversalIncomplete)?
                    .ok_or(ProbeError::RequiredConstTraversalIncomplete)?;
            let global_id = GlobalId {
                instance: target_instance,
                promoted: unevaluated.promoted,
            };
            let associated_key = (unevaluated.promoted.is_none()
                && matches!(
                    self.tcx.def_kind(unevaluated.def),
                    DefKind::AssocConst { .. }
                )
                && self.tcx.trait_of_assoc(unevaluated.def).is_some())
            .then(|| {
                self.tcx.erase_and_anonymize_regions(
                    typing_env.as_query_input((unevaluated.def, unevaluated.args)),
                )
            });
            if let Some(key) = associated_key {
                let (selection_key, selection, raw_instance) =
                    self.checked_associated_request(key)?;
                let proof = self.checked_associated_item_proof(key)?;
                if raw_instance != target_instance
                    || proof.selection_key != selection_key
                    || proof.source != selection.top_source
                    || proof.final_instance != target_instance
                {
                    return Err(ProbeError::RequiredConstTraversalIncomplete);
                }
            }
            self.insert_required_const_use(RequiredConstUseProbe {
                owner: owner.to_owned(),
                request_definition: display_def_path(self.tcx, unevaluated.def),
                request_arguments: generic_arguments(unevaluated.args),
                target: const_identity(self.tcx, global_id),
                collection,
                site: span_site(self.tcx, operand.span)?,
            })?;
            targets.push(RequiredConstTarget {
                global_id,
                site: operand.span,
                associated_key,
            });
        }

        Ok(targets)
    }

    fn insert_required_const_use(
        &mut self,
        probe: RequiredConstUseProbe,
    ) -> Result<(), ProbeError> {
        if let Some(existing) = self.required_const_uses.iter().find(|existing| {
            existing.owner == probe.owner
                && existing.request_definition == probe.request_definition
                && existing.request_arguments == probe.request_arguments
                && existing.collection == probe.collection
                && existing.site == probe.site
        }) {
            if existing == &probe {
                return Ok(());
            }
            return Err(ProbeError::MonoProofConflict);
        }
        self.required_const_uses.push(probe);
        Ok(())
    }

    fn validate_associated_const_observations(
        &self,
        owner: MonoTraceNode<'tcx>,
        successors: &MonoSuccessors<'tcx>,
        targets: &[RequiredConstTarget<'tcx>],
    ) -> Result<(), ProbeError> {
        let mut expected = Vec::new();
        for target in targets {
            let Some(key) = target.associated_key else {
                continue;
            };
            let site = if target.site.is_dummy() {
                MonoTraceSite::CompilerGenerated
            } else {
                MonoTraceSite::Source(target.site)
            };
            let tuple = (key, site);
            if !expected.contains(&tuple) {
                expected.push(tuple);
            }
        }
        if expected.len() != successors.associated_consts.len() {
            return Err(ProbeError::MonoObservationIncomplete);
        }
        for ((expected_key, expected_site), observed) in
            expected.into_iter().zip(successors.associated_consts)
        {
            if observed.owner != owner
                || observed.proof_key != expected_key
                || observed.site != expected_site
            {
                return Err(ProbeError::MonoObservationIncomplete);
            }
        }
        Ok(())
    }

    fn visit_const(
        &mut self,
        global_id: GlobalId<'tcx>,
        mode: CollectionMode,
    ) -> Result<(), ProbeError> {
        let visit_key = (global_id, mode);
        if self.const_done.contains(&visit_key) {
            return Ok(());
        }
        if !self.const_active.insert(visit_key) {
            return Err(ProbeError::RequiredConstCycle);
        }

        let body = if let Some(promoted) = global_id.promoted {
            self.tcx
                .promoted_mir(global_id.instance.def_id())
                .get(promoted)
                .ok_or(ProbeError::RequiredConstTraversalIncomplete)?
        } else {
            self.tcx.mir_for_ctfe(global_id.instance.def_id())
        };
        let collection = probe_collection_for_mode(mode);
        self.collect_const_trait_function_uses(global_id, body, collection)?;
        let owner = format!("{:?}", const_identity(self.tcx, global_id));
        let targets = self.required_const_targets(&owner, global_id.instance, body, collection)?;
        for target in targets {
            self.visit_const(target.global_id, mode)?;
        }

        self.const_active.remove(&visit_key);
        self.const_done.insert(visit_key);
        Ok(())
    }

    fn collect_const_trait_function_uses(
        &mut self,
        global_id: GlobalId<'tcx>,
        body: &mir::Body<'tcx>,
        collection: ProbeCollection,
    ) -> Result<(), ProbeError> {
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let mir::StatementKind::Assign(assignment) = &statement.kind else {
                    continue;
                };
                let mir::Rvalue::Cast(
                    mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_), _),
                    operand,
                    _,
                ) = &assignment.1
                else {
                    continue;
                };
                let operand_ty = operand.ty(body, self.tcx);
                let operand_ty = global_id
                    .instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(self.tcx, operand_ty),
                    )
                    .map_err(|_| ProbeError::RequiredConstTraversalIncomplete)?;
                let ty::FnDef(item, arguments) = *operand_ty.kind() else {
                    continue;
                };
                let arguments = arguments
                    .no_bound_vars()
                    .ok_or(ProbeError::RequiredConstTraversalIncomplete)?;
                if self.tcx.trait_of_assoc(item).is_none() {
                    continue;
                }
                self.record_const_trait_function_use(
                    global_id,
                    item,
                    arguments,
                    collection,
                    statement.source_info.span,
                )?;
            }
        }
        Ok(())
    }

    fn record_const_trait_function_use(
        &mut self,
        body: GlobalId<'tcx>,
        item: DefId,
        arguments: ty::GenericArgsRef<'tcx>,
        collection: ProbeCollection,
        span: Span,
    ) -> Result<(), ProbeError> {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let request = self
            .tcx
            .erase_and_anonymize_regions(typing_env.as_query_input((item, arguments)));
        let (_, selection, raw_instance) = self.checked_associated_request(request)?;
        let codegen_instance = Instance::resolve_for_fn_ptr(
            self.tcx,
            request.typing_env,
            request.value.0,
            request.value.1,
        )
        .ok_or(ProbeError::MonoProofIncomplete)?;
        let (mut local_impls, mut local_leaves) =
            selection_local_dependencies(self.tcx, selection)?;
        self.extend_associated_dependencies(
            request,
            selection,
            raw_instance,
            &mut local_impls,
            &mut local_leaves,
        )?;
        local_impls.sort();
        local_impls.dedup();
        local_leaves.sort();
        local_leaves.dedup();
        let probe = ConstTraitFunctionUseProbe {
            body: const_identity(self.tcx, body),
            item: display_def_path(self.tcx, item),
            arguments: generic_arguments(arguments),
            raw_instance: format!("{raw_instance:?}"),
            codegen_instance: format!("{codegen_instance:?}"),
            collection,
            site: span_site(self.tcx, span)?,
            local_impls,
            local_leaves,
        };
        if let Some(existing) = self.const_trait_function_uses.iter().find(|existing| {
            existing.body == probe.body
                && existing.item == probe.item
                && existing.arguments == probe.arguments
                && existing.collection == probe.collection
                && existing.site == probe.site
        }) {
            if existing == &probe {
                return Ok(());
            }
            return Err(ProbeError::MonoProofConflict);
        }
        self.const_trait_function_uses.push(probe);
        Ok(())
    }
}

#[cfg(not(rust_item_dependencies_patched))]
fn collect_macro_invocations(_tcx: TyCtxt<'_>) -> Result<Vec<MacroInvocationProbe>, ProbeError> {
    Ok(Vec::new())
}

#[cfg(rust_item_dependencies_patched)]
fn collect_macro_invocations(tcx: TyCtxt<'_>) -> Result<Vec<MacroInvocationProbe>, ProbeError> {
    let mut generated_definitions = BTreeMap::<ExpansionKeyProbe, Vec<String>>::new();
    for definition in tcx.iter_local_def_id() {
        let expansion = tcx.expn_that_defined(definition.to_def_id());
        if expansion != ExpnId::root() && matches!(expansion.expn_data().kind, ExpnKind::Macro(..))
        {
            generated_definitions
                .entry(expansion_key(expansion))
                .or_default()
                .push(display_def_path(tcx, definition.to_def_id()));
        }
    }
    for definitions in generated_definitions.values_mut() {
        definitions.sort();
        definitions.dedup();
    }

    let raw_origins = tcx
        .resolutions(())
        .macro_invocation_origins
        .items()
        .map(|(&expansion, record)| (expansion_key(expansion), expansion, record))
        .into_sorted_stable_ord_by_key(|(key, _, _)| &key.0);
    let observed = raw_origins
        .iter()
        .map(|(key, _, _)| *key)
        .collect::<BTreeSet<_>>();
    let mut macro_invocations = raw_origins
        .into_iter()
        .map(|(expansion, expansion_id, record)| {
            let data = expansion_id.expn_data();
            let discovered_in = optional_expansion_key(record.discovered_in_expansion);
            let discovered_in_kind = expansion_kind(record.discovered_in_expansion);
            let parent = optional_expansion_key(data.parent);
            let parent_kind = expansion_kind(data.parent);
            if !relation_is_observed(discovered_in, discovered_in_kind.as_ref(), &observed)
                || !relation_is_observed(parent, parent_kind.as_ref(), &observed)
            {
                return Err(ProbeError::ExpansionOriginIncomplete);
            }
            let source_call_parent = optional_expansion_key(data.call_site.ctxt().outer_expn());
            let written = discovered_in.is_none();

            Ok(MacroInvocationProbe {
                expansion,
                discovered_in,
                discovered_in_kind,
                parent,
                source_call_parent,
                kind: data.kind.descr(),
                fragment_kind: format!("{:?}", record.fragment_kind),
                implementation_kind: format!("{:?}", record.implementation_kind),
                macro_definition: data.macro_def_id.map(|id| display_def_path(tcx, id)),
                written_invocation_range: written
                    .then(|| expansion_source_relative_range(tcx, data.call_site))
                    .transpose()?,
                written_node_range: written
                    .then(|| expansion_source_relative_range(tcx, record.invocation_node_span))
                    .transpose()?,
                source_node_range: main_source_relative_range(tcx, record.invocation_node_span)?,
                written_target_range: if written {
                    record
                        .target_span
                        .map(|span| expansion_source_relative_range(tcx, span))
                        .transpose()?
                } else {
                    None
                },
                generated_definitions: generated_definitions.remove(&expansion).unwrap_or_default(),
                resolved_import_uses: collect_macro_import_uses(tcx, record)?,
            })
        })
        .collect::<Result<Vec<_>, ProbeError>>()?;

    if !generated_definitions.is_empty() {
        return Err(ProbeError::ExpansionOriginIncomplete);
    }

    macro_invocations.sort_by(|left, right| left.expansion.cmp(&right.expansion));
    Ok(macro_invocations)
}

#[cfg(rust_item_dependencies_patched)]
fn collect_macro_import_uses(
    tcx: TyCtxt<'_>,
    origin: &rustc_middle::ty::MacroInvocationOrigin,
) -> Result<Vec<MacroResolvedImportUseProbe>, ProbeError> {
    let mut uses = origin
        .resolved_import_uses
        .iter()
        .map(|record| {
            let mut import_chain = Vec::with_capacity(record.import_chain.len());
            for step in &record.import_chain {
                let definition = step.definition.to_def_id();
                let span = tcx
                    .hir_span_if_local(definition)
                    .ok_or(ProbeError::MacroImportProvenanceIncomplete)?;
                import_chain.push(ResolvedImportStepProbe {
                    kind: match step.kind {
                        rustc_middle::ty::MacroImportKind::Single => ImportKindProbe::Single,
                        rustc_middle::ty::MacroImportKind::Glob => ImportKindProbe::Glob,
                        rustc_middle::ty::MacroImportKind::ExternCrate => {
                            ImportKindProbe::ExternCrate
                        }
                        rustc_middle::ty::MacroImportKind::MacroUse => ImportKindProbe::MacroUse,
                        rustc_middle::ty::MacroImportKind::MacroExport => {
                            ImportKindProbe::MacroExport
                        }
                    },
                    definition: Some(display_def_path(tcx, definition)),
                    source_range: Some(source_relative_range(tcx, span)?),
                });
            }
            Ok(MacroResolvedImportUseProbe {
                path_range: main_source_relative_range(tcx, record.path_span)?,
                segment_range: main_source_relative_range(tcx, record.segment_span)?,
                namespace: format!("{:?}", record.namespace),
                target: record
                    .target
                    .opt_def_id()
                    .map(|definition| display_def_path(tcx, definition))
                    .unwrap_or_else(|| format!("{:?}", record.target)),
                import_chain,
            })
        })
        .collect::<Result<Vec<_>, ProbeError>>()?;
    uses.sort();
    Ok(uses)
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_key(expansion: ExpnId) -> ExpansionKeyProbe {
    ExpansionKeyProbe(expansion.expn_hash().local_hash().as_u64())
}

#[cfg(rust_item_dependencies_patched)]
fn optional_expansion_key(expansion: ExpnId) -> Option<ExpansionKeyProbe> {
    (expansion != ExpnId::root()).then(|| expansion_key(expansion))
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_kind(expansion: ExpnId) -> Option<ExpansionKindProbe> {
    if expansion == ExpnId::root() {
        return None;
    }
    let data = expansion.expn_data();
    let description = data.kind.descr();
    Some(match data.kind {
        ExpnKind::Macro(..) => ExpansionKindProbe::Macro(description),
        ExpnKind::AstPass(..) => ExpansionKindProbe::AstPass(description),
        ExpnKind::Desugaring(..) => ExpansionKindProbe::Desugaring(description),
        ExpnKind::Root => return None,
    })
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn relation_is_observed(
    relation: Option<ExpansionKeyProbe>,
    kind: Option<&ExpansionKindProbe>,
    observed: &BTreeSet<ExpansionKeyProbe>,
) -> bool {
    match (relation, kind) {
        (None, None) => true,
        (Some(key), Some(ExpansionKindProbe::Macro(_))) => observed.contains(&key),
        (Some(_), Some(ExpansionKindProbe::AstPass(_) | ExpansionKindProbe::Desugaring(_))) => true,
        (None, Some(_)) | (Some(_), None) => false,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_source_relative_range(tcx: TyCtxt<'_>, span: Span) -> Result<(u32, u32), ProbeError> {
    source_relative_range(tcx, span).map_err(|_| ProbeError::ExpansionOriginIncomplete)
}

#[cfg(rust_item_dependencies_patched)]
fn main_source_relative_range(
    tcx: TyCtxt<'_>,
    span: Span,
) -> Result<Option<(u32, u32)>, ProbeError> {
    if span.is_dummy() {
        return Err(ProbeError::ExpansionOriginIncomplete);
    }
    let source_map = tcx.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos {
        return Err(ProbeError::ExpansionOriginIncomplete);
    }
    if start.sf.name.short().to_string() != "main.rs" {
        return Ok(None);
    }
    Ok(Some((start.pos.0, end.pos.0)))
}

#[cfg(rust_item_dependencies_patched)]
fn collect_typeck_impl_dependencies(
    tcx: TyCtxt<'_>,
) -> Result<Vec<TypeckImplDependencyProbe>, ProbeError> {
    let dependencies = tcx
        .typeck_impl_dependencies(())
        .map_err(|_| ProbeError::TypeckImplDependenciesIncomplete)?;
    let mut dependencies = dependencies
        .iter()
        .map(|dependency| {
            Ok(TypeckImplDependencyProbe {
                source_owner: display_def_path(tcx, dependency.source_owner.to_def_id()),
                source_range: source_relative_range(tcx, dependency.source_span)
                    .map_err(|_| ProbeError::TypeckImplDependenciesIncomplete)?,
                implementation: display_def_path(tcx, dependency.impl_def_id.to_def_id()),
                associated_item: dependency
                    .associated_item
                    .map(|item| display_def_path(tcx, item)),
            })
        })
        .collect::<Result<Vec<_>, ProbeError>>()?;
    dependencies.sort();
    dependencies.dedup();
    Ok(dependencies)
}

#[cfg(not(rust_item_dependencies_patched))]
fn collect_import_provenance(
    _tcx: TyCtxt<'_>,
) -> Result<(Vec<ResolvedImportUseProbe>, Vec<SelectedTraitImportProbe>), ProbeError> {
    Ok((Vec::new(), Vec::new()))
}

#[cfg(rust_item_dependencies_patched)]
fn collect_import_provenance(
    tcx: TyCtxt<'_>,
) -> Result<(Vec<ResolvedImportUseProbe>, Vec<SelectedTraitImportProbe>), ProbeError> {
    let mut resolved_import_uses = tcx
        .resolutions(())
        .resolved_import_uses
        .iter()
        .map(|record| {
            Ok(ResolvedImportUseProbe {
                owner: display_def_path(tcx, record.owner.to_def_id()),
                path_range: source_relative_range(tcx, record.path_span)?,
                segment_range: source_relative_range(tcx, record.segment_span)?,
                namespace: format!("{:?}", record.namespace),
                target: record
                    .target
                    .opt_def_id()
                    .map(|definition| display_def_path(tcx, definition))
                    .unwrap_or_else(|| format!("{:?}", record.target)),
                import_chain: record
                    .import_chain
                    .iter()
                    .copied()
                    .map(|step| import_step(tcx, step))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        })
        .collect::<Result<Vec<_>, ProbeError>>()?;
    resolved_import_uses.sort_by(|left, right| {
        left.owner
            .cmp(&right.owner)
            .then(left.path_range.cmp(&right.path_range))
            .then(left.segment_range.cmp(&right.segment_range))
            .then(left.namespace.cmp(&right.namespace))
            .then(left.target.cmp(&right.target))
            .then(left.import_chain.cmp(&right.import_chain))
    });
    resolved_import_uses.dedup();

    let mut typeck_roots = Vec::new();
    for body_owner in tcx.hir_body_owners() {
        let root = tcx.typeck_root_def_id_local(body_owner);
        if !typeck_roots.contains(&root) {
            typeck_roots.push(root);
        }
    }
    typeck_roots.sort_by_key(|root| tcx.def_path_str(root.to_def_id()));

    let mut selected_trait_imports = Vec::new();
    for root in typeck_roots {
        let results = tcx.typeck(root);
        for (local_id, import_ids) in results.selected_trait_imports().items_in_stable_order() {
            let site = HirId {
                owner: results.hir_owner,
                local_id,
            };
            let selected_item = results
                .type_dependent_def_id(site)
                .ok_or(ProbeError::ImportProvenanceIncomplete)?;
            let import_chain = import_ids
                .iter()
                .copied()
                .map(|definition| {
                    let definition = definition.to_def_id();
                    let span = tcx
                        .hir_span_if_local(definition)
                        .ok_or(ProbeError::ImportProvenanceIncomplete)?;
                    Ok(ImportLeafProbe {
                        definition: display_def_path(tcx, definition),
                        source_range: source_relative_range(tcx, span)?,
                    })
                })
                .collect::<Result<Vec<_>, ProbeError>>()?;
            selected_trait_imports.push(SelectedTraitImportProbe {
                owner: display_def_path(tcx, results.hir_owner.to_def_id()),
                site_range: source_relative_range(tcx, tcx.hir_span(site))?,
                selected_item: display_def_path(tcx, selected_item),
                import_chain,
            });
        }
    }
    selected_trait_imports.sort_by(|left, right| {
        left.owner
            .cmp(&right.owner)
            .then(left.site_range.cmp(&right.site_range))
            .then(left.selected_item.cmp(&right.selected_item))
            .then(left.import_chain.cmp(&right.import_chain))
    });
    selected_trait_imports.dedup();

    Ok((resolved_import_uses, selected_trait_imports))
}

#[cfg(rust_item_dependencies_patched)]
fn import_step(tcx: TyCtxt<'_>, step: Reexport) -> Result<ResolvedImportStepProbe, ProbeError> {
    let (kind, definition) = match step {
        Reexport::Single(definition) => (ImportKindProbe::Single, Some(definition)),
        Reexport::Glob(definition) => (ImportKindProbe::Glob, Some(definition)),
        Reexport::ExternCrate(definition) => (ImportKindProbe::ExternCrate, Some(definition)),
        Reexport::MacroUse => (ImportKindProbe::MacroUse, None),
        Reexport::MacroExport => (ImportKindProbe::MacroExport, None),
    };
    let source_range = definition
        .and_then(|definition| tcx.hir_span_if_local(definition))
        .map(|span| source_relative_range(tcx, span))
        .transpose()?;
    Ok(ResolvedImportStepProbe {
        kind,
        definition: definition.map(|definition| display_def_path(tcx, definition)),
        source_range,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn source_relative_range(tcx: TyCtxt<'_>, span: Span) -> Result<(u32, u32), ProbeError> {
    if span.is_dummy() {
        return Err(ProbeError::ImportProvenanceIncomplete);
    }
    let source_map = tcx.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos {
        return Err(ProbeError::ImportProvenanceIncomplete);
    }
    Ok((start.pos.0, end.pos.0))
}

fn mono_child(tcx: TyCtxt<'_>, collection: ProbeCollection, item: MonoItem<'_>) -> MonoChildProbe {
    match item {
        MonoItem::Fn(instance) => MonoChildProbe {
            collection,
            kind: format!("Fn({:?})", instance.def),
            definition: display_def_path(tcx, instance.def_id()),
            instance: Some(format!("{instance:?}")),
        },
        MonoItem::Static(definition) => MonoChildProbe {
            collection,
            kind: "Static".to_owned(),
            definition: display_def_path(tcx, definition),
            instance: None,
        },
        MonoItem::GlobalAsm(item) => MonoChildProbe {
            collection,
            kind: "GlobalAsm".to_owned(),
            definition: display_def_path(tcx, item.owner_id.to_def_id()),
            instance: None,
        },
    }
}

fn display_def_path(tcx: TyCtxt<'_>, definition: DefId) -> String {
    let path = tcx.def_path_str(definition);
    if definition.is_local() {
        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        if path == crate_name || path.starts_with(&format!("{crate_name}::")) {
            path
        } else {
            format!("{crate_name}::{path}")
        }
    } else {
        path
    }
}

struct SingleSourceLoader {
    source: Arc<str>,
    working_directory: PathBuf,
    denied_source_paths: Arc<Mutex<Vec<PathBuf>>>,
}

impl FileLoader for SingleSourceLoader {
    fn file_exists(&self, path: &Path) -> bool {
        if path == Path::new("main.rs") {
            true
        } else {
            self.record_denied(path);
            false
        }
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(self.source.to_string())
        } else {
            self.record_denied(path);
            Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "compiler qualification source loader rejected {}",
                    path.display()
                ),
            ))
        }
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        if self.file_exists(path) {
            Ok(Arc::from(self.source.as_bytes()))
        } else {
            self.record_denied(path);
            Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "compiler qualification source loader rejected {}",
                    path.display()
                ),
            ))
        }
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        Ok(self.working_directory.clone())
    }
}

impl SingleSourceLoader {
    fn record_denied(&self, path: &Path) {
        self.denied_source_paths
            .lock()
            .expect("denied source path mutex is poisoned")
            .push(path.to_owned());
    }
}

#[cfg(test)]
mod tests {
    #[cfg(rust_item_dependencies_patched)]
    use super::fingerprint_identity;
    use super::{
        ExpansionKeyProbe, ExpansionKindProbe, ProbeConfig, probe_arguments, relation_is_observed,
    };
    #[cfg(rust_item_dependencies_patched)]
    use rustc_data_structures::fingerprint::Fingerprint;
    use std::collections::BTreeSet;
    use std::path::PathBuf;

    #[test]
    fn compiler_probe_uses_normal_lints_without_writing_metadata() {
        let arguments = probe_arguments(&ProbeConfig {
            sysroot: PathBuf::from("sentinel-sysroot"),
            target: "sentinel-target".to_owned(),
            edition: "2021".to_owned(),
        });

        assert_eq!(
            arguments,
            [
                "rust-item-dependencies-compiler-qualification",
                "main.rs",
                "--crate-name=rust_item_dependencies_compiler_qualification",
                "--crate-type=bin",
                "--edition=2021",
                "--target=sentinel-target",
                "--sysroot",
                "sentinel-sysroot",
                "--emit=metadata=-",
            ]
        );
    }

    #[test]
    fn a_missing_macro_relation_is_not_accepted_as_a_synthetic_expansion() {
        let key = ExpansionKeyProbe(1);
        let macro_kind = ExpansionKindProbe::Macro("forward!".to_owned());
        let ast_pass = ExpansionKindProbe::AstPass("standard library imports".to_owned());
        let desugaring = ExpansionKindProbe::Desugaring("desugaring of for loop".to_owned());
        let mut observed = BTreeSet::new();

        assert!(!relation_is_observed(
            Some(key),
            Some(&macro_kind),
            &observed
        ));
        assert!(relation_is_observed(Some(key), Some(&ast_pass), &observed));
        assert!(relation_is_observed(
            Some(key),
            Some(&desugaring),
            &observed
        ));

        observed.insert(key);
        assert!(relation_is_observed(
            Some(key),
            Some(&macro_kind),
            &observed
        ));
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn allocation_fingerprint_halves_have_fixed_width() {
        let first = fingerprint_identity(Fingerprint::new(1_u64, 0x23_u64));
        let second = fingerprint_identity(Fingerprint::new(0x12_u64, 3_u64));

        assert_eq!(first, "00000000000000010000000000000023");
        assert_eq!(second, "00000000000000120000000000000003");
        assert_ne!(first, second);
    }
}
