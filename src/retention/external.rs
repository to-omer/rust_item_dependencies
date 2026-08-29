#[cfg(test)]
use std::cell::Cell;
#[cfg(rust_item_dependencies_patched)]
use std::collections::HashSet;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

#[cfg(rust_item_dependencies_patched)]
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use crate::definitions::CollectedDefinitions;
use crate::dependency_graph::{DependencyGraph, GraphNode};
use crate::graph::{DefinitionId, DefinitionKind};
#[cfg(rust_item_dependencies_patched)]
use crate::source::original_span_range;
use crate::source::{CfgState, SourceInventory, SourceUnitId};

use super::{Retention, RetentionError, SourceConstraints};
#[cfg(rust_item_dependencies_patched)]
use super::{SourceSiteOwnerIndex, source_site_owner};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ExternalDependencyKind {
    MacrosOnly,
    Conditional,
    Unconditional,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalCrateDependency {
    pub(super) crate_identity: u64,
    pub(super) kind: ExternalDependencyKind,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalCrateLoad {
    pub(super) direct: ExternalCrateDependency,
    pub(super) closure: Vec<ExternalCrateDependency>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ExternalCrateBindingTarget {
    SelfCrate,
    External(ExternalCrateLoad),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalCrateBinding {
    pub(super) definition: DefinitionId,
    pub(super) target: ExternalCrateBindingTarget,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalCrateActivation {
    pub(super) source: Option<SourceUnitId>,
    pub(super) load: ExternalCrateLoad,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CompilerGeneratedCrateActivation {
    pub(super) load: ExternalCrateLoad,
    pub(super) condition: Option<u64>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ExternalMetadataProviderKind {
    CompilerBuiltins,
    PanicRuntime,
    ProfilerRuntime,
    ExternalNativeLink,
    GlobalAllocator,
    AllocErrorHandler,
    DefaultLibAllocator,
    WeakLangItem(u32),
    ExternallyImplementableItemImplementation,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalMetadataProvider {
    pub(super) crate_identity: u64,
    pub(super) kind: ExternalMetadataProviderKind,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ExternalMetadataRequirementKind {
    Allocator,
    PanicRuntime,
    MissingLangItem(u32),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ExternalMetadataRequirement {
    pub(super) crate_identity: u64,
    pub(super) kind: ExternalMetadataRequirementKind,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct LocalMetadataRequirement {
    pub(super) source: Option<SourceUnitId>,
    pub(super) kind: ExternalMetadataRequirementKind,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ExternalCompilerMetadataFact {
    Provider {
        crate_identity: u64,
        provider: ExternalMetadataProviderKind,
        dependency_kind: ExternalDependencyKind,
    },
    Requirement(ExternalMetadataRequirementKind),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ExternalCompilerExpectation {
    pub(super) metadata: BTreeSet<ExternalCompilerMetadataFact>,
    pub(super) external_crates: BTreeSet<ExternalCrateDependency>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ExternalCompilerObservation {
    pub(super) metadata: BTreeSet<ExternalCompilerMetadataFact>,
    pub(super) loaded_crates: BTreeSet<ExternalCrateDependency>,
}

#[cfg(test)]
thread_local! {
    static OMIT_EXTERNAL_METADATA_AFTER_OBSERVATIONS: Cell<Option<usize>> = const { Cell::new(None) };
}

#[cfg(test)]
pub(crate) fn with_one_omitted_external_compiler_metadata_fact<T>(f: impl FnOnce() -> T) -> T {
    OMIT_EXTERNAL_METADATA_AFTER_OBSERVATIONS.with(|remaining| {
        assert!(
            remaining.get().is_none(),
            "metadata omission must not be nested"
        );
        remaining.set(Some(2));
    });
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            OMIT_EXTERNAL_METADATA_AFTER_OBSERVATIONS.with(|remaining| remaining.set(None));
        }
    }
    let _reset = Reset;
    f()
}

#[cfg(test)]
fn omit_external_compiler_metadata_fact() -> bool {
    OMIT_EXTERNAL_METADATA_AFTER_OBSERVATIONS.with(|remaining| match remaining.get() {
        Some(1) => {
            remaining.set(None);
            true
        }
        Some(count) => {
            remaining.set(Some(count - 1));
            false
        }
        None => false,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ExternalCompilerOutcomeDifference {
    Metadata {
        original: ExternalCompilerExpectation,
        reduced: ExternalCompilerObservation,
    },
    ExternalCrate {
        crate_identity: u64,
        original: ExternalDependencyKind,
        reduced: Option<ExternalDependencyKind>,
    },
}

impl ExternalCompilerOutcomeDifference {
    pub(crate) fn kind(&self) -> &'static str {
        match self {
            Self::Metadata { .. } => "external_compiler_metadata",
            Self::ExternalCrate { .. } => "external_compiler_crate_dependency_kind",
        }
    }

    pub(crate) fn original(&self) -> String {
        match self {
            Self::Metadata { original, .. } => format!("{:?}", original.metadata),
            Self::ExternalCrate {
                crate_identity,
                original,
                ..
            } => format!("crate {crate_identity:#018x} at {original:?}"),
        }
    }

    pub(crate) fn reduced(&self) -> String {
        match self {
            Self::Metadata { reduced, .. } => format!("{:?}", reduced.metadata),
            Self::ExternalCrate {
                crate_identity,
                reduced,
                ..
            } => reduced.map_or_else(
                || format!("crate {crate_identity:#018x} is absent"),
                |kind| format!("crate {crate_identity:#018x} at {kind:?}"),
            ),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct ExternalCrateFacts {
    pub(super) loaded_crates: Vec<ExternalCrateDependency>,
    pub(super) user_artifact_crates: Vec<u64>,
    pub(super) bindings: Vec<ExternalCrateBinding>,
    pub(super) activations: Vec<ExternalCrateActivation>,
    pub(super) compiler_generated_activations: Vec<CompilerGeneratedCrateActivation>,
    pub(super) providers: Vec<ExternalMetadataProvider>,
    pub(super) requirements: Vec<ExternalMetadataRequirement>,
    pub(super) local_requirements: Vec<LocalMetadataRequirement>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum CompilerCrateLoadCarrier {
    Definition(DefinitionId),
    Source(SourceUnitId),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct CompilerCrateLoadDisjunction {
    pub(super) trigger: Option<GraphNode>,
    pub(super) choices: Vec<CompilerCrateLoadCarrier>,
}
#[cfg(rust_item_dependencies_patched)]
pub(super) fn collect_external_crate_facts(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
    local_definitions: &[LocalDefId],
    definition_units: &[SourceUnitId],
    external_artifact_directory: Option<&Path>,
) -> Result<ExternalCrateFacts, RetentionError> {
    use rustc_hir::attrs::LangItem;
    use rustc_hir::{ItemKind, find_attr};
    use rustc_middle::ty::{CompilerMetadataProvider, CompilerMetadataRequirement};
    use rustc_session::cstore::CrateDepKind;
    use rustc_span::kw;

    let source_sites = SourceSiteOwnerIndex::new(source)?;

    fn dependency_kind(kind: CrateDepKind) -> ExternalDependencyKind {
        match kind {
            CrateDepKind::MacrosOnly => ExternalDependencyKind::MacrosOnly,
            CrateDepKind::Conditional => ExternalDependencyKind::Conditional,
            CrateDepKind::Unconditional => ExternalDependencyKind::Unconditional,
        }
    }

    fn dependency(
        tcx: TyCtxt<'_>,
        crate_num: rustc_hir::def_id::CrateNum,
    ) -> ExternalCrateDependency {
        ExternalCrateDependency {
            crate_identity: tcx.stable_crate_id(crate_num).as_u64(),
            kind: dependency_kind(tcx.crate_dep_kind(crate_num)),
        }
    }

    fn load(
        tcx: TyCtxt<'_>,
        root: rustc_middle::ty::ExternalCrateLoad,
        loaded: &BTreeMap<rustc_hir::def_id::CrateNum, ExternalCrateDependency>,
        cache: &mut BTreeMap<rustc_middle::ty::ExternalCrateLoad, ExternalCrateLoad>,
    ) -> Result<ExternalCrateLoad, RetentionError> {
        if let Some(load) = cache.get(&root) {
            return Ok(load.clone());
        }
        let cold = tcx.crate_dependency_closure(root);
        let warm = tcx.crate_dependency_closure(root);
        if !std::ptr::eq(cold, warm) {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        let closure = cold
            .iter()
            .map(|dependency| {
                let loaded = loaded
                    .get(&dependency.crate_num)
                    .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
                Ok(ExternalCrateDependency {
                    crate_identity: loaded.crate_identity,
                    kind: dependency_kind(dependency.kind),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let direct_loaded = loaded
            .get(&root.crate_num)
            .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
        let direct = ExternalCrateDependency {
            crate_identity: direct_loaded.crate_identity,
            kind: dependency_kind(root.kind),
        };
        if closure
            .iter()
            .filter(|dependency| **dependency == direct)
            .count()
            != 1
        {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        let load = ExternalCrateLoad { direct, closure };
        cache.insert(root, load.clone());
        Ok(load)
    }

    // Crate-level compiler metadata is not uniformly restricted to
    // `used_crates`: allocator, runtime, builtins, and EII processing scan the
    // complete registered CStore. Keep that complete set as the identity and
    // final-kind universe; the rustc provider query itself applies the
    // narrower used-crate rule where required (notably weak lang items).
    let cold_loaded = tcx.crates(());
    let warm_loaded = tcx.crates(());
    if !std::ptr::eq(cold_loaded, warm_loaded) {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }
    let mut loaded = BTreeMap::new();
    let mut loaded_identities = BTreeSet::new();
    let mut user_artifact_crates = BTreeSet::new();
    for &crate_num in cold_loaded {
        let dependency = dependency(tcx, crate_num);
        if loaded.insert(crate_num, dependency).is_some()
            || !loaded_identities.insert(dependency.crate_identity)
        {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        if external_artifact_directory.is_some_and(|directory| {
            tcx.used_crate_source(crate_num)
                .paths()
                .any(|path| path.starts_with(directory))
        }) {
            user_artifact_crates.insert(dependency.crate_identity);
        }
    }
    if definitions
        .graph
        .external_definitions
        .iter()
        .any(|definition| !loaded_identities.contains(&definition.key.crate_identity))
    {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }

    let resolutions = tcx.resolutions(());
    let mut loads = BTreeMap::new();
    let mut bindings = Vec::new();
    let mut mapped_definitions = HashSet::new();
    for definition in definitions
        .graph
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::ExternCrate)
    {
        let local = *local_definitions
            .get(definition.id.0 as usize)
            .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
        if tcx.def_kind(local) != DefKind::ExternCrate {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        let target = if let Some(&crate_num) = resolutions.extern_crate_map.get(&local) {
            mapped_definitions.insert(local);
            let root = resolutions
                .extern_crate_loads
                .get(&local)
                .copied()
                .filter(|root| root.crate_num == crate_num)
                .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
            ExternalCrateBindingTarget::External(load(tcx, root, &loaded, &mut loads)?)
        } else if matches!(
            tcx.hir_expect_item(local).kind,
            ItemKind::ExternCrate(Some(name), _) if name == kw::SelfLower
        ) {
            ExternalCrateBindingTarget::SelfCrate
        } else {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        };
        bindings.push(ExternalCrateBinding {
            definition: definition.id,
            target,
        });
    }
    if resolutions.extern_crate_map.len() != resolutions.extern_crate_loads.len()
        || resolutions.extern_crate_map.items().any(|(&local, _)| {
            !mapped_definitions.contains(&local)
                || !resolutions.extern_crate_loads.contains_key(&local)
                || definitions
                    .definition_id(local)
                    .and_then(|id| definitions.graph.definitions.get(id.0 as usize))
                    .is_none_or(|definition| definition.kind != DefinitionKind::ExternCrate)
        })
    {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }

    let mut activations = BTreeSet::new();
    for activation in &resolutions.extern_prelude_path_activations {
        let range = original_span_range(
            compiler,
            &source.offsets,
            activation.path_span.source_callsite(),
        )
        .map_err(|_| RetentionError::IncompleteExternalCrateConstraints)?;
        activations.insert(ExternalCrateActivation {
            source: Some(source_site_owner(&source_sites, range)?),
            load: load(tcx, activation.load, &loaded, &mut loads)?,
        });
    }
    let cold_source_free = tcx.source_free_crate_activations(());
    let warm_source_free = tcx.source_free_crate_activations(());
    if !std::ptr::eq(cold_source_free, warm_source_free) {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }
    for &root in cold_source_free {
        activations.insert(ExternalCrateActivation {
            source: None,
            load: load(tcx, root, &loaded, &mut loads)?,
        });
    }

    let cold_generated = tcx.compiler_generated_crate_activations(());
    let warm_generated = tcx.compiler_generated_crate_activations(());
    if !std::ptr::eq(cold_generated, warm_generated) {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }
    let compiler_generated_activations = cold_generated
        .iter()
        .map(|activation| {
            let condition = activation
                .condition
                .map(|crate_num| {
                    loaded
                        .get(&crate_num)
                        .map(|dependency| dependency.crate_identity)
                        .ok_or(RetentionError::IncompleteExternalCrateConstraints)
                })
                .transpose()?;
            Ok(CompilerGeneratedCrateActivation {
                load: load(tcx, activation.load, &loaded, &mut loads)?,
                condition,
            })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    if compiler_generated_activations.len() != cold_generated.len() {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }

    let mut providers = BTreeSet::new();
    let mut requirements = BTreeSet::new();
    for (&crate_num, dependency) in &loaded {
        let cold = tcx.compiler_metadata_providers(crate_num);
        let warm = tcx.compiler_metadata_providers(crate_num);
        if !std::ptr::eq(cold, warm) {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        for &provider in cold {
            let kind = match provider {
                CompilerMetadataProvider::CompilerBuiltins => {
                    ExternalMetadataProviderKind::CompilerBuiltins
                }
                CompilerMetadataProvider::PanicRuntime => {
                    ExternalMetadataProviderKind::PanicRuntime
                }
                CompilerMetadataProvider::ProfilerRuntime => {
                    ExternalMetadataProviderKind::ProfilerRuntime
                }
                CompilerMetadataProvider::ExternalNativeLink => {
                    ExternalMetadataProviderKind::ExternalNativeLink
                }
                CompilerMetadataProvider::GlobalAllocator => {
                    ExternalMetadataProviderKind::GlobalAllocator
                }
                CompilerMetadataProvider::AllocErrorHandler => {
                    ExternalMetadataProviderKind::AllocErrorHandler
                }
                CompilerMetadataProvider::DefaultLibAllocator => {
                    ExternalMetadataProviderKind::DefaultLibAllocator
                }
                CompilerMetadataProvider::WeakLangItem(item) => {
                    ExternalMetadataProviderKind::WeakLangItem(item as u32)
                }
                CompilerMetadataProvider::ExternallyImplementableItemImplementation => {
                    ExternalMetadataProviderKind::ExternallyImplementableItemImplementation
                }
            };
            if !providers.insert(ExternalMetadataProvider {
                crate_identity: dependency.crate_identity,
                kind,
            }) {
                return Err(RetentionError::IncompleteExternalCrateConstraints);
            }
        }
        let cold = tcx.compiler_metadata_requirements(crate_num);
        let warm = tcx.compiler_metadata_requirements(crate_num);
        if !std::ptr::eq(cold, warm) {
            return Err(RetentionError::IncompleteExternalCrateConstraints);
        }
        for &requirement in cold {
            let kind = match requirement {
                CompilerMetadataRequirement::Allocator => {
                    ExternalMetadataRequirementKind::Allocator
                }
                CompilerMetadataRequirement::PanicRuntime => {
                    ExternalMetadataRequirementKind::PanicRuntime
                }
                CompilerMetadataRequirement::MissingLangItem(item) => {
                    ExternalMetadataRequirementKind::MissingLangItem(item as u32)
                }
            };
            requirements.insert(ExternalMetadataRequirement {
                crate_identity: dependency.crate_identity,
                kind,
            });
        }
    }

    let mut local_requirements = BTreeSet::new();
    if find_attr!(tcx, crate, NeedsAllocator) {
        local_requirements.insert(LocalMetadataRequirement {
            source: None,
            kind: ExternalMetadataRequirementKind::Allocator,
        });
    }
    if find_attr!(tcx, crate, NeedsPanicRuntime) {
        local_requirements.insert(LocalMetadataRequirement {
            source: None,
            kind: ExternalMetadataRequirementKind::PanicRuntime,
        });
    }
    let local_missing = tcx
        .lang_items()
        .missing
        .iter()
        .copied()
        .filter(|item| item.is_weak())
        .collect::<Vec<_>>();
    for &item in &local_missing {
        if item == LangItem::EhPersonality {
            local_requirements.insert(LocalMetadataRequirement {
                source: None,
                kind: ExternalMetadataRequirementKind::MissingLangItem(item as u32),
            });
        }
    }
    for (definition, &local) in definitions.graph.definitions.iter().zip(local_definitions) {
        if definition
            .parent
            .and_then(|parent| definitions.graph.definitions.get(parent.0 as usize))
            .is_none_or(|parent| parent.kind != DefinitionKind::ForeignModule)
        {
            continue;
        }
        let rustc_hir::Node::ForeignItem(_) = tcx.hir_node_by_def_id(local) else {
            continue;
        };
        let Some(item) = find_attr!(tcx, local, Lang(item) => item) else {
            continue;
        };
        let item = *item;
        if !item.is_weak() || !local_missing.contains(&item) || item == LangItem::EhPersonality {
            continue;
        }
        let source = *definition_units
            .get(definition.id.0 as usize)
            .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
        local_requirements.insert(LocalMetadataRequirement {
            source: Some(source),
            kind: ExternalMetadataRequirementKind::MissingLangItem(item as u32),
        });
    }
    if local_missing.iter().any(|&item| {
        let kind = ExternalMetadataRequirementKind::MissingLangItem(item as u32);
        !local_requirements
            .iter()
            .any(|requirement| requirement.kind == kind)
    }) {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }

    bindings.sort();
    let mut loaded_crates = loaded.into_values().collect::<Vec<_>>();
    loaded_crates.sort();
    Ok(ExternalCrateFacts {
        loaded_crates,
        user_artifact_crates: user_artifact_crates.into_iter().collect(),
        bindings,
        activations: activations.into_iter().collect(),
        compiler_generated_activations: compiler_generated_activations.into_iter().collect(),
        providers: providers.into_iter().collect(),
        requirements: requirements.into_iter().collect(),
        local_requirements: local_requirements.into_iter().collect(),
    })
}

#[cfg(not(rust_item_dependencies_patched))]
pub(super) fn collect_external_crate_facts(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _definitions: &CollectedDefinitions,
    _local_definitions: &[LocalDefId],
    _definition_units: &[SourceUnitId],
    _external_artifact_directory: Option<&Path>,
) -> Result<ExternalCrateFacts, RetentionError> {
    Ok(ExternalCrateFacts::default())
}

pub(crate) fn external_compiler_expectation(
    graph: &DependencyGraph,
    constraints: &SourceConstraints,
    retention: &Retention,
) -> Result<ExternalCompilerExpectation, RetentionError> {
    let loaded = external_loaded_crates(&constraints.external_crates)?;
    let metadata = external_compiler_metadata(&constraints.external_crates, &loaded)?;
    let external_crates = retention
        .compile_required
        .iter()
        .filter_map(|node| match node {
            GraphNode::ExternalDefinition(definition) => Some(*definition),
            _ => None,
        })
        .map(|definition| {
            let definition = graph
                .definitions
                .external_definitions
                .get(definition.0 as usize)
                .filter(|candidate| candidate.id == definition)
                .ok_or(RetentionError::IncompleteExternalCrateConstraints)?;
            Ok(ExternalCrateDependency {
                crate_identity: definition.key.crate_identity,
                kind: *loaded
                    .get(&definition.key.crate_identity)
                    .ok_or(RetentionError::IncompleteExternalCrateConstraints)?,
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(ExternalCompilerExpectation {
        metadata,
        external_crates,
    })
}

pub(crate) fn external_compiler_observation(
    constraints: &SourceConstraints,
) -> Result<ExternalCompilerObservation, RetentionError> {
    let loaded = external_loaded_crates(&constraints.external_crates)?;
    let metadata = external_compiler_metadata(&constraints.external_crates, &loaded)?;
    #[cfg(test)]
    let metadata = {
        let mut metadata = metadata;
        if omit_external_compiler_metadata_fact() {
            let fact = metadata
                .iter()
                .next()
                .copied()
                .expect("the mutation fixture must observe external compiler metadata");
            metadata.remove(&fact);
        }
        metadata
    };
    Ok(ExternalCompilerObservation {
        metadata,
        loaded_crates: loaded
            .into_iter()
            .map(|(crate_identity, kind)| ExternalCrateDependency {
                crate_identity,
                kind,
            })
            .collect(),
    })
}

pub(crate) fn external_compiler_outcome_difference(
    original: &ExternalCompilerExpectation,
    reduced: &ExternalCompilerObservation,
) -> Option<ExternalCompilerOutcomeDifference> {
    if original.metadata != reduced.metadata {
        return Some(ExternalCompilerOutcomeDifference::Metadata {
            original: original.clone(),
            reduced: reduced.clone(),
        });
    }
    let reduced_crates = reduced
        .loaded_crates
        .iter()
        .map(|dependency| (dependency.crate_identity, dependency.kind))
        .collect::<BTreeMap<_, _>>();
    original.external_crates.iter().find_map(|dependency| {
        let reduced = reduced_crates.get(&dependency.crate_identity).copied();
        (reduced != Some(dependency.kind)).then_some(
            ExternalCompilerOutcomeDifference::ExternalCrate {
                crate_identity: dependency.crate_identity,
                original: dependency.kind,
                reduced,
            },
        )
    })
}

fn external_loaded_crates(
    facts: &ExternalCrateFacts,
) -> Result<BTreeMap<u64, ExternalDependencyKind>, RetentionError> {
    let loaded = facts
        .loaded_crates
        .iter()
        .map(|dependency| (dependency.crate_identity, dependency.kind))
        .collect::<BTreeMap<_, _>>();
    (loaded.len() == facts.loaded_crates.len())
        .then_some(loaded)
        .ok_or(RetentionError::IncompleteExternalCrateConstraints)
}

fn external_compiler_metadata(
    facts: &ExternalCrateFacts,
    loaded: &BTreeMap<u64, ExternalDependencyKind>,
) -> Result<BTreeSet<ExternalCompilerMetadataFact>, RetentionError> {
    let metadata_providers = facts.providers.iter().copied().collect::<BTreeSet<_>>();
    if metadata_providers.len() != facts.providers.len()
        || !order_sensitive_provider_identities_are_unique(&metadata_providers)
    {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }
    let requirements = facts.requirements.iter().copied().collect::<BTreeSet<_>>();
    let local_requirements = facts
        .local_requirements
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if requirements.len() != facts.requirements.len()
        || local_requirements.len() != facts.local_requirements.len()
        || requirements
            .iter()
            .any(|requirement| !loaded.contains_key(&requirement.crate_identity))
    {
        return Err(RetentionError::IncompleteExternalCrateConstraints);
    }
    let mut metadata = metadata_providers
        .into_iter()
        .map(|provider| {
            Ok(ExternalCompilerMetadataFact::Provider {
                crate_identity: provider.crate_identity,
                provider: provider.kind,
                dependency_kind: *loaded
                    .get(&provider.crate_identity)
                    .ok_or(RetentionError::IncompleteExternalCrateConstraints)?,
            })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    metadata.extend(
        requirements
            .into_iter()
            .map(|requirement| requirement.kind)
            .chain(
                local_requirements
                    .into_iter()
                    .map(|requirement| requirement.kind),
            )
            .map(ExternalCompilerMetadataFact::Requirement),
    );
    Ok(metadata)
}

fn order_sensitive_provider_identities_are_unique(
    providers: &BTreeSet<ExternalMetadataProvider>,
) -> bool {
    [
        ExternalMetadataProviderKind::CompilerBuiltins,
        ExternalMetadataProviderKind::ProfilerRuntime,
        ExternalMetadataProviderKind::DefaultLibAllocator,
    ]
    .into_iter()
    .all(|kind| {
        providers
            .iter()
            .filter(|provider| provider.kind == kind)
            .map(|provider| provider.crate_identity)
            .collect::<BTreeSet<_>>()
            .len()
            <= 1
    })
}

pub(super) fn validate_external_crate_facts(
    source: &SourceInventory,
    graph: &DependencyGraph,
    definition_units: &[SourceUnitId],
    facts: &ExternalCrateFacts,
) -> Result<Vec<CompilerCrateLoadDisjunction>, RetentionError> {
    let incomplete = RetentionError::IncompleteExternalCrateConstraints;
    let loaded = facts
        .loaded_crates
        .iter()
        .map(|dependency| (dependency.crate_identity, dependency.kind))
        .collect::<BTreeMap<_, _>>();
    if loaded.len() != facts.loaded_crates.len()
        || graph
            .definitions
            .external_definitions
            .iter()
            .any(|definition| !loaded.contains_key(&definition.key.crate_identity))
    {
        return Err(incomplete);
    }

    let validate_load = |load: &ExternalCrateLoad| -> Result<(), RetentionError> {
        let closure = load
            .closure
            .iter()
            .map(|dependency| (dependency.crate_identity, dependency.kind))
            .collect::<BTreeMap<_, _>>();
        if load.closure.is_empty()
            || closure.len() != load.closure.len()
            || closure.get(&load.direct.crate_identity) != Some(&load.direct.kind)
            || load
                .closure
                .iter()
                .filter(|dependency| **dependency == load.direct)
                .count()
                != 1
            || closure.iter().any(|(identity, kind)| {
                loaded
                    .get(identity)
                    .is_none_or(|loaded_kind| loaded_kind < kind)
            })
        {
            return Err(incomplete);
        }
        Ok(())
    };

    let expected_bindings = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::ExternCrate)
        .map(|definition| definition.id)
        .collect::<BTreeSet<_>>();
    let actual_bindings = facts
        .bindings
        .iter()
        .map(|binding| binding.definition)
        .collect::<BTreeSet<_>>();
    if expected_bindings != actual_bindings || actual_bindings.len() != facts.bindings.len() {
        return Err(incomplete);
    }

    let mut source_loads = BTreeSet::new();
    for binding in &facts.bindings {
        definition_units
            .get(binding.definition.0 as usize)
            .ok_or(incomplete)?;
        match &binding.target {
            ExternalCrateBindingTarget::SelfCrate => {}
            ExternalCrateBindingTarget::External(load) => {
                validate_load(load)?;
                source_loads.insert((
                    CompilerCrateLoadCarrier::Definition(binding.definition),
                    load.clone(),
                ));
            }
        }
    }

    let activations = facts.activations.iter().collect::<BTreeSet<_>>();
    if activations.len() != facts.activations.len() {
        return Err(incomplete);
    }
    let mut source_free_loads = BTreeSet::new();
    for activation in &facts.activations {
        validate_load(&activation.load)?;
        if let Some(unit) = activation.source {
            if source
                .units
                .get(unit.0 as usize)
                .is_none_or(|unit| unit.cfg_state != CfgState::Active)
            {
                return Err(incomplete);
            }
            source_loads.insert((
                CompilerCrateLoadCarrier::Source(unit),
                activation.load.clone(),
            ));
        } else {
            source_free_loads.insert(activation.load.clone());
        }
    }

    let generated_activations = facts
        .compiler_generated_activations
        .iter()
        .collect::<BTreeSet<_>>();
    if generated_activations.len() != facts.compiler_generated_activations.len() {
        return Err(incomplete);
    }
    for activation in &facts.compiler_generated_activations {
        validate_load(&activation.load)?;
        if activation
            .condition
            .is_some_and(|identity| !loaded.contains_key(&identity))
        {
            return Err(incomplete);
        }
    }

    let classified_crates = facts
        .bindings
        .iter()
        .filter_map(|binding| match &binding.target {
            ExternalCrateBindingTarget::SelfCrate => None,
            ExternalCrateBindingTarget::External(load) => Some(load),
        })
        .chain(facts.activations.iter().map(|activation| &activation.load))
        .chain(
            facts
                .compiler_generated_activations
                .iter()
                .map(|activation| &activation.load),
        )
        .flat_map(|load| {
            load.closure
                .iter()
                .map(|dependency| dependency.crate_identity)
        })
        .collect::<BTreeSet<_>>();
    if classified_crates != loaded.keys().copied().collect() {
        return Err(incomplete);
    }

    // Compiler-generated loads are monotone positive consequences of either
    // the local crate/compiler settings or an already-loaded external crate.
    // Propagate each generated load to the same source that loads its
    // condition. A condition can be present through any dependency kind; that
    // is the compiler's injection contract and is intentionally distinct from
    // the strength checks used to satisfy provider requirements below.
    loop {
        let source_count = source_loads.len();
        let source_free_count = source_free_loads.len();
        for activation in &facts.compiler_generated_activations {
            let Some(condition) = activation.condition else {
                source_free_loads.insert(activation.load.clone());
                continue;
            };
            if source_free_loads.iter().any(|load| {
                load.closure
                    .iter()
                    .any(|dependency| dependency.crate_identity == condition)
            }) {
                source_free_loads.insert(activation.load.clone());
            }
            let triggering_sources = source_loads
                .iter()
                .filter_map(|(carrier, load)| {
                    load.closure
                        .iter()
                        .any(|dependency| dependency.crate_identity == condition)
                        .then_some(*carrier)
                })
                .collect::<Vec<_>>();
            for carrier in triggering_sources {
                source_loads.insert((carrier, activation.load.clone()));
            }
        }
        if source_loads.len() == source_count && source_free_loads.len() == source_free_count {
            break;
        }
    }

    let satisfies = |load: &ExternalCrateLoad, required: ExternalCrateDependency| {
        load.closure.iter().any(|dependency| {
            dependency.crate_identity == required.crate_identity && dependency.kind >= required.kind
        })
    };

    let providers = facts.providers.iter().copied().collect::<BTreeSet<_>>();
    if providers.len() != facts.providers.len()
        || !order_sensitive_provider_identities_are_unique(&providers)
        || providers
            .iter()
            .any(|provider| !loaded.contains_key(&provider.crate_identity))
    {
        return Err(incomplete);
    }
    let user_artifact_crates = facts
        .user_artifact_crates
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if user_artifact_crates.len() != facts.user_artifact_crates.len()
        || user_artifact_crates
            .iter()
            .any(|identity| !loaded.contains_key(identity))
    {
        return Err(incomplete);
    }
    for provider in providers.iter().filter(|provider| {
        provider.kind == ExternalMetadataProviderKind::ExternalNativeLink
            && user_artifact_crates.contains(&provider.crate_identity)
    }) {
        let required = ExternalCrateDependency {
            crate_identity: provider.crate_identity,
            kind: *loaded.get(&provider.crate_identity).ok_or(incomplete)?,
        };
        let fixed_source_load = source_loads.iter().any(|(carrier, load)| {
            matches!(carrier, CompilerCrateLoadCarrier::Source(unit)
                if source.units[unit.0 as usize].kind
                    == crate::source::WrittenUnitKind::CrateRoot)
                && satisfies(load, required)
        });
        if !fixed_source_load
            && !source_free_loads
                .iter()
                .any(|load| satisfies(load, required))
        {
            return Err(RetentionError::UnsupportedExternalNativeLink);
        }
    }
    let metadata_requirements = facts.requirements.iter().copied().collect::<BTreeSet<_>>();
    if metadata_requirements.len() != facts.requirements.len()
        || metadata_requirements
            .iter()
            .any(|requirement| !loaded.contains_key(&requirement.crate_identity))
    {
        return Err(incomplete);
    }
    let local_requirements = facts
        .local_requirements
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if local_requirements.len() != facts.local_requirements.len()
        || local_requirements.iter().any(|requirement| {
            requirement.source.is_some_and(|unit| {
                source
                    .units
                    .get(unit.0 as usize)
                    .is_none_or(|unit| unit.cfg_state != CfgState::Active)
            })
        })
    {
        return Err(incomplete);
    }

    let mut requirements = BTreeSet::new();
    for definition in &graph.definitions.external_definitions {
        let required = ExternalCrateDependency {
            crate_identity: definition.key.crate_identity,
            kind: *loaded
                .get(&definition.key.crate_identity)
                .ok_or(incomplete)?,
        };
        requirements.insert((Some(GraphNode::ExternalDefinition(definition.id)), required));
    }
    for provider in providers {
        let required = ExternalCrateDependency {
            crate_identity: provider.crate_identity,
            kind: *loaded.get(&provider.crate_identity).ok_or(incomplete)?,
        };
        requirements.insert((None, required));
    }

    let mut disjunctions = BTreeSet::new();
    for (trigger, required) in requirements {
        if source_free_loads
            .iter()
            .any(|load| satisfies(load, required))
        {
            continue;
        }
        let choices = source_loads
            .iter()
            .filter_map(|(carrier, load)| satisfies(load, required).then_some(*carrier))
            .collect::<BTreeSet<_>>();
        if choices.is_empty() {
            return Err(incomplete);
        }
        disjunctions.insert(CompilerCrateLoadDisjunction {
            trigger,
            choices: choices.into_iter().collect(),
        });
    }
    let requirement_kinds = metadata_requirements
        .iter()
        .map(|requirement| requirement.kind)
        .chain(
            local_requirements
                .iter()
                .map(|requirement| requirement.kind),
        )
        .collect::<BTreeSet<_>>();
    for kind in requirement_kinds {
        if local_requirements
            .iter()
            .any(|requirement| requirement.kind == kind && requirement.source.is_none())
        {
            continue;
        }
        let carriers = metadata_requirements
            .iter()
            .filter(|requirement| requirement.kind == kind)
            .map(|requirement| requirement.crate_identity)
            .collect::<BTreeSet<_>>();
        if source_free_loads.iter().any(|load| {
            load.closure
                .iter()
                .any(|dependency| carriers.contains(&dependency.crate_identity))
        }) {
            continue;
        }
        let mut choices = local_requirements
            .iter()
            .filter_map(|requirement| {
                (requirement.kind == kind)
                    .then_some(requirement.source)
                    .flatten()
                    .map(CompilerCrateLoadCarrier::Source)
            })
            .collect::<BTreeSet<_>>();
        choices.extend(source_loads.iter().filter_map(|(carrier, load)| {
            load.closure
                .iter()
                .any(|dependency| carriers.contains(&dependency.crate_identity))
                .then_some(*carrier)
        }));
        if choices.is_empty() {
            return Err(incomplete);
        }
        disjunctions.insert(CompilerCrateLoadDisjunction {
            trigger: None,
            choices: choices.into_iter().collect(),
        });
    }
    Ok(disjunctions.into_iter().collect())
}
