//! Owned monomorphization nodes and dependencies rooted at the program entry.

use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use crate::definitions::{CollectedDefinitions, DefinitionError};
use crate::dependency_graph::{DependencyEdge, MonoId, MonoNode, ProofNode, RootRecord};
use crate::graph::DefinitionId;
use crate::source::SourceInventory;

#[cfg(rust_item_dependencies_patched)]
use std::collections::{HashSet, VecDeque};

#[cfg(rust_item_dependencies_patched)]
use rustc_hir::def::DefKind;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mir;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, GlobalId};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::mono::{
    CollectionMode, MonoItem, MonoProofUse, MonoSuccessors, MonoTraceCollection, MonoTraceNode,
    MonoTraceRoot, MonoTraceSite, MonoUseCause,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::adjustment::PointerCoercion;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{self, Instance};
#[cfg(rust_item_dependencies_patched)]
use rustc_session::config::EntryFnType;
#[cfg(rust_item_dependencies_patched)]
use rustc_span::Span;

#[cfg(rust_item_dependencies_patched)]
use crate::compiler_terms::{CompilerTermError, CompilerTermKind, TermHasher};
#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{
    AllocationDescriptor, AllocationKey, AllocationPathPart, AllocationPathSite, AllocationRootKey,
    DependencyKind, EvidenceOrigin, GraphNode, MonoCollection, MonoDependencyKind, MonoInstanceKey,
    MonoInstanceRole, MonoKey, ObservationSite, RootReason,
};
#[cfg(rust_item_dependencies_patched)]
use crate::graph::DefinitionTarget;
#[cfg(rust_item_dependencies_patched)]
use crate::selection::{SelectionCollectionError, SelectionCollector};
#[cfg(rust_item_dependencies_patched)]
use crate::source::original_span_range;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CollectedMonomorphization {
    pub(crate) proofs: Vec<ProofNode>,
    pub(crate) mono_nodes: Vec<MonoNode>,
    pub(crate) edges: Vec<DependencyEdge>,
    pub(crate) main_definition: DefinitionId,
    pub(crate) main_instance: MonoId,
    pub(crate) compiler_required_roots: Vec<RootRecord>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MonomorphizationError {
    IncompleteObservation,
    QueryFailed,
    CacheMismatch,
    StockEndpointMismatch,
    InvalidRoot,
    InvalidNode,
    InvalidEdge,
    TooManyNodes,
    CompilerTerm,
    Definition,
    Selection,
    AllocationIdentity,
}

impl From<DefinitionError> for MonomorphizationError {
    fn from(_: DefinitionError) -> Self {
        Self::Definition
    }
}

#[cfg(rust_item_dependencies_patched)]
impl From<CompilerTermError> for MonomorphizationError {
    fn from(_: CompilerTermError) -> Self {
        Self::CompilerTerm
    }
}

#[cfg(rust_item_dependencies_patched)]
impl From<SelectionCollectionError> for MonomorphizationError {
    fn from(_: SelectionCollectionError) -> Self {
        Self::Selection
    }
}

#[cfg(not(rust_item_dependencies_patched))]
pub(crate) fn collect_monomorphization(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _definitions: &mut CollectedDefinitions,
) -> Result<CollectedMonomorphization, MonomorphizationError> {
    Err(MonomorphizationError::IncompleteObservation)
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn collect_monomorphization<'a, 'tcx>(
    compiler: &Compiler,
    tcx: TyCtxt<'tcx>,
    source: &SourceInventory,
    definitions: &'a mut CollectedDefinitions,
) -> Result<CollectedMonomorphization, MonomorphizationError> {
    MonoCollector::new(compiler, tcx, source, definitions)?.collect()
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct Seed<'tcx> {
    root: MonoTraceRoot<'tcx>,
    reason: Option<RootReason>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct RawProof<'tcx> {
    from: MonoTraceNode<'tcx>,
    proof: MonoProofUse<'tcx>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RawIdentity<'tcx> {
    Trace(MonoTraceNode<'tcx>),
    Const(GlobalId<'tcx>),
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct RequiredConstEdge<'tcx> {
    from: RawIdentity<'tcx>,
    target: GlobalId<'tcx>,
    request: Option<
        ty::PseudoCanonicalInput<'tcx, (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    >,
    collection: MonoTraceCollection,
    site: Span,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct ConstFunctionEdge<'tcx> {
    from: GlobalId<'tcx>,
    target: Instance<'tcx>,
    request: ty::PseudoCanonicalInput<'tcx, (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    site: Span,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone)]
struct OwnedRawNode<'tcx> {
    raw: RawIdentity<'tcx>,
    key: MonoKey,
    materialized_definition: Option<DefinitionTarget>,
    allocation_observation: Option<AllocationDescriptor>,
}

#[cfg(rust_item_dependencies_patched)]
struct MonoCollector<'a, 'tcx> {
    compiler: &'a Compiler,
    tcx: TyCtxt<'tcx>,
    source: &'a SourceInventory,
    definitions: &'a mut CollectedDefinitions,
    seeds: Vec<Seed<'tcx>>,
    roots: Vec<MonoTraceNode<'tcx>>,
    facts: Vec<rustc_middle::mono::MonoUseFact<'tcx>>,
    proofs: Vec<RawProof<'tcx>>,
    required_consts: Vec<RequiredConstEdge<'tcx>>,
    const_functions: Vec<ConstFunctionEdge<'tcx>>,
    seen: HashSet<(MonoTraceRoot<'tcx>, CollectionMode)>,
    const_active: HashSet<(GlobalId<'tcx>, CollectionMode)>,
    const_done: HashSet<(GlobalId<'tcx>, CollectionMode)>,
}

#[cfg(rust_item_dependencies_patched)]
impl<'a, 'tcx> MonoCollector<'a, 'tcx> {
    fn new(
        compiler: &'a Compiler,
        tcx: TyCtxt<'tcx>,
        source: &'a SourceInventory,
        definitions: &'a mut CollectedDefinitions,
    ) -> Result<Self, MonomorphizationError> {
        let (main, EntryFnType::Main { .. }) =
            tcx.entry_fn(()).ok_or(MonomorphizationError::InvalidRoot)?;
        let main = Instance::mono(tcx, main);
        let start_definition = tcx
            .lang_items()
            .start_fn()
            .ok_or(MonomorphizationError::InvalidRoot)?;
        let output = tcx
            .fn_sig(main.def_id())
            .no_bound_vars()
            .ok_or(MonomorphizationError::InvalidRoot)?
            .output()
            .no_bound_vars()
            .ok_or(MonomorphizationError::InvalidRoot)?;
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let output = tcx
            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(output))
            .map_err(|_| MonomorphizationError::InvalidRoot)?;
        let start = Instance::try_resolve(
            tcx,
            typing_env,
            start_definition,
            tcx.mk_args(&[output.into()]),
        )
        .map_err(|_| MonomorphizationError::InvalidRoot)?
        .ok_or(MonomorphizationError::InvalidRoot)?;

        let mut seeds = vec![
            Seed {
                root: MonoTraceRoot::Fn(main),
                reason: None,
            },
            Seed {
                root: MonoTraceRoot::Fn(start),
                reason: Some(RootReason::StartInstance),
            },
        ];
        for definition in tcx.iter_local_def_id() {
            if !matches!(
                tcx.def_kind(definition),
                DefKind::Static { nested: false, .. }
            ) {
                continue;
            }
            let flags = tcx.codegen_fn_attrs(definition).flags;
            if flags.intersects(CodegenFnAttrFlags::USED_COMPILER | CodegenFnAttrFlags::USED_LINKER)
            {
                seeds.push(Seed {
                    root: MonoTraceRoot::Static {
                        def_id: definition.to_def_id(),
                        trigger_span: tcx.def_span(definition),
                    },
                    reason: Some(RootReason::UsedAttribute),
                });
            }
        }
        Ok(Self {
            compiler,
            tcx,
            source,
            definitions,
            roots: seeds.iter().map(|seed| trace_root(seed.root)).collect(),
            seeds,
            facts: Vec::new(),
            proofs: Vec::new(),
            required_consts: Vec::new(),
            const_functions: Vec::new(),
            seen: HashSet::new(),
            const_active: HashSet::new(),
            const_done: HashSet::new(),
        })
    }

    fn collect(mut self) -> Result<CollectedMonomorphization, MonomorphizationError> {
        let mut queue = VecDeque::new();
        for seed in &self.seeds {
            queue.push_back((seed.root, CollectionMode::UsedItems));
        }
        while let Some((root, mode)) = queue.pop_front() {
            if !self.seen.insert((root, mode)) {
                continue;
            }
            let successors = self.successors(root, mode)?;
            self.facts.extend(successors.facts.iter().copied());
            self.proofs
                .extend(successors.proof_uses.iter().copied().map(|proof| RawProof {
                    from: proof.from,
                    proof,
                }));
            let owner = trace_root(root);
            let (instance, body) = match root {
                MonoTraceRoot::Fn(instance) => (instance, self.tcx.instance_mir(instance.def)),
                MonoTraceRoot::Static { def_id, .. } => {
                    let instance = Instance::mono(self.tcx, def_id);
                    (instance, self.tcx.instance_mir(instance.def))
                }
            };
            let required = self.required_const_edges(
                RawIdentity::Trace(owner),
                instance,
                body,
                trace_collection(mode),
            )?;
            self.validate_associated_const_uses(owner, &required, successors.associated_consts)?;
            for edge in required.iter().copied() {
                self.insert_required_const(edge)?;
            }
            for target in required {
                self.visit_const(target.target, mode)?;
            }
            for item in successors.used {
                queue.push_back((trace_item(item.node, item.span)?, CollectionMode::UsedItems));
            }
            for item in successors.mentioned {
                queue.push_back((
                    trace_item(item.node, item.span)?,
                    CollectionMode::MentionedItems,
                ));
            }
        }
        self.finish()
    }

    fn required_const_edges(
        &self,
        from: RawIdentity<'tcx>,
        instance: Instance<'tcx>,
        body: &mir::Body<'tcx>,
        collection: MonoTraceCollection,
    ) -> Result<Vec<RequiredConstEdge<'tcx>>, MonomorphizationError> {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut edges = Vec::new();
        for operand in body.required_consts() {
            let constant = instance
                .try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    ty::EarlyBinder::bind(self.tcx, operand.const_),
                )
                .map_err(|_| MonomorphizationError::QueryFailed)?;
            let mir::Const::Unevaluated(unevaluated, _) = constant else {
                if matches!(constant, mir::Const::Ty(_, value) if value.try_to_value().is_some()) {
                    continue;
                }
                return Err(MonomorphizationError::IncompleteObservation);
            };
            let target =
                Instance::try_resolve(self.tcx, typing_env, unevaluated.def, unevaluated.args)
                    .map_err(|_| MonomorphizationError::QueryFailed)?
                    .ok_or(MonomorphizationError::IncompleteObservation)?;
            let request = (unevaluated.promoted.is_none()
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
            edges.push(RequiredConstEdge {
                from,
                target: GlobalId {
                    instance: target,
                    promoted: unevaluated.promoted,
                },
                request,
                collection,
                site: operand.span,
            });
        }
        Ok(edges)
    }

    fn validate_associated_const_uses(
        &self,
        owner: MonoTraceNode<'tcx>,
        required: &[RequiredConstEdge<'tcx>],
        observed: &[rustc_middle::mono::MonoAssociatedConstUse<'tcx>],
    ) -> Result<(), MonomorphizationError> {
        let mut expected = Vec::new();
        for edge in required {
            let Some(request) = edge.request else {
                continue;
            };
            let item = (request, trace_site(edge.site));
            if !expected.contains(&item) {
                expected.push(item);
            }
        }
        if expected.len() != observed.len()
            || expected
                .iter()
                .zip(observed)
                .any(|(&(request, site), use_)| {
                    use_.owner != owner || use_.proof_key != request || use_.site != site
                })
        {
            return Err(MonomorphizationError::StockEndpointMismatch);
        }
        Ok(())
    }

    fn visit_const(
        &mut self,
        global_id: GlobalId<'tcx>,
        mode: CollectionMode,
    ) -> Result<(), MonomorphizationError> {
        let key = (global_id, mode);
        if self.const_done.contains(&key) {
            return Ok(());
        }
        if !self.const_active.insert(key) {
            return Err(MonomorphizationError::InvalidEdge);
        }
        if !self.tcx.is_mir_available(global_id.instance.def_id()) {
            if global_id.instance.def_id().is_local() {
                return Err(MonomorphizationError::IncompleteObservation);
            }
            self.const_active.remove(&key);
            self.const_done.insert(key);
            return Ok(());
        }
        let body = if let Some(promoted) = global_id.promoted {
            self.tcx
                .promoted_mir(global_id.instance.def_id())
                .get(promoted)
                .ok_or(MonomorphizationError::IncompleteObservation)?
        } else {
            self.tcx.mir_for_ctfe(global_id.instance.def_id())
        };
        self.collect_const_function_edges(global_id, body)?;
        let required = self.required_const_edges(
            RawIdentity::Const(global_id),
            global_id.instance,
            body,
            trace_collection(mode),
        )?;
        for edge in required.iter().copied() {
            self.insert_required_const(edge)?;
        }
        for target in required {
            self.visit_const(target.target, mode)?;
        }
        self.const_active.remove(&key);
        self.const_done.insert(key);
        Ok(())
    }

    fn collect_const_function_edges(
        &mut self,
        global_id: GlobalId<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> Result<(), MonomorphizationError> {
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
                let operand_type = global_id
                    .instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        ty::EarlyBinder::bind(self.tcx, operand.ty(body, self.tcx)),
                    )
                    .map_err(|_| MonomorphizationError::QueryFailed)?;
                let ty::FnDef(item, arguments) = *operand_type.kind() else {
                    continue;
                };
                let arguments = arguments
                    .no_bound_vars()
                    .ok_or(MonomorphizationError::IncompleteObservation)?;
                if self.tcx.trait_of_assoc(item).is_none() {
                    continue;
                }
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let request = self
                    .tcx
                    .erase_and_anonymize_regions(typing_env.as_query_input((item, arguments)));
                let target = Instance::resolve_for_fn_ptr(
                    self.tcx,
                    request.typing_env,
                    request.value.0,
                    request.value.1,
                )
                .ok_or(MonomorphizationError::IncompleteObservation)?;
                self.insert_const_function(ConstFunctionEdge {
                    from: global_id,
                    target,
                    request,
                    site: statement.source_info.span,
                })?;
            }
        }
        Ok(())
    }

    fn insert_required_const(
        &mut self,
        edge: RequiredConstEdge<'tcx>,
    ) -> Result<(), MonomorphizationError> {
        let same_observation = |existing: &RequiredConstEdge<'tcx>| {
            existing.from == edge.from
                && existing.collection == edge.collection
                && existing.site == edge.site
                && existing.request == edge.request
        };
        if self
            .required_consts
            .iter()
            .any(|existing| same_observation(existing) && existing.target == edge.target)
        {
            return Ok(());
        }
        if edge.request.is_some() && self.required_consts.iter().any(same_observation) {
            return Err(MonomorphizationError::InvalidEdge);
        }
        self.required_consts.push(edge);
        Ok(())
    }

    fn insert_const_function(
        &mut self,
        edge: ConstFunctionEdge<'tcx>,
    ) -> Result<(), MonomorphizationError> {
        if let Some(existing) = self.const_functions.iter().find(|existing| {
            existing.from == edge.from
                && existing.request == edge.request
                && existing.site == edge.site
        }) {
            return (existing.target == edge.target)
                .then_some(())
                .ok_or(MonomorphizationError::InvalidEdge);
        }
        self.const_functions.push(edge);
        Ok(())
    }

    fn successors(
        &self,
        root: MonoTraceRoot<'tcx>,
        mode: CollectionMode,
    ) -> Result<&'tcx MonoSuccessors<'tcx>, MonomorphizationError> {
        let key = (root, mode);
        let cold = self
            .tcx
            .mono_successors(key)
            .map_err(|_| MonomorphizationError::QueryFailed)?;
        let warm = self
            .tcx
            .mono_successors(key)
            .map_err(|_| MonomorphizationError::QueryFailed)?;
        if !std::ptr::eq(cold, warm) {
            return Err(MonomorphizationError::CacheMismatch);
        }
        if let MonoTraceRoot::Fn(instance) = root {
            let stock = self
                .tcx
                .items_of_instance((instance, mode))
                .map_err(|_| MonomorphizationError::QueryFailed)?;
            if cold.used != stock.0 || cold.mentioned != stock.1 {
                return Err(MonomorphizationError::StockEndpointMismatch);
            }
        }
        validate_fact_endpoints(cold)?;
        Ok(cold)
    }

    fn finish(mut self) -> Result<CollectedMonomorphization, MonomorphizationError> {
        let mut trace_nodes = self.roots.clone();
        for fact in &self.facts {
            push_unique(&mut trace_nodes, fact.from);
            push_unique(&mut trace_nodes, fact.to);
        }
        for proof in &self.proofs {
            push_unique(&mut trace_nodes, proof.from);
        }
        for edge in &self.const_functions {
            push_unique(
                &mut trace_nodes,
                MonoTraceNode::Item(MonoItem::Fn(edge.target)),
            );
        }
        self.validate_memory_references(&trace_nodes)?;

        let allocation_paths = self.allocation_paths(&trace_nodes)?;
        let mut raw_nodes = trace_nodes
            .iter()
            .copied()
            .map(RawIdentity::Trace)
            .collect::<Vec<_>>();
        for edge in &self.required_consts {
            push_unique_identity(&mut raw_nodes, edge.from);
            push_unique_identity(&mut raw_nodes, RawIdentity::Const(edge.target));
        }
        for edge in &self.const_functions {
            push_unique_identity(&mut raw_nodes, RawIdentity::Const(edge.from));
        }
        let mut owned = raw_nodes
            .iter()
            .copied()
            .map(|raw| self.owned_identity(raw, &allocation_paths))
            .collect::<Result<Vec<_>, _>>()?;
        owned.sort_by(|left, right| left.key.cmp(&right.key));
        if let Some(pair) = owned.windows(2).find(|pair| pair[0].key == pair[1].key) {
            return Err(if matches!(&pair[0].key, MonoKey::Allocation(_)) {
                MonomorphizationError::AllocationIdentity
            } else {
                MonomorphizationError::InvalidNode
            });
        }
        let mono_nodes = owned
            .iter()
            .enumerate()
            .map(|(index, node)| {
                Ok(MonoNode {
                    id: MonoId(
                        index
                            .try_into()
                            .map_err(|_| MonomorphizationError::TooManyNodes)?,
                    ),
                    key: node.key.clone(),
                    materialized_definition: node.materialized_definition,
                    allocation_observation: node.allocation_observation.clone(),
                })
            })
            .collect::<Result<Vec<_>, MonomorphizationError>>()?;

        let node_id = |raw| {
            owned
                .iter()
                .position(|node| node.raw == raw)
                .and_then(|index| u32::try_from(index).ok())
                .map(MonoId)
                .ok_or(MonomorphizationError::InvalidNode)
        };
        let mut edges = Vec::new();
        for fact in &self.facts {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(node_id(RawIdentity::Trace(fact.from))?),
                to: GraphNode::Mono(node_id(RawIdentity::Trace(fact.to))?),
                kind: DependencyKind::Mono {
                    relation: dependency_kind(fact.cause),
                    collection: collection(fact.collection),
                },
                sites: vec![observation_site(self.compiler, self.source, fact.site)?],
                evidence: EvidenceOrigin::PatchedObserver,
            });
        }
        for required in &self.required_consts {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(node_id(required.from)?),
                to: GraphNode::Mono(node_id(RawIdentity::Const(required.target))?),
                kind: DependencyKind::Mono {
                    relation: MonoDependencyKind::ConstAllocation,
                    collection: collection(required.collection),
                },
                sites: vec![observation_site(
                    self.compiler,
                    self.source,
                    trace_site(required.site),
                )?],
                evidence: EvidenceOrigin::Derived,
            });
        }
        for function in &self.const_functions {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(node_id(RawIdentity::Const(function.from))?),
                to: GraphNode::Mono(node_id(RawIdentity::Trace(MonoTraceNode::Item(
                    MonoItem::Fn(function.target),
                )))?),
                kind: DependencyKind::Mono {
                    relation: MonoDependencyKind::FunctionPointer,
                    collection: MonoCollection::Mentioned,
                },
                sites: vec![observation_site(
                    self.compiler,
                    self.source,
                    trace_site(function.site),
                )?],
                evidence: EvidenceOrigin::Derived,
            });
        }
        for node in &mono_nodes {
            if let Some(target) = node.materialized_definition {
                edges.push(DependencyEdge {
                    from: GraphNode::Mono(node.id),
                    to: definition_node(target),
                    kind: DependencyKind::MaterializesDefinition,
                    sites: Vec::new(),
                    evidence: EvidenceOrigin::Derived,
                });
            }
        }

        let mut selection = SelectionCollector::new(self.tcx, self.definitions);
        let mut proof_roots = Vec::new();
        for raw in &self.proofs {
            let observed = selection.collect_mono_proof_use(raw.proof)?;
            proof_roots.push((
                raw.proof,
                node_id(RawIdentity::Trace(raw.from))?,
                observed,
                EvidenceOrigin::PatchedObserver,
            ));
            let supertraits = match raw.proof.proof {
                rustc_middle::mono::MonoProof::TraitSelection { proof_key }
                    if raw.proof.cause == MonoUseCause::VTableConstruction =>
                {
                    selection.collect_supertrait_selections(proof_key)?
                }
                rustc_middle::mono::MonoProof::AssociatedItem { selection_key, .. } => {
                    selection.collect_supertrait_selections(selection_key)?
                }
                _ => Vec::new(),
            };
            for supertrait in supertraits {
                proof_roots.push((
                    raw.proof,
                    node_id(RawIdentity::Trace(raw.from))?,
                    supertrait,
                    EvidenceOrigin::Derived,
                ));
            }
        }
        let mut derived_proofs = Vec::new();
        for required in &self.required_consts {
            let Some(request) = required.request else {
                continue;
            };
            let raw_instance = self
                .tcx
                .resolve_instance_raw(request)
                .map_err(|_| MonomorphizationError::QueryFailed)?
                .ok_or(MonomorphizationError::IncompleteObservation)?;
            if raw_instance != required.target.instance {
                return Err(MonomorphizationError::StockEndpointMismatch);
            }
            let observed = selection.collect_associated_item(request, required.target.instance)?;
            let selection_key = associated_selection_key(self.tcx, request)?;
            derived_proofs.push((
                node_id(RawIdentity::Const(required.target))?,
                observed,
                MonoDependencyKind::ConstAllocation,
                MonoCollection::Mentioned,
                trace_site(required.site),
                EvidenceOrigin::Derived,
            ));
            for supertrait in selection.collect_supertrait_selections(selection_key)? {
                derived_proofs.push((
                    node_id(RawIdentity::Const(required.target))?,
                    supertrait,
                    MonoDependencyKind::ConstAllocation,
                    MonoCollection::Mentioned,
                    trace_site(required.site),
                    EvidenceOrigin::Derived,
                ));
            }
        }
        for function in &self.const_functions {
            let observed = selection.collect_associated_item(function.request, function.target)?;
            let selection_key = associated_selection_key(self.tcx, function.request)?;
            derived_proofs.push((
                node_id(RawIdentity::Const(function.from))?,
                observed,
                MonoDependencyKind::FunctionPointer,
                MonoCollection::Mentioned,
                trace_site(function.site),
                EvidenceOrigin::Derived,
            ));
            for supertrait in selection.collect_supertrait_selections(selection_key)? {
                derived_proofs.push((
                    node_id(RawIdentity::Const(function.from))?,
                    supertrait,
                    MonoDependencyKind::FunctionPointer,
                    MonoCollection::Mentioned,
                    trace_site(function.site),
                    EvidenceOrigin::Derived,
                ));
            }
        }
        let selected = selection.finish()?;
        for (proof_use, from, observed, evidence) in proof_roots {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(from),
                to: GraphNode::Proof(selected.canonical_id(observed)?),
                kind: DependencyKind::SelectionProof {
                    relation: dependency_kind(proof_use.cause),
                    collection: collection(proof_use.collection),
                },
                sites: vec![observation_site(
                    self.compiler,
                    self.source,
                    proof_use.site,
                )?],
                evidence,
            });
        }
        for (from, observed, relation, collection, site, evidence) in derived_proofs {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(from),
                to: GraphNode::Proof(selected.canonical_id(observed)?),
                kind: DependencyKind::SelectionProof {
                    relation,
                    collection,
                },
                sites: vec![observation_site(self.compiler, self.source, site)?],
                evidence,
            });
        }
        let (proofs, proof_edges) = selected.into_graph_parts();
        edges.extend(proof_edges);

        let main_raw = trace_root(self.seeds[0].root);
        let main_instance = node_id(RawIdentity::Trace(main_raw))?;
        let main_definition = self
            .tcx
            .entry_fn(())
            .and_then(|(definition, _)| definition.as_local())
            .and_then(|definition| self.definitions.definition_id(definition))
            .ok_or(MonomorphizationError::InvalidRoot)?;
        let compiler_required_roots = self
            .seeds
            .iter()
            .filter_map(|seed| seed.reason.map(|reason| (seed.root, reason)))
            .map(|(root, reason)| {
                Ok(RootRecord {
                    node: node_id(RawIdentity::Trace(trace_root(root)))?,
                    reason,
                })
            })
            .collect::<Result<Vec<_>, MonomorphizationError>>()?;

        Ok(CollectedMonomorphization {
            proofs,
            mono_nodes,
            edges,
            main_definition,
            main_instance,
            compiler_required_roots,
        })
    }

    fn allocation_paths(
        &mut self,
        raw_nodes: &[MonoTraceNode<'tcx>],
    ) -> Result<Vec<(AllocId, AllocationKey)>, MonomorphizationError> {
        let expected = raw_nodes
            .iter()
            .filter(|node| matches!(node, MonoTraceNode::Allocation(_)))
            .count();
        let mut paths = Vec::<(AllocId, AllocationKey)>::new();
        let mut changed = true;
        while changed {
            changed = false;
            for index in 0..self.facts.len() {
                let fact = self.facts[index];
                let MonoTraceNode::Allocation(target) = fact.to else {
                    continue;
                };
                if !matches!(
                    fact.cause,
                    MonoUseCause::ConstAllocation | MonoUseCause::AllocationReference
                ) {
                    return Err(MonomorphizationError::InvalidEdge);
                }
                let (root, mut path) = match fact.from {
                    MonoTraceNode::Allocation(source) => {
                        let Some((_, key)) = paths.iter().find(|(id, _)| *id == source) else {
                            continue;
                        };
                        (key.root.clone(), key.path.clone())
                    }
                    source => (self.allocation_root(source)?, Vec::new()),
                };
                let path_site = allocation_path_site(self.compiler, self.source, fact.site)?;
                path.push(AllocationPathPart {
                    relation: dependency_kind(fact.cause),
                    collection: collection(fact.collection),
                    site: path_site,
                    same_role_ordinal: self.allocation_ordinal(index, path_site)?,
                });
                let candidate = AllocationKey { root, path };
                match paths.iter_mut().find(|(id, _)| *id == target) {
                    Some((_, existing)) if candidate < *existing => {
                        *existing = candidate;
                        changed = true;
                    }
                    None => {
                        paths.push((target, candidate));
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
        if paths.len() != expected {
            return Err(MonomorphizationError::AllocationIdentity);
        }
        Ok(paths)
    }

    fn allocation_ordinal(
        &self,
        index: usize,
        site: AllocationPathSite,
    ) -> Result<u32, MonomorphizationError> {
        let fact = self.facts[index];
        let mut targets = Vec::new();
        for previous in &self.facts[..index] {
            if previous.from == fact.from
                && previous.cause == fact.cause
                && previous.collection == fact.collection
                && allocation_path_site(self.compiler, self.source, previous.site)? == site
                && let MonoTraceNode::Allocation(target) = previous.to
                && !targets.contains(&target)
            {
                targets.push(target);
            }
        }
        targets
            .len()
            .try_into()
            .map_err(|_| MonomorphizationError::TooManyNodes)
    }

    fn validate_memory_references(
        &self,
        nodes: &[MonoTraceNode<'tcx>],
    ) -> Result<(), MonomorphizationError> {
        let mut expected = HashSet::new();
        for &node in nodes {
            let MonoTraceNode::Allocation(parent) = node else {
                continue;
            };
            let GlobalAlloc::Memory(memory) = self.tcx.global_alloc(parent) else {
                continue;
            };
            for &(offset, provenance) in memory.inner().provenance().ptrs().iter() {
                expected.insert((parent, offset.bytes(), provenance.alloc_id()));
            }
        }
        let observed = self
            .facts
            .iter()
            .filter_map(|fact| {
                let MonoTraceNode::Allocation(parent) = fact.from else {
                    return None;
                };
                if !matches!(self.tcx.global_alloc(parent), GlobalAlloc::Memory(_)) {
                    return None;
                }
                match (fact.to, fact.cause, fact.site) {
                    (
                        MonoTraceNode::Allocation(child),
                        MonoUseCause::AllocationReference,
                        MonoTraceSite::AllocationOffset(offset),
                    ) => Some(Ok((parent, offset, child))),
                    _ => Some(Err(MonomorphizationError::InvalidEdge)),
                }
            })
            .collect::<Result<HashSet<_>, _>>()?;
        if observed != expected {
            return Err(MonomorphizationError::StockEndpointMismatch);
        }
        Ok(())
    }

    fn allocation_root(
        &mut self,
        node: MonoTraceNode<'tcx>,
    ) -> Result<AllocationRootKey, MonomorphizationError> {
        Ok(match self.nonallocation_node(node)?.key {
            MonoKey::Instance { instance, role } => AllocationRootKey::Instance { instance, role },
            MonoKey::Static { definition } => AllocationRootKey::Static(definition),
            MonoKey::VTable {
                concrete_type,
                trait_reference,
            } => AllocationRootKey::VTable {
                concrete_type,
                trait_reference,
            },
            MonoKey::Allocation(_) => return Err(MonomorphizationError::InvalidNode),
        })
    }

    fn owned_node(
        &mut self,
        raw: MonoTraceNode<'tcx>,
        paths: &[(AllocId, AllocationKey)],
    ) -> Result<OwnedRawNode<'tcx>, MonomorphizationError> {
        if let MonoTraceNode::Allocation(id) = raw {
            let key = paths
                .iter()
                .find(|(candidate, _)| *candidate == id)
                .map(|(_, key)| key.clone())
                .ok_or(MonomorphizationError::AllocationIdentity)?;
            return Ok(OwnedRawNode {
                raw: RawIdentity::Trace(raw),
                key: MonoKey::Allocation(key),
                materialized_definition: None,
                allocation_observation: Some(self.allocation_descriptor(id)?),
            });
        }
        self.nonallocation_node(raw)
    }

    fn nonallocation_node(
        &mut self,
        raw: MonoTraceNode<'tcx>,
    ) -> Result<OwnedRawNode<'tcx>, MonomorphizationError> {
        let (key, materialized_definition) = match raw {
            MonoTraceNode::Item(MonoItem::Fn(instance)) => {
                let definition = self.definitions.target(self.tcx, instance.def_id())?;
                (
                    MonoKey::Instance {
                        instance: self.instance_key(instance)?,
                        role: MonoInstanceRole::Callable,
                    },
                    Some(definition),
                )
            }
            MonoTraceNode::Item(MonoItem::Static(definition)) => {
                let local = definition
                    .as_local()
                    .and_then(|definition| self.definitions.definition_id(definition))
                    .ok_or(MonomorphizationError::InvalidNode)?;
                let key = self
                    .definitions
                    .identity_key(local)
                    .ok_or(MonomorphizationError::InvalidNode)?
                    .clone();
                (
                    MonoKey::Static { definition: key },
                    Some(DefinitionTarget::Local(local)),
                )
            }
            MonoTraceNode::Item(MonoItem::GlobalAsm(_)) => {
                return Err(MonomorphizationError::IncompleteObservation);
            }
            MonoTraceNode::VTable {
                concrete_ty,
                trait_ref,
            } => {
                let concrete_type = TermHasher::new(self.tcx, self.definitions)
                    .canonicalize(CompilerTermKind::Type, &concrete_ty)?;
                let trait_reference = trait_ref
                    .map(|reference| {
                        TermHasher::new(self.tcx, self.definitions)
                            .canonicalize(CompilerTermKind::TraitGoal, &reference)
                    })
                    .transpose()?;
                (
                    MonoKey::VTable {
                        concrete_type,
                        trait_reference,
                    },
                    None,
                )
            }
            MonoTraceNode::Allocation(_) => return Err(MonomorphizationError::InvalidNode),
        };
        Ok(OwnedRawNode {
            raw: RawIdentity::Trace(raw),
            key,
            materialized_definition,
            allocation_observation: None,
        })
    }

    fn owned_identity(
        &mut self,
        raw: RawIdentity<'tcx>,
        paths: &[(AllocId, AllocationKey)],
    ) -> Result<OwnedRawNode<'tcx>, MonomorphizationError> {
        match raw {
            RawIdentity::Trace(trace) => self.owned_node(trace, paths),
            RawIdentity::Const(global_id) => self.owned_const(global_id),
        }
    }

    fn owned_const(
        &mut self,
        global_id: GlobalId<'tcx>,
    ) -> Result<OwnedRawNode<'tcx>, MonomorphizationError> {
        let definition = self
            .definitions
            .target(self.tcx, global_id.instance.def_id())?;
        Ok(OwnedRawNode {
            raw: RawIdentity::Const(global_id),
            key: MonoKey::Instance {
                instance: self.instance_key(global_id.instance)?,
                role: MonoInstanceRole::Const {
                    promoted: global_id.promoted.map(|promoted| promoted.as_u32()),
                },
            },
            materialized_definition: Some(definition),
            allocation_observation: None,
        })
    }

    fn instance_key(
        &mut self,
        instance: Instance<'tcx>,
    ) -> Result<MonoInstanceKey, MonomorphizationError> {
        let definition = self.definitions.target_key(self.tcx, instance.def_id())?;
        let arguments = TermHasher::new(self.tcx, self.definitions)
            .canonicalize(CompilerTermKind::GenericArguments, &instance.args)?;
        let kind = TermHasher::new(self.tcx, self.definitions)
            .canonicalize(CompilerTermKind::Instance, &instance.def)?;
        Ok(MonoInstanceKey {
            definition,
            arguments,
            kind,
        })
    }

    fn allocation_descriptor(
        &mut self,
        allocation: AllocId,
    ) -> Result<AllocationDescriptor, MonomorphizationError> {
        Ok(match self.tcx.global_alloc(allocation) {
            GlobalAlloc::Memory(_) => AllocationDescriptor::Memory,
            GlobalAlloc::Function { instance } => AllocationDescriptor::Function {
                instance: TermHasher::new(self.tcx, self.definitions)
                    .canonicalize(CompilerTermKind::Instance, &instance)?,
            },
            GlobalAlloc::Static(definition) => AllocationDescriptor::Static {
                definition: self.definitions.target_key(self.tcx, definition)?,
            },
            GlobalAlloc::VTable(concrete, predicates) => AllocationDescriptor::VTable {
                concrete_type: TermHasher::new(self.tcx, self.definitions)
                    .canonicalize(CompilerTermKind::Type, &concrete)?,
                predicates: TermHasher::new(self.tcx, self.definitions)
                    .canonicalize(CompilerTermKind::VTable, &predicates)?,
            },
            GlobalAlloc::TypeId { ty } => AllocationDescriptor::TypeId {
                value_type: TermHasher::new(self.tcx, self.definitions)
                    .canonicalize(CompilerTermKind::Type, &ty)?,
            },
        })
    }
}

#[cfg(rust_item_dependencies_patched)]
fn trace_root(root: MonoTraceRoot<'_>) -> MonoTraceNode<'_> {
    match root {
        MonoTraceRoot::Fn(instance) => MonoTraceNode::Item(MonoItem::Fn(instance)),
        MonoTraceRoot::Static { def_id, .. } => MonoTraceNode::Item(MonoItem::Static(def_id)),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn validate_fact_endpoints(successors: &MonoSuccessors<'_>) -> Result<(), MonomorphizationError> {
    for (collection, endpoints) in [
        (MonoTraceCollection::Used, successors.used),
        (MonoTraceCollection::Mentioned, successors.mentioned),
    ] {
        let mut observed = Vec::new();
        for fact in successors
            .facts
            .iter()
            .filter(|fact| fact.collection == collection)
        {
            let MonoTraceNode::Item(item) = fact.to else {
                continue;
            };
            if !observed.contains(&item) {
                observed.push(item);
            }
        }
        let expected = endpoints.iter().map(|item| item.node).collect::<Vec<_>>();
        if observed != expected {
            return Err(MonomorphizationError::StockEndpointMismatch);
        }
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn trace_item<'tcx>(
    item: MonoItem<'tcx>,
    span: Span,
) -> Result<MonoTraceRoot<'tcx>, MonomorphizationError> {
    match item {
        MonoItem::Fn(instance) => Ok(MonoTraceRoot::Fn(instance)),
        MonoItem::Static(def_id) => Ok(MonoTraceRoot::Static {
            def_id,
            trigger_span: span,
        }),
        MonoItem::GlobalAsm(_) => Err(MonomorphizationError::IncompleteObservation),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn push_unique<'tcx>(nodes: &mut Vec<MonoTraceNode<'tcx>>, node: MonoTraceNode<'tcx>) {
    if !nodes.contains(&node) {
        nodes.push(node);
    }
}

#[cfg(rust_item_dependencies_patched)]
fn push_unique_identity<'tcx>(nodes: &mut Vec<RawIdentity<'tcx>>, node: RawIdentity<'tcx>) {
    if !nodes.contains(&node) {
        nodes.push(node);
    }
}

#[cfg(rust_item_dependencies_patched)]
fn trace_collection(mode: CollectionMode) -> MonoTraceCollection {
    match mode {
        CollectionMode::UsedItems => MonoTraceCollection::Used,
        CollectionMode::MentionedItems => MonoTraceCollection::Mentioned,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn trace_site(span: Span) -> MonoTraceSite {
    if span.is_dummy() {
        MonoTraceSite::CompilerGenerated
    } else {
        MonoTraceSite::Source(span)
    }
}

#[cfg(rust_item_dependencies_patched)]
fn associated_selection_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    request: ty::PseudoCanonicalInput<'tcx, (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
) -> Result<ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>, MonomorphizationError> {
    let trait_id = tcx
        .trait_of_assoc(request.value.0)
        .ok_or(MonomorphizationError::InvalidEdge)?;
    let arguments = tcx
        .try_normalize_erasing_regions(
            request.typing_env,
            ty::Unnormalized::new_wip(request.value.1),
        )
        .map_err(|_| MonomorphizationError::QueryFailed)?;
    Ok(request
        .typing_env
        .as_query_input(ty::TraitRef::from_assoc(tcx, trait_id, arguments)))
}

#[cfg(rust_item_dependencies_patched)]
fn definition_node(target: DefinitionTarget) -> GraphNode {
    match target {
        DefinitionTarget::Local(id) => GraphNode::Definition(id),
        DefinitionTarget::External(id) => GraphNode::ExternalDefinition(id),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn collection(value: MonoTraceCollection) -> MonoCollection {
    match value {
        MonoTraceCollection::Used => MonoCollection::Used,
        MonoTraceCollection::Mentioned => MonoCollection::Mentioned,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn dependency_kind(value: MonoUseCause) -> MonoDependencyKind {
    match value {
        MonoUseCause::DirectCall => MonoDependencyKind::DirectCall,
        MonoUseCause::FunctionPointer => MonoDependencyKind::FunctionPointer,
        MonoUseCause::ClosureFunctionPointer => MonoDependencyKind::ClosureFunctionPointer,
        MonoUseCause::InlineAsmSymbol => MonoDependencyKind::InlineAsmSymbol,
        MonoUseCause::StaticReference => MonoDependencyKind::StaticReference,
        MonoUseCause::ThreadLocalReference => MonoDependencyKind::ThreadLocalReference,
        MonoUseCause::DropGlue => MonoDependencyKind::DropGlue,
        MonoUseCause::VTableConstruction => MonoDependencyKind::VTableConstruction,
        MonoUseCause::VTableMethod => MonoDependencyKind::VTableMethod,
        MonoUseCause::VTableDrop => MonoDependencyKind::VTableDrop,
        MonoUseCause::SupertraitVTable => MonoDependencyKind::SupertraitVTable,
        MonoUseCause::ConstAllocation => MonoDependencyKind::ConstAllocation,
        MonoUseCause::AllocationReference => MonoDependencyKind::AllocationReference,
        MonoUseCause::ThreadLocalShim => MonoDependencyKind::ThreadLocalShim,
        MonoUseCause::CompilerRequirement => MonoDependencyKind::CompilerRequirement,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn observation_site(
    compiler: &Compiler,
    source: &SourceInventory,
    site: MonoTraceSite,
) -> Result<ObservationSite, MonomorphizationError> {
    Ok(match site {
        MonoTraceSite::Source(span) if span.is_dummy() => ObservationSite::CompilerGenerated,
        MonoTraceSite::Source(span) => {
            let span = span.source_callsite();
            let map = compiler.sess.source_map();
            let start = map.lookup_byte_offset(span.lo());
            let end = map.lookup_byte_offset(span.hi());
            if start.sf.start_pos != end.sf.start_pos {
                return Err(MonomorphizationError::InvalidEdge);
            }
            if start.sf.name.short().to_string() == "main.rs" {
                ObservationSite::Source(
                    original_span_range(compiler, &source.offsets, span)
                        .map_err(|_| MonomorphizationError::InvalidEdge)?,
                )
            } else {
                ObservationSite::ExternalSource
            }
        }
        MonoTraceSite::AllocationOffset(offset) => ObservationSite::AllocationOffset(offset),
        MonoTraceSite::VTableSlot(slot) => ObservationSite::VTableSlot(slot),
        MonoTraceSite::CompilerGenerated => ObservationSite::CompilerGenerated,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn allocation_path_site(
    compiler: &Compiler,
    source: &SourceInventory,
    site: MonoTraceSite,
) -> Result<AllocationPathSite, MonomorphizationError> {
    Ok(match observation_site(compiler, source, site)? {
        ObservationSite::Source(range) => AllocationPathSite::Source(range),
        ObservationSite::ExternalSource => AllocationPathSite::ExternalSource,
        ObservationSite::AllocationOffset(_) => AllocationPathSite::AllocationReference,
        ObservationSite::CompilerGenerated => AllocationPathSite::CompilerGenerated,
        ObservationSite::VTableSlot(_) => return Err(MonomorphizationError::InvalidEdge),
    })
}
