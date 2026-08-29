//! Owned trait-solver proofs observed during monomorphization.

#![cfg(rust_item_dependencies_patched)]

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def::DefKind;
use rustc_middle::mono::{
    MonoItem, MonoProof, MonoProofUse, MonoTraceCollection, MonoTraceNode, MonoTraceSite,
    MonoUseCause,
};
use rustc_middle::traits::{
    BuiltinImplSource, CodegenAssociatedItemProof, CodegenAssociatedItemProofError,
    CodegenProjectionSource, CodegenProjectionTraceResult, CodegenSelectionProof,
    CodegenSolverTrace, CodegenSpecializationNode, ImplSource,
};
use rustc_middle::ty::{self, Instance, TyCtxt, TypeVisitableExt, Unnormalized, Upcast};
use rustc_serialize::{Encodable, Encoder};

use crate::compiler_terms::{
    CanonicalCompilerTerm, CompilerTermError, CompilerTermKind, TermHasher,
};
use crate::definitions::{CollectedDefinitions, DefinitionError};
use crate::dependency_graph::{
    BuiltinTraitTarget, BuiltinTraitTargetKind, DependencyEdge, DependencyKind, EvidenceOrigin,
    GraphNode, MonoInstanceKey, ProjectionOutcome, ProjectionSourceKind, ProofId, ProofKey,
    ProofNode, ProofNodeKind, ProofRelationKind, SelectionSource, SelectionSourceKind,
    SolverTracePayload, SpecializationNode, SpecializationNodeKind,
};
use crate::graph::DefinitionTarget;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SolverRelationKind {
    TraceObligation,
    TraceTraitSelection,
    TraceProjection,
    TraceFulfillment,
    TraceCycle,
    QueryTraceRoot,
    TraitSelectionNested,
    ProjectionOwner,
    ProjectionSelectedTrait,
    ProjectionNested,
    FulfillmentNested,
    CycleMember,
    AssociatedSelection,
    AssociatedLeaf,
    AssociatedDefining,
    AssociatedFinalizing,
    SpecializationAncestor,
    SelectedImplementation,
    SelectedProjectionItem,
    AutoTraitProof,
    TraitDefinition,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SolverRelationTarget {
    Proof(ProofId),
    Definition(DefinitionTarget),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SolverRelation {
    pub(crate) from: ProofId,
    pub(crate) to: SolverRelationTarget,
    pub(crate) kind: SolverRelationKind,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CollectedSelectionProofs {
    pub(crate) nodes: Vec<ProofNode>,
    pub(crate) relations: Vec<SolverRelation>,
    observed_to_canonical: Vec<ProofId>,
}

impl CollectedSelectionProofs {
    pub(crate) fn canonical_id(
        &self,
        observed: ProofId,
    ) -> Result<ProofId, SelectionCollectionError> {
        remapped(&self.observed_to_canonical, observed)
    }

    pub(crate) fn into_graph_parts(self) -> (Vec<ProofNode>, Vec<DependencyEdge>) {
        let edges = self
            .relations
            .into_iter()
            .map(SolverRelation::into_dependency_edge)
            .collect();
        (self.nodes, edges)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SelectionCollectionError {
    QueryFailed,
    CacheMismatch,
    StockResultMismatch,
    InvalidInput,
    InvalidTrace,
    ConflictingProof,
    TooManyProofs,
    CompilerTerm(CompilerTermError),
    Definition(DefinitionError),
}

impl From<CompilerTermError> for SelectionCollectionError {
    fn from(error: CompilerTermError) -> Self {
        Self::CompilerTerm(error)
    }
}

impl From<DefinitionError> for SelectionCollectionError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

pub(crate) struct SelectionCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    definitions: &'a mut CollectedDefinitions,
    nodes: Vec<ProofNode>,
    ids: BTreeMap<ProofKey, ProofId>,
    relations: BTreeSet<SolverRelation>,
    relation_slots: BTreeMap<(ProofId, SolverRelationKind, u32), SolverRelationTarget>,
    conflicting_relation: bool,
}

impl<'a, 'tcx> SelectionCollector<'a, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, definitions: &'a mut CollectedDefinitions) -> Self {
        Self {
            tcx,
            definitions,
            nodes: Vec::new(),
            ids: BTreeMap::new(),
            relations: BTreeSet::new(),
            relation_slots: BTreeMap::new(),
            conflicting_relation: false,
        }
    }

    pub(crate) fn finish(mut self) -> Result<CollectedSelectionProofs, SelectionCollectionError> {
        if self.conflicting_relation {
            return Err(SelectionCollectionError::ConflictingProof);
        }
        self.insert_projection_owner_relations()?;
        let mut order = (0..self.nodes.len()).collect::<Vec<_>>();
        order.sort_by(|&left, &right| self.nodes[left].key.cmp(&self.nodes[right].key));
        let mut remap = vec![ProofId(0); self.nodes.len()];
        for (new_index, &old_index) in order.iter().enumerate() {
            remap[old_index] = ProofId(ordinal(new_index)?);
        }
        let mut nodes = Vec::with_capacity(self.nodes.len());
        for (new_index, old_index) in order.into_iter().enumerate() {
            let mut node = self.nodes[old_index].clone();
            node.id = ProofId(ordinal(new_index)?);
            remap_node_references(&mut node.kind, &remap)?;
            nodes.push(node);
        }
        let mut relations = Vec::with_capacity(self.relations.len());
        for mut relation in self.relations {
            relation.from = remapped(&remap, relation.from)?;
            if let SolverRelationTarget::Proof(to) = &mut relation.to {
                *to = remapped(&remap, *to)?;
            }
            relations.push(relation);
        }
        relations
            .sort_by_key(|relation| (relation.from, relation.kind, relation.ordinal, relation.to));
        Ok(CollectedSelectionProofs {
            nodes,
            relations,
            observed_to_canonical: remap,
        })
    }

    pub(crate) fn collect_mono_proof_use(
        &mut self,
        proof_use: MonoProofUse<'tcx>,
    ) -> Result<ProofId, SelectionCollectionError> {
        match proof_use.proof {
            MonoProof::TraitSelection { .. } => match proof_use.cause {
                MonoUseCause::VTableConstruction => {}
                MonoUseCause::SupertraitVTable
                    if matches!(proof_use.from, MonoTraceNode::VTable { .. })
                        && matches!(proof_use.site, MonoTraceSite::VTableSlot(_)) => {}
                _ => return Err(SelectionCollectionError::InvalidInput),
            },
            MonoProof::Projection { .. } => {
                if proof_use.cause != MonoUseCause::VTableConstruction {
                    return Err(SelectionCollectionError::InvalidInput);
                }
            }
            MonoProof::AssociatedItem {
                request,
                raw_instance,
                codegen_instance,
                ..
            } => {
                self.validate_codegen_instance(proof_use, request, raw_instance, codegen_instance)?
            }
        }
        self.collect_mono_proof(proof_use.proof)
    }

    /// Expands the explicit supertrait clauses of the concrete implementation
    /// selected for `key`. Vtable slots cannot represent marker supertraits, so
    /// this definition-level constraint is joined independently of slot facts.
    pub(crate) fn collect_supertrait_selections(
        &mut self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
    ) -> Result<Vec<ProofId>, SelectionCollectionError> {
        let mut active = Vec::new();
        let mut collected = Vec::new();
        self.collect_supertrait_selections_inner(key, &mut active, &mut collected)?;
        Ok(collected)
    }

    fn collect_supertrait_selections_inner(
        &mut self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
        active: &mut Vec<ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>>,
        collected: &mut Vec<ProofId>,
    ) -> Result<(), SelectionCollectionError> {
        if active.contains(&key) {
            return Err(SelectionCollectionError::InvalidTrace);
        }
        let proof = self.checked_selection_proof(key)?;
        let ImplSource::UserDefined(selected) = &proof.top_source else {
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
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        if selected_trait_ref != key.value {
            return Err(SelectionCollectionError::StockResultMismatch);
        }
        active.push(key);
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
                // Associated-type bindings in a supertrait declaration are
                // projection clauses. Their proofs are collected from the
                // compiler's codegen projection trace, not as trait selections.
                continue;
            };
            let predicate = self.tcx.instantiate_bound_regions_with_erased(predicate);
            let predicate = self
                .tcx
                .try_normalize_erasing_regions(key.typing_env, Unnormalized::new_wip(predicate))
                .map_err(|_| SelectionCollectionError::QueryFailed)?;
            let super_key = self
                .tcx
                .erase_and_anonymize_regions(key.typing_env.as_query_input(predicate.trait_ref));
            let id = self.collect_selection(super_key)?;
            if !collected.contains(&id) {
                collected.push(id);
            }
            self.collect_supertrait_selections_inner(super_key, active, collected)?;
        }
        active.pop();
        Ok(())
    }

    fn collect_mono_proof(
        &mut self,
        proof: MonoProof<'tcx>,
    ) -> Result<ProofId, SelectionCollectionError> {
        match proof {
            MonoProof::TraitSelection { proof_key } => self.collect_selection(proof_key),
            MonoProof::Projection {
                proof_key,
                expected,
            } => self.collect_projection(proof_key, expected),
            MonoProof::AssociatedItem {
                selection_key,
                request,
                raw_instance,
                codegen_instance,
            } => {
                let (expected_selection_key, expected_raw_instance) =
                    self.associated_request(request)?;
                if selection_key != expected_selection_key || raw_instance != expected_raw_instance
                {
                    return Err(SelectionCollectionError::StockResultMismatch);
                }
                self.collect_associated_item(request, codegen_instance)
            }
        }
    }

    fn validate_codegen_instance(
        &self,
        proof_use: MonoProofUse<'tcx>,
        request: ty::PseudoCanonicalInput<
            'tcx,
            (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>),
        >,
        raw_instance: Instance<'tcx>,
        codegen_instance: Instance<'tcx>,
    ) -> Result<(), SelectionCollectionError> {
        match proof_use.cause {
            MonoUseCause::DirectCall if codegen_instance == raw_instance => Ok(()),
            MonoUseCause::FunctionPointer | MonoUseCause::InlineAsmSymbol => {
                let expected = match proof_use.collection {
                    MonoTraceCollection::Used => Instance::resolve_for_fn_ptr(
                        self.tcx,
                        request.typing_env,
                        request.value.0,
                        request.value.1,
                    )
                    .ok_or(SelectionCollectionError::StockResultMismatch)?,
                    MonoTraceCollection::Mentioned => raw_instance,
                };
                if codegen_instance == expected {
                    Ok(())
                } else {
                    Err(SelectionCollectionError::StockResultMismatch)
                }
            }
            MonoUseCause::PreOptimizationDirectCall
            | MonoUseCause::PreOptimizationFunctionPointer
            | MonoUseCause::PreOptimizationInlineAsmSymbol => {
                if proof_use.collection != MonoTraceCollection::Mentioned
                    || !matches!(proof_use.from, MonoTraceNode::Item(MonoItem::Fn(_)))
                    || !matches!(
                        proof_use.site,
                        MonoTraceSite::Source(_) | MonoTraceSite::CompilerGenerated
                    )
                {
                    return Err(SelectionCollectionError::InvalidInput);
                }
                if codegen_instance == raw_instance {
                    Ok(())
                } else {
                    Err(SelectionCollectionError::StockResultMismatch)
                }
            }
            MonoUseCause::VTableMethod => {
                let MonoTraceNode::VTable {
                    trait_ref: Some(trait_ref),
                    ..
                } = proof_use.from
                else {
                    return Err(SelectionCollectionError::InvalidInput);
                };
                let MonoTraceSite::VTableSlot(slot) = proof_use.site else {
                    return Err(SelectionCollectionError::InvalidInput);
                };
                let cold = self
                    .tcx
                    .codegen_vtable_method_witnesses(trait_ref)
                    .map_err(|_| SelectionCollectionError::QueryFailed)?;
                let warm = self
                    .tcx
                    .codegen_vtable_method_witnesses(trait_ref)
                    .map_err(|_| SelectionCollectionError::QueryFailed)?;
                if !std::ptr::eq(cold, warm) {
                    return Err(SelectionCollectionError::CacheMismatch);
                }
                match cold.iter().find(|witness| witness.slot == slot) {
                    Some(witness)
                        if witness.request == request
                            && witness.codegen_instance == codegen_instance =>
                    {
                        Ok(())
                    }
                    _ => Err(SelectionCollectionError::StockResultMismatch),
                }
            }
            _ => Err(SelectionCollectionError::InvalidInput),
        }
    }

    pub(crate) fn collect_selection(
        &mut self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
    ) -> Result<ProofId, SelectionCollectionError> {
        if key.typing_env != ty::TypingEnv::fully_monomorphized()
            || key.value.has_non_region_param()
            || key.value.has_non_region_infer()
        {
            return Err(SelectionCollectionError::InvalidInput);
        }

        let proof = self.checked_selection_proof(key)?;
        let trace = self.collect_trace(&proof.trace)?;
        let root = trace.root;
        let root_obligation = proof
            .trace
            .obligations
            .get(proof.trace.root.0 as usize)
            .ok_or(SelectionCollectionError::InvalidTrace)?;
        let expected_predicate = ty::Binder::dummy(key.value).upcast(self.tcx);
        if root_obligation.param_env != key.typing_env.param_env
            || root_obligation.predicate != expected_predicate
        {
            return Err(SelectionCollectionError::StockResultMismatch);
        }
        let root_source = proof
            .trace
            .trait_selections
            .iter()
            .find(|selection| selection.node == proof.trace.root)
            .map(|selection| &selection.source);
        if root_source != Some(&proof.top_source) {
            return Err(SelectionCollectionError::InvalidTrace);
        }
        self.attach_query_trace(root, trace)?;
        Ok(root)
    }

    pub(crate) fn collect_projection(
        &mut self,
        key: ty::PseudoCanonicalInput<'tcx, ty::AliasTerm<'tcx>>,
        expected: ty::Term<'tcx>,
    ) -> Result<ProofId, SelectionCollectionError> {
        if key.typing_env != ty::TypingEnv::fully_monomorphized()
            || !matches!(key.value.kind, ty::AliasTermKind::ProjectionTy { .. })
            || key.value.args.has_non_region_param()
            || key.value.args.has_non_region_infer()
            || expected.has_non_region_param()
            || expected.has_non_region_infer()
        {
            return Err(SelectionCollectionError::InvalidInput);
        }

        let proof = self.checked_projection_proof(key)?;
        if proof.normalized_term != expected {
            return Err(SelectionCollectionError::StockResultMismatch);
        }
        let trace = self.collect_trace(&proof.trace)?;
        let projection_id = self
            .projection_id(key.typing_env.param_env, key.value)?
            .ok_or(SelectionCollectionError::InvalidTrace)?;

        let root_obligation = proof
            .trace
            .obligations
            .get(proof.trace.root.0 as usize)
            .ok_or(SelectionCollectionError::InvalidTrace)?;
        let expected_predicate = ty::Binder::dummy(ty::ProjectionPredicate {
            projection_term: key.value,
            term: proof.normalized_term,
        })
        .upcast(self.tcx);
        if root_obligation.param_env != key.typing_env.param_env
            || root_obligation.predicate != expected_predicate
            || !proof.trace.projections.iter().any(|projection| {
                projection.param_env == key.typing_env.param_env
                    && projection.projection == key.value
                    && projection.owners.contains(&proof.trace.root)
            })
        {
            return Err(SelectionCollectionError::InvalidTrace);
        }
        let normalized_result = self.projection_result_term(proof.normalized_term)?;
        self.attach_projection_query(projection_id, trace, normalized_result)?;
        Ok(projection_id)
    }

    pub(crate) fn collect_associated_item(
        &mut self,
        request: ty::PseudoCanonicalInput<
            'tcx,
            (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>),
        >,
        codegen_instance: Instance<'tcx>,
    ) -> Result<ProofId, SelectionCollectionError> {
        let (selection_key, raw_instance) = self.associated_request(request)?;
        if codegen_instance.args.has_non_region_param()
            || codegen_instance.args.has_non_region_infer()
        {
            return Err(SelectionCollectionError::InvalidInput);
        }
        let selection_id = self.collect_selection(selection_key)?;
        let selection = self.checked_selection_proof(selection_key)?;
        let request_term = self.associated_request_term(request)?;
        let raw_instance_key = self.instance_key(raw_instance)?;
        let codegen_instance_key = self.instance_key(codegen_instance)?;
        let key = ProofKey::AssociatedItem {
            request: request_term.clone(),
            raw_instance: raw_instance_key.clone(),
            codegen_instance: codegen_instance_key.clone(),
        };
        let source_kind = selection_source_kind(&selection.top_source);
        let (leaf, defining_node, finalizing_node, ancestor_path) = match &selection.top_source {
            ImplSource::UserDefined(selected) => {
                let proof = self.checked_associated_item_proof(request)?;
                if proof.selection_key != selection_key
                    || proof.source != selection.top_source
                    || proof.final_instance != raw_instance
                    || proof.final_instance.def_id() != proof.leaf_item
                {
                    return Err(SelectionCollectionError::StockResultMismatch);
                }
                let trait_id = self
                    .tcx
                    .trait_of_assoc(request.value.0)
                    .ok_or(SelectionCollectionError::InvalidInput)?;
                let leaf = self.definitions.target(self.tcx, proof.leaf_item)?;
                let defining = self.specialization_node(proof.defining_node)?;
                let finalizing = proof
                    .finalizing_node
                    .map(|node| self.specialization_node(node))
                    .transpose()?;
                let ancestors = proof
                    .ancestor_path
                    .iter()
                    .copied()
                    .map(|node| self.specialization_node(node))
                    .collect::<Result<Vec<_>, _>>()?;
                if ancestors.is_empty()
                    || ancestors.first()
                        != Some(&(
                            SpecializationKind::Impl,
                            self.definitions.target(self.tcx, selected.impl_def_id)?,
                        ))
                    || ancestors.last()
                        != Some(&(
                            SpecializationKind::Trait,
                            self.definitions.target(self.tcx, trait_id)?,
                        ))
                    || !ancestors.contains(&defining)
                    || finalizing.is_some_and(|node| !ancestors.contains(&node))
                {
                    return Err(SelectionCollectionError::InvalidTrace);
                }
                (
                    Some(leaf),
                    Some(specialization_node(defining)),
                    finalizing.map(specialization_node),
                    ancestors
                        .into_iter()
                        .map(specialization_node)
                        .collect::<Vec<_>>(),
                )
            }
            ImplSource::Param(_) | ImplSource::Builtin(_, _) => {
                match self.tcx.codegen_associated_item_proof(request) {
                    Err(CodegenAssociatedItemProofError::UnsupportedSource) => {}
                    Ok(_) | Err(_) => {
                        return Err(SelectionCollectionError::StockResultMismatch);
                    }
                }
                (None, None, None, Vec::new())
            }
        };
        let node = ProofNode {
            id: ProofId(0),
            key,
            kind: ProofNodeKind::AssociatedItem {
                request: request_term,
                raw_instance: raw_instance_key,
                codegen_instance: codegen_instance_key,
                selection: selection_id,
                source_kind,
                leaf,
                defining_node,
                finalizing_node,
                ancestor_path: ancestor_path.clone(),
            },
        };
        let id = self.intern_node(node)?;
        self.insert_relation(
            id,
            SolverRelationTarget::Proof(selection_id),
            SolverRelationKind::AssociatedSelection,
            0,
        );
        if let Some(leaf) = leaf {
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(leaf),
                SolverRelationKind::AssociatedLeaf,
                0,
            );
        }
        if let Some(defining_node) = defining_node {
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(defining_node.target),
                SolverRelationKind::AssociatedDefining,
                0,
            );
        }
        if let Some(finalizing_node) = finalizing_node {
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(finalizing_node.target),
                SolverRelationKind::AssociatedFinalizing,
                0,
            );
        }
        for (index, ancestor) in ancestor_path.into_iter().enumerate() {
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(ancestor.target),
                SolverRelationKind::SpecializationAncestor,
                ordinal(index)?,
            );
        }
        Ok(id)
    }

    fn checked_selection_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
    ) -> Result<&'tcx CodegenSelectionProof<'tcx>, SelectionCollectionError> {
        let cold = self
            .tcx
            .codegen_selection_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        let warm = self
            .tcx
            .codegen_selection_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        if !std::ptr::eq(cold, warm) {
            return Err(SelectionCollectionError::CacheMismatch);
        }
        let stock = self
            .tcx
            .codegen_select_candidate(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        if cold.top_source != *stock {
            return Err(SelectionCollectionError::StockResultMismatch);
        }
        Ok(cold)
    }

    fn checked_projection_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, ty::AliasTerm<'tcx>>,
    ) -> Result<&'tcx rustc_middle::traits::CodegenProjectionProof<'tcx>, SelectionCollectionError>
    {
        let cold = self
            .tcx
            .codegen_projection_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        let warm = self
            .tcx
            .codegen_projection_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        if !std::ptr::eq(cold, warm) {
            return Err(SelectionCollectionError::CacheMismatch);
        }
        let stock = self
            .tcx
            .try_normalize_generic_arg_after_erasing_regions(
                key.typing_env
                    .as_query_input(key.value.to_term(self.tcx, ty::IsRigid::No).into_arg()),
            )
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        let stock = match stock.kind() {
            ty::GenericArgKind::Type(value) => value.into(),
            ty::GenericArgKind::Const(value) => value.into(),
            ty::GenericArgKind::Lifetime(_) => {
                return Err(SelectionCollectionError::StockResultMismatch);
            }
        };
        if cold.normalized_term != stock {
            return Err(SelectionCollectionError::StockResultMismatch);
        }
        Ok(cold)
    }

    fn checked_associated_item_proof(
        &self,
        key: ty::PseudoCanonicalInput<'tcx, (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    ) -> Result<&'tcx CodegenAssociatedItemProof<'tcx>, SelectionCollectionError> {
        let cold = self
            .tcx
            .codegen_associated_item_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        let warm = self
            .tcx
            .codegen_associated_item_proof(key)
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        if !std::ptr::eq(cold, warm) {
            return Err(SelectionCollectionError::CacheMismatch);
        }
        Ok(cold)
    }

    fn associated_request(
        &self,
        request: ty::PseudoCanonicalInput<
            'tcx,
            (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>),
        >,
    ) -> Result<
        (
            ty::PseudoCanonicalInput<'tcx, ty::TraitRef<'tcx>>,
            Instance<'tcx>,
        ),
        SelectionCollectionError,
    > {
        if request.typing_env != ty::TypingEnv::fully_monomorphized()
            || !matches!(
                self.tcx.def_kind(request.value.0),
                DefKind::AssocFn | DefKind::AssocConst { .. }
            )
            || request.value.1.has_non_region_param()
            || request.value.1.has_non_region_infer()
        {
            return Err(SelectionCollectionError::InvalidInput);
        }
        let trait_id = self
            .tcx
            .trait_of_assoc(request.value.0)
            .ok_or(SelectionCollectionError::InvalidInput)?;
        let receiver_arguments = self
            .tcx
            .try_normalize_erasing_regions(
                request.typing_env,
                Unnormalized::new_wip(request.value.1),
            )
            .map_err(|_| SelectionCollectionError::QueryFailed)?;
        let selection_key = request.typing_env.as_query_input(ty::TraitRef::from_assoc(
            self.tcx,
            trait_id,
            receiver_arguments,
        ));
        let raw_instance = self
            .tcx
            .resolve_instance_raw(request)
            .map_err(|_| SelectionCollectionError::QueryFailed)?
            .ok_or(SelectionCollectionError::StockResultMismatch)?;
        Ok((selection_key, raw_instance))
    }

    fn collect_trace(
        &mut self,
        trace: &CodegenSolverTrace<'tcx>,
    ) -> Result<SolverTracePayload, SelectionCollectionError> {
        let mut obligations = Vec::with_capacity(trace.obligations.len());
        for obligation in &trace.obligations {
            let environment = self.environment_term(obligation.param_env)?;
            let predicate = self.predicate_term(obligation.predicate)?;
            let key = ProofKey::Obligation {
                environment: environment.clone(),
                predicate: predicate.clone(),
            };
            let node = ProofNode {
                id: ProofId(0),
                key,
                kind: ProofNodeKind::Obligation {
                    environment,
                    predicate,
                    source: None,
                    selection_nested: None,
                    fulfillment_nested: None,
                    query_trace: None,
                },
            };
            obligations.push(self.intern_node(node)?);
        }
        let root = proof_id(&obligations, trace.root)?;

        let mut trait_selections = Vec::with_capacity(trace.trait_selections.len());
        for selection in &trace.trait_selections {
            let node = proof_id(&obligations, selection.node)?;
            let obligation = trace
                .obligations
                .get(selection.node.0 as usize)
                .ok_or(SelectionCollectionError::InvalidTrace)?;
            let (source, _) = self.selection_source(&selection.source, obligation.predicate)?;
            let nested = selection
                .nested
                .iter()
                .copied()
                .map(|nested| proof_id(&obligations, nested))
                .collect::<Result<Vec<_>, _>>()?;
            self.attach_selection(node, source.clone(), nested.clone())?;
            self.insert_selection_source_relations(node, &source);
            for (nested_index, nested) in nested.into_iter().enumerate() {
                self.insert_relation(
                    node,
                    SolverRelationTarget::Proof(nested),
                    SolverRelationKind::TraitSelectionNested,
                    ordinal(nested_index)?,
                );
            }
            trait_selections.push(node);
        }

        let mut projections = Vec::with_capacity(trace.projections.len());
        for projection in &trace.projections {
            if projection.owners.is_empty() {
                return Err(SelectionCollectionError::InvalidTrace);
            }
            let environment = self.environment_term(projection.param_env)?;
            let alias = self.projection_goal_term(projection.projection)?;
            let (source_kind, source, implementation) =
                self.projection_source(&projection.source)?;
            let selected_trait = projection
                .selected_trait_node
                .map(|node| proof_id(&obligations, node))
                .transpose()?;
            let selected_item = projection
                .selected_projection_item
                .map(|item| self.definitions.target(self.tcx, item))
                .transpose()?;
            if matches!(
                projection.source,
                CodegenProjectionSource::Selected(ImplSource::UserDefined(_))
            ) != selected_item.is_some()
            {
                return Err(SelectionCollectionError::InvalidTrace);
            }
            match (&projection.source, selected_trait) {
                (CodegenProjectionSource::Selected(source), Some(node)) => {
                    self.validate_projection_selection(
                        &obligations,
                        projection.param_env,
                        projection.projection,
                        source,
                        node,
                    )?;
                }
                (CodegenProjectionSource::Selected(_), None)
                | (CodegenProjectionSource::ParamEnv(_), Some(_))
                | (CodegenProjectionSource::TraitDef(_), Some(_))
                | (CodegenProjectionSource::Object(_), Some(_))
                | (CodegenProjectionSource::NoApplicableCandidate, Some(_)) => {
                    return Err(SelectionCollectionError::InvalidTrace);
                }
                (CodegenProjectionSource::ParamEnv(_), None)
                | (CodegenProjectionSource::TraitDef(_), None)
                | (CodegenProjectionSource::Object(_), None)
                | (CodegenProjectionSource::NoApplicableCandidate, None) => {}
            }
            let (outcome, nested) = match &projection.result {
                CodegenProjectionTraceResult::Progress { raw_term, nested } => (
                    ProjectionOutcome::Progress {
                        raw_term: self.projection_result_term(*raw_term)?,
                    },
                    nested.as_slice(),
                ),
                CodegenProjectionTraceResult::NoProgress(term) => {
                    if matches!(
                        projection.source,
                        CodegenProjectionSource::NoApplicableCandidate
                    ) && *term != projection.projection.to_term(self.tcx, ty::IsRigid::No)
                    {
                        return Err(SelectionCollectionError::InvalidTrace);
                    }
                    (
                        ProjectionOutcome::NoProgress {
                            term: self.projection_result_term(*term)?,
                        },
                        &[][..],
                    )
                }
            };
            let key = ProofKey::Projection {
                environment: environment.clone(),
                alias: alias.clone(),
            };
            let owners = projection
                .owners
                .iter()
                .copied()
                .map(|owner| proof_id(&obligations, owner))
                .collect::<Result<Vec<_>, _>>()?;
            let nested = nested
                .iter()
                .copied()
                .map(|nested| proof_id(&obligations, nested))
                .collect::<Result<Vec<_>, _>>()?;
            let projection_id = self.intern_node(ProofNode {
                id: ProofId(0),
                key,
                kind: ProofNodeKind::Projection {
                    environment,
                    alias,
                    source_kind,
                    source,
                    outcome,
                    selected_trait,
                    selected_impl: implementation,
                    selected_item,
                    owners: owners.clone(),
                    nested: nested.clone(),
                    query_trace: None,
                    normalized_result: None,
                },
            })?;
            if let Some(implementation) = implementation {
                self.insert_relation(
                    projection_id,
                    SolverRelationTarget::Definition(implementation),
                    SolverRelationKind::SelectedImplementation,
                    0,
                );
            }
            if let Some(selected_trait) = selected_trait {
                self.insert_relation(
                    projection_id,
                    SolverRelationTarget::Proof(selected_trait),
                    SolverRelationKind::ProjectionSelectedTrait,
                    0,
                );
            }
            if let Some(selected_item) = selected_item {
                self.insert_relation(
                    projection_id,
                    SolverRelationTarget::Definition(selected_item),
                    SolverRelationKind::SelectedProjectionItem,
                    0,
                );
            }
            for (nested_index, nested) in nested.into_iter().enumerate() {
                self.insert_relation(
                    projection_id,
                    SolverRelationTarget::Proof(nested),
                    SolverRelationKind::ProjectionNested,
                    ordinal(nested_index)?,
                );
            }
            projections.push(projection_id);
        }

        let mut fulfillments = Vec::with_capacity(trace.fulfillments.len());
        for fulfillment in &trace.fulfillments {
            let node = proof_id(&obligations, fulfillment.node)?;
            let mut nested = fulfillment
                .nested
                .iter()
                .copied()
                .map(|nested| proof_id(&obligations, nested))
                .collect::<Result<Vec<_>, _>>()?;
            // Fulfillment dependencies are a set. Query-local node order can
            // differ between otherwise identical solver traces.
            canonicalize_proof_ids(&self.nodes, &mut nested)?;
            self.attach_fulfillment(node, nested.clone())?;
            for (nested_index, nested) in nested.into_iter().enumerate() {
                self.insert_relation(
                    node,
                    SolverRelationTarget::Proof(nested),
                    SolverRelationKind::FulfillmentNested,
                    ordinal(nested_index)?,
                );
            }
            fulfillments.push(node);
        }

        let mut cycles = Vec::with_capacity(trace.cycles.len());
        for cycle in &trace.cycles {
            if cycle.nodes.is_empty() || !cycle.coinductive {
                return Err(SelectionCollectionError::InvalidTrace);
            }
            let members = cycle
                .nodes
                .iter()
                .copied()
                .map(|node| proof_id(&obligations, node))
                .collect::<Result<Vec<_>, _>>()?;
            let member_keys = members
                .iter()
                .map(|member| self.nodes[member.0 as usize].key.clone())
                .collect();
            let cycle_id = self.intern_node(ProofNode {
                id: ProofId(0),
                key: ProofKey::Cycle {
                    members: member_keys,
                    coinductive: cycle.coinductive,
                },
                kind: ProofNodeKind::Cycle {
                    members: members.clone(),
                    coinductive: cycle.coinductive,
                },
            })?;
            for (member_index, member) in members.into_iter().enumerate() {
                self.insert_relation(
                    cycle_id,
                    SolverRelationTarget::Proof(member),
                    SolverRelationKind::CycleMember,
                    ordinal(member_index)?,
                );
            }
            cycles.push(cycle_id);
        }
        Ok(SolverTracePayload {
            root,
            obligations,
            trait_selections,
            projections,
            fulfillments,
            cycles,
        })
    }

    fn validate_projection_selection(
        &mut self,
        obligations: &[ProofId],
        environment: ty::ParamEnv<'tcx>,
        projection: ty::AliasTerm<'tcx>,
        source: &ImplSource<'tcx, ()>,
        selected: ProofId,
    ) -> Result<(), SelectionCollectionError> {
        let expected_environment = self.environment_term(environment)?;
        let expected_predicate = self
            .predicate_term(ty::Binder::dummy(projection.trait_ref(self.tcx)).upcast(self.tcx))?;
        let expected_key = ProofKey::Obligation {
            environment: expected_environment,
            predicate: expected_predicate,
        };
        if !obligations.contains(&selected) || self.nodes[selected.0 as usize].key != expected_key {
            return Err(SelectionCollectionError::InvalidTrace);
        }
        let expected_predicate = ty::Binder::dummy(projection.trait_ref(self.tcx)).upcast(self.tcx);
        let (expected_source, _) = self.selection_source(source, expected_predicate)?;
        match &self.nodes[selected.0 as usize].kind {
            ProofNodeKind::Obligation {
                source: Some(actual),
                ..
            } if *actual == expected_source => Ok(()),
            _ => Err(SelectionCollectionError::InvalidTrace),
        }
    }

    fn projection_id(
        &mut self,
        environment: ty::ParamEnv<'tcx>,
        projection: ty::AliasTerm<'tcx>,
    ) -> Result<Option<ProofId>, SelectionCollectionError> {
        let key = ProofKey::Projection {
            environment: self.environment_term(environment)?,
            alias: self.projection_goal_term(projection)?,
        };
        Ok(self.ids.get(&key).copied())
    }

    fn attach_selection(
        &mut self,
        id: ProofId,
        source: SelectionSource,
        nested: Vec<ProofId>,
    ) -> Result<(), SelectionCollectionError> {
        match &mut self.nodes[id.0 as usize].kind {
            ProofNodeKind::Obligation {
                source: existing_source,
                selection_nested,
                ..
            } => {
                if !optional_compatible(existing_source, Some(&source))
                    || !optional_compatible(selection_nested, Some(&nested))
                {
                    return Err(SelectionCollectionError::ConflictingProof);
                }
                merge_optional(existing_source, source);
                merge_optional(selection_nested, nested);
                Ok(())
            }
            _ => Err(SelectionCollectionError::ConflictingProof),
        }
    }

    fn attach_fulfillment(
        &mut self,
        id: ProofId,
        nested: Vec<ProofId>,
    ) -> Result<(), SelectionCollectionError> {
        match &mut self.nodes[id.0 as usize].kind {
            ProofNodeKind::Obligation {
                fulfillment_nested, ..
            } => merge_optional(fulfillment_nested, nested)
                .then_some(())
                .ok_or(SelectionCollectionError::ConflictingProof),
            _ => Err(SelectionCollectionError::ConflictingProof),
        }
    }

    fn attach_query_trace(
        &mut self,
        id: ProofId,
        trace: SolverTracePayload,
    ) -> Result<(), SelectionCollectionError> {
        match &mut self.nodes[id.0 as usize].kind {
            ProofNodeKind::Obligation { query_trace, .. }
            | ProofNodeKind::Projection { query_trace, .. } => {
                if !merge_optional(query_trace, trace.clone()) {
                    return Err(SelectionCollectionError::ConflictingProof);
                }
            }
            _ => return Err(SelectionCollectionError::ConflictingProof),
        }
        self.insert_relation(
            id,
            SolverRelationTarget::Proof(trace.root),
            SolverRelationKind::QueryTraceRoot,
            0,
        );
        self.insert_trace_relations(id, SolverRelationKind::TraceObligation, trace.obligations)?;
        self.insert_trace_relations(
            id,
            SolverRelationKind::TraceTraitSelection,
            trace.trait_selections,
        )?;
        self.insert_trace_relations(id, SolverRelationKind::TraceProjection, trace.projections)?;
        self.insert_trace_relations(id, SolverRelationKind::TraceFulfillment, trace.fulfillments)?;
        self.insert_trace_relations(id, SolverRelationKind::TraceCycle, trace.cycles)?;
        Ok(())
    }

    fn attach_projection_query(
        &mut self,
        id: ProofId,
        trace: SolverTracePayload,
        normalized_result: CanonicalCompilerTerm,
    ) -> Result<(), SelectionCollectionError> {
        match &mut self.nodes[id.0 as usize].kind {
            ProofNodeKind::Projection {
                normalized_result: existing,
                ..
            } => {
                if !merge_optional(existing, normalized_result) {
                    return Err(SelectionCollectionError::ConflictingProof);
                }
            }
            _ => return Err(SelectionCollectionError::ConflictingProof),
        }
        self.attach_query_trace(id, trace)
    }

    fn insert_trace_relations(
        &mut self,
        from: ProofId,
        kind: SolverRelationKind,
        targets: Vec<ProofId>,
    ) -> Result<(), SelectionCollectionError> {
        for (index, target) in targets.into_iter().enumerate() {
            self.insert_relation(
                from,
                SolverRelationTarget::Proof(target),
                kind,
                ordinal(index)?,
            );
        }
        Ok(())
    }

    fn insert_selection_source_relations(&mut self, id: ProofId, source: &SelectionSource) {
        if let Some(implementation) = source.implementation {
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(implementation),
                SolverRelationKind::SelectedImplementation,
                0,
            );
        }
        if let Some(builtin_trait) = source.builtin_trait {
            let kind = match builtin_trait.kind {
                BuiltinTraitTargetKind::TraitDefinition => SolverRelationKind::TraitDefinition,
                BuiltinTraitTargetKind::AutoTrait => SolverRelationKind::AutoTraitProof,
            };
            self.insert_relation(
                id,
                SolverRelationTarget::Definition(builtin_trait.target),
                kind,
                0,
            );
        }
    }

    fn intern_node(&mut self, mut node: ProofNode) -> Result<ProofId, SelectionCollectionError> {
        if let Some(&id) = self.ids.get(&node.key) {
            if merge_node(&mut self.nodes[id.0 as usize], node)? {
                return Ok(id);
            }
            return Err(SelectionCollectionError::ConflictingProof);
        }
        let id = ProofId(
            self.nodes
                .len()
                .try_into()
                .map_err(|_| SelectionCollectionError::TooManyProofs)?,
        );
        node.id = id;
        self.ids.insert(node.key.clone(), id);
        self.nodes.push(node);
        Ok(id)
    }

    fn insert_projection_owner_relations(&mut self) -> Result<(), SelectionCollectionError> {
        let projections = self
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, ProofNodeKind::Projection { .. }).then_some(node.id)
            })
            .collect::<Vec<_>>();
        for projection in projections {
            let ProofNodeKind::Projection { owners, .. } = &self.nodes[projection.0 as usize].kind
            else {
                unreachable!()
            };
            let mut owners = owners.clone();
            canonicalize_proof_ids(&self.nodes, &mut owners)?;
            let ProofNodeKind::Projection { owners: stored, .. } =
                &mut self.nodes[projection.0 as usize].kind
            else {
                unreachable!()
            };
            *stored = owners.clone();
            for (index, owner) in owners.iter().copied().enumerate() {
                self.insert_relation(
                    projection,
                    SolverRelationTarget::Proof(owner),
                    SolverRelationKind::ProjectionOwner,
                    ordinal(index)?,
                );
            }
        }
        Ok(())
    }

    fn insert_relation(
        &mut self,
        from: ProofId,
        to: SolverRelationTarget,
        kind: SolverRelationKind,
        ordinal: u32,
    ) {
        let slot = (from, kind, ordinal);
        if self
            .relation_slots
            .insert(slot, to)
            .is_some_and(|existing| existing != to)
        {
            self.conflicting_relation = true;
        }
        self.relations.insert(SolverRelation {
            from,
            to,
            kind,
            ordinal,
        });
    }

    fn selection_source(
        &mut self,
        source: &ImplSource<'tcx, ()>,
        predicate: ty::Predicate<'tcx>,
    ) -> Result<(SelectionSource, Option<DefinitionTarget>), SelectionCollectionError> {
        let (kind, implementation, builtin_trait) = match source {
            ImplSource::UserDefined(data) => (
                SelectionSourceKind::UserDefined,
                Some(self.definitions.target(self.tcx, data.impl_def_id)?),
                None,
            ),
            ImplSource::Param(_) => (SelectionSourceKind::Parameter, None, None),
            ImplSource::Builtin(builtin, _) => {
                let trait_id = predicate
                    .as_trait_clause()
                    .ok_or(SelectionCollectionError::InvalidTrace)?
                    .def_id();
                let target = self.definitions.target(self.tcx, trait_id)?;
                let kind = if matches!(builtin, BuiltinImplSource::Object { .. })
                    || !self.tcx.trait_is_auto(trait_id)
                {
                    BuiltinTraitTargetKind::TraitDefinition
                } else {
                    BuiltinTraitTargetKind::AutoTrait
                };
                (
                    SelectionSourceKind::Builtin,
                    None,
                    Some(BuiltinTraitTarget { kind, target }),
                )
            }
        };
        let term = TermHasher::new(self.tcx, self.definitions)
            .canonicalize(CompilerTermKind::SolverSource, source)?;
        Ok((
            SelectionSource {
                kind,
                term,
                implementation,
                builtin_trait,
            },
            implementation,
        ))
    }

    fn projection_source(
        &mut self,
        source: &CodegenProjectionSource<'tcx>,
    ) -> Result<
        (
            ProjectionSourceKind,
            CanonicalCompilerTerm,
            Option<DefinitionTarget>,
        ),
        SelectionCollectionError,
    > {
        let (kind, implementation) = match source {
            CodegenProjectionSource::ParamEnv(_) => {
                (ProjectionSourceKind::ParameterEnvironment, None)
            }
            CodegenProjectionSource::TraitDef(_) => (ProjectionSourceKind::TraitDefinition, None),
            CodegenProjectionSource::Object(_) => (ProjectionSourceKind::Object, None),
            CodegenProjectionSource::Selected(ImplSource::UserDefined(data)) => (
                ProjectionSourceKind::SelectedUserDefined,
                Some(self.definitions.target(self.tcx, data.impl_def_id)?),
            ),
            CodegenProjectionSource::Selected(ImplSource::Param(_)) => {
                (ProjectionSourceKind::SelectedParameter, None)
            }
            CodegenProjectionSource::Selected(ImplSource::Builtin(_, _)) => {
                (ProjectionSourceKind::SelectedBuiltin, None)
            }
            CodegenProjectionSource::NoApplicableCandidate => {
                (ProjectionSourceKind::NoApplicableCandidate, None)
            }
        };
        let term = TermHasher::new(self.tcx, self.definitions).canonicalize_with(
            CompilerTermKind::SolverSource,
            |encoder| match source {
                CodegenProjectionSource::ParamEnv(predicate) => {
                    encoder.emit_u8(0);
                    encode_projection_predicate(encoder, *predicate);
                }
                CodegenProjectionSource::TraitDef(predicate) => {
                    encoder.emit_u8(1);
                    encode_projection_predicate(encoder, *predicate);
                }
                CodegenProjectionSource::Object(predicate) => {
                    encoder.emit_u8(2);
                    encode_projection_predicate(encoder, *predicate);
                }
                CodegenProjectionSource::Selected(source) => {
                    encoder.emit_u8(3);
                    source.encode(encoder);
                }
                CodegenProjectionSource::NoApplicableCandidate => encoder.emit_u8(4),
            },
        )?;
        Ok((kind, term, implementation))
    }

    fn environment_term(
        &mut self,
        environment: ty::ParamEnv<'tcx>,
    ) -> Result<CanonicalCompilerTerm, SelectionCollectionError> {
        Ok(
            TermHasher::new(self.tcx, self.definitions).canonicalize_with(
                CompilerTermKind::SolverTrace,
                |encoder| {
                    encoder.emit_u8(0);
                    environment.encode(encoder);
                },
            )?,
        )
    }

    fn predicate_term(
        &mut self,
        predicate: ty::Predicate<'tcx>,
    ) -> Result<CanonicalCompilerTerm, SelectionCollectionError> {
        Ok(TermHasher::new(self.tcx, self.definitions)
            .canonicalize(CompilerTermKind::Predicate, &predicate)?)
    }

    fn projection_goal_term(
        &mut self,
        projection: ty::AliasTerm<'tcx>,
    ) -> Result<CanonicalCompilerTerm, SelectionCollectionError> {
        Ok(TermHasher::new(self.tcx, self.definitions)
            .canonicalize(CompilerTermKind::ProjectionGoal, &projection)?)
    }

    fn projection_result_term(
        &mut self,
        term: ty::Term<'tcx>,
    ) -> Result<CanonicalCompilerTerm, SelectionCollectionError> {
        Ok(
            TermHasher::new(self.tcx, self.definitions).canonicalize_with(
                CompilerTermKind::Synthetic,
                |encoder| {
                    encoder.emit_u8(0);
                    term.encode(encoder);
                },
            )?,
        )
    }

    fn associated_request_term(
        &mut self,
        request: ty::PseudoCanonicalInput<
            'tcx,
            (rustc_hir::def_id::DefId, ty::GenericArgsRef<'tcx>),
        >,
    ) -> Result<CanonicalCompilerTerm, SelectionCollectionError> {
        Ok(
            TermHasher::new(self.tcx, self.definitions).canonicalize_with(
                CompilerTermKind::AssociatedItemProof,
                |encoder| {
                    encoder.emit_u8(0);
                    request.typing_env.param_env.encode(encoder);
                    request.value.0.encode(encoder);
                    request.value.1.encode(encoder);
                },
            )?,
        )
    }

    fn instance_key(
        &mut self,
        instance: Instance<'tcx>,
    ) -> Result<MonoInstanceKey, SelectionCollectionError> {
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

    fn specialization_node(
        &mut self,
        node: CodegenSpecializationNode,
    ) -> Result<(SpecializationKind, DefinitionTarget), SelectionCollectionError> {
        Ok(match node {
            CodegenSpecializationNode::Impl(definition) => (
                SpecializationKind::Impl,
                self.definitions.target(self.tcx, definition)?,
            ),
            CodegenSpecializationNode::Trait(definition) => (
                SpecializationKind::Trait,
                self.definitions.target(self.tcx, definition)?,
            ),
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SpecializationKind {
    Impl,
    Trait,
}

impl From<SpecializationKind> for SpecializationNodeKind {
    fn from(kind: SpecializationKind) -> Self {
        match kind {
            SpecializationKind::Impl => Self::Impl,
            SpecializationKind::Trait => Self::Trait,
        }
    }
}

fn specialization_node(
    (kind, target): (SpecializationKind, DefinitionTarget),
) -> SpecializationNode {
    SpecializationNode {
        kind: kind.into(),
        target,
    }
}

fn selection_source_kind(source: &ImplSource<'_, ()>) -> SelectionSourceKind {
    match source {
        ImplSource::UserDefined(_) => SelectionSourceKind::UserDefined,
        ImplSource::Param(_) => SelectionSourceKind::Parameter,
        ImplSource::Builtin(_, _) => SelectionSourceKind::Builtin,
    }
}

impl SolverRelation {
    fn into_dependency_edge(self) -> DependencyEdge {
        let to = match self.to {
            SolverRelationTarget::Proof(id) => GraphNode::Proof(id),
            SolverRelationTarget::Definition(DefinitionTarget::Local(id)) => {
                GraphNode::Definition(id)
            }
            SolverRelationTarget::Definition(DefinitionTarget::External(id)) => {
                GraphNode::ExternalDefinition(id)
            }
        };
        DependencyEdge {
            from: GraphNode::Proof(self.from),
            to,
            kind: DependencyKind::ProofRelation {
                relation: self.kind.into(),
                ordinal: self.ordinal,
            },
            sites: Vec::new(),
            evidence: EvidenceOrigin::PatchedObserver,
        }
    }
}

impl From<SolverRelationKind> for ProofRelationKind {
    fn from(kind: SolverRelationKind) -> Self {
        match kind {
            SolverRelationKind::TraceObligation => Self::TraceObligation,
            SolverRelationKind::TraceTraitSelection => Self::TraceTraitSelection,
            SolverRelationKind::TraceProjection => Self::TraceProjection,
            SolverRelationKind::TraceFulfillment => Self::TraceFulfillment,
            SolverRelationKind::TraceCycle => Self::TraceCycle,
            SolverRelationKind::QueryTraceRoot => Self::QueryTraceRoot,
            SolverRelationKind::TraitSelectionNested => Self::TraitSelectionNested,
            SolverRelationKind::ProjectionOwner => Self::ProjectionOwner,
            SolverRelationKind::ProjectionSelectedTrait => Self::ProjectionSelectedTrait,
            SolverRelationKind::ProjectionNested => Self::ProjectionNested,
            SolverRelationKind::FulfillmentNested => Self::FulfillmentNested,
            SolverRelationKind::CycleMember => Self::CycleMember,
            SolverRelationKind::AssociatedSelection => Self::AssociatedSelection,
            SolverRelationKind::AssociatedLeaf => Self::AssociatedLeaf,
            SolverRelationKind::AssociatedDefining => Self::AssociatedDefining,
            SolverRelationKind::AssociatedFinalizing => Self::AssociatedFinalizing,
            SolverRelationKind::SpecializationAncestor => Self::SpecializationAncestor,
            SolverRelationKind::SelectedImplementation => Self::SelectedImpl,
            SolverRelationKind::SelectedProjectionItem => Self::SelectedTraitItem,
            SolverRelationKind::AutoTraitProof => Self::AutoTraitProof,
            SolverRelationKind::TraitDefinition => Self::TraitDefinition,
        }
    }
}

fn remap_node_references(
    kind: &mut ProofNodeKind,
    remap: &[ProofId],
) -> Result<(), SelectionCollectionError> {
    match kind {
        ProofNodeKind::Obligation {
            selection_nested,
            fulfillment_nested,
            query_trace,
            ..
        } => {
            remap_optional_ids(selection_nested, remap)?;
            remap_optional_ids(fulfillment_nested, remap)?;
            if let Some(trace) = query_trace {
                remap_trace(trace, remap)?;
            }
        }
        ProofNodeKind::Projection {
            selected_trait,
            owners,
            nested,
            query_trace,
            ..
        } => {
            if let Some(selected_trait) = selected_trait {
                *selected_trait = remapped(remap, *selected_trait)?;
            }
            remap_ids(owners, remap)?;
            remap_ids(nested, remap)?;
            if let Some(trace) = query_trace {
                remap_trace(trace, remap)?;
            }
        }
        ProofNodeKind::AssociatedItem { selection, .. } => {
            *selection = remapped(remap, *selection)?;
        }
        ProofNodeKind::Cycle { members, .. } => {
            for member in members {
                *member = remapped(remap, *member)?;
            }
        }
    }
    Ok(())
}

fn remap_optional_ids(
    ids: &mut Option<Vec<ProofId>>,
    remap: &[ProofId],
) -> Result<(), SelectionCollectionError> {
    if let Some(ids) = ids {
        remap_ids(ids, remap)?;
    }
    Ok(())
}

fn remap_ids(ids: &mut [ProofId], remap: &[ProofId]) -> Result<(), SelectionCollectionError> {
    for id in ids {
        *id = remapped(remap, *id)?;
    }
    Ok(())
}

fn remap_trace(
    trace: &mut SolverTracePayload,
    remap: &[ProofId],
) -> Result<(), SelectionCollectionError> {
    trace.root = remapped(remap, trace.root)?;
    remap_ids(&mut trace.obligations, remap)?;
    remap_ids(&mut trace.trait_selections, remap)?;
    remap_ids(&mut trace.projections, remap)?;
    remap_ids(&mut trace.fulfillments, remap)?;
    remap_ids(&mut trace.cycles, remap)
}

fn remapped(remap: &[ProofId], old: ProofId) -> Result<ProofId, SelectionCollectionError> {
    remap
        .get(old.0 as usize)
        .copied()
        .ok_or(SelectionCollectionError::InvalidTrace)
}

fn proof_id(
    obligations: &[ProofId],
    node: rustc_middle::traits::CodegenProofNodeId,
) -> Result<ProofId, SelectionCollectionError> {
    obligations
        .get(node.0 as usize)
        .copied()
        .ok_or(SelectionCollectionError::InvalidTrace)
}

fn encode_projection_predicate<'tcx>(
    encoder: &mut TermHasher<'_, 'tcx>,
    predicate: ty::PolyProjectionPredicate<'tcx>,
) {
    predicate.bound_vars().encode(encoder);
    let predicate = predicate.skip_binder();
    predicate.projection_term.encode(encoder);
    predicate.term.encode(encoder);
}

fn ordinal(index: usize) -> Result<u32, SelectionCollectionError> {
    index
        .try_into()
        .map_err(|_| SelectionCollectionError::TooManyProofs)
}

fn merge_node(
    existing: &mut ProofNode,
    incoming: ProofNode,
) -> Result<bool, SelectionCollectionError> {
    if existing.key != incoming.key {
        return Ok(false);
    }
    match (&mut existing.kind, incoming.kind) {
        (
            ProofNodeKind::Obligation {
                environment: left_environment,
                predicate: left_predicate,
                source: left_source,
                selection_nested: left_selection_nested,
                fulfillment_nested: left_fulfillment_nested,
                query_trace: left_query_trace,
            },
            ProofNodeKind::Obligation {
                environment: right_environment,
                predicate: right_predicate,
                source: right_source,
                selection_nested: right_selection_nested,
                fulfillment_nested: right_fulfillment_nested,
                query_trace: right_query_trace,
            },
        ) if *left_environment == right_environment && *left_predicate == right_predicate => {
            if !optional_compatible(left_source, right_source.as_ref())
                || !optional_compatible(left_selection_nested, right_selection_nested.as_ref())
                || !optional_compatible(left_fulfillment_nested, right_fulfillment_nested.as_ref())
                || !optional_compatible(left_query_trace, right_query_trace.as_ref())
            {
                return Ok(false);
            }
            merge_optional_option(left_source, right_source);
            merge_optional_option(left_selection_nested, right_selection_nested);
            merge_optional_option(left_fulfillment_nested, right_fulfillment_nested);
            merge_optional_option(left_query_trace, right_query_trace);
            Ok(true)
        }
        (
            ProofNodeKind::Projection {
                environment: left_environment,
                alias: left_alias,
                source_kind: left_source_kind,
                source: left_source,
                outcome: left_outcome,
                selected_trait: left_selected_trait,
                selected_impl: left_selected_impl,
                selected_item: left_selected_item,
                owners: left_owners,
                nested: left_nested,
                query_trace: left_query_trace,
                normalized_result: left_normalized_result,
            },
            ProofNodeKind::Projection {
                environment: right_environment,
                alias: right_alias,
                source_kind: right_source_kind,
                source: right_source,
                outcome: right_outcome,
                selected_trait: right_selected_trait,
                selected_impl: right_selected_impl,
                selected_item: right_selected_item,
                owners: right_owners,
                nested: right_nested,
                query_trace: right_query_trace,
                normalized_result: right_normalized_result,
            },
        ) if *left_environment == right_environment
            && *left_alias == right_alias
            && *left_source_kind == right_source_kind
            && *left_source == right_source
            && *left_outcome == right_outcome
            && *left_selected_trait == right_selected_trait
            && *left_selected_impl == right_selected_impl
            && *left_selected_item == right_selected_item
            && *left_nested == right_nested =>
        {
            if !optional_compatible(left_query_trace, right_query_trace.as_ref())
                || !optional_compatible(left_normalized_result, right_normalized_result.as_ref())
            {
                return Ok(false);
            }
            merge_optional_option(left_query_trace, right_query_trace);
            merge_optional_option(left_normalized_result, right_normalized_result);
            left_owners.extend(right_owners);
            Ok(true)
        }
        (left, right) => Ok(*left == right),
    }
}

fn merge_optional<T: Eq>(existing: &mut Option<T>, incoming: T) -> bool {
    merge_optional_option(existing, Some(incoming))
}

fn optional_compatible<T: Eq>(existing: &Option<T>, incoming: Option<&T>) -> bool {
    match (existing.as_ref(), incoming) {
        (Some(left), Some(right)) => left == right,
        _ => true,
    }
}

fn merge_optional_option<T: Eq>(existing: &mut Option<T>, incoming: Option<T>) -> bool {
    match (&*existing, incoming) {
        (Some(left), Some(right)) => *left == right,
        (None, Some(right)) => {
            *existing = Some(right);
            true
        }
        (_, None) => true,
    }
}

fn canonicalize_proof_ids(
    nodes: &[ProofNode],
    ids: &mut Vec<ProofId>,
) -> Result<(), SelectionCollectionError> {
    if ids.iter().any(|id| id.0 as usize >= nodes.len()) {
        return Err(SelectionCollectionError::InvalidTrace);
    }
    ids.sort_by(|left, right| nodes[left.0 as usize].key.cmp(&nodes[right.0 as usize].key));
    ids.dedup();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(tag: u8) -> CanonicalCompilerTerm {
        CanonicalCompilerTerm {
            schema_version: 1,
            bytes: vec![tag],
        }
    }

    fn trace() -> SolverTracePayload {
        SolverTracePayload {
            root: ProofId(0),
            obligations: vec![ProofId(0), ProofId(1)],
            trait_selections: vec![ProofId(0)],
            projections: vec![ProofId(2)],
            fulfillments: vec![ProofId(1)],
            cycles: vec![ProofId(3)],
        }
    }

    fn projection(
        query_trace: Option<SolverTracePayload>,
        normalized_result: Option<CanonicalCompilerTerm>,
    ) -> ProofNode {
        projection_with_owners(vec![ProofId(0)], query_trace, normalized_result)
    }

    fn projection_with_owners(
        owners: Vec<ProofId>,
        query_trace: Option<SolverTracePayload>,
        normalized_result: Option<CanonicalCompilerTerm>,
    ) -> ProofNode {
        let environment = term(1);
        let alias = term(2);
        ProofNode {
            id: ProofId(2),
            key: ProofKey::Projection {
                environment: environment.clone(),
                alias: alias.clone(),
            },
            kind: ProofNodeKind::Projection {
                environment,
                alias,
                source_kind: ProjectionSourceKind::NoApplicableCandidate,
                source: term(3),
                outcome: ProjectionOutcome::NoProgress { term: term(4) },
                selected_trait: None,
                selected_impl: None,
                selected_item: None,
                owners,
                nested: Vec::new(),
                query_trace,
                normalized_result,
            },
        }
    }

    fn obligation(id: u32, environment_tag: u8) -> ProofNode {
        let environment = term(environment_tag);
        let predicate = term(9);
        ProofNode {
            id: ProofId(id),
            key: ProofKey::Obligation {
                environment: environment.clone(),
                predicate: predicate.clone(),
            },
            kind: ProofNodeKind::Obligation {
                environment,
                predicate,
                source: None,
                selection_nested: None,
                fulfillment_nested: None,
                query_trace: None,
            },
        }
    }

    #[test]
    fn projection_owners_merge_as_an_observation_order_independent_set() {
        let nodes = vec![obligation(0, 2), obligation(1, 1)];
        let mut forward = projection_with_owners(vec![ProofId(0)], None, None);
        assert!(
            merge_node(
                &mut forward,
                projection_with_owners(vec![ProofId(1), ProofId(0)], None, None),
            )
            .unwrap()
        );
        let ProofNodeKind::Projection {
            owners: forward, ..
        } = &mut forward.kind
        else {
            unreachable!()
        };
        canonicalize_proof_ids(&nodes, forward).unwrap();

        let mut reverse = projection_with_owners(vec![ProofId(1), ProofId(0)], None, None);
        assert!(
            merge_node(
                &mut reverse,
                projection_with_owners(vec![ProofId(0)], None, None),
            )
            .unwrap()
        );
        let ProofNodeKind::Projection {
            owners: reverse, ..
        } = &mut reverse.kind
        else {
            unreachable!()
        };
        canonicalize_proof_ids(&nodes, reverse).unwrap();

        assert_eq!(forward, &vec![ProofId(1), ProofId(0)]);
        assert_eq!(reverse, forward);
    }

    #[test]
    fn fulfillment_nested_nodes_merge_across_reversed_trace_order() {
        let nodes = vec![obligation(0, 2), obligation(1, 1), obligation(2, 3)];
        let mut forward = vec![ProofId(0), ProofId(1), ProofId(2)];
        let mut reverse = vec![ProofId(2), ProofId(1), ProofId(0)];
        canonicalize_proof_ids(&nodes, &mut forward).unwrap();
        canonicalize_proof_ids(&nodes, &mut reverse).unwrap();
        assert_eq!(forward, vec![ProofId(1), ProofId(0), ProofId(2)]);
        assert_eq!(reverse, forward);

        let mut existing = obligation(3, 4);
        let ProofNodeKind::Obligation {
            fulfillment_nested, ..
        } = &mut existing.kind
        else {
            unreachable!()
        };
        *fulfillment_nested = Some(forward.clone());

        let mut incoming = obligation(3, 4);
        let ProofNodeKind::Obligation {
            fulfillment_nested, ..
        } = &mut incoming.kind
        else {
            unreachable!()
        };
        *fulfillment_nested = Some(reverse);

        assert!(merge_node(&mut existing, incoming).unwrap());
        let ProofNodeKind::Obligation {
            fulfillment_nested: Some(merged),
            ..
        } = &existing.kind
        else {
            unreachable!()
        };
        assert_eq!(merged, &forward);
    }

    #[test]
    fn a_nested_projection_accepts_one_matching_query_result() {
        let expected_trace = trace();
        let expected_result = term(5);
        let mut existing = projection(None, None);
        assert!(
            merge_node(
                &mut existing,
                projection(Some(expected_trace.clone()), Some(expected_result.clone())),
            )
            .unwrap()
        );
        let ProofNodeKind::Projection {
            query_trace,
            normalized_result,
            ..
        } = &existing.kind
        else {
            unreachable!();
        };
        assert_eq!(query_trace.as_ref(), Some(&expected_trace));
        assert_eq!(normalized_result.as_ref(), Some(&expected_result));

        assert!(
            !merge_node(
                &mut existing,
                projection(Some(expected_trace), Some(term(6))),
            )
            .unwrap()
        );
        let ProofNodeKind::Projection {
            normalized_result, ..
        } = &existing.kind
        else {
            unreachable!();
        };
        assert_eq!(normalized_result.as_ref(), Some(&expected_result));
    }

    #[test]
    fn canonical_remap_updates_query_and_projection_references() {
        let mut kind = projection(Some(trace()), Some(term(5))).kind;
        remap_node_references(&mut kind, &[ProofId(2), ProofId(0), ProofId(3), ProofId(1)])
            .unwrap();
        let ProofNodeKind::Projection {
            owners,
            query_trace: Some(trace),
            ..
        } = kind
        else {
            unreachable!();
        };
        assert_eq!(owners, vec![ProofId(2)]);
        assert_eq!(trace.root, ProofId(2));
        assert_eq!(trace.obligations, vec![ProofId(2), ProofId(0)]);
        assert_eq!(trace.trait_selections, vec![ProofId(2)]);
        assert_eq!(trace.projections, vec![ProofId(3)]);
        assert_eq!(trace.fulfillments, vec![ProofId(0)]);
        assert_eq!(trace.cycles, vec![ProofId(1)]);
    }
}
