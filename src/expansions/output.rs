//! Validation and lowering of declarative-macro output products.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::FxHashMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_span::ExpnId;

#[cfg(rust_item_dependencies_patched)]
use crate::definitions::CollectedDefinitions;
use crate::dependency_graph::{
    DependencyEdge, DependencyKind, ExpansionId, ExpansionKind, ExpansionNode, GraphNode,
};
use crate::graph::{Definition, DefinitionId, DefinitionOrigin};
use crate::macro_output::MacroOutputRange;
#[cfg(rust_item_dependencies_patched)]
use crate::macro_output::ValidatedMacroOwnerOutput;
#[cfg(test)]
use crate::macro_output::normalize_discarded_output_ranges;
#[cfg(any(rust_item_dependencies_patched, test))]
use crate::macro_output::{ValidatedMacroOutputLedger, laminar_output_ranges};
#[cfg(test)]
use crate::source::SourceUnitId;
#[cfg(rust_item_dependencies_patched)]
use crate::source::declarative_generation_parent;
#[cfg(any(rust_item_dependencies_patched, test))]
use crate::source::{ByteRange, OwnedPiece, PieceKind};

use super::ExpansionError;
#[cfg(rust_item_dependencies_patched)]
use super::RawExpansion;
#[cfg(test)]
use super::provenance::{
    ComponentRepetitionIndex, IndexedSourceUnit, SourceAncestorExclusions, SourceAncestryIndex,
    SourceUnitIntervalIndex, containing_child, with_flat_product_basis_index,
};
#[cfg(any(rust_item_dependencies_patched, test))]
use super::provenance::{IndexedInterval, IntervalStartIndex};
use super::provenance::{MacroContributorDag, MacroContributorSetId};
#[cfg(rust_item_dependencies_patched)]
use super::provenance::{MacroProvenance, PreparedProducer};

/// All producer-local output ledgers and the one contributor DAG their root
/// identifiers belong to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MacroProducerCoverageInventory {
    contributor_dag: Arc<MacroContributorDag>,
    producers: Vec<MacroProducerCoverage>,
}

/// The complete semantic-output census for local declarative macro
/// occurrences. Unlike [`MacroProducerCoverageInventory`], this inventory is
/// independent of source refinement and contains no editable-source
/// provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MacroCompleteOutputMeaningInventory {
    producers: Vec<MacroCompleteOutputMeaning>,
}

impl MacroCompleteOutputMeaningInventory {
    fn new(producers: Vec<MacroCompleteOutputMeaning>) -> Result<Self, ExpansionError> {
        if producers.windows(2).any(|pair| pair[0] >= pair[1])
            || producers.iter().any(|producer| {
                (!producer.intrinsic && producer.dependent_expansions.is_empty())
                    || producer
                        .dependent_expansions
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                    || producer
                        .actual_demand_definitions
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                    || producer
                        .output_demands
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                    || producer.output_demands.iter().any(|demand| {
                        demand.carriers.is_empty()
                            || demand.carriers.windows(2).any(|pair| pair[0] >= pair[1])
                            || (demand.dependent_expansions.is_empty()
                                && demand.required_expansions.is_empty())
                            || demand
                                .dependent_expansions
                                .windows(2)
                                .any(|pair| pair[0] >= pair[1])
                            || demand
                                .required_expansions
                                .windows(2)
                                .any(|pair| pair[0] >= pair[1])
                            || demand.dependent_expansions.iter().any(|expansion| {
                                demand.required_expansions.binary_search(expansion).is_ok()
                            })
                    })
            })
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        Ok(Self { producers })
    }

    pub(crate) fn producers(&self) -> &[MacroCompleteOutputMeaning] {
        &self.producers
    }

    #[cfg(test)]
    pub(crate) fn test_new(producers: Vec<MacroCompleteOutputMeaning>) -> Self {
        Self::new(producers).expect("test output-meaning facts must be structurally valid")
    }
}

/// Meaning carried by one nonempty, completely observed declarative macro
/// output. A producer is meaningful when it has intrinsic output or at least
/// one dependent child expansion is meaningful.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroCompleteOutputMeaning {
    producer: ExpansionId,
    intrinsic: bool,
    residual_intrinsic: bool,
    dependent_expansions: Box<[ExpansionId]>,
    actual_demand_definitions: Box<[DefinitionId]>,
    output_demands: Box<[MacroOutputDemand]>,
}

impl MacroCompleteOutputMeaning {
    pub(crate) fn producer(&self) -> ExpansionId {
        self.producer
    }

    pub(crate) fn intrinsic(&self) -> bool {
        self.intrinsic
    }

    pub(crate) fn residual_intrinsic(&self) -> bool {
        self.residual_intrinsic
    }

    pub(crate) fn dependent_expansions(&self) -> &[ExpansionId] {
        &self.dependent_expansions
    }

    pub(crate) fn actual_demand_definitions(&self) -> &[DefinitionId] {
        &self.actual_demand_definitions
    }

    pub(crate) fn output_demands(&self) -> &[MacroOutputDemand] {
        &self.output_demands
    }

    #[cfg(test)]
    pub(crate) fn test_new(
        producer: ExpansionId,
        intrinsic: bool,
        dependent_expansions: Vec<ExpansionId>,
    ) -> Self {
        Self {
            producer,
            intrinsic,
            residual_intrinsic: intrinsic,
            dependent_expansions: dependent_expansions.into_boxed_slice(),
            actual_demand_definitions: Box::new([]),
            output_demands: Box::new([]),
        }
    }

    #[cfg(test)]
    pub(crate) fn test_set_actual_demand(
        &mut self,
        residual_intrinsic: bool,
        actual_demand_definitions: Vec<DefinitionId>,
        output_demands: Vec<(Vec<DefinitionId>, Vec<ExpansionId>, Vec<ExpansionId>)>,
    ) {
        self.residual_intrinsic = residual_intrinsic;
        self.actual_demand_definitions = actual_demand_definitions.into_boxed_slice();
        self.output_demands = output_demands
            .into_iter()
            .map(
                |(carriers, dependent_expansions, required_expansions)| MacroOutputDemand {
                    carriers: carriers.into_boxed_slice(),
                    dependent_expansions: dependent_expansions.into_boxed_slice(),
                    required_expansions: required_expansions.into_boxed_slice(),
                },
            )
            .collect();
    }
}

impl MacroProducerCoverageInventory {
    fn new(
        contributor_dag: Arc<MacroContributorDag>,
        producers: Vec<MacroProducerCoverage>,
    ) -> Result<Self, ExpansionError> {
        let mut identity_cohorts =
            BTreeMap::<MacroContributorSetId, (usize, BTreeSet<MacroContributorSetId>)>::new();
        if producers.iter().any(|producer| {
            producer.materialization_groups.iter().any(|group| {
                group.contributor_roots.is_empty()
                    || group
                        .contributor_roots
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                    || group
                        .contributor_roots
                        .iter()
                        .any(|root| contributor_dag.node(*root).is_none())
                    || group
                        .identity_cohort_root
                        .is_some_and(|root| contributor_dag.node(root).is_none())
            })
        }) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        for group in producers
            .iter()
            .flat_map(|producer| &producer.materialization_groups)
        {
            if let Some(root) = group.identity_cohort_root {
                let cohort = identity_cohorts.entry(root).or_default();
                cohort.0 += 1;
                cohort.1.extend(group.contributor_roots.iter().copied());
            }
        }
        for (gate, (uses, roots)) in identity_cohorts {
            let valid_gate = match roots.iter().copied().collect::<Vec<_>>().as_slice() {
                [root] => gate == *root,
                [] => false,
                expected => contributor_dag
                    .node(gate)
                    .is_some_and(|(local, parents)| local.is_empty() && parents == expected),
            };
            if uses < 2 || !valid_gate {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        Ok(Self {
            contributor_dag,
            producers,
        })
    }

    pub(crate) fn contributor_dag(&self) -> &MacroContributorDag {
        &self.contributor_dag
    }

    pub(crate) fn shared_contributor_dag(&self) -> Arc<MacroContributorDag> {
        Arc::clone(&self.contributor_dag)
    }

    pub(crate) fn producers(&self) -> &[MacroProducerCoverage] {
        &self.producers
    }

    #[cfg(test)]
    pub(crate) fn test_new(producers: Vec<MacroProducerCoverage>) -> Self {
        let max_source = producers
            .iter()
            .flat_map(|producer| &producer.materialization_groups)
            .flat_map(|group| group.contributor_roots.iter())
            .map(|root| root.test_source_unit().0)
            .max();
        Self {
            contributor_dag: Arc::new(MacroContributorDag::test_source_singletons(max_source)),
            producers,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_producers_mut(&mut self) -> &mut Vec<MacroProducerCoverage> {
        &mut self.producers
    }
}

/// The independent and exhaustive output ledger emitted by one macro
/// producer. Construction uses the same prepared token provenance as
/// definition identity, so the observer census and lowered constraints cannot
/// diverge.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroProducerCoverage {
    pub(super) producer: ExpansionId,
    pub(super) output_token_count: u32,
    /// Normalized output ranges removed by compiler configuration before they
    /// could materialize a product or owner effect.
    pub(super) discarded_outputs: Vec<MacroOutputRange>,
    pub(super) materialization_groups: Vec<MacroOutputMaterializationGroup>,
}

impl MacroProducerCoverage {
    pub(crate) fn producer(&self) -> ExpansionId {
        self.producer
    }

    pub(crate) fn output_token_count(&self) -> u32 {
        self.output_token_count
    }

    pub(crate) fn discarded_outputs(&self) -> &[MacroOutputRange] {
        &self.discarded_outputs
    }

    pub(crate) fn materialization_groups(&self) -> &[MacroOutputMaterializationGroup] {
        &self.materialization_groups
    }

    #[cfg(test)]
    pub(crate) fn test_new(
        producer: ExpansionId,
        output_token_count: u32,
        materialization_groups: Vec<MacroOutputMaterializationGroup>,
    ) -> Self {
        Self {
            producer,
            output_token_count,
            discarded_outputs: Vec::new(),
            materialization_groups,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_set_discarded_outputs(&mut self, discarded_outputs: Vec<MacroOutputRange>) {
        self.discarded_outputs = discarded_outputs;
    }

    #[cfg(test)]
    pub(crate) fn test_set_output_token_count(&mut self, output_token_count: u32) {
        self.output_token_count = output_token_count;
    }

    #[cfg(test)]
    pub(crate) fn test_materialization_groups_mut(
        &mut self,
    ) -> &mut Vec<MacroOutputMaterializationGroup> {
        &mut self.materialization_groups
    }

    #[cfg(test)]
    pub(crate) fn test_single_slice_group_mut(&mut self, group: usize) -> &mut MacroOutputSlice {
        let slices = &mut self.materialization_groups[group].output_slices;
        let [slice] = slices.as_mut_slice() else {
            panic!("test expected one output slice in the materialization group")
        };
        slice
    }
}

/// Output classes which are materialized by one producer-local source
/// contributor set. Group membership is an explicit observer fact; equal
/// contributor values in two groups do not merge them.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroOutputMaterializationGroup {
    pub(super) contributor_roots: Box<[MacroContributorSetId]>,
    /// Retention-only gate shared by all producer-local groups in one
    /// definition-identity component. Producer provenance continues to use
    /// `contributor_roots` exclusively.
    pub(super) identity_cohort_root: Option<MacroContributorSetId>,
    pub(super) output_demands: Box<[MacroOutputDemand]>,
    pub(super) output_slices: Vec<MacroOutputSlice>,
}

/// Child products whose source is controlled by demand for their nearest
/// generated-definition container, or the producer's source owner when no
/// such container exists.
///
/// Required children are needed whenever a carrier is compiled. Dependent
/// children are independently removable and need the group only when both a
/// carrier and that child are demanded.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroOutputDemand {
    carriers: Box<[DefinitionId]>,
    dependent_expansions: Box<[ExpansionId]>,
    required_expansions: Box<[ExpansionId]>,
}

impl MacroOutputDemand {
    /// Definitions whose compiler demand activates this clause. Multiple
    /// definitions describe one exact generated-product class; any member is
    /// sufficient.
    pub(crate) fn carriers(&self) -> &[DefinitionId] {
        &self.carriers
    }

    pub(crate) fn dependent_expansions(&self) -> &[ExpansionId] {
        &self.dependent_expansions
    }

    pub(crate) fn required_expansions(&self) -> &[ExpansionId] {
        &self.required_expansions
    }
}

impl MacroOutputMaterializationGroup {
    pub(crate) fn contributor_roots(&self) -> &[MacroContributorSetId] {
        &self.contributor_roots
    }

    pub(crate) fn identity_cohort_root(&self) -> Option<MacroContributorSetId> {
        self.identity_cohort_root
    }

    pub(crate) fn output_demands(&self) -> &[MacroOutputDemand] {
        &self.output_demands
    }

    pub(crate) fn output_slices(&self) -> &[MacroOutputSlice] {
        &self.output_slices
    }

    #[cfg(test)]
    pub(crate) fn test_new(
        contributors: Vec<SourceUnitId>,
        output_slices: Vec<MacroOutputSlice>,
    ) -> Self {
        let contributor_roots = contributors
            .into_iter()
            .map(MacroContributorSetId::test_from_source_unit)
            .collect::<Vec<_>>();
        Self {
            contributor_roots: contributor_roots.into_boxed_slice(),
            identity_cohort_root: None,
            output_demands: Box::new([]),
            output_slices,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_set_output_demands(
        &mut self,
        demands: Vec<(Vec<DefinitionId>, Vec<ExpansionId>, Vec<ExpansionId>)>,
    ) {
        self.output_demands = demands
            .into_iter()
            .map(
                |(carriers, dependent_expansions, required_expansions)| MacroOutputDemand {
                    carriers: carriers.into_boxed_slice(),
                    dependent_expansions: dependent_expansions.into_boxed_slice(),
                    required_expansions: required_expansions.into_boxed_slice(),
                },
            )
            .collect();
    }

    #[cfg(test)]
    pub(crate) fn contributors(&self) -> Vec<SourceUnitId> {
        self.contributor_roots
            .iter()
            .map(|root| root.test_source_unit())
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn test_set_contributors(&mut self, contributors: Vec<SourceUnitId>) {
        let roots = contributors
            .into_iter()
            .map(MacroContributorSetId::test_from_source_unit)
            .collect::<Vec<_>>();
        self.contributor_roots = roots.into_boxed_slice();
    }

    #[cfg(test)]
    pub(crate) fn test_output_slices_mut(&mut self) -> &mut Vec<MacroOutputSlice> {
        &mut self.output_slices
    }
}

/// One syntax-product class in a macro output ledger. Its representation is
/// private so consumers can validate but cannot manufacture production facts.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroOutputSlice {
    pub(super) output_ranges: Vec<MacroOutputRange>,
    pub(super) class: MacroOutputClass,
}

impl MacroOutputSlice {
    pub(crate) fn output_ranges(&self) -> &[MacroOutputRange] {
        &self.output_ranges
    }

    pub(crate) fn products(&self) -> Option<&[GraphNode]> {
        match &self.class {
            MacroOutputClass::Products(products) => Some(products),
            MacroOutputClass::OwnerEffect { .. } => None,
        }
    }

    pub(crate) fn owner_effect(&self) -> Option<(DefinitionId, &[GraphNode], &MacroOwnerEffect)> {
        match &self.class {
            MacroOutputClass::Products(_) => None,
            MacroOutputClass::OwnerEffect {
                owner,
                members,
                effect,
            } => Some((*owner, members, effect)),
        }
    }

    #[cfg(test)]
    pub(crate) fn test_new_products(
        output_ranges: Vec<MacroOutputRange>,
        products: Vec<GraphNode>,
    ) -> Self {
        Self {
            output_ranges,
            class: MacroOutputClass::Products(products),
        }
    }

    #[cfg(test)]
    pub(crate) fn test_new_owner_effect(
        output_ranges: Vec<MacroOutputRange>,
        owner: DefinitionId,
    ) -> Self {
        Self {
            output_ranges,
            class: MacroOutputClass::OwnerEffect {
                owner,
                members: Vec::new(),
                effect: MacroOwnerEffect::Semantic,
            },
        }
    }

    #[cfg(test)]
    pub(crate) fn test_set_transparent_owner_effect(&mut self, dependent_products: Vec<GraphNode>) {
        let MacroOutputClass::OwnerEffect { effect, .. } = &mut self.class else {
            panic!("test slice is not an owner effect");
        };
        *effect = MacroOwnerEffect::TransparentShell { dependent_products };
    }

    #[cfg(test)]
    pub(crate) fn test_output_ranges_mut(&mut self) -> &mut Vec<MacroOutputRange> {
        &mut self.output_ranges
    }

    #[cfg(test)]
    pub(crate) fn test_set_products(&mut self, products: Vec<GraphNode>) {
        self.class = MacroOutputClass::Products(products);
    }

    #[cfg(test)]
    pub(crate) fn test_set_owner_effect(&mut self, owner: DefinitionId) {
        self.class = MacroOutputClass::OwnerEffect {
            owner,
            members: Vec::new(),
            effect: MacroOwnerEffect::Semantic,
        };
    }

    #[cfg(test)]
    pub(crate) fn test_set_owner_members(&mut self, members: Vec<GraphNode>) {
        let MacroOutputClass::OwnerEffect {
            members: existing, ..
        } = &mut self.class
        else {
            panic!("test slice is not an owner effect");
        };
        *existing = members;
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum MacroOutputClass {
    Products(Vec<GraphNode>),
    OwnerEffect {
        owner: DefinitionId,
        members: Vec<GraphNode>,
        effect: MacroOwnerEffect,
    },
}

/// Meaning carried by output tokens which do not belong to an independent
/// compiler product.
///
/// A semantic effect is conservatively retained with its source owner. A
/// transparent shell consists only of parser-observed structural syntax
/// around the listed products, and therefore inherits their meaning.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum MacroOwnerEffect {
    Semantic,
    TransparentShell { dependent_products: Vec<GraphNode> },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MacroDefinitionProductRole {
    Root,
    Subordinate,
}

/// Classifies whether one generated definition is an independently
/// materialized syntax node. Compiler-generated roles remain subordinate even
/// when rustc reports an item-like definition kind.
pub(crate) fn macro_definition_product_role(
    definition: &Definition,
) -> Option<MacroDefinitionProductRole> {
    match definition.origin {
        DefinitionOrigin::Expanded {
            generated_role: Some(_),
            ..
        }
        | DefinitionOrigin::CompilerGenerated { .. } => {
            return Some(MacroDefinitionProductRole::Subordinate);
        }
        DefinitionOrigin::Expanded {
            generated_role: None,
            ..
        } => {}
        DefinitionOrigin::Written { .. } | DefinitionOrigin::Injected { .. } => return None,
    }

    Some(match definition.kind {
        crate::graph::DefinitionKind::Crate => return None,
        crate::graph::DefinitionKind::Module
        | crate::graph::DefinitionKind::Function
        | crate::graph::DefinitionKind::Static
        | crate::graph::DefinitionKind::Const
        | crate::graph::DefinitionKind::TypeAlias
        | crate::graph::DefinitionKind::Struct
        | crate::graph::DefinitionKind::Enum
        | crate::graph::DefinitionKind::Union
        | crate::graph::DefinitionKind::Trait
        | crate::graph::DefinitionKind::TraitAlias
        | crate::graph::DefinitionKind::AssociatedType
        | crate::graph::DefinitionKind::AssociatedFunction
        | crate::graph::DefinitionKind::AssociatedConst
        | crate::graph::DefinitionKind::Impl
        | crate::graph::DefinitionKind::ExternCrate
        | crate::graph::DefinitionKind::Use
        | crate::graph::DefinitionKind::ForeignModule
        | crate::graph::DefinitionKind::ForeignType
        | crate::graph::DefinitionKind::GlobalAsm
        | crate::graph::DefinitionKind::Macro => MacroDefinitionProductRole::Root,
        crate::graph::DefinitionKind::OpaqueType
        | crate::graph::DefinitionKind::Variant
        | crate::graph::DefinitionKind::Field
        | crate::graph::DefinitionKind::Constructor
        | crate::graph::DefinitionKind::TypeParameter
        | crate::graph::DefinitionKind::ConstParameter
        | crate::graph::DefinitionKind::LifetimeParameter
        | crate::graph::DefinitionKind::Closure
        | crate::graph::DefinitionKind::Coroutine
        | crate::graph::DefinitionKind::CoroutineClosure
        | crate::graph::DefinitionKind::SyntheticCoroutineBody
        | crate::graph::DefinitionKind::AnonymousConst
        | crate::graph::DefinitionKind::InlineConst => MacroDefinitionProductRole::Subordinate,
    })
}

pub(crate) fn validated_outputless_macro_expansions(
    expansions: &[ExpansionNode],
    edges: &[DependencyEdge],
    candidates: &[ExpansionId],
) -> Option<BTreeSet<ExpansionId>> {
    let candidate_count = candidates.len();
    let candidates = candidates.iter().copied().collect::<BTreeSet<_>>();
    if candidates.len() != candidate_count
        || candidates.iter().any(|candidate| {
            expansions
                .get(candidate.0 as usize)
                .is_none_or(|expansion| {
                    expansion.id != *candidate
                        || !matches!(expansion.kind, ExpansionKind::Macro { .. })
                        || expansion.implementation.is_none()
                })
        })
        || expansions.iter().any(|expansion| {
            [
                expansion.discovered_in,
                expansion.semantic_parent,
                expansion.source_call_parent,
            ]
            .into_iter()
            .flatten()
            .any(|parent| candidates.contains(&parent))
        })
    {
        return None;
    }
    if edges.iter().any(|edge| {
        candidates.contains(&match edge.to {
            GraphNode::Expansion(expansion) => expansion,
            _ => return false,
        }) && matches!(
            edge.kind,
            DependencyKind::GeneratedBy
                | DependencyKind::ExpansionDiscoveredIn
                | DependencyKind::ExpansionSemanticParent
                | DependencyKind::ExpansionSourceCallParent
        )
    }) {
        return None;
    }
    Some(candidates)
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ObservedProduct {
    output: MacroOutputRange,
    product: GraphNode,
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct ClassifiedDefinitionProducts {
    products: Vec<ObservedProduct>,
    owner_members: Vec<ObservedProduct>,
    owner: Option<DefinitionId>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DefinitionProductContainer {
    Root(DefinitionId),
    Owner(DefinitionId),
}

#[cfg(any(rust_item_dependencies_patched, test))]
pub(super) struct MacroProductIdentityRangeIndex {
    source_len: u32,
    pieces: Box<[ByteRange]>,
    tokens: Box<[ByteRange]>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl MacroProductIdentityRangeIndex {
    pub(super) fn new(source: &str, pieces: &[OwnedPiece]) -> Result<Self, ExpansionError> {
        let source_len =
            u32::try_from(source.len()).map_err(|_| ExpansionError::IncompleteOrigin)?;
        let mut cursor = 0;
        let mut ranges = Vec::with_capacity(pieces.len());
        let mut tokens = Vec::new();
        for piece in pieces {
            if piece.range.start != cursor
                || piece.range.start >= piece.range.end
                || piece.range.end > source_len
                || !source.is_char_boundary(piece.range.start as usize)
                || !source.is_char_boundary(piece.range.end as usize)
            {
                return Err(ExpansionError::IncompleteOrigin);
            }
            ranges.push(piece.range);
            if piece.kind == PieceKind::Token {
                tokens.push(piece.range);
            }
            cursor = piece.range.end;
        }
        if cursor != source_len {
            return Err(ExpansionError::IncompleteOrigin);
        }
        Ok(Self {
            source_len,
            pieces: ranges.into_boxed_slice(),
            tokens: tokens.into_boxed_slice(),
        })
    }

    pub(super) fn identity_range(
        &self,
        full_range: ByteRange,
    ) -> Result<ByteRange, ExpansionError> {
        self.identity_range_with_probe(full_range, || {})
    }

    fn identity_range_with_probe(
        &self,
        full_range: ByteRange,
        mut probe: impl FnMut(),
    ) -> Result<ByteRange, ExpansionError> {
        if full_range.start >= full_range.end || full_range.end > self.source_len {
            return Err(ExpansionError::IncompleteOrigin);
        }
        self.pieces
            .binary_search_by(|piece| {
                probe();
                piece.start.cmp(&full_range.start)
            })
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        self.pieces
            .binary_search_by(|piece| {
                probe();
                piece.end.cmp(&full_range.end)
            })
            .map_err(|_| ExpansionError::IncompleteOrigin)?;

        let first = self.tokens.partition_point(|token| {
            probe();
            token.end <= full_range.start
        });
        let after_last = self.tokens.partition_point(|token| {
            probe();
            token.start < full_range.end
        });
        let (first, last) = self.tokens[first..after_last]
            .first()
            .zip(self.tokens[first..after_last].last())
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let range = ByteRange {
            start: first.start,
            end: last.end,
        };
        full_range
            .contains(range)
            .then_some(range)
            .ok_or(ExpansionError::IncompleteOrigin)
    }

    #[cfg(test)]
    fn identity_range_work(
        &self,
        full_range: ByteRange,
    ) -> Result<(ByteRange, usize), ExpansionError> {
        let mut work = 0;
        let range = self.identity_range_with_probe(full_range, || work += 1)?;
        Ok((range, work))
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn classify_definition_products(
    definitions: &[Definition],
    generated: &BTreeSet<DefinitionId>,
    observed_outputs: &BTreeMap<DefinitionId, MacroOutputRange>,
) -> Result<ClassifiedDefinitionProducts, ExpansionError> {
    if observed_outputs
        .keys()
        .any(|definition| !generated.contains(definition))
    {
        return Err(ExpansionError::IncompleteOrigin);
    }

    let definition = |id: DefinitionId| {
        definitions
            .get(id.0 as usize)
            .filter(|definition| definition.id == id)
            .ok_or(ExpansionError::IncompleteOrigin)
    };
    let may_inherit_output = |definition: &Definition| {
        matches!(
            definition.origin,
            DefinitionOrigin::CompilerGenerated { .. }
                | DefinitionOrigin::Expanded {
                    generated_role: Some(_),
                    ..
                }
        ) && macro_definition_product_role(definition)
            == Some(MacroDefinitionProductRole::Subordinate)
    };
    let mut resolved_outputs = observed_outputs.clone();
    for &id in generated {
        if resolved_outputs.contains_key(&id) {
            continue;
        }
        if !may_inherit_output(definition(id)?) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut current = id;
        let mut path = Vec::new();
        let mut active = BTreeSet::new();
        let output = loop {
            if let Some(&output) = resolved_outputs.get(&current) {
                break output;
            }
            if !active.insert(current) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let current_definition = definition(current)?;
            if !generated.contains(&current) || !may_inherit_output(current_definition) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            path.push(current);
            current = current_definition
                .parent
                .ok_or(ExpansionError::IncompleteOrigin)?;
        };
        for member in path {
            if resolved_outputs.insert(member, output).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
    }
    let mut containers = BTreeMap::new();
    for &id in generated {
        if macro_definition_product_role(definition(id)?) == Some(MacroDefinitionProductRole::Root)
        {
            containers.insert(id, DefinitionProductContainer::Root(id));
        }
    }
    for &id in generated {
        if containers.contains_key(&id) {
            continue;
        }
        let mut current = id;
        let mut path = Vec::new();
        let mut active = BTreeSet::new();
        let container = loop {
            if let Some(&container) = containers.get(&current) {
                break container;
            }
            if !active.insert(current) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let record = definition(current)?;
            let Some(role) = macro_definition_product_role(record) else {
                if generated.contains(&current) {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                break DefinitionProductContainer::Owner(current);
            };
            if !generated.contains(&current) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            match role {
                MacroDefinitionProductRole::Root => {
                    break DefinitionProductContainer::Root(current);
                }
                MacroDefinitionProductRole::Subordinate => {
                    path.push(current);
                    current = record.parent.ok_or(ExpansionError::IncompleteOrigin)?;
                }
            }
        };
        for member in path {
            if containers.insert(member, container).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
    }

    let mut products = Vec::new();
    let mut owner_members = Vec::new();
    let mut owner = None;
    for &id in generated {
        let output = *resolved_outputs
            .get(&id)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        match containers
            .get(&id)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?
        {
            DefinitionProductContainer::Root(root) => {
                let root_output = *resolved_outputs
                    .get(&root)
                    .ok_or(ExpansionError::IncompleteOrigin)?;
                if !root_output.contains(output) {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                products.push(ObservedProduct {
                    output: root_output,
                    product: GraphNode::Definition(id),
                });
            }
            DefinitionProductContainer::Owner(member_owner) => {
                if owner
                    .replace(member_owner)
                    .is_some_and(|owner| owner != member_owner)
                {
                    return Err(ExpansionError::IncompleteOrigin);
                }
                owner_members.push(ObservedProduct {
                    output,
                    product: GraphNode::Definition(id),
                });
            }
        }
    }
    products.sort();
    owner_members.sort_by_key(|member| member.product);
    if owner_members
        .windows(2)
        .any(|pair| pair[0].product >= pair[1].product)
    {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok(ClassifiedDefinitionProducts {
        products,
        owner_members,
        owner,
    })
}

#[cfg(test)]
mod product_classification_tests {
    use super::*;
    use crate::graph::{DefinitionKey, DefinitionKind, GeneratedRole};
    use crate::source::{ByteRange, OwnedPiece, PieceKind, WrittenUnitKind};

    fn identity_index(segments: &[(&str, PieceKind)]) -> (String, MacroProductIdentityRangeIndex) {
        let source = segments
            .iter()
            .map(|(segment, _)| *segment)
            .collect::<String>();
        let mut start = 0;
        let pieces = segments
            .iter()
            .map(|(segment, kind)| {
                let end = start + u32::try_from(segment.len()).unwrap();
                let piece = OwnedPiece {
                    range: ByteRange { start, end },
                    owner: SourceUnitId(0),
                    kind: *kind,
                };
                start = end;
                piece
            })
            .collect::<Vec<_>>();
        let index = MacroProductIdentityRangeIndex::new(&source, &pieces).unwrap();
        (source, index)
    }

    fn range(start: u32, end: u32) -> MacroOutputRange {
        MacroOutputRange { start, end }
    }

    fn output_classes(
        products: &[ObservedProduct],
        discarded: &[MacroOutputRange],
        output_token_count: u32,
        source_owner: Option<DefinitionId>,
    ) -> Result<PendingOutputClasses, ExpansionError> {
        let ledger = ValidatedMacroOutputLedger::new(
            output_token_count,
            products.iter().map(|product| product.output).collect(),
            discarded.to_vec(),
        )
        .ok_or(ExpansionError::IncompleteOrigin)?;
        super::output_classes(products, &ledger, source_owner)
    }

    fn output_classes_with_work(
        products: &[ObservedProduct],
        discarded: &[MacroOutputRange],
        output_token_count: u32,
        source_owner: Option<DefinitionId>,
    ) -> Result<(PendingOutputClasses, OutputClassWork), ExpansionError> {
        let ledger = ValidatedMacroOutputLedger::new(
            output_token_count,
            products.iter().map(|product| product.output).collect(),
            discarded.to_vec(),
        )
        .ok_or(ExpansionError::IncompleteOrigin)?;
        super::output_classes_with_work(products, &ledger, source_owner)
    }

    fn validate_owner_member_classes(
        members: &[ObservedProduct],
        products: &[ObservedProduct],
        discarded: &[MacroOutputRange],
        output_token_count: u32,
        classes: &[(MacroOutputRange, PendingOutputClass)],
    ) -> Result<Vec<GraphNode>, ExpansionError> {
        let live_outputs = products
            .iter()
            .chain(members)
            .map(|product| product.output)
            .collect();
        let ledger =
            ValidatedMacroOutputLedger::new(output_token_count, live_outputs, discarded.to_vec())
                .ok_or(ExpansionError::IncompleteOrigin)?;
        super::validate_owner_member_classes(members, products, &ledger, classes)
    }

    #[test]
    fn product_identity_range_uses_the_token_piece_envelope() {
        let (source, index) = identity_index(&[
            ("  ", PieceKind::Trivia),
            ("kept", PieceKind::Token),
            (",", PieceKind::Token),
            (" ", PieceKind::Trivia),
            ("/* next */", PieceKind::Trivia),
            (" ", PieceKind::Trivia),
        ]);
        let full_range = ByteRange {
            start: 0,
            end: u32::try_from(source.len()).unwrap(),
        };
        let identity = index.identity_range(full_range).unwrap();

        assert_eq!(
            identity,
            ByteRange { start: 2, end: 7 },
            "leading and trailing trivia must not change identity",
        );
        assert_eq!(
            &source[identity.start as usize..identity.end as usize],
            "kept,",
            "significant punctuation remains part of identity",
        );
    }

    #[test]
    fn product_identity_range_rejects_a_trivia_only_unit() {
        let (source, index) = identity_index(&[
            (" \t", PieceKind::Trivia),
            ("/* no parser token */", PieceKind::Trivia),
            (" ", PieceKind::Trivia),
        ]);
        assert_eq!(
            index.identity_range(ByteRange {
                start: 0,
                end: u32::try_from(source.len()).unwrap(),
            }),
            Err(ExpansionError::IncompleteOrigin)
        );
    }

    #[test]
    fn product_identity_range_skips_bom_and_shebang_trivia() {
        let (source, index) = identity_index(&[
            ("\u{feff}", PieceKind::Trivia),
            ("#!/usr/bin/env rustx\n", PieceKind::Trivia),
            ("kept", PieceKind::Token),
            ("\n", PieceKind::Trivia),
        ]);
        let start = u32::try_from("\u{feff}#!/usr/bin/env rustx\n".len()).unwrap();

        assert_eq!(
            index
                .identity_range(ByteRange {
                    start: 0,
                    end: u32::try_from(source.len()).unwrap(),
                })
                .unwrap(),
            ByteRange {
                start,
                end: start + 4,
            }
        );
    }

    #[test]
    fn product_identity_range_rejects_non_piece_and_utf8_boundary_cuts() {
        let (source, index) = identity_index(&[
            ("éclair", PieceKind::Token),
            (" ", PieceKind::Trivia),
            ("+", PieceKind::Token),
            (" ", PieceKind::Trivia),
            ("β", PieceKind::Token),
        ]);
        let end = u32::try_from(source.len()).unwrap();

        for range in [
            ByteRange { start: 0, end: 0 },
            ByteRange { start: 1, end },
            ByteRange { start: 2, end },
            ByteRange {
                start: 0,
                end: end - 1,
            },
            ByteRange {
                start: 0,
                end: end + 1,
            },
        ] {
            assert_eq!(
                index.identity_range(range),
                Err(ExpansionError::IncompleteOrigin),
                "range {range:?} must fail closed",
            );
        }
    }

    #[test]
    fn product_identity_index_rejects_malformed_piece_coverage() {
        let piece = |start, end| OwnedPiece {
            range: ByteRange { start, end },
            owner: SourceUnitId(0),
            kind: PieceKind::Token,
        };
        for pieces in [
            vec![piece(0, 1), piece(2, 3)],
            vec![piece(0, 2), piece(1, 3)],
            vec![piece(1, 3)],
            vec![piece(0, 2)],
            vec![piece(0, 0), piece(0, 3)],
        ] {
            assert!(MacroProductIdentityRangeIndex::new("abc", &pieces).is_err());
        }
    }

    #[test]
    fn nested_product_identity_queries_do_logarithmic_work() {
        const TOKENS: usize = 1 << 15;
        let segments = (0..TOKENS)
            .flat_map(|_| [("x", PieceKind::Token), (" ", PieceKind::Trivia)])
            .collect::<Vec<_>>();
        let (source, index) = identity_index(&segments);
        let end = u32::try_from(source.len()).unwrap();
        let mut work = 0;

        for start in (0..end).step_by(2) {
            let (range, query_work) = index.identity_range_work(ByteRange { start, end }).unwrap();
            assert_eq!(
                range,
                ByteRange {
                    start,
                    end: end - 1
                }
            );
            work += query_work;
        }

        assert!(work <= TOKENS * 68, "observed {work} index probes");
    }

    fn written_owner() -> Definition {
        Definition {
            id: DefinitionId(0),
            key: DefinitionKey(Vec::new()),
            kind: DefinitionKind::Function,
            parent: None,
            origin: DefinitionOrigin::Written {
                unit: SourceUnitId(0),
                unit_range: ByteRange { start: 0, end: 100 },
                anchor: ByteRange { start: 0, end: 100 },
                unit_kind: WrittenUnitKind::Item,
                unit_ordinal: 0,
            },
        }
    }

    fn expanded(
        id: u32,
        kind: DefinitionKind,
        parent: u32,
        generated_role: Option<GeneratedRole>,
    ) -> Definition {
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(Vec::new()),
            kind,
            parent: Some(DefinitionId(parent)),
            origin: DefinitionOrigin::Expanded {
                invocation: SourceUnitId(1),
                invocation_range: ByteRange { start: 10, end: 20 },
                generated_role,
                ordinal: 0,
            },
        }
    }

    #[test]
    fn body_local_subordinates_belong_to_the_owner_effect() {
        let definitions = vec![
            written_owner(),
            expanded(1, DefinitionKind::Closure, 0, None),
            expanded(2, DefinitionKind::AnonymousConst, 0, None),
            expanded(3, DefinitionKind::InlineConst, 2, None),
        ];
        let generated = [DefinitionId(1), DefinitionId(2), DefinitionId(3)]
            .into_iter()
            .collect();
        let observed = BTreeMap::from([
            (DefinitionId(1), range(0, 2)),
            (DefinitionId(2), range(2, 4)),
            (DefinitionId(3), range(2, 4)),
        ]);

        let classified = classify_definition_products(&definitions, &generated, &observed)
            .expect("complete subordinate census must classify");

        assert!(classified.products.is_empty());
        assert_eq!(classified.owner, Some(DefinitionId(0)));
        assert_eq!(
            classified
                .owner_members
                .into_iter()
                .map(|member| member.product)
                .collect::<Vec<_>>(),
            vec![
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
                GraphNode::Definition(DefinitionId(3)),
            ]
        );
    }

    #[test]
    fn subordinates_use_the_nearest_generated_root_on_the_parent_chain() {
        let definitions = vec![
            written_owner(),
            expanded(1, DefinitionKind::Function, 0, None),
            expanded(2, DefinitionKind::Function, 1, None),
            expanded(3, DefinitionKind::Closure, 2, None),
            expanded(4, DefinitionKind::Field, 1, None),
            expanded(
                5,
                DefinitionKind::AssociatedType,
                1,
                Some(GeneratedRole::AnonymousAssociatedType),
            ),
        ];
        let generated = (1..=5).map(DefinitionId).collect();
        let observed = BTreeMap::from([
            (DefinitionId(1), range(0, 10)),
            (DefinitionId(2), range(2, 8)),
            (DefinitionId(3), range(3, 4)),
            (DefinitionId(4), range(8, 9)),
        ]);

        let classified = classify_definition_products(&definitions, &generated, &observed)
            .expect("nested roots and their subordinates must classify");
        let products = classified
            .products
            .into_iter()
            .map(|product| (product.product, product.output))
            .collect::<BTreeMap<_, _>>();

        assert!(classified.owner_members.is_empty());
        assert_eq!(
            products[&GraphNode::Definition(DefinitionId(1))],
            range(0, 10)
        );
        assert_eq!(
            products[&GraphNode::Definition(DefinitionId(2))],
            range(2, 8)
        );
        assert_eq!(
            products[&GraphNode::Definition(DefinitionId(3))],
            range(2, 8)
        );
        assert_eq!(
            products[&GraphNode::Definition(DefinitionId(4))],
            range(0, 10)
        );
        assert_eq!(
            products[&GraphNode::Definition(DefinitionId(5))],
            range(0, 10)
        );
    }

    #[test]
    fn subordinate_classification_rejects_incomplete_or_cross_producer_roots() {
        let definitions = vec![
            written_owner(),
            expanded(1, DefinitionKind::Function, 0, None),
            expanded(2, DefinitionKind::Closure, 1, None),
        ];
        let both = [DefinitionId(1), DefinitionId(2)].into_iter().collect();
        let outside_root = BTreeMap::from([
            (DefinitionId(1), range(0, 5)),
            (DefinitionId(2), range(6, 7)),
        ]);
        assert_eq!(
            classify_definition_products(&definitions, &both, &outside_root).map(|_| ()),
            Err(ExpansionError::IncompleteOrigin)
        );

        let only_child = [DefinitionId(2)].into_iter().collect();
        let child_output = BTreeMap::from([(DefinitionId(2), range(1, 2))]);
        assert_eq!(
            classify_definition_products(&definitions, &only_child, &child_output).map(|_| ()),
            Err(ExpansionError::IncompleteOrigin)
        );

        let missing_explicit_subordinate = BTreeMap::from([(DefinitionId(1), range(0, 5))]);
        assert_eq!(
            classify_definition_products(&definitions, &both, &missing_explicit_subordinate)
                .map(|_| ()),
            Err(ExpansionError::IncompleteOrigin)
        );

        assert_eq!(
            classify_definition_products(&definitions, &both, &BTreeMap::new()).map(|_| ()),
            Err(ExpansionError::IncompleteOrigin)
        );
    }

    #[test]
    fn owner_member_range_may_contain_a_nested_product_but_needs_owner_residual() {
        let owner = DefinitionId(0);
        let member = ObservedProduct {
            output: range(0, 10),
            product: GraphNode::Definition(DefinitionId(1)),
        };
        let nested = ObservedProduct {
            output: range(2, 8),
            product: GraphNode::Definition(DefinitionId(2)),
        };
        let classes = output_classes(&[nested], &[], 10, Some(owner)).unwrap();

        assert_eq!(
            validate_owner_member_classes(&[member], &[nested], &[], 10, classes.intervals()),
            Ok(vec![member.product])
        );

        let whole = ObservedProduct {
            output: range(0, 10),
            product: nested.product,
        };
        let classes = output_classes(&[whole], &[], 10, Some(owner)).unwrap();
        assert_eq!(
            validate_owner_member_classes(&[member], &[whole], &[], 10, classes.intervals()),
            Err(ExpansionError::IncompleteOrigin)
        );
    }

    #[test]
    fn owner_member_range_rejects_a_partially_overlapping_product() {
        let member = ObservedProduct {
            output: range(0, 10),
            product: GraphNode::Definition(DefinitionId(1)),
        };
        let crossing = ObservedProduct {
            output: range(5, 12),
            product: GraphNode::Definition(DefinitionId(2)),
        };
        let classes = output_classes(&[crossing], &[], 12, Some(DefinitionId(0))).unwrap();

        assert_eq!(
            validate_owner_member_classes(&[member], &[crossing], &[], 12, classes.intervals(),),
            Err(ExpansionError::IncompleteOrigin)
        );
    }

    #[test]
    fn discarded_output_is_excluded_from_product_and_owner_materialization() {
        let owner = DefinitionId(0);
        let product = ObservedProduct {
            output: range(0, 10),
            product: GraphNode::Definition(DefinitionId(1)),
        };
        let classes = output_classes(&[product], &[range(3, 7)], 10, Some(owner)).unwrap();

        assert_eq!(
            classes.intervals(),
            &[
                (range(0, 3), PendingOutputClass::Products(ProductClassId(0))),
                (
                    range(7, 10),
                    PendingOutputClass::Products(ProductClassId(0))
                ),
            ],
        );
        assert_eq!(classes.product_classes, vec![vec![product.product]]);

        let all_discarded = output_classes(&[], &[range(0, 10)], 10, None).unwrap();
        assert!(all_discarded.intervals().is_empty());
        assert!(all_discarded.product_classes.is_empty());
    }

    #[test]
    fn discarded_output_must_be_normalized_and_only_nested_in_live_products() {
        let product = |output| ObservedProduct {
            output,
            product: GraphNode::Definition(DefinitionId(1)),
        };
        assert_eq!(
            normalize_discarded_output_ranges(vec![range(3, 5), range(1, 2), range(2, 3)], 10,),
            Some(vec![range(1, 2), range(2, 3), range(3, 5)]),
        );
        assert!(normalize_discarded_output_ranges(vec![range(1, 4), range(3, 5)], 10).is_none());
        assert!(output_classes(&[], &[range(1, 4), range(3, 5)], 10, None).is_err());
        assert!(output_classes(&[], &[range(0, 3), range(3, 5)], 5, None).is_ok());
        assert!(output_classes(&[], &[range(9, 11)], 10, None).is_err());
        assert!(output_classes(&[product(range(1, 4))], &[range(1, 4)], 10, None).is_err());
        assert!(
            output_classes(
                &[product(range(0, 4))],
                &[range(0, 2), range(2, 4)],
                4,
                None,
            )
            .is_err()
        );
        assert!(
            output_classes(
                &[product(range(0, 4))],
                &[range(0, 1), range(2, 4)],
                4,
                None,
            )
            .is_ok()
        );
        assert!(
            output_classes(
                &[product(range(0, 4))],
                &[range(1, 2), range(2, 3)],
                4,
                None,
            )
            .is_ok()
        );
        assert!(output_classes(&[product(range(2, 3))], &[range(1, 4)], 10, None).is_err());
        assert!(output_classes(&[product(range(0, 3))], &[range(2, 4)], 10, None).is_err());
        assert!(output_classes(&[product(range(0, 5))], &[range(2, 4)], 5, None).is_ok());
        assert!(
            output_classes(
                &[product(range(0, 3)), product(range(3, 6))],
                &[range(1, 3), range(3, 5)],
                6,
                None,
            )
            .is_ok()
        );
    }

    #[test]
    fn owner_member_allows_discarded_tokens_but_still_needs_live_owner_output() {
        let owner = DefinitionId(0);
        let member = ObservedProduct {
            output: range(0, 10),
            product: GraphNode::Definition(DefinitionId(1)),
        };
        let nested = ObservedProduct {
            output: range(2, 6),
            product: GraphNode::Definition(DefinitionId(2)),
        };
        let discarded = [range(8, 10)];
        let classes = output_classes(&[nested], &discarded, 10, Some(owner)).unwrap();
        assert_eq!(
            validate_owner_member_classes(
                &[member],
                &[nested],
                &discarded,
                10,
                classes.intervals(),
            ),
            Ok(vec![member.product]),
        );

        let nested = ObservedProduct {
            output: range(0, 8),
            product: nested.product,
        };
        let classes = output_classes(&[nested], &discarded, 10, Some(owner)).unwrap();
        assert_eq!(
            validate_owner_member_classes(
                &[member],
                &[nested],
                &discarded,
                10,
                classes.intervals(),
            ),
            Err(ExpansionError::IncompleteOrigin),
        );
    }

    #[test]
    fn source_frontier_intersection_matches_the_ancestor_set_definition() {
        let ancestry = SourceAncestryIndex::from_parents(vec![
            None,
            Some(SourceUnitId(0)),
            Some(SourceUnitId(0)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(2)),
            Some(SourceUnitId(2)),
            None,
        ])
        .unwrap();

        let oracle =
            |left: &[SourceUnitId], right: &[SourceUnitId], excluded: &BTreeSet<SourceUnitId>| {
                let closure = |units: &[SourceUnitId]| {
                    units
                        .iter()
                        .flat_map(|unit| ancestry.ancestors(*unit).unwrap())
                        .filter(|unit| !excluded.contains(unit))
                        .collect::<BTreeSet<_>>()
                };
                let common = closure(left)
                    .intersection(&closure(right))
                    .copied()
                    .collect::<BTreeSet<_>>();
                let mut deepest = common
                    .iter()
                    .copied()
                    .filter(|candidate| {
                        !common.iter().copied().any(|descendant| {
                            descendant != *candidate
                                && ancestry.is_ancestor(*candidate, descendant).unwrap()
                        })
                    })
                    .collect::<Vec<_>>();
                deepest.sort_by_key(|unit| ancestry.entry(*unit).unwrap());
                deepest
            };

        for excluded_descendants in [Vec::new(), vec![SourceUnitId(0)], vec![SourceUnitId(1)]] {
            let excluded = excluded_descendants
                .iter()
                .flat_map(|unit| ancestry.ancestors(*unit).unwrap())
                .collect::<BTreeSet<_>>();
            let exclusions =
                SourceAncestorExclusions::new(&ancestry, excluded_descendants).unwrap();
            for left_mask in 0_u16..(1 << 8) {
                let left = ancestry
                    .deepest_antichain((0..8).filter_map(|index| {
                        (left_mask & (1 << index) != 0).then_some(SourceUnitId(index))
                    }))
                    .unwrap();
                for right_mask in 0_u16..(1 << 8) {
                    let right = ancestry
                        .deepest_antichain((0..8).filter_map(|index| {
                            (right_mask & (1 << index) != 0).then_some(SourceUnitId(index))
                        }))
                        .unwrap();
                    assert_eq!(
                        ancestry
                            .intersect_frontiers(&left, &right, &exclusions)
                            .unwrap(),
                        oracle(&left, &right, &excluded),
                    );
                }
            }
        }
    }

    #[test]
    fn product_basis_range_index_handles_deep_nested_queries() {
        const DEPTH: usize = 1_024;
        let parents = (0..DEPTH)
            .map(|index| (index != 0).then(|| SourceUnitId((index - 1) as u32)))
            .collect();
        let ancestry = SourceAncestryIndex::from_parents(parents).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, []).unwrap();
        with_flat_product_basis_index(
            &ancestry,
            &excluded,
            &(0..DEPTH)
                .map(|ordinal| vec![SourceUnitId(ordinal as u32)])
                .collect::<Vec<_>>(),
            |index| {
                for start in 0..DEPTH {
                    let expected = vec![SourceUnitId(start as u32)];
                    let range = MacroOutputRange {
                        start: start as u32,
                        end: DEPTH as u32,
                    };
                    assert_eq!(index.intersection(range).unwrap(), expected);
                    assert_eq!(index.intersection(range).unwrap(), expected);
                }
                assert_eq!(
                    index
                        .intersection(MacroOutputRange {
                            start: 512,
                            end: 768,
                        })
                        .unwrap(),
                    vec![SourceUnitId(512)],
                );
                Ok(())
            },
        )
        .unwrap();

        let ancestry =
            SourceAncestryIndex::from_parents(vec![None, Some(SourceUnitId(0))]).unwrap();
        let excluded = SourceAncestorExclusions::new(&ancestry, [SourceUnitId(0)]).unwrap();
        with_flat_product_basis_index(
            &ancestry,
            &excluded,
            &[vec![SourceUnitId(0)], vec![SourceUnitId(1)]],
            |index| {
                assert!(
                    index
                        .intersection(MacroOutputRange { start: 0, end: 2 })
                        .unwrap()
                        .is_empty(),
                    "an observed empty basis must remain distinct from missing provenance",
                );
                Ok(())
            },
        )
        .unwrap();
    }

    #[test]
    fn product_basis_range_index_matches_token_ancestor_intersection() {
        let ancestry = SourceAncestryIndex::from_parents(vec![
            None,
            Some(SourceUnitId(0)),
            Some(SourceUnitId(0)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(2)),
            Some(SourceUnitId(2)),
            None,
        ])
        .unwrap();
        let tokens = vec![
            vec![SourceUnitId(3), SourceUnitId(5)],
            vec![SourceUnitId(4), SourceUnitId(6)],
            vec![SourceUnitId(3), SourceUnitId(4)],
            vec![SourceUnitId(5), SourceUnitId(6)],
            vec![SourceUnitId(7)],
        ];
        for excluded_descendants in [Vec::new(), vec![SourceUnitId(1)]] {
            let exclusions =
                SourceAncestorExclusions::new(&ancestry, excluded_descendants.clone()).unwrap();
            let excluded = excluded_descendants
                .into_iter()
                .flat_map(|unit| ancestry.ancestors(unit).unwrap())
                .collect::<BTreeSet<_>>();
            with_flat_product_basis_index(&ancestry, &exclusions, &tokens, |index| {
                for start in 0..tokens.len() {
                    for end in start + 1..=tokens.len() {
                        let mut common = None::<BTreeSet<SourceUnitId>>;
                        for contributors in &tokens[start..end] {
                            let ancestors = contributors
                                .iter()
                                .flat_map(|unit| ancestry.ancestors(*unit).unwrap())
                                .filter(|unit| !excluded.contains(unit))
                                .collect::<BTreeSet<_>>();
                            match &mut common {
                                Some(common) => common.retain(|unit| ancestors.contains(unit)),
                                None => common = Some(ancestors),
                            }
                        }
                        let common = common.unwrap();
                        let expected = ancestry.deepest_antichain(common.iter().copied()).unwrap();
                        assert_eq!(
                            index
                                .intersection(MacroOutputRange {
                                    start: start as u32,
                                    end: end as u32,
                                })
                                .unwrap(),
                            expected,
                        );
                    }
                }
                Ok(())
            })
            .unwrap();
        }
    }

    #[test]
    fn product_output_ranges_must_be_laminar() {
        assert!(laminar_output_ranges([
            range(0, 10),
            range(0, 10),
            range(1, 4),
            range(4, 8),
            range(10, 12),
        ]));
        assert!(!laminar_output_ranges([range(0, 5), range(4, 8)]));
        assert!(!laminar_output_ranges([range(2, 2)]));
    }

    #[test]
    fn component_repetition_index_handles_deep_forests_without_materializing_paths() {
        const DEPTH: usize = 1_024;
        let parents = (0..DEPTH)
            .map(|index| (index != 0).then(|| index - 1))
            .collect::<Vec<_>>();
        let repetitions = (0..DEPTH).map(|index| index % 127 == 0).collect::<Vec<_>>();
        let index = ComponentRepetitionIndex::new(&parents, &repetitions).unwrap();
        let expected = (0..DEPTH)
            .filter(|index| index % 127 == 0)
            .collect::<Vec<_>>();
        assert!(index.matches(DEPTH - 1, expected.iter().copied()));
        assert!(!index.matches(DEPTH - 1, expected.iter().rev().copied()));
        assert_eq!(index.nearest.len(), DEPTH);
        assert_eq!(index.previous.len(), DEPTH);

        let mut cyclic = parents;
        cyclic[0] = Some(DEPTH - 1);
        assert!(ComponentRepetitionIndex::new(&cyclic, &repetitions).is_none());
        assert!(ComponentRepetitionIndex::new(&[Some(1)], &[false]).is_none());
    }

    #[test]
    fn template_interval_lookup_is_logarithmic_and_preserves_exact_outer_ranges() {
        let flat = IntervalStartIndex::from_start_ordered(vec![
            IndexedInterval {
                start: 0,
                end: 20,
                value: SourceUnitId(1),
            },
            IndexedInterval {
                start: 0,
                end: 20,
                value: SourceUnitId(2),
            },
            IndexedInterval {
                start: 4,
                end: 16,
                value: SourceUnitId(3),
            },
            IndexedInterval {
                start: 20,
                end: 30,
                value: SourceUnitId(4),
            },
        ])
        .unwrap();
        let index = SourceUnitIntervalIndex {
            root: SourceUnitId(0),
            children: BTreeMap::new(),
            flat,
        };

        assert_eq!(
            index
                .innermost_container(ByteRange { start: 0, end: 20 })
                .unwrap(),
            Some(SourceUnitId(1)),
        );
        assert_eq!(
            index
                .innermost_container(ByteRange { start: 6, end: 8 })
                .unwrap(),
            Some(SourceUnitId(3)),
        );
        assert_eq!(
            index
                .innermost_container(ByteRange { start: 15, end: 22 })
                .unwrap(),
            None,
        );
    }

    #[test]
    fn owner_member_validation_uses_indexed_product_and_class_ranges() {
        const MEMBERS: u32 = 1_024;
        let products = (0..MEMBERS)
            .map(|index| ObservedProduct {
                output: range(index * 2, index * 2 + 1),
                product: GraphNode::Definition(DefinitionId(index + 1)),
            })
            .collect::<Vec<_>>();
        let members = (0..MEMBERS)
            .map(|index| ObservedProduct {
                output: range(index * 2, index * 2 + 2),
                product: GraphNode::Definition(DefinitionId(MEMBERS + index + 1)),
            })
            .collect::<Vec<_>>();
        let classes = output_classes(&products, &[], MEMBERS * 2, Some(DefinitionId(0))).unwrap();

        assert_eq!(
            validate_owner_member_classes(
                &members,
                &products,
                &[],
                MEMBERS * 2,
                classes.intervals(),
            )
            .unwrap()
            .len(),
            MEMBERS as usize,
        );
    }

    #[test]
    fn nested_output_intervals_share_stored_product_payloads() {
        const OUTER_PRODUCTS: u32 = 512;
        const NESTED_RANGES: u32 = 512;
        let output_token_count = NESTED_RANGES * 2 + 1;
        let mut products = (0..OUTER_PRODUCTS)
            .map(|index| ObservedProduct {
                output: range(0, output_token_count),
                product: GraphNode::Definition(DefinitionId(index + 1)),
            })
            .collect::<Vec<_>>();
        products.extend((0..NESTED_RANGES).map(|index| ObservedProduct {
            output: range(index * 2 + 1, index * 2 + 2),
            product: GraphNode::Definition(DefinitionId(OUTER_PRODUCTS + index + 1)),
        }));

        let (classes, work) =
            output_classes_with_work(&products, &[], output_token_count, None).unwrap();

        assert_eq!(classes.intervals.len(), output_token_count as usize);
        assert_eq!(classes.product_classes.len(), NESTED_RANGES as usize + 1);
        assert_eq!(
            classes.product_classes.iter().map(Vec::len).sum::<usize>(),
            (OUTER_PRODUCTS + NESTED_RANGES) as usize,
        );
        assert_eq!(
            work.product_payload_elements,
            (OUTER_PRODUCTS + NESTED_RANGES) as usize,
            "payload work grows with stored products, not outer products times intervals",
        );
        assert_eq!(work.classified_intervals, output_token_count as usize);
        assert_eq!(
            work.product_class_resolutions, output_token_count as usize,
            "each interval resolves only one dense payload identifier",
        );
    }

    #[test]
    fn macro_output_demands_use_the_nearest_definition_or_source_owner() {
        let products = [
            ObservedProduct {
                output: range(0, 10),
                product: GraphNode::Definition(DefinitionId(1)),
            },
            ObservedProduct {
                output: range(2, 8),
                product: GraphNode::Definition(DefinitionId(2)),
            },
            ObservedProduct {
                output: range(3, 4),
                product: GraphNode::Expansion(ExpansionId(10)),
            },
            ObservedProduct {
                output: range(8, 9),
                product: GraphNode::Expansion(ExpansionId(11)),
            },
            ObservedProduct {
                output: range(10, 11),
                product: GraphNode::Expansion(ExpansionId(12)),
            },
        ];
        let roles = BTreeMap::from([
            (range(3, 4), MacroOutputDemandRole::Required),
            (range(8, 9), MacroOutputDemandRole::Dependent),
            (range(10, 11), MacroOutputDemandRole::Required),
        ]);

        let demands = macro_output_demands(&products, &roles, Some(DefinitionId(0))).unwrap();

        let carriers_for = |child| {
            let class = demands.by_child.get(&child).unwrap().carrier_class;
            demands.carrier_classes[class].as_ref()
        };
        assert_eq!(carriers_for(ExpansionId(10)), &[DefinitionId(2)]);
        assert_eq!(carriers_for(ExpansionId(11)), &[DefinitionId(1)]);
        assert_eq!(carriers_for(ExpansionId(12)), &[DefinitionId(0)]);
        assert_eq!(
            demands.by_child[&ExpansionId(10)].role,
            MacroOutputDemandRole::Required,
        );
        assert_eq!(
            demands.by_child[&ExpansionId(11)].role,
            MacroOutputDemandRole::Dependent,
        );
    }

    #[test]
    fn macro_output_demand_lowering_indexes_carriers_and_children() {
        const DEMANDS: u32 = 1_024;
        let mut products = Vec::with_capacity(DEMANDS as usize * 2);
        let mut roles = BTreeMap::new();
        let mut product_classes = Vec::with_capacity(DEMANDS as usize);
        for index in 0..DEMANDS {
            let carrier = DefinitionId(index);
            let child = ExpansionId(index);
            let carrier_output = range(index * 4, index * 4 + 3);
            let child_output = range(index * 4 + 1, index * 4 + 2);
            products.push(ObservedProduct {
                output: carrier_output,
                product: GraphNode::Definition(carrier),
            });
            products.push(ObservedProduct {
                output: child_output,
                product: GraphNode::Expansion(child),
            });
            roles.insert(
                child_output,
                if index % 2 == 0 {
                    MacroOutputDemandRole::Dependent
                } else {
                    MacroOutputDemandRole::Required
                },
            );
            product_classes.push(vec![
                GraphNode::Definition(carrier),
                GraphNode::Expansion(child),
            ]);
        }
        products.sort();

        let (demands, mut work) = macro_output_demands_with_work(&products, &roles, None).unwrap();
        let all = demands.all_demands_with_work(&mut work).unwrap();
        for products in &product_classes {
            assert_eq!(
                demands
                    .demands_for_products_with_work(products, &mut work)
                    .unwrap()
                    .len(),
                1,
            );
        }

        assert_eq!(all.len(), DEMANDS as usize);
        for (index, demand) in all.iter().enumerate() {
            let carrier = DefinitionId(index as u32);
            let child = ExpansionId(index as u32);
            assert_eq!(demand.carriers.as_ref(), &[carrier]);
            if index % 2 == 0 {
                assert_eq!(demand.dependent_expansions.as_ref(), &[child]);
                assert!(demand.required_expansions.is_empty());
            } else {
                assert!(demand.dependent_expansions.is_empty());
                assert_eq!(demand.required_expansions.as_ref(), &[child]);
            }
        }
        assert_eq!(work.child_products, DEMANDS as usize);
        assert!(
            work.carrier_index_node_visits <= DEMANDS as usize * 32,
            "each carrier lookup must visit only logarithmically many index nodes",
        );
        assert_eq!(
            work.grouped_children,
            DEMANDS as usize * 2,
            "complete and per-class inventories must each visit every child once",
        );
    }

    #[test]
    fn sibling_interval_overlap_and_ambiguity_fail_closed() {
        let equal = [
            IndexedSourceUnit {
                unit: SourceUnitId(1),
                range: ByteRange { start: 0, end: 5 },
            },
            IndexedSourceUnit {
                unit: SourceUnitId(2),
                range: ByteRange { start: 0, end: 5 },
            },
        ];
        assert_eq!(
            containing_child(&equal, ByteRange { start: 1, end: 2 }, false),
            Err(ExpansionError::IncompleteOrigin),
        );

        let crossing = [
            IndexedSourceUnit {
                unit: SourceUnitId(1),
                range: ByteRange { start: 0, end: 5 },
            },
            IndexedSourceUnit {
                unit: SourceUnitId(2),
                range: ByteRange { start: 5, end: 10 },
            },
        ];
        assert_eq!(
            containing_child(&crossing, ByteRange { start: 4, end: 6 }, true),
            Err(ExpansionError::IncompleteOrigin),
        );
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProductClassId(u32);

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PendingOutputClass {
    Products(ProductClassId),
    OwnerEffect(DefinitionId),
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct PendingOutputClasses {
    intervals: Vec<(MacroOutputRange, PendingOutputClass)>,
    product_classes: Vec<Vec<GraphNode>>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
type PendingOutputClassParts = (
    Vec<(MacroOutputRange, PendingOutputClass)>,
    Vec<Option<Vec<GraphNode>>>,
);

#[cfg(any(rust_item_dependencies_patched, test))]
impl PendingOutputClasses {
    fn intervals(&self) -> &[(MacroOutputRange, PendingOutputClass)] {
        &self.intervals
    }

    fn into_parts(self) -> PendingOutputClassParts {
        (
            self.intervals,
            self.product_classes.into_iter().map(Some).collect(),
        )
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Default)]
struct OutputClassWork {
    #[cfg(test)]
    product_payload_elements: usize,
    #[cfg(test)]
    classified_intervals: usize,
    #[cfg(test)]
    product_class_resolutions: usize,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl OutputClassWork {
    fn record_product_payload(&mut self, elements: usize) {
        #[cfg(test)]
        {
            self.product_payload_elements += elements;
        }
        #[cfg(not(test))]
        let _ = elements;
    }

    fn record_interval(&mut self, is_product: bool) {
        #[cfg(test)]
        {
            self.classified_intervals += 1;
            self.product_class_resolutions += usize::from(is_product);
        }
        #[cfg(not(test))]
        let _ = is_product;
    }
}

#[cfg(rust_item_dependencies_patched)]
struct CoverageLowerer<'a> {
    definitions: &'a CollectedDefinitions,
    provenance: &'a MacroProvenance,
    raw: &'a [RawExpansion],
    expansion_ids: FxHashMap<ExpnId, ExpansionId>,
    generated_definitions: Vec<BTreeSet<DefinitionId>>,
    generated_children: Vec<BTreeSet<ExpansionId>>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MacroOutputDemandRole {
    Dependent,
    Required,
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Clone, Copy)]
struct IndexedMacroOutputDemand {
    carrier_class: usize,
    role: MacroOutputDemandRole,
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct MacroOutputDemandIndex {
    carrier_classes: Vec<Box<[DefinitionId]>>,
    by_child: BTreeMap<ExpansionId, IndexedMacroOutputDemand>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl MacroOutputDemandIndex {
    fn all_demands(&self) -> Result<Vec<MacroOutputDemand>, ExpansionError> {
        self.all_demands_with_work(&mut MacroOutputDemandWork::default())
    }

    fn all_demands_with_work(
        &self,
        work: &mut MacroOutputDemandWork,
    ) -> Result<Vec<MacroOutputDemand>, ExpansionError> {
        self.group_children(self.by_child.keys().copied(), work)
    }

    fn demands_for_products(
        &self,
        products: &[GraphNode],
    ) -> Result<Vec<MacroOutputDemand>, ExpansionError> {
        self.demands_for_products_with_work(products, &mut MacroOutputDemandWork::default())
    }

    fn demands_for_products_with_work(
        &self,
        products: &[GraphNode],
        work: &mut MacroOutputDemandWork,
    ) -> Result<Vec<MacroOutputDemand>, ExpansionError> {
        self.group_children(
            products.iter().filter_map(|product| match product {
                GraphNode::Expansion(expansion) => Some(*expansion),
                _ => None,
            }),
            work,
        )
    }

    fn group_children(
        &self,
        children: impl IntoIterator<Item = ExpansionId>,
        work: &mut MacroOutputDemandWork,
    ) -> Result<Vec<MacroOutputDemand>, ExpansionError> {
        let mut seen = BTreeSet::new();
        let mut grouped = BTreeMap::<usize, (BTreeSet<ExpansionId>, BTreeSet<ExpansionId>)>::new();
        for child in children {
            work.record_grouped_child();
            if !seen.insert(child) {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let demand = self
                .by_child
                .get(&child)
                .copied()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let group = grouped.entry(demand.carrier_class).or_default();
            let inserted = match demand.role {
                MacroOutputDemandRole::Dependent => group.0.insert(child),
                MacroOutputDemandRole::Required => group.1.insert(child),
            };
            if !inserted {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }

        let mut demands = grouped
            .into_iter()
            .map(
                |(carrier_class, (dependent_expansions, required_expansions))| {
                    Ok(MacroOutputDemand {
                        carriers: self
                            .carrier_classes
                            .get(carrier_class)
                            .ok_or(ExpansionError::IncompleteOrigin)?
                            .clone(),
                        dependent_expansions: dependent_expansions.into_iter().collect(),
                        required_expansions: required_expansions.into_iter().collect(),
                    })
                },
            )
            .collect::<Result<Vec<_>, ExpansionError>>()?;
        demands.sort();
        Ok(demands)
    }
}

#[cfg(any(rust_item_dependencies_patched, test))]
#[derive(Default)]
struct MacroOutputDemandWork {
    #[cfg(test)]
    child_products: usize,
    #[cfg(test)]
    carrier_index_node_visits: usize,
    #[cfg(test)]
    grouped_children: usize,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl MacroOutputDemandWork {
    fn record_child_product(&mut self) {
        #[cfg(test)]
        {
            self.child_products += 1;
        }
    }

    fn record_carrier_index_node(&mut self) {
        #[cfg(test)]
        {
            self.carrier_index_node_visits += 1;
        }
    }

    fn record_grouped_child(&mut self) {
        #[cfg(test)]
        {
            self.grouped_children += 1;
        }
    }
}

#[cfg(rust_item_dependencies_patched)]
struct ClassifiedMacroOutputs {
    products: Vec<ObservedProduct>,
    owner_members: Vec<ObservedProduct>,
    owner_effect: MacroOwnerEffect,
    dependent_expansions: Vec<ExpansionId>,
    output_demands: MacroOutputDemandIndex,
    residual_intrinsic: bool,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn lower_macro_output_inventories(
    definitions: &CollectedDefinitions,
    provenance: &MacroProvenance,
    raw: &[RawExpansion],
    expansion_ids: FxHashMap<ExpnId, ExpansionId>,
    edges: &[DependencyEdge],
) -> Result<
    (
        MacroProducerCoverageInventory,
        MacroCompleteOutputMeaningInventory,
    ),
    ExpansionError,
> {
    CoverageLowerer::new(definitions, provenance, raw, expansion_ids, edges)?.collect()
}

#[cfg(rust_item_dependencies_patched)]
impl<'a> CoverageLowerer<'a> {
    fn new(
        definitions: &'a CollectedDefinitions,
        provenance: &'a MacroProvenance,
        raw: &'a [RawExpansion],
        expansion_ids: FxHashMap<ExpnId, ExpansionId>,
        edges: &[DependencyEdge],
    ) -> Result<Self, ExpansionError> {
        if expansion_ids.len() != raw.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let mut generated_definitions = vec![BTreeSet::new(); raw.len()];
        for edge in edges {
            if edge.kind != DependencyKind::GeneratedBy {
                continue;
            }
            let (GraphNode::Definition(definition), GraphNode::Expansion(producer)) =
                (edge.from, edge.to)
            else {
                return Err(ExpansionError::IncompleteOrigin);
            };
            generated_definitions
                .get_mut(producer.0 as usize)
                .ok_or(ExpansionError::IncompleteOrigin)?
                .insert(definition);
        }
        let mut generated_children = vec![BTreeSet::new(); raw.len()];
        for (child_index, child) in raw.iter().enumerate() {
            if !matches!(child.kind, ExpansionKind::Macro { .. }) {
                continue;
            }
            let Some(parent) =
                declarative_generation_parent(child.discovered_in, child.source_call_parent)
            else {
                continue;
            };
            let Some(parent_id) = expansion_ids.get(&parent).copied() else {
                continue;
            };
            let parent = raw
                .get(parent_id.0 as usize)
                .filter(|candidate| candidate.compiler_id == parent)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if matches!(parent.kind, ExpansionKind::Macro { .. }) {
                generated_children[parent_id.0 as usize].insert(ExpansionId(child_index as u32));
            }
        }
        Ok(Self {
            definitions,
            provenance,
            raw,
            expansion_ids,
            generated_definitions,
            generated_children,
        })
    }

    fn collect(
        self,
    ) -> Result<
        (
            MacroProducerCoverageInventory,
            MacroCompleteOutputMeaningInventory,
        ),
        ExpansionError,
    > {
        let classified_outputs = self
            .provenance
            .producers
            .iter()
            .map(|(&compiler_id, prepared)| {
                self.classified_outputs(compiler_id, prepared)
                    .map(|classified| (compiler_id, classified))
            })
            .collect::<Result<FxHashMap<_, _>, _>>()?;
        let complete_output_meaning = self.complete_output_meaning(&classified_outputs)?;
        let mut coverage = Vec::with_capacity(self.provenance.coverage_producer_order.len());
        for &compiler_id in &self.provenance.coverage_producer_order {
            let prepared = self
                .provenance
                .producers
                .get(&compiler_id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let classified = classified_outputs
                .get(&compiler_id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            coverage.push(self.coverage_for(compiler_id, prepared, classified)?);
        }
        coverage.sort_by_key(|coverage| coverage.producer);
        if coverage
            .windows(2)
            .any(|pair| pair[0].producer == pair[1].producer)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let contributor_dag = coalesce_definition_identity_cohorts(
            &mut coverage,
            &self.definitions.graph,
            self.definitions.product_bases(),
            &self.provenance.contributor_dag,
        )?;
        Ok((
            MacroProducerCoverageInventory::new(Arc::new(contributor_dag), coverage)?,
            complete_output_meaning,
        ))
    }

    fn complete_output_meaning(
        &self,
        classified_outputs: &FxHashMap<ExpnId, ClassifiedMacroOutputs>,
    ) -> Result<MacroCompleteOutputMeaningInventory, ExpansionError> {
        let mut meanings = Vec::with_capacity(self.provenance.producers.len());
        for (&compiler_id, prepared) in &self.provenance.producers {
            if prepared.ledger.output_token_count() == 0 {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let producer = self
                .expansion_ids
                .get(&compiler_id)
                .copied()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let classified = classified_outputs
                .get(&compiler_id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let raw = self
                .raw
                .get(producer.0 as usize)
                .filter(|raw| raw.compiler_id == compiler_id)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            let intrinsic = !self.generated_definitions[producer.0 as usize].is_empty()
                || classified.owner_effect == MacroOwnerEffect::Semantic;
            if !intrinsic && classified.dependent_expansions.is_empty() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let output_demands = classified.output_demands.all_demands()?;
            let mut actual_demand_definitions = self.generated_definitions[producer.0 as usize]
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            if classified.residual_intrinsic {
                actual_demand_definitions
                    .insert(raw.source_owner.ok_or(ExpansionError::IncompleteOrigin)?);
            }
            meanings.push(MacroCompleteOutputMeaning {
                producer,
                intrinsic,
                residual_intrinsic: classified.residual_intrinsic,
                dependent_expansions: classified.dependent_expansions.clone().into_boxed_slice(),
                actual_demand_definitions: actual_demand_definitions.into_iter().collect(),
                output_demands: output_demands.into_boxed_slice(),
            });
        }
        meanings.sort();
        MacroCompleteOutputMeaningInventory::new(meanings)
    }

    fn classified_outputs(
        &self,
        compiler_id: ExpnId,
        prepared: &PreparedProducer,
    ) -> Result<ClassifiedMacroOutputs, ExpansionError> {
        let producer = self
            .expansion_ids
            .get(&compiler_id)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let raw = self
            .raw
            .get(producer.0 as usize)
            .filter(|raw| raw.compiler_id == compiler_id)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let mut observed_definitions = BTreeMap::new();
        for &(definition, output) in &prepared.definition_outputs {
            let id = self
                .definitions
                .definition_id(definition)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            if observed_definitions.insert(id, output).is_some() {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        let mut observed_product_outputs = observed_definitions
            .values()
            .copied()
            .collect::<BTreeSet<_>>();
        let generated_definitions = self
            .generated_definitions
            .get(producer.0 as usize)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let ClassifiedDefinitionProducts {
            mut products,
            owner_members,
            owner: member_owner,
        } = classify_definition_products(
            &self.definitions.graph.definitions,
            generated_definitions,
            &observed_definitions,
        )?;
        if !owner_members.is_empty() && member_owner != raw.source_owner {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let mut dependent_expansions = Vec::with_capacity(prepared.child_outputs.len());
        for &(child, output) in &prepared.child_outputs {
            let child = self
                .expansion_ids
                .get(&child)
                .copied()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            dependent_expansions.push(child);
            observed_product_outputs.insert(output);
            products.push(ObservedProduct {
                output,
                product: GraphNode::Expansion(child),
            });
        }
        dependent_expansions.sort();
        if dependent_expansions
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
            || self
                .generated_children
                .get(producer.0 as usize)
                .is_none_or(|children| {
                    children
                        .iter()
                        .copied()
                        .ne(dependent_expansions.iter().copied())
                })
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        products.sort();
        let (owner_effect, roles_by_output) = lower_macro_owner_effect(
            &prepared.owner_output,
            &products,
            &observed_product_outputs,
            !owner_members.is_empty(),
        )?;
        let output_demands = macro_output_demands(&products, &roles_by_output, raw.source_owner)?;
        Ok(ClassifiedMacroOutputs {
            products,
            owner_members,
            owner_effect,
            dependent_expansions,
            output_demands,
            residual_intrinsic: prepared.owner_output.intrinsic(),
        })
    }

    fn coverage_for(
        &self,
        compiler_id: ExpnId,
        prepared: &PreparedProducer,
        classified: &ClassifiedMacroOutputs,
    ) -> Result<MacroProducerCoverage, ExpansionError> {
        let producer = self
            .expansion_ids
            .get(&compiler_id)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let raw = self
            .expansion_ids
            .get(&compiler_id)
            .and_then(|id| self.raw.get(id.0 as usize))
            .filter(|raw| raw.compiler_id == compiler_id)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        let token_contributors = self
            .provenance
            .token_contributors
            .get(&compiler_id)
            .ok_or(ExpansionError::IncompleteOrigin)?;
        if token_contributors.output_token_count()? != prepared.ledger.output_token_count() {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let ClassifiedMacroOutputs {
            products,
            owner_members,
            owner_effect,
            output_demands,
            ..
        } = classified;
        let mut product_ranges = BTreeMap::new();
        if products.iter().any(|product| {
            product_ranges
                .insert(product.product, product.output)
                .is_some()
        }) {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let interval_classes = output_classes(&products, &prepared.ledger, raw.source_owner)?;
        let owner_members = validate_owner_member_classes(
            &owner_members,
            &products,
            &prepared.ledger,
            interval_classes.intervals(),
        )?;
        let (interval_classes, mut product_classes) = interval_classes.into_parts();
        let mut classes = BTreeMap::<
            PendingOutputClass,
            (Vec<MacroOutputRange>, BTreeSet<MacroContributorSetId>),
        >::new();
        for (range, class) in interval_classes {
            let entry = classes.entry(class).or_default();
            entry.0.push(range);
            entry.1.extend(token_contributors.roots_for_range(range)?);
        }

        let mut pending = classes.into_iter().collect::<Vec<_>>();
        pending.sort_by_key(|(_, (ranges, _))| ranges[0].start);
        let mut saw_owner_effect = false;
        let mut materialization_groups = Vec::with_capacity(pending.len());
        for (class, (mut output_ranges, contributors)) in pending {
            output_ranges.sort();
            let contributor_roots = contributors.into_iter().collect::<Vec<_>>();
            if contributor_roots.is_empty() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            let (class, group_output_demands) = match class {
                PendingOutputClass::Products(id) => {
                    let products = product_classes
                        .get_mut(id.0 as usize)
                        .and_then(Option::take)
                        .ok_or(ExpansionError::IncompleteOrigin)?;
                    let group_output_demands = output_demands.demands_for_products(&products)?;
                    (MacroOutputClass::Products(products), group_output_demands)
                }
                PendingOutputClass::OwnerEffect(owner) => {
                    if saw_owner_effect {
                        return Err(ExpansionError::IncompleteOrigin);
                    }
                    saw_owner_effect = true;
                    (
                        MacroOutputClass::OwnerEffect {
                            owner,
                            members: owner_members.clone(),
                            effect: owner_effect.clone(),
                        },
                        Vec::new(),
                    )
                }
            };
            materialization_groups.push(MacroOutputMaterializationGroup {
                contributor_roots: contributor_roots.into_boxed_slice(),
                identity_cohort_root: None,
                output_demands: group_output_demands.into_boxed_slice(),
                output_slices: vec![MacroOutputSlice {
                    output_ranges,
                    class,
                }],
            });
        }
        if !owner_members.is_empty() && !saw_owner_effect {
            return Err(ExpansionError::IncompleteOrigin);
        }
        Ok(MacroProducerCoverage {
            producer,
            output_token_count: prepared.ledger.output_token_count(),
            discarded_outputs: prepared.ledger.discarded_outputs().to_vec(),
            materialization_groups,
        })
    }
}

#[cfg(rust_item_dependencies_patched)]
fn lower_macro_owner_effect(
    observed: &ValidatedMacroOwnerOutput,
    products: &[ObservedProduct],
    observed_product_outputs: &BTreeSet<MacroOutputRange>,
    has_owner_members: bool,
) -> Result<
    (
        MacroOwnerEffect,
        BTreeMap<MacroOutputRange, MacroOutputDemandRole>,
    ),
    ExpansionError,
> {
    if has_owner_members && !observed.intrinsic() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let mut products_by_output = BTreeMap::<MacroOutputRange, BTreeSet<GraphNode>>::new();
    for product in products {
        products_by_output
            .entry(product.output)
            .or_default()
            .insert(product.product);
    }
    let mut roles_by_output = BTreeMap::new();
    for (&output, role) in observed
        .dependent_outputs()
        .iter()
        .map(|output| (output, MacroOutputDemandRole::Dependent))
        .chain(
            observed
                .required_outputs()
                .iter()
                .map(|output| (output, MacroOutputDemandRole::Required)),
        )
    {
        if roles_by_output.insert(output, role).is_some() {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    if observed_product_outputs
        .iter()
        .copied()
        .ne(roles_by_output.keys().copied())
    {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let effect = if observed.intrinsic() {
        MacroOwnerEffect::Semantic
    } else {
        let dependent_products = products_by_output
            .values()
            .flat_map(|products| products.iter().copied())
            .collect::<BTreeSet<_>>();
        if dependent_products.is_empty() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        MacroOwnerEffect::TransparentShell {
            dependent_products: dependent_products.into_iter().collect(),
        }
    };
    Ok((effect, roles_by_output))
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn macro_output_demands(
    products: &[ObservedProduct],
    roles_by_output: &BTreeMap<MacroOutputRange, MacroOutputDemandRole>,
    fallback_owner: Option<DefinitionId>,
) -> Result<MacroOutputDemandIndex, ExpansionError> {
    macro_output_demands_with_work(products, roles_by_output, fallback_owner)
        .map(|(demands, _)| demands)
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn macro_output_demands_with_work(
    products: &[ObservedProduct],
    roles_by_output: &BTreeMap<MacroOutputRange, MacroOutputDemandRole>,
    fallback_owner: Option<DefinitionId>,
) -> Result<(MacroOutputDemandIndex, MacroOutputDemandWork), ExpansionError> {
    let mut definitions_by_output = BTreeMap::<MacroOutputRange, BTreeSet<DefinitionId>>::new();
    for product in products {
        if let GraphNode::Definition(definition) = product.product {
            definitions_by_output
                .entry(product.output)
                .or_default()
                .insert(definition);
        }
    }

    let mut ordered_definition_ranges = definitions_by_output.keys().copied().collect::<Vec<_>>();
    ordered_definition_ranges.sort_by_key(|output| (output.start, std::cmp::Reverse(output.end)));
    if !laminar_output_ranges(ordered_definition_ranges.iter().copied()) {
        return Err(ExpansionError::IncompleteOrigin);
    }

    let mut carrier_classes = Vec::with_capacity(ordered_definition_ranges.len() + 1);
    let mut carrier_intervals = Vec::with_capacity(ordered_definition_ranges.len());
    for output in ordered_definition_ranges {
        let carrier_class = carrier_classes.len();
        let carriers = definitions_by_output
            .get(&output)
            .ok_or(ExpansionError::IncompleteOrigin)?
            .iter()
            .copied()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        carrier_classes.push(carriers);
        carrier_intervals.push(IndexedInterval {
            start: output.start,
            end: output.end,
            value: carrier_class,
        });
    }
    let carrier_index = IntervalStartIndex::from_start_ordered(carrier_intervals)?;
    let mut fallback_class = None;
    let mut by_child = BTreeMap::new();
    let mut work = MacroOutputDemandWork::default();
    for product in products {
        let GraphNode::Expansion(child) = product.product else {
            continue;
        };
        work.record_child_product();
        let carrier_class = if let Some(carrier_class) = carrier_index
            .innermost_container_with_probe(product.output.start, product.output.end, || {
                work.record_carrier_index_node();
            }) {
            carrier_class
        } else if let Some(carrier_class) = fallback_class {
            carrier_class
        } else {
            let carrier_class = carrier_classes.len();
            carrier_classes.push(
                vec![fallback_owner.ok_or(ExpansionError::IncompleteOrigin)?].into_boxed_slice(),
            );
            fallback_class = Some(carrier_class);
            carrier_class
        };
        let role = roles_by_output
            .get(&product.output)
            .copied()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        if definitions_by_output.contains_key(&product.output)
            && role != MacroOutputDemandRole::Dependent
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        if by_child
            .insert(
                child,
                IndexedMacroOutputDemand {
                    carrier_class,
                    role,
                },
            )
            .is_some()
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    Ok((
        MacroOutputDemandIndex {
            carrier_classes,
            by_child,
        },
        work,
    ))
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn coalesce_definition_identity_cohorts(
    coverage: &mut [MacroProducerCoverage],
    definitions: &crate::graph::DefinitionGraph,
    product_bases: &[Option<Vec<crate::source::MacroProductSource>>],
    contributor_dag: &MacroContributorDag,
) -> Result<MacroContributorDag, ExpansionError> {
    if product_bases.len() != definitions.definitions.len() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    type Group = (
        Option<DefinitionId>,
        crate::graph::DefinitionOriginKey,
        Option<Vec<crate::source::MacroProductSource>>,
        crate::graph::DefinitionKind,
        Option<String>,
    );

    let mut groups = BTreeMap::<Group, Vec<DefinitionId>>::new();
    for definition in &definitions.definitions {
        if !matches!(definition.origin, DefinitionOrigin::Expanded { .. }) {
            continue;
        }
        let leaf = definition
            .key
            .0
            .last()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        groups
            .entry((
                definition.parent,
                leaf.origin.clone(),
                product_bases
                    .get(definition.id.0 as usize)
                    .ok_or(ExpansionError::IncompleteOrigin)?
                    .clone(),
                definition.kind,
                leaf.name.clone(),
            ))
            .or_default()
            .push(definition.id);
    }

    let group_count = coverage
        .iter()
        .map(|producer| producer.materialization_groups.len())
        .sum::<usize>();
    let mut local_parents = (0..group_count).collect::<Vec<_>>();
    let mut identity_parents = (0..group_count).collect::<Vec<_>>();
    let mut product_groups = BTreeMap::<DefinitionId, usize>::new();
    let mut flat_producers = Vec::with_capacity(group_count);
    let mut flat_contributor_roots = Vec::with_capacity(group_count);
    let mut flat = 0;
    for (producer_index, producer) in coverage.iter().enumerate() {
        for group in &producer.materialization_groups {
            if group.contributor_roots.is_empty() || group.output_slices.is_empty() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            for slice in &group.output_slices {
                let definitions = match &slice.class {
                    MacroOutputClass::Products(products) => products.as_slice(),
                    MacroOutputClass::OwnerEffect { members, .. } => members.as_slice(),
                };
                for product in definitions {
                    if let GraphNode::Definition(definition) = product
                        && product_groups.insert(*definition, flat).is_some()
                    {
                        return Err(ExpansionError::IncompleteOrigin);
                    }
                }
            }
            flat_producers.push(producer_index);
            flat_contributor_roots.push(group.contributor_roots.clone());
            flat += 1;
        }
    }

    fn root(parents: &mut [usize], mut index: usize) -> usize {
        while parents[index] != index {
            let parent = parents[index];
            parents[index] = parents[parent];
            index = parents[index];
        }
        index
    }
    for members in groups.values().filter(|members| members.len() > 1) {
        let observed_members = members
            .iter()
            .filter(|member| product_groups.contains_key(member))
            .count();
        if observed_members == 0 {
            continue;
        }
        if observed_members != members.len() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let materializations = members
            .iter()
            .map(|member| {
                product_groups
                    .get(member)
                    .copied()
                    .ok_or(ExpansionError::IncompleteOrigin)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let first = *materializations
            .first()
            .ok_or(ExpansionError::IncompleteOrigin)?;
        for &materialization in &materializations[1..] {
            let left = root(&mut identity_parents, first);
            let right = root(&mut identity_parents, materialization);
            if left != right {
                identity_parents[right] = left;
            }
        }

        let mut materializations_by_producer = BTreeMap::<usize, Vec<usize>>::new();
        for materialization in materializations {
            let producer = *flat_producers
                .get(materialization)
                .ok_or(ExpansionError::IncompleteOrigin)?;
            materializations_by_producer
                .entry(producer)
                .or_default()
                .push(materialization);
        }
        for materializations in materializations_by_producer.values() {
            let first = *materializations
                .first()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            for &materialization in &materializations[1..] {
                let left = root(&mut local_parents, first);
                let right = root(&mut local_parents, materialization);
                if left != right {
                    local_parents[right] = left;
                }
            }
        }
    }

    let mut identity_components =
        BTreeMap::<usize, (BTreeSet<(usize, usize)>, BTreeSet<MacroContributorSetId>)>::new();
    for flat in 0..group_count {
        let identity = root(&mut identity_parents, flat);
        let local = root(&mut local_parents, flat);
        let component = identity_components.entry(identity).or_default();
        component.0.insert((flat_producers[flat], local));
        component
            .1
            .extend(flat_contributor_roots[flat].iter().copied());
    }
    identity_components.retain(|_, (groups, _)| groups.len() > 1);
    let component_ids = identity_components.keys().copied().collect::<Vec<_>>();
    let unions = identity_components
        .values()
        .map(|(_, roots)| roots.iter().copied().collect::<Vec<_>>().into_boxed_slice())
        .collect::<Vec<_>>();
    let (contributor_dag, identity_roots) = contributor_dag.with_parent_unions(&unions)?;
    let identity_root_by_component = component_ids
        .into_iter()
        .zip(identity_roots)
        .collect::<BTreeMap<_, _>>();

    let mut flattened = Vec::with_capacity(group_count);
    for (producer_index, producer) in coverage.iter_mut().enumerate() {
        flattened.extend(
            std::mem::take(&mut producer.materialization_groups)
                .into_iter()
                .map(|group| (producer_index, group)),
        );
    }
    if flattened.len() != group_count {
        return Err(ExpansionError::IncompleteOrigin);
    }

    let mut merged = BTreeMap::<
        (usize, usize),
        (
            BTreeSet<MacroContributorSetId>,
            Option<MacroContributorSetId>,
            BTreeSet<MacroOutputDemand>,
            Vec<MacroOutputSlice>,
        ),
    >::new();
    flat = 0;
    for (producer_index, group) in flattened {
        let local = root(&mut local_parents, flat);
        let identity = root(&mut identity_parents, flat);
        let identity_root = identity_root_by_component.get(&identity).copied();
        let entry = merged.entry((producer_index, local)).or_default();
        if let Some(existing) = entry.1
            && Some(existing) != identity_root
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        entry.0.extend(group.contributor_roots.iter().copied());
        entry.1 = identity_root.or(entry.1);
        entry.2.extend(group.output_demands);
        entry.3.extend(group.output_slices);
        flat += 1;
    }

    for (
        (producer_index, _),
        (contributors, identity_cohort_root, output_demands, mut output_slices),
    ) in merged
    {
        output_slices.sort_by_key(|slice| {
            slice
                .output_ranges
                .first()
                .map(|range| range.start)
                .unwrap_or(u32::MAX)
        });
        coverage
            .get_mut(producer_index)
            .ok_or(ExpansionError::IncompleteOrigin)?
            .materialization_groups
            .push(MacroOutputMaterializationGroup {
                contributor_roots: contributors
                    .into_iter()
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
                identity_cohort_root,
                output_demands: output_demands.into_iter().collect(),
                output_slices,
            });
    }
    for producer in coverage {
        producer.materialization_groups.sort_by_key(|group| {
            group
                .output_slices
                .iter()
                .flat_map(|slice| &slice.output_ranges)
                .map(|range| range.start)
                .min()
                .unwrap_or(u32::MAX)
        });
        if producer
            .materialization_groups
            .iter()
            .any(|group| group.output_slices.is_empty())
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    Ok(contributor_dag)
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn output_classes(
    products: &[ObservedProduct],
    ledger: &ValidatedMacroOutputLedger,
    source_owner: Option<DefinitionId>,
) -> Result<PendingOutputClasses, ExpansionError> {
    output_classes_with_work(products, ledger, source_owner).map(|(classes, _)| classes)
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn output_classes_with_work(
    products: &[ObservedProduct],
    ledger: &ValidatedMacroOutputLedger,
    source_owner: Option<DefinitionId>,
) -> Result<(PendingOutputClasses, OutputClassWork), ExpansionError> {
    let output_token_count = ledger.output_token_count();
    let discarded = ledger.discarded_outputs();
    let mut products_by_range = BTreeMap::<MacroOutputRange, BTreeSet<GraphNode>>::new();
    for &product in products {
        if !ledger.contains_live_output(product.output)
            || !products_by_range
                .entry(product.output)
                .or_default()
                .insert(product.product)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }

    // Store each complete product-range payload once. Sweep intervals carry
    // only its dense identifier, so repeatedly exposing a large outer product
    // around nested products does not clone that payload for every interval.
    let mut work = OutputClassWork::default();
    let mut class_by_range = BTreeMap::<MacroOutputRange, ProductClassId>::new();
    let mut product_classes = Vec::with_capacity(products_by_range.len());
    for (range, products) in products_by_range {
        let products = products.into_iter().collect::<Vec<_>>();
        let id = u32::try_from(product_classes.len())
            .map(ProductClassId)
            .map_err(|_| ExpansionError::IncompleteOrigin)?;
        work.record_product_payload(products.len());
        product_classes.push(products);
        if class_by_range.insert(range, id).is_some() {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }

    let mut starts = BTreeMap::<u32, Vec<MacroOutputRange>>::new();
    let mut ends = BTreeMap::<u32, Vec<MacroOutputRange>>::new();
    let mut positions = BTreeSet::from([0, output_token_count]);
    for &range in class_by_range.keys() {
        starts.entry(range.start).or_default().push(range);
        ends.entry(range.end).or_default().push(range);
        positions.insert(range.start);
        positions.insert(range.end);
    }
    for &range in discarded {
        positions.insert(range.start);
        positions.insert(range.end);
    }
    let positions = positions.into_iter().collect::<Vec<_>>();
    let mut active = BTreeSet::<(u32, u32, u32)>::new();
    let mut discarded_index = 0;
    let mut classified = Vec::new();
    for pair in positions.windows(2) {
        let position = pair[0];
        for range in ends.get(&position).into_iter().flatten() {
            if !active.remove(&(range.len(), range.start, range.end)) {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        for range in starts.get(&position).into_iter().flatten() {
            if !active.insert((range.len(), range.start, range.end)) {
                return Err(ExpansionError::IncompleteOrigin);
            }
        }
        let range = MacroOutputRange {
            start: position,
            end: pair[1],
        };
        if range.is_empty() {
            continue;
        }
        while discarded
            .get(discarded_index)
            .is_some_and(|discarded| discarded.end <= position)
        {
            discarded_index += 1;
        }
        if discarded
            .get(discarded_index)
            .is_some_and(|discarded| discarded.start <= range.start && range.end <= discarded.end)
        {
            continue;
        }
        let class = if let Some(&(_, start, end)) = active.first() {
            let id = class_by_range
                .get(&MacroOutputRange { start, end })
                .copied()
                .ok_or(ExpansionError::IncompleteOrigin)?;
            PendingOutputClass::Products(id)
        } else {
            PendingOutputClass::OwnerEffect(source_owner.ok_or(ExpansionError::IncompleteOrigin)?)
        };
        work.record_interval(matches!(class, PendingOutputClass::Products(_)));
        classified.push((range, class));
    }
    for range in ends.get(&output_token_count).into_iter().flatten() {
        if !active.remove(&(range.len(), range.start, range.end)) {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    if !active.is_empty() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok((
        PendingOutputClasses {
            intervals: classified,
            product_classes,
        },
        work,
    ))
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn validate_owner_member_classes(
    members: &[ObservedProduct],
    products: &[ObservedProduct],
    ledger: &ValidatedMacroOutputLedger,
    classes: &[(MacroOutputRange, PendingOutputClass)],
) -> Result<Vec<GraphNode>, ExpansionError> {
    if members.is_empty() {
        return Ok(Vec::new());
    }
    if members
        .iter()
        .any(|member| !ledger.contains_live_output(member.output))
    {
        return Err(ExpansionError::IncompleteOrigin);
    }

    let mut product_ranges = products
        .iter()
        .map(|product| product.output)
        .collect::<Vec<_>>();
    product_ranges.sort();
    product_ranges.dedup();
    let product_ranges = IntervalStartIndex::from_start_ordered(
        product_ranges
            .into_iter()
            .map(|range| IndexedInterval {
                start: range.start,
                end: range.end,
                value: (),
            })
            .collect(),
    )?;

    if classes.iter().any(|(range, _)| range.is_empty())
        || classes
            .windows(2)
            .any(|pair| pair[0].0.end > pair[1].0.start)
    {
        return Err(ExpansionError::IncompleteOrigin);
    }
    let mut owner_prefix = Vec::with_capacity(classes.len() + 1);
    owner_prefix.push(0_usize);
    for (_, class) in classes {
        owner_prefix.push(
            owner_prefix.last().copied().unwrap_or(0)
                + usize::from(matches!(class, PendingOutputClass::OwnerEffect(_))),
        );
    }

    for member in members {
        if member.output.is_empty() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let before = product_ranges.lower_bound_start(member.output.start);
        if product_ranges
            .maximum_end(0, before)
            .is_some_and(|end| end > member.output.start)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let within = product_ranges.lower_bound_start(member.output.end);
        if product_ranges
            .maximum_end(before, within)
            .is_some_and(|end| end > member.output.end)
        {
            return Err(ExpansionError::IncompleteOrigin);
        }

        let first = classes.partition_point(|(range, _)| range.end <= member.output.start);
        let end = classes.partition_point(|(range, _)| range.start < member.output.end);
        if first >= end || owner_prefix[end] == owner_prefix[first] {
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    Ok(members.iter().map(|member| member.product).collect())
}
