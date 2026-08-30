use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use crate::dependency_graph::{
    DependencyGraph, DependencyKind, ExpansionId, ExpansionKind, ExpansionNode, GraphNode,
    MacroImplementationKind,
};
use crate::expansions::{
    MacroCompleteOutputMeaningInventory, MacroContributorDag, MacroContributorSetId,
    MacroDefinitionProductRole, MacroOutputRange, MacroOwnerEffect, MacroProducerCoverage,
    MacroProducerCoverageInventory, macro_definition_product_role,
};
use crate::graph::{DefinitionId, DefinitionOrigin, DefinitionTarget};
use crate::source::{
    CfgState, DeclarativeContributorParent, DeclarativeGenerationParentState,
    DeclarativeSourceUnitKind, SourceInventory, SourceUnitId, WrittenUnitKind,
    declarative_generation_parent, resolve_declarative_contributor_parent,
};

use super::{
    MacroRuleSelectionRequirement, RetentionError, ValidatedCompilerMemberConstraints,
    macro_rule_requirement_matches, retain_source_unit,
};

/// Generated output which has no independent compiler graph node.
///
/// Semantic output is retained with its owner. A parser-proven transparent
/// shell instead follows its explicitly classified dependent products. Once
/// the contributors survive, generated members materialize when the owner is
/// required.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct MacroOwnerRequirement {
    pub(super) owner: DefinitionId,
    pub(super) members: Vec<DefinitionId>,
    pub(super) effect: MacroOwnerEffect,
}

/// Every compiler product and owner effect controlled by one explicit source
/// materialization group.
///
/// `producer` is the single macro expansion that transcribed every member of
/// the group. Keeping any product or owner member keeps the group's
/// contributors. Conversely, keeping every contributor materializes all
/// products and the members of each already-required owner. Transparent owner
/// shells use their product dependencies instead of their owner as the source
/// trigger.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct MacroMaterialization {
    pub(super) producer: ExpansionId,
    pub(super) products: Vec<GraphNode>,
    pub(super) owner_requirements: Vec<MacroOwnerRequirement>,
    pub(super) contributor_roots: Box<[MacroContributorSetId]>,
    pub(super) identity_cohort_root: Option<MacroContributorSetId>,
}

impl MacroMaterialization {
    fn retention_roots(&self) -> &[MacroContributorSetId] {
        self.identity_cohort_root
            .as_ref()
            .map_or(self.contributor_roots.as_ref(), std::slice::from_ref)
    }
}

#[derive(Clone)]
struct ValidatedContributorDag {
    node_indices: BTreeMap<MacroContributorSetId, usize>,
    local_sources: Vec<Box<[SourceUnitId]>>,
    parents: Vec<Vec<usize>>,
    children: Vec<Vec<usize>>,
    nodes_by_source: BTreeMap<SourceUnitId, Vec<usize>>,
    groups_by_root: Vec<Vec<usize>>,
}

/// Producer-level meaning carried by materialized macro output.
///
/// A group is intrinsically meaningful when it contains a non-expansion
/// compiler product, a semantic owner effect, or an expansion outside the
/// completely observed declarative-macro producer set. A transparent owner
/// shell and a classified child expansion inherit meaning from their explicit
/// product dependencies. The shared reverse index evaluates that least fixed
/// point and opens shell contributors without retaining transitive producer
/// sets.
#[derive(Clone)]
struct MacroOutputMeaningIndex {
    producers: Box<[ExpansionId]>,
    producer_indices: BTreeMap<ExpansionId, usize>,
    producer_by_group: Box<[usize]>,
    group_has_intrinsic_output: Box<[bool]>,
    dependent_groups_by_product: BTreeMap<GraphNode, Vec<usize>>,
    dependent_groups_by_product_group: Vec<Vec<usize>>,
    static_intrinsic_producers: Box<[bool]>,
    dependent_producers_by_child: Vec<Vec<usize>>,
    demand_producers_by_trigger: BTreeMap<DefinitionId, Vec<usize>>,
    producer_demand_facts: Box<[(usize, MacroGroupDemand)]>,
    #[cfg(test)]
    indexed_fact_visits: usize,
}

#[derive(Default)]
pub(super) struct MacroOutputMeaningStats {
    #[cfg(test)]
    pub(super) group_visits: usize,
    #[cfg(test)]
    pub(super) dependency_visits: usize,
    #[cfg(test)]
    pub(super) producer_activations: usize,
    #[cfg(test)]
    pub(super) index_visits: usize,
}

impl MacroOutputMeaningStats {
    fn visit_group(&mut self) {
        #[cfg(test)]
        {
            self.group_visits += 1;
        }
    }

    fn visit_dependency(&mut self) {
        #[cfg(test)]
        {
            self.dependency_visits += 1;
        }
    }

    fn activate_producer(&mut self) {
        #[cfg(test)]
        {
            self.producer_activations += 1;
        }
    }
}

#[derive(Clone)]
pub(super) struct ValidatedMacroProducts {
    contributor_dag: Arc<MacroContributorDag>,
    contributor_index: ValidatedContributorDag,
    pub(super) materializations: Vec<MacroMaterialization>,
    pub(super) delegated_macro_expansions: BTreeSet<ExpansionId>,
    pub(super) product_groups: BTreeMap<GraphNode, usize>,
    actual_definition_classes: Vec<Box<[GraphNode]>>,
    actual_definition_class_by_definition: BTreeMap<GraphNode, usize>,
    compile_trigger_groups: BTreeMap<GraphNode, Vec<usize>>,
    producer_groups: BTreeMap<ExpansionId, Vec<usize>>,
    demand_clauses: Box<[MacroDemandClause]>,
    demand_clauses_by_carrier: BTreeMap<DefinitionId, Vec<usize>>,
    dependent_demand_clauses_by_child: BTreeMap<ExpansionId, Vec<usize>>,
    contributor_class_by_group: Vec<usize>,
    contributor_class_roots: Vec<Box<[MacroContributorSetId]>>,
    output_meaning: MacroOutputMeaningIndex,
}

pub(super) struct PendingMacroMaterializationGroup {
    pub(super) producer: ExpansionId,
    pub(super) products: BTreeSet<GraphNode>,
    pub(super) product_classes: Vec<Box<[GraphNode]>>,
    pub(super) owner_requirements: BTreeSet<MacroOwnerRequirement>,
    pub(super) contributor_roots: Box<[MacroContributorSetId]>,
    pub(super) identity_cohort_root: Option<MacroContributorSetId>,
    pub(super) output_demands: BTreeSet<MacroGroupDemand>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct MacroGroupDemand {
    pub(super) carriers: Box<[DefinitionId]>,
    pub(super) dependent_expansions: Box<[ExpansionId]>,
    pub(super) required_expansions: Box<[ExpansionId]>,
}

struct LoweredMacroMaterializations {
    materializations: Vec<MacroMaterialization>,
    product_classes: Vec<Box<[Box<[GraphNode]>]>>,
    output_demands: Vec<Box<[MacroGroupDemand]>>,
}

struct MacroProductClassFacts {
    groups: Vec<Box<[Box<[GraphNode]>]>>,
    require_complete: bool,
}

struct MacroOutputDemandFacts {
    groups: Vec<Box<[MacroGroupDemand]>>,
    require_complete: bool,
}

struct MacroGroupFacts {
    product_classes: MacroProductClassFacts,
    output_demands: MacroOutputDemandFacts,
}

#[derive(Clone)]
struct MacroDemandClause {
    target: MacroDemandTarget,
    required_expansions: Box<[ExpansionId]>,
    opaque_dependent: bool,
}

#[derive(Clone, Copy)]
enum MacroDemandTarget {
    Producer(usize),
    Group(usize),
}

pub(super) struct MacroProducerClassification<'a> {
    refined: &'a BTreeSet<ExpansionId>,
    complete_output_meaning: &'a ValidatedCompleteMacroOutputMeaning,
}

#[derive(Clone)]
pub(super) struct ValidatedCompleteMacroOutputMeaning {
    universe: BTreeSet<ExpansionId>,
    records: BTreeMap<ExpansionId, CompleteMacroOutputMeaningRecord>,
}

#[derive(Clone)]
struct CompleteMacroOutputMeaningRecord {
    intrinsic: bool,
    residual_intrinsic: bool,
    dependent_expansions: Box<[ExpansionId]>,
    actual_demand_definitions: Box<[DefinitionId]>,
    output_demands: Box<[MacroGroupDemand]>,
}

impl<'a> MacroProducerClassification<'a> {
    pub(super) fn new(
        refined: &'a BTreeSet<ExpansionId>,
        complete_output_meaning: &'a ValidatedCompleteMacroOutputMeaning,
    ) -> Self {
        Self {
            refined,
            complete_output_meaning,
        }
    }

    pub(super) fn delegates_expansion_use(&self, expansion: ExpansionId) -> bool {
        self.refined.contains(&expansion)
            || self
                .complete_output_meaning
                .is_directly_outputless(expansion)
    }
}

impl ValidatedCompleteMacroOutputMeaning {
    fn is_directly_outputless(&self, producer: ExpansionId) -> bool {
        self.universe.contains(&producer) && !self.records.contains_key(&producer)
    }
}

pub(super) fn validate_complete_macro_output_meaning(
    graph: &DependencyGraph,
    inventory: &MacroCompleteOutputMeaningInventory,
    directly_outputless: &BTreeSet<ExpansionId>,
) -> Result<ValidatedCompleteMacroOutputMeaning, RetentionError> {
    let mut generated_definitions_by_producer =
        BTreeMap::<ExpansionId, BTreeSet<DefinitionId>>::new();
    for edge in &graph.edges {
        if edge.kind != DependencyKind::GeneratedBy {
            continue;
        }
        let (GraphNode::Definition(definition), GraphNode::Expansion(producer)) =
            (edge.from, edge.to)
        else {
            return Err(RetentionError::InvalidGraph);
        };
        generated_definitions_by_producer
            .entry(producer)
            .or_default()
            .insert(definition);
    }
    let mut children_by_parent = BTreeMap::<ExpansionId, BTreeSet<ExpansionId>>::new();
    for child in &graph.expansions {
        if !matches!(child.kind, ExpansionKind::Macro { .. }) {
            continue;
        }
        if let Some(parent) = immediate_macro_parent(graph, child)? {
            children_by_parent
                .entry(parent)
                .or_default()
                .insert(child.id);
        }
    }
    let valid_macro = |producer: ExpansionId| {
        graph
            .expansions
            .get(producer.0 as usize)
            .filter(|expansion| expansion.id == producer)
            .is_some_and(|expansion| {
                matches!(expansion.kind, ExpansionKind::Macro { .. })
                    && expansion.implementation.is_some()
            })
    };
    let valid_local_declarative = |producer: ExpansionId| {
        graph
            .expansions
            .get(producer.0 as usize)
            .filter(|expansion| expansion.id == producer)
            .is_some_and(|expansion| {
                valid_macro(producer)
                    && expansion.implementation == Some(MacroImplementationKind::Declarative)
                    && matches!(
                        expansion.macro_definition,
                        Some(DefinitionTarget::Local(definition))
                            if graph
                                .definitions
                                .definitions
                                .get(definition.0 as usize)
                                .is_some_and(|candidate| {
                                    candidate.id == definition
                                        && candidate.kind
                                            == crate::graph::DefinitionKind::Macro
                                })
                    )
            })
    };

    let mut records = BTreeMap::new();
    for record in inventory.producers() {
        let producer = record.producer();
        if !valid_local_declarative(producer)
            || directly_outputless.contains(&producer)
            || (!record.intrinsic() && record.dependent_expansions().is_empty())
            || record
                .dependent_expansions()
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
        {
            return Err(RetentionError::InvalidConstraint);
        }
        let expansion = &graph.expansions[producer.0 as usize];
        if record.residual_intrinsic() && !record.intrinsic() {
            return Err(RetentionError::InvalidConstraint);
        }
        let mut expected_demand_definitions = generated_definitions_by_producer
            .get(&producer)
            .cloned()
            .unwrap_or_default();
        if record.residual_intrinsic() {
            expected_demand_definitions.insert(
                expansion
                    .source_owner
                    .ok_or(RetentionError::InvalidConstraint)?,
            );
        }
        if expected_demand_definitions
            .iter()
            .copied()
            .ne(record.actual_demand_definitions().iter().copied())
            || record.intrinsic()
                != (record.residual_intrinsic()
                    || generated_definitions_by_producer
                        .get(&producer)
                        .is_some_and(|definitions| !definitions.is_empty()))
        {
            return Err(RetentionError::InvalidConstraint);
        }
        for &child in record.dependent_expansions() {
            let child = graph
                .expansions
                .get(child.0 as usize)
                .filter(|candidate| candidate.id == child)
                .ok_or(RetentionError::InvalidConstraint)?;
            if !matches!(child.kind, ExpansionKind::Macro { .. })
                || immediate_macro_parent(graph, child)? != Some(producer)
            {
                return Err(RetentionError::InvalidConstraint);
            }
        }
        let mut role_children = BTreeSet::new();
        for demand in record.output_demands() {
            for &carrier in demand.carriers() {
                if graph
                    .definitions
                    .definitions
                    .get(carrier.0 as usize)
                    .is_none_or(|candidate| candidate.id != carrier)
                    || (expansion.source_owner != Some(carrier)
                        && !generated_definitions_by_producer
                            .get(&producer)
                            .is_some_and(|definitions| definitions.contains(&carrier)))
                {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
            for &child in demand
                .dependent_expansions()
                .iter()
                .chain(demand.required_expansions())
            {
                if !role_children.insert(child) {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
        }
        if role_children
            .iter()
            .copied()
            .ne(record.dependent_expansions().iter().copied())
            || children_by_parent
                .get(&producer)
                .into_iter()
                .flatten()
                .copied()
                .ne(record.dependent_expansions().iter().copied())
        {
            return Err(RetentionError::InvalidConstraint);
        }
        if records
            .insert(
                producer,
                CompleteMacroOutputMeaningRecord {
                    intrinsic: record.intrinsic(),
                    residual_intrinsic: record.residual_intrinsic(),
                    dependent_expansions: record.dependent_expansions().into(),
                    actual_demand_definitions: record.actual_demand_definitions().into(),
                    output_demands: record
                        .output_demands()
                        .iter()
                        .map(|demand| MacroGroupDemand {
                            carriers: demand.carriers().into(),
                            dependent_expansions: demand.dependent_expansions().into(),
                            required_expansions: demand.required_expansions().into(),
                        })
                        .collect(),
                },
            )
            .is_some()
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    if directly_outputless.iter().any(|&producer| {
        !valid_macro(producer)
            || generated_definitions_by_producer
                .get(&producer)
                .is_some_and(|definitions| !definitions.is_empty())
            || children_by_parent
                .get(&producer)
                .is_some_and(|children| !children.is_empty())
    }) {
        return Err(RetentionError::InvalidConstraint);
    }
    let mut universe = directly_outputless.clone();
    universe.extend(records.keys().copied());
    Ok(ValidatedCompleteMacroOutputMeaning { universe, records })
}

impl MacroOutputMeaningIndex {
    fn new(
        materializations: &[MacroMaterialization],
        product_groups: &BTreeMap<GraphNode, usize>,
        refined_producers: &BTreeSet<ExpansionId>,
        complete_output_meaning: &ValidatedCompleteMacroOutputMeaning,
    ) -> Result<Self, RetentionError> {
        if !refined_producers.is_subset(&complete_output_meaning.universe) {
            return Err(RetentionError::InvalidConstraint);
        }
        let producers = complete_output_meaning
            .universe
            .iter()
            .copied()
            .collect::<Box<[_]>>();
        let producer_indices = producers
            .iter()
            .enumerate()
            .map(|(index, &producer)| (producer, index))
            .collect::<BTreeMap<_, _>>();
        let mut static_intrinsic_producers = vec![false; producers.len()];
        let mut dependent_producers_by_child = vec![Vec::new(); producers.len()];
        let mut demand_producers_by_trigger = BTreeMap::<DefinitionId, Vec<usize>>::new();
        let mut producer_demand_facts = Vec::new();
        #[cfg(test)]
        let mut indexed_fact_visits = 0;
        for (&producer, record) in &complete_output_meaning.records {
            #[cfg(test)]
            {
                indexed_fact_visits += 1;
            }
            let producer_index = producer_indices
                .get(&producer)
                .copied()
                .ok_or(RetentionError::InvalidConstraint)?;
            for &definition in &record.actual_demand_definitions {
                demand_producers_by_trigger
                    .entry(definition)
                    .or_default()
                    .push(producer_index);
            }
            for demand in &record.output_demands {
                producer_demand_facts.push((producer_index, demand.clone()));
            }
            if refined_producers.contains(&producer) {
                continue;
            }
            static_intrinsic_producers[producer_index] = record.intrinsic;
            for &child in &record.dependent_expansions {
                #[cfg(test)]
                {
                    indexed_fact_visits += 1;
                }
                if let Some(&child) = producer_indices.get(&child) {
                    dependent_producers_by_child[child].push(producer_index);
                } else {
                    // An unobserved, builtin, procedural, or otherwise opaque
                    // child is semantic output. It cannot be inferred empty.
                    static_intrinsic_producers[producer_index] = true;
                }
            }
        }
        let mut producer_by_group = Vec::with_capacity(materializations.len());
        let mut group_has_intrinsic_output = Vec::with_capacity(materializations.len());
        let mut dependent_groups_by_product = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut dependent_groups_by_product_group = vec![Vec::new(); materializations.len()];

        for (group, materialization) in materializations.iter().enumerate() {
            #[cfg(test)]
            {
                indexed_fact_visits += 1;
            }
            if !refined_producers.contains(&materialization.producer) {
                return Err(RetentionError::InvalidConstraint);
            }
            let producer = producer_indices
                .get(&materialization.producer)
                .copied()
                .ok_or(RetentionError::InvalidConstraint)?;
            producer_by_group.push(producer);
            let mut intrinsic = false;
            for &product in &materialization.products {
                if let GraphNode::Expansion(child) = product
                    && producer_indices.contains_key(&child)
                {
                    dependent_groups_by_product
                        .entry(product)
                        .or_default()
                        .push(group);
                } else {
                    intrinsic = true;
                }
            }
            for requirement in &materialization.owner_requirements {
                match &requirement.effect {
                    MacroOwnerEffect::Semantic => intrinsic = true,
                    MacroOwnerEffect::TransparentShell { dependent_products } => {
                        if !requirement.members.is_empty()
                            || dependent_products.is_empty()
                            || dependent_products.windows(2).any(|pair| pair[0] >= pair[1])
                        {
                            return Err(RetentionError::InvalidConstraint);
                        }
                        for &product in dependent_products {
                            match product {
                                GraphNode::Expansion(child) => {
                                    dependent_groups_by_product
                                        .entry(product)
                                        .or_default()
                                        .push(group);
                                    if !producer_indices.contains_key(&child) {
                                        intrinsic = true;
                                    }
                                }
                                GraphNode::Definition(_) => {
                                    let dependency_group = product_groups
                                        .get(&product)
                                        .copied()
                                        .ok_or(RetentionError::InvalidConstraint)?;
                                    if dependency_group == group {
                                        intrinsic = true;
                                    } else {
                                        dependent_groups_by_product
                                            .entry(product)
                                            .or_default()
                                            .push(group);
                                    }
                                }
                                GraphNode::ExternalDefinition(_)
                                | GraphNode::Proof(_)
                                | GraphNode::Mono(_) => {
                                    return Err(RetentionError::InvalidConstraint);
                                }
                            }
                        }
                    }
                }
            }
            group_has_intrinsic_output.push(intrinsic);
        }
        for groups in dependent_groups_by_product.values_mut() {
            groups.sort_unstable();
            groups.dedup();
        }
        for (&product, groups) in &dependent_groups_by_product {
            if matches!(product, GraphNode::Definition(_)) {
                let dependency_group = product_groups
                    .get(&product)
                    .copied()
                    .ok_or(RetentionError::InvalidConstraint)?;
                dependent_groups_by_product_group[dependency_group].extend(groups);
            }
        }
        for groups in &mut dependent_groups_by_product_group {
            groups.sort_unstable();
            groups.dedup();
        }
        for producers in &mut dependent_producers_by_child {
            producers.sort_unstable();
            producers.dedup();
        }
        for producers in demand_producers_by_trigger.values_mut() {
            producers.sort_unstable();
            producers.dedup();
        }

        Ok(Self {
            producers,
            producer_indices,
            producer_by_group: producer_by_group.into_boxed_slice(),
            group_has_intrinsic_output: group_has_intrinsic_output.into_boxed_slice(),
            dependent_groups_by_product,
            dependent_groups_by_product_group,
            static_intrinsic_producers: static_intrinsic_producers.into_boxed_slice(),
            dependent_producers_by_child,
            demand_producers_by_trigger,
            producer_demand_facts: producer_demand_facts.into_boxed_slice(),
            #[cfg(test)]
            indexed_fact_visits,
        })
    }

    fn meaningful_producers(
        &self,
        active_groups: &[bool],
    ) -> Result<(Vec<bool>, MacroOutputMeaningStats), RetentionError> {
        if active_groups.len() != self.producer_by_group.len()
            || self.group_has_intrinsic_output.len() != self.producer_by_group.len()
        {
            return Err(RetentionError::InvalidConstraint);
        }
        let mut stats = MacroOutputMeaningStats::default();
        #[cfg(test)]
        {
            stats.index_visits = self.indexed_fact_visits;
        }
        let mut meaningful = vec![false; self.producers.len()];
        let mut pending = VecDeque::new();
        for (producer, &intrinsic) in self.static_intrinsic_producers.iter().enumerate() {
            if intrinsic {
                meaningful[producer] = true;
                stats.activate_producer();
                pending.push_back(producer);
            }
        }
        for (group, &active) in active_groups.iter().enumerate() {
            stats.visit_group();
            if active && self.group_has_intrinsic_output[group] {
                let producer = self.producer_by_group[group];
                if !meaningful[producer] {
                    meaningful[producer] = true;
                    stats.activate_producer();
                    pending.push_back(producer);
                }
            }
        }
        for (product_group, dependent_groups) in
            self.dependent_groups_by_product_group.iter().enumerate()
        {
            if !active_groups[product_group] {
                continue;
            }
            for &group in dependent_groups {
                stats.visit_dependency();
                if !active_groups[group] {
                    continue;
                }
                let producer = self.producer_by_group[group];
                if !meaningful[producer] {
                    meaningful[producer] = true;
                    stats.activate_producer();
                    pending.push_back(producer);
                }
            }
        }
        while let Some(child) = pending.pop_front() {
            for &producer in &self.dependent_producers_by_child[child] {
                stats.visit_dependency();
                if !meaningful[producer] {
                    meaningful[producer] = true;
                    stats.activate_producer();
                    pending.push_back(producer);
                }
            }
            let child = GraphNode::Expansion(self.producers[child]);
            for &group in self
                .dependent_groups_by_product
                .get(&child)
                .into_iter()
                .flatten()
            {
                stats.visit_dependency();
                if !active_groups[group] {
                    continue;
                }
                let producer = self.producer_by_group[group];
                if !meaningful[producer] {
                    meaningful[producer] = true;
                    stats.activate_producer();
                    pending.push_back(producer);
                }
            }
        }
        Ok((meaningful, stats))
    }

    fn product_is_meaningful(&self, product: GraphNode, meaningful: &[bool]) -> bool {
        let GraphNode::Expansion(expansion) = product else {
            return true;
        };
        self.producer_indices
            .get(&expansion)
            .is_none_or(|&producer| meaningful[producer])
    }

    fn outputless_producers(
        &self,
        active_groups: &[bool],
    ) -> Result<(BTreeSet<ExpansionId>, MacroOutputMeaningStats), RetentionError> {
        let (meaningful, stats) = self.meaningful_producers(active_groups)?;
        Ok((
            self.producers
                .iter()
                .zip(meaningful)
                .filter_map(|(&producer, meaningful)| (!meaningful).then_some(producer))
                .collect(),
            stats,
        ))
    }
}

pub(super) fn outputless_complete_macro_outputs(
    complete_output_meaning: &ValidatedCompleteMacroOutputMeaning,
) -> Result<BTreeSet<ExpansionId>, RetentionError> {
    let product_groups = BTreeMap::new();
    MacroOutputMeaningIndex::new(
        &[],
        &product_groups,
        &BTreeSet::new(),
        complete_output_meaning,
    )?
    .outputless_producers(&[])
    .map(|(outputless, _)| outputless)
}

#[cfg(test)]
pub(super) fn outputless_complete_macro_outputs_with_stats(
    complete_output_meaning: &ValidatedCompleteMacroOutputMeaning,
) -> Result<(BTreeSet<ExpansionId>, MacroOutputMeaningStats), RetentionError> {
    let product_groups = BTreeMap::new();
    MacroOutputMeaningIndex::new(
        &[],
        &product_groups,
        &BTreeSet::new(),
        complete_output_meaning,
    )?
    .outputless_producers(&[])
}

/// Delta-driven macro materialization, output-meaning, and compiler-member
/// closure. Every retained compiler node and source unit is consumed once;
/// reverse indexes then visit only the constraints that mention that delta.
pub(super) struct RetentionClosure<'a> {
    macro_products: &'a ValidatedMacroProducts,
    compiler_members: Option<&'a ValidatedCompilerMemberConstraints>,
    seen_presence: BTreeSet<GraphNode>,
    processed_presence: BTreeSet<GraphNode>,
    seen_actual_definitions: BTreeSet<DefinitionId>,
    seen_actual_products: BTreeSet<GraphNode>,
    seen_source: BTreeSet<SourceUnitId>,
    pending_presence: VecDeque<GraphNode>,
    pending_actual_definitions: VecDeque<DefinitionId>,
    pending_actual_products: VecDeque<GraphNode>,
    pending_source: VecDeque<SourceUnitId>,
    initialized: bool,
    macro_sources_opened: Vec<bool>,
    contributor_requested: Vec<bool>,
    contributor_complete: Vec<bool>,
    contributor_missing_sources: Vec<usize>,
    contributor_missing_parents: Vec<usize>,
    group_missing_roots: Vec<usize>,
    pending_requested_contributors: VecDeque<usize>,
    pending_complete_contributors: VecDeque<usize>,
    macro_materialized: Vec<bool>,
    group_has_meaningful_dependency: Vec<bool>,
    meaningful_producers: Vec<bool>,
    pending_meaningful_producers: VecDeque<usize>,
    demanded_producers: Vec<bool>,
    pending_demanded_producers: VecDeque<usize>,
    processed_demanded_children: BTreeSet<ExpansionId>,
    pending_required_expansions: VecDeque<ExpansionId>,
    demand_clause_has_carrier: Vec<bool>,
    demand_clause_has_dependent_child: Vec<bool>,
    demand_clause_satisfied: Vec<bool>,
    conditional_compile_member_state: Vec<u8>,
    conditional_actual_member_state: Vec<u8>,
    actual_definition_class_processed: Vec<bool>,
    #[cfg(test)]
    pub(super) macro_fact_visits: usize,
    #[cfg(test)]
    pub(super) output_meaning_fact_visits: usize,
    #[cfg(test)]
    pub(super) compile_trigger_visits: usize,
    #[cfg(test)]
    pub(super) compile_member_fact_visits: usize,
    #[cfg(test)]
    pub(super) actual_member_fact_visits: usize,
    #[cfg(test)]
    pub(super) demand_fact_visits: usize,
}

impl<'a> RetentionClosure<'a> {
    pub(super) fn new(
        macro_products: &'a ValidatedMacroProducts,
        compiler_members: Option<&'a ValidatedCompilerMemberConstraints>,
    ) -> Self {
        let meaningful_producers = macro_products
            .output_meaning
            .static_intrinsic_producers
            .to_vec();
        let pending_meaningful_producers = meaningful_producers
            .iter()
            .enumerate()
            .filter_map(|(producer, &meaningful)| meaningful.then_some(producer))
            .collect();
        Self {
            macro_products,
            compiler_members,
            seen_presence: BTreeSet::new(),
            processed_presence: BTreeSet::new(),
            seen_actual_definitions: BTreeSet::new(),
            seen_actual_products: BTreeSet::new(),
            seen_source: BTreeSet::new(),
            pending_presence: VecDeque::new(),
            pending_actual_definitions: VecDeque::new(),
            pending_actual_products: VecDeque::new(),
            pending_source: VecDeque::new(),
            initialized: false,
            macro_sources_opened: vec![false; macro_products.materializations.len()],
            contributor_requested: vec![false; macro_products.contributor_index.parents.len()],
            contributor_complete: vec![false; macro_products.contributor_index.parents.len()],
            contributor_missing_sources: macro_products
                .contributor_index
                .local_sources
                .iter()
                .map(|sources| sources.len())
                .collect(),
            contributor_missing_parents: macro_products
                .contributor_index
                .parents
                .iter()
                .map(Vec::len)
                .collect(),
            group_missing_roots: macro_products
                .materializations
                .iter()
                .map(|materialization| materialization.retention_roots().len())
                .collect(),
            pending_requested_contributors: VecDeque::new(),
            pending_complete_contributors: macro_products
                .contributor_index
                .parents
                .iter()
                .zip(&macro_products.contributor_index.local_sources)
                .enumerate()
                .filter_map(|(node, (parents, sources))| {
                    (parents.is_empty() && sources.is_empty()).then_some(node)
                })
                .collect(),
            macro_materialized: vec![false; macro_products.materializations.len()],
            group_has_meaningful_dependency: vec![false; macro_products.materializations.len()],
            meaningful_producers,
            pending_meaningful_producers,
            demanded_producers: vec![false; macro_products.output_meaning.producers.len()],
            pending_demanded_producers: VecDeque::new(),
            processed_demanded_children: BTreeSet::new(),
            pending_required_expansions: VecDeque::new(),
            demand_clause_has_carrier: vec![false; macro_products.demand_clauses.len()],
            demand_clause_has_dependent_child: vec![false; macro_products.demand_clauses.len()],
            demand_clause_satisfied: vec![false; macro_products.demand_clauses.len()],
            conditional_compile_member_state: vec![
                0;
                compiler_members.map_or(0, |members| {
                    members.conditional_requirements.len()
                })
            ],
            conditional_actual_member_state: vec![
                0;
                compiler_members.map_or(0, |members| {
                    members.conditional_requirements.len()
                })
            ],
            actual_definition_class_processed: vec![
                false;
                macro_products.actual_definition_classes.len()
            ],
            #[cfg(test)]
            macro_fact_visits: 0,
            #[cfg(test)]
            output_meaning_fact_visits: 0,
            #[cfg(test)]
            compile_trigger_visits: 0,
            #[cfg(test)]
            compile_member_fact_visits: 0,
            #[cfg(test)]
            actual_member_fact_visits: 0,
            #[cfg(test)]
            demand_fact_visits: 0,
        }
    }

    pub(super) fn seed(
        &mut self,
        compile_present: &BTreeSet<GraphNode>,
        actual_required: &BTreeSet<GraphNode>,
        retained_units: &BTreeSet<SourceUnitId>,
    ) -> Result<(), RetentionError> {
        if self.initialized || !actual_required.is_subset(compile_present) {
            return Err(RetentionError::InvalidConstraint);
        }
        self.initialized = true;
        self.add_presence(compile_present.iter().copied());
        self.add_actual(actual_required.iter().copied());
        self.add_source(retained_units.iter().copied());
        Ok(())
    }

    pub(super) fn add_presence(&mut self, nodes: impl IntoIterator<Item = GraphNode>) {
        for node in nodes {
            if self.seen_presence.insert(node) {
                self.pending_presence.push_back(node);
            }
        }
    }

    pub(super) fn add_actual(&mut self, nodes: impl IntoIterator<Item = GraphNode>) {
        for node in nodes {
            if let GraphNode::Definition(definition) = node
                && self.seen_actual_definitions.insert(definition)
            {
                self.pending_actual_definitions.push_back(definition);
            }
            if self.seen_actual_products.insert(node) {
                self.pending_actual_products.push_back(node);
            }
        }
    }

    #[cfg(test)]
    pub(super) fn add_actual_definitions(
        &mut self,
        definitions: impl IntoIterator<Item = DefinitionId>,
    ) {
        self.add_actual(definitions.into_iter().map(GraphNode::Definition));
    }

    pub(super) fn add_source(&mut self, units: impl IntoIterator<Item = SourceUnitId>) {
        for unit in units {
            if self.seen_source.insert(unit) {
                self.pending_source.push_back(unit);
            }
        }
    }

    fn require_actual(
        &mut self,
        actual_required: &mut BTreeSet<GraphNode>,
        newly_actual: &mut Vec<GraphNode>,
        compile_present: &mut BTreeSet<GraphNode>,
        newly_present: &mut Vec<GraphNode>,
        node: GraphNode,
    ) {
        self.require_materialized_compile(compile_present, newly_present, node);
        if actual_required.insert(node) {
            newly_actual.push(node);
            self.add_actual([node]);
        }
    }

    fn retain_source(
        &mut self,
        retained_units: &mut BTreeSet<SourceUnitId>,
        newly_retained_units: &mut Vec<SourceUnitId>,
        unit: SourceUnitId,
    ) {
        if retain_source_unit(retained_units, newly_retained_units, unit) {
            self.add_source([unit]);
        }
    }

    fn require_materialized_compile(
        &mut self,
        compile_required: &mut BTreeSet<GraphNode>,
        newly_required: &mut Vec<GraphNode>,
        node: GraphNode,
    ) {
        if compile_required.insert(node) {
            newly_required.push(node);
            self.add_presence([node]);
        }
    }

    pub(super) fn close(
        &mut self,
        compile_present: &mut BTreeSet<GraphNode>,
        newly_present: &mut Vec<GraphNode>,
        actual_required: &mut BTreeSet<GraphNode>,
        newly_actual: &mut Vec<GraphNode>,
        retained_units: &mut BTreeSet<SourceUnitId>,
        newly_retained_units: &mut Vec<SourceUnitId>,
    ) {
        while !self.pending_presence.is_empty()
            || !self.pending_actual_definitions.is_empty()
            || !self.pending_actual_products.is_empty()
            || !self.pending_source.is_empty()
            || !self.pending_requested_contributors.is_empty()
            || !self.pending_complete_contributors.is_empty()
            || !self.pending_meaningful_producers.is_empty()
            || !self.pending_demanded_producers.is_empty()
            || !self.pending_required_expansions.is_empty()
        {
            while let Some(product) = self.pending_actual_products.pop_front() {
                let Some(&class) = self
                    .macro_products
                    .actual_definition_class_by_definition
                    .get(&product)
                else {
                    continue;
                };
                if self.actual_definition_class_processed[class] {
                    continue;
                }
                self.actual_definition_class_processed[class] = true;
                let products = self.macro_products.actual_definition_classes[class].clone();
                for product in products {
                    self.require_actual(
                        actual_required,
                        newly_actual,
                        compile_present,
                        newly_present,
                        product,
                    );
                }
            }

            while let Some(node) = self.pending_presence.pop_front() {
                let first_processing = self.processed_presence.insert(node);
                debug_assert!(first_processing);
                if let GraphNode::Definition(trigger) = node
                    && let Some(members) = self.compiler_members
                {
                    if let Some(required) = members.requirements_by_trigger.get(&trigger) {
                        for &required in required {
                            #[cfg(test)]
                            {
                                self.compile_member_fact_visits += 1;
                            }
                            self.require_materialized_compile(
                                compile_present,
                                newly_present,
                                GraphNode::Definition(required),
                            );
                        }
                    }
                    if let Some(conditionals) = members.conditional_by_trigger.get(&trigger) {
                        for &(index, bit) in conditionals {
                            #[cfg(test)]
                            {
                                self.compile_member_fact_visits += 1;
                            }
                            let state = &mut self.conditional_compile_member_state[index];
                            *state |= bit;
                            if *state == 3 {
                                self.require_materialized_compile(
                                    compile_present,
                                    newly_present,
                                    GraphNode::Definition(
                                        members.conditional_requirements[index].required,
                                    ),
                                );
                            }
                        }
                    }
                }
                self.process_macro_trigger(node, compile_present, newly_present);
            }

            while let Some(trigger) = self.pending_actual_definitions.pop_front() {
                if let Some(members) = self.compiler_members {
                    if let Some(required) = members.requirements_by_trigger.get(&trigger) {
                        for &required in required {
                            #[cfg(test)]
                            {
                                self.actual_member_fact_visits += 1;
                            }
                            self.require_actual(
                                actual_required,
                                newly_actual,
                                compile_present,
                                newly_present,
                                GraphNode::Definition(required),
                            );
                        }
                    }
                    if let Some(conditionals) = members.conditional_by_trigger.get(&trigger) {
                        for &(index, bit) in conditionals {
                            #[cfg(test)]
                            {
                                self.actual_member_fact_visits += 1;
                            }
                            let state = &mut self.conditional_actual_member_state[index];
                            *state |= bit;
                            if *state == 3 {
                                self.require_actual(
                                    actual_required,
                                    newly_actual,
                                    compile_present,
                                    newly_present,
                                    GraphNode::Definition(
                                        members.conditional_requirements[index].required,
                                    ),
                                );
                            }
                        }
                    }
                }
                self.process_demand_trigger(trigger);
            }

            while let Some(unit) = self.pending_source.pop_front() {
                let nodes = self
                    .macro_products
                    .contributor_index
                    .nodes_by_source
                    .get(&unit)
                    .cloned()
                    .unwrap_or_default();
                for node in nodes {
                    #[cfg(test)]
                    {
                        self.macro_fact_visits += 1;
                    }
                    let remaining = &mut self.contributor_missing_sources[node];
                    debug_assert_ne!(*remaining, 0);
                    *remaining -= 1;
                    self.queue_contributor_if_complete(node);
                }
            }

            while let Some(node) = self.pending_requested_contributors.pop_front() {
                let local_sources =
                    self.macro_products.contributor_index.local_sources[node].to_vec();
                let parents = self.macro_products.contributor_index.parents[node].clone();
                for source in local_sources {
                    #[cfg(test)]
                    {
                        self.macro_fact_visits += 1;
                    }
                    self.retain_source(retained_units, newly_retained_units, source);
                }
                for parent in parents {
                    #[cfg(test)]
                    {
                        self.macro_fact_visits += 1;
                    }
                    self.request_contributor(parent);
                }
            }

            while let Some(node) = self.pending_complete_contributors.pop_front() {
                if self.contributor_complete[node]
                    || self.contributor_missing_sources[node] != 0
                    || self.contributor_missing_parents[node] != 0
                {
                    continue;
                }
                self.contributor_complete[node] = true;
                let children = self.macro_products.contributor_index.children[node].clone();
                for child in children {
                    #[cfg(test)]
                    {
                        self.macro_fact_visits += 1;
                    }
                    let missing = &mut self.contributor_missing_parents[child];
                    debug_assert_ne!(*missing, 0);
                    *missing -= 1;
                    self.queue_contributor_if_complete(child);
                }
                let groups = self.macro_products.contributor_index.groups_by_root[node].clone();
                for group in groups {
                    #[cfg(test)]
                    {
                        self.macro_fact_visits += 1;
                    }
                    let missing = &mut self.group_missing_roots[group];
                    debug_assert_ne!(*missing, 0);
                    *missing -= 1;
                    if *missing == 0 && !self.macro_materialized[group] {
                        self.macro_materialized[group] = true;
                        self.activate_group_meaning(group);
                        self.materialize_group_outputs(group, compile_present, newly_present);
                    }
                }
            }

            while let Some(child) = self.pending_meaningful_producers.pop_front() {
                self.process_meaningful_producer(child, compile_present, newly_present);
            }

            while let Some(producer) = self.pending_demanded_producers.pop_front() {
                let child = self.macro_products.output_meaning.producers[producer];
                if self.processed_demanded_children.insert(child) {
                    self.require_actual(
                        actual_required,
                        newly_actual,
                        compile_present,
                        newly_present,
                        GraphNode::Expansion(child),
                    );
                    self.process_demanded_child(child);
                }
            }

            while let Some(child) = self.pending_required_expansions.pop_front() {
                self.require_actual(
                    actual_required,
                    newly_actual,
                    compile_present,
                    newly_present,
                    GraphNode::Expansion(child),
                );
                self.process_demanded_child(child);
            }
        }
    }

    fn process_macro_trigger(
        &mut self,
        node: GraphNode,
        compile_required: &mut BTreeSet<GraphNode>,
        newly_required: &mut Vec<GraphNode>,
    ) {
        if !self
            .macro_products
            .output_meaning
            .product_is_meaningful(node, &self.meaningful_producers)
        {
            return;
        }
        let groups = self
            .macro_products
            .compile_trigger_groups
            .get(&node)
            .cloned()
            .unwrap_or_default();
        for group in groups {
            #[cfg(test)]
            {
                self.macro_fact_visits += 1;
                self.compile_trigger_visits += 1;
            }
            self.group_has_meaningful_dependency[group] = true;
            self.request_group_sources(group);
            if self.macro_materialized[group] {
                let owner_members = self.macro_products.materializations[group]
                    .owner_requirements
                    .iter()
                    .filter(|requirement| node == GraphNode::Definition(requirement.owner))
                    .flat_map(|requirement| {
                        requirement
                            .members
                            .iter()
                            .copied()
                            .map(GraphNode::Definition)
                    })
                    .collect::<Vec<_>>();
                for member in owner_members {
                    self.require_materialized_compile(compile_required, newly_required, member);
                }
            }
        }
    }

    fn process_demand_trigger(&mut self, definition: DefinitionId) {
        let producers = self
            .macro_products
            .output_meaning
            .demand_producers_by_trigger
            .get(&definition)
            .cloned()
            .unwrap_or_default();
        for producer in producers {
            #[cfg(test)]
            {
                self.demand_fact_visits += 1;
            }
            self.activate_demanded_producer(producer);
        }
        let clauses = self
            .macro_products
            .demand_clauses_by_carrier
            .get(&definition)
            .cloned()
            .unwrap_or_default();
        for clause in clauses {
            #[cfg(test)]
            {
                self.demand_fact_visits += 1;
            }
            if !self.demand_clause_has_carrier[clause] {
                self.demand_clause_has_carrier[clause] = true;
                self.request_demand_clause_if_ready(clause);
            }
        }
    }

    fn activate_demanded_producer(&mut self, producer: usize) {
        if !self.demanded_producers[producer] {
            self.demanded_producers[producer] = true;
            self.pending_demanded_producers.push_back(producer);
        }
    }

    fn process_demanded_child(&mut self, child: ExpansionId) {
        let clauses = self
            .macro_products
            .dependent_demand_clauses_by_child
            .get(&child)
            .cloned()
            .unwrap_or_default();
        for clause in clauses {
            #[cfg(test)]
            {
                self.demand_fact_visits += 1;
            }
            if !self.demand_clause_has_dependent_child[clause] {
                self.demand_clause_has_dependent_child[clause] = true;
                self.request_demand_clause_if_ready(clause);
            }
        }
    }

    fn request_demand_clause_if_ready(&mut self, clause: usize) {
        let demand = self.macro_products.demand_clauses[clause].clone();
        if !self.demand_clause_satisfied[clause]
            && self.demand_clause_has_carrier[clause]
            && (!demand.required_expansions.is_empty()
                || demand.opaque_dependent
                || self.demand_clause_has_dependent_child[clause])
        {
            self.demand_clause_satisfied[clause] = true;
            for child in demand.required_expansions {
                self.activate_required_child(child);
            }
            match demand.target {
                MacroDemandTarget::Producer(producer) => self.activate_demanded_producer(producer),
                MacroDemandTarget::Group(group) => self.request_group_sources(group),
            }
        }
    }

    fn activate_required_child(&mut self, child: ExpansionId) {
        if let Some(&producer) = self
            .macro_products
            .output_meaning
            .producer_indices
            .get(&child)
        {
            self.activate_demanded_producer(producer);
        } else if self.processed_demanded_children.insert(child) {
            self.pending_required_expansions.push_back(child);
        }
    }

    fn request_group_sources(&mut self, group: usize) {
        if self.macro_sources_opened[group] {
            return;
        }
        self.macro_sources_opened[group] = true;
        let roots = self.macro_products.materializations[group]
            .retention_roots()
            .iter()
            .map(|root| self.macro_products.contributor_index.node_indices[root])
            .collect::<Vec<_>>();
        for root in roots {
            self.request_contributor(root);
        }
    }

    fn activate_group_meaning(&mut self, group: usize) {
        #[cfg(test)]
        {
            self.output_meaning_fact_visits += 1;
        }
        let meaning = &self.macro_products.output_meaning;
        if meaning.group_has_intrinsic_output[group] || self.group_has_meaningful_dependency[group]
        {
            self.activate_producer(meaning.producer_by_group[group]);
        }
    }

    fn activate_producer(&mut self, producer: usize) {
        if !self.meaningful_producers[producer] {
            self.meaningful_producers[producer] = true;
            self.pending_meaningful_producers.push_back(producer);
        }
    }

    fn materialize_group_outputs(
        &mut self,
        group: usize,
        compile_required: &mut BTreeSet<GraphNode>,
        newly_required: &mut Vec<GraphNode>,
    ) {
        let materialization = &self.macro_products.materializations[group];
        let mut products = materialization.products.clone();
        let owner_requirements = materialization.owner_requirements.clone();
        for requirement in &owner_requirements {
            if compile_required.contains(&GraphNode::Definition(requirement.owner)) {
                products.extend(
                    requirement
                        .members
                        .iter()
                        .copied()
                        .map(GraphNode::Definition),
                );
            }
        }
        for product in products {
            self.require_materialized_compile(compile_required, newly_required, product);
        }
    }

    fn process_meaningful_producer(
        &mut self,
        child: usize,
        compile_required: &mut BTreeSet<GraphNode>,
        newly_required: &mut Vec<GraphNode>,
    ) {
        let dependent_producers = self
            .macro_products
            .output_meaning
            .dependent_producers_by_child[child]
            .clone();
        for producer in dependent_producers {
            #[cfg(test)]
            {
                self.output_meaning_fact_visits += 1;
            }
            self.activate_producer(producer);
        }
        let child_node = GraphNode::Expansion(self.macro_products.output_meaning.producers[child]);
        let was_processed = self.processed_presence.contains(&child_node);
        let dependent_groups = self
            .macro_products
            .output_meaning
            .dependent_groups_by_product
            .get(&child_node)
            .cloned()
            .unwrap_or_default();
        for group in dependent_groups {
            #[cfg(test)]
            {
                self.macro_fact_visits += 1;
                self.output_meaning_fact_visits += 1;
            }
            let newly_meaningful = !self.group_has_meaningful_dependency[group];
            self.group_has_meaningful_dependency[group] = true;
            if newly_meaningful && self.macro_materialized[group] {
                self.activate_producer(self.macro_products.output_meaning.producer_by_group[group]);
            }
        }
        if was_processed {
            self.process_macro_trigger(child_node, compile_required, newly_required);
        }
    }

    fn request_contributor(&mut self, node: usize) {
        if !self.contributor_requested[node] {
            self.contributor_requested[node] = true;
            self.pending_requested_contributors.push_back(node);
        }
    }

    fn queue_contributor_if_complete(&mut self, node: usize) {
        if !self.contributor_complete[node]
            && self.contributor_missing_sources[node] == 0
            && self.contributor_missing_parents[node] == 0
        {
            self.pending_complete_contributors.push_back(node);
        }
    }
}

impl ValidatedMacroProducts {
    pub(super) fn new_with_dag(
        contributor_dag: Arc<MacroContributorDag>,
        source_unit_count: usize,
        materializations: Vec<MacroMaterialization>,
        delegated_macro_expansions: BTreeSet<ExpansionId>,
    ) -> Result<Self, RetentionError> {
        let producer_universe = materializations
            .iter()
            .map(|materialization| materialization.producer)
            .collect();
        Self::new_with_dag_and_producers(
            contributor_dag,
            source_unit_count,
            materializations,
            delegated_macro_expansions,
            producer_universe,
        )
    }

    fn new_with_dag_and_producers(
        contributor_dag: Arc<MacroContributorDag>,
        source_unit_count: usize,
        materializations: Vec<MacroMaterialization>,
        delegated_macro_expansions: BTreeSet<ExpansionId>,
        producer_universe: BTreeSet<ExpansionId>,
    ) -> Result<Self, RetentionError> {
        let complete_output_meaning = ValidatedCompleteMacroOutputMeaning {
            universe: producer_universe.clone(),
            records: BTreeMap::new(),
        };
        let product_groups = macro_product_groups(&materializations)?;
        let output_meaning = MacroOutputMeaningIndex::new(
            &materializations,
            &product_groups,
            &producer_universe,
            &complete_output_meaning,
        )?;
        let output_demands = vec![Box::<[MacroGroupDemand]>::default(); materializations.len()];
        let product_classes = singleton_product_class_facts(&materializations);
        Self::new_with_dag_and_output_meaning(
            contributor_dag,
            source_unit_count,
            materializations,
            delegated_macro_expansions,
            product_groups,
            output_meaning,
            MacroGroupFacts {
                product_classes,
                output_demands: MacroOutputDemandFacts {
                    groups: output_demands,
                    require_complete: false,
                },
            },
        )
    }

    fn new_with_dag_and_output_meaning(
        contributor_dag: Arc<MacroContributorDag>,
        source_unit_count: usize,
        materializations: Vec<MacroMaterialization>,
        delegated_macro_expansions: BTreeSet<ExpansionId>,
        product_groups: BTreeMap<GraphNode, usize>,
        output_meaning: MacroOutputMeaningIndex,
        group_facts: MacroGroupFacts,
    ) -> Result<Self, RetentionError> {
        let MacroGroupFacts {
            product_classes: product_class_facts,
            output_demands,
        } = group_facts;
        if output_demands.groups.len() != materializations.len()
            || product_class_facts.groups.len() != materializations.len()
        {
            return Err(RetentionError::InvalidConstraint);
        }
        let mut node_indices = BTreeMap::new();
        let mut local_sources = Vec::with_capacity(contributor_dag.node_count());
        let mut parents = Vec::with_capacity(contributor_dag.node_count());
        let mut children = Vec::<Vec<usize>>::with_capacity(contributor_dag.node_count());
        let mut nodes_by_source = BTreeMap::<SourceUnitId, Vec<usize>>::new();
        let mut node_has_source = Vec::with_capacity(contributor_dag.node_count());
        for (expected_index, (id, local, parent_ids)) in contributor_dag.nodes().enumerate() {
            if node_indices.insert(id, expected_index).is_some()
                || local.windows(2).any(|pair| pair[0] >= pair[1])
                || local
                    .iter()
                    .any(|unit| unit.0 as usize >= source_unit_count)
                || parent_ids.windows(2).any(|pair| pair[0] >= pair[1])
            {
                return Err(RetentionError::InvalidConstraint);
            }
            let parent_indices = parent_ids
                .iter()
                .map(|parent| {
                    node_indices
                        .get(parent)
                        .copied()
                        .ok_or(RetentionError::InvalidConstraint)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let has_source =
                !local.is_empty() || parent_indices.iter().any(|&parent| node_has_source[parent]);
            for &unit in local {
                nodes_by_source
                    .entry(unit)
                    .or_default()
                    .push(expected_index);
            }
            for &parent in &parent_indices {
                children[parent].push(expected_index);
            }
            local_sources.push(local.to_vec().into_boxed_slice());
            parents.push(parent_indices);
            children.push(Vec::new());
            node_has_source.push(has_source);
        }
        if local_sources.len() != contributor_dag.node_count() {
            return Err(RetentionError::InvalidConstraint);
        }

        let mut compile_trigger_groups = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut actual_definition_classes = Vec::new();
        let mut actual_definition_class_by_definition = BTreeMap::new();
        let mut producer_groups = BTreeMap::<ExpansionId, Vec<usize>>::new();
        let mut demand_clauses = Vec::new();
        let mut demand_clauses_by_carrier = BTreeMap::<DefinitionId, Vec<usize>>::new();
        let mut dependent_demand_clauses_by_child = BTreeMap::<ExpansionId, Vec<usize>>::new();
        for (producer, demand) in output_meaning.producer_demand_facts.iter() {
            index_macro_demand_clause(
                MacroDemandTarget::Producer(*producer),
                demand,
                &mut demand_clauses,
                &mut demand_clauses_by_carrier,
                &mut dependent_demand_clauses_by_child,
                &output_meaning.producer_indices,
            )?;
        }
        let mut groups_by_root = vec![Vec::new(); contributor_dag.node_count()];
        let mut contributor_classes = BTreeMap::<Box<[MacroContributorSetId]>, usize>::new();
        let mut contributor_class_by_group = Vec::with_capacity(materializations.len());
        let mut contributor_class_roots = Vec::new();
        let mut identity_cohorts =
            BTreeMap::<MacroContributorSetId, (usize, BTreeSet<MacroContributorSetId>)>::new();
        for materialization in &materializations {
            if let Some(root) = materialization.identity_cohort_root {
                let cohort = identity_cohorts.entry(root).or_default();
                cohort.0 += 1;
                cohort
                    .1
                    .extend(materialization.contributor_roots.iter().copied());
            }
        }
        for (&root, (uses, local_roots)) in &identity_cohorts {
            let gate = node_indices
                .get(&root)
                .copied()
                .ok_or(RetentionError::InvalidConstraint)?;
            let expected = local_roots
                .iter()
                .map(|root| {
                    node_indices
                        .get(root)
                        .copied()
                        .ok_or(RetentionError::InvalidConstraint)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let valid_gate = match expected.as_slice() {
                [local] => gate == *local,
                [] => false,
                _ => local_sources[gate].is_empty() && parents[gate] == expected,
            };
            if *uses < 2 || !valid_gate {
                return Err(RetentionError::InvalidConstraint);
            }
        }
        for (group, materialization) in materializations.iter().enumerate() {
            if (materialization.products.is_empty()
                && materialization.owner_requirements.is_empty())
                || materialization
                    .products
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                || materialization.contributor_roots.is_empty()
                || materialization
                    .contributor_roots
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
            {
                return Err(RetentionError::InvalidConstraint);
            }
            let mut classified_products = BTreeSet::new();
            for class in &product_class_facts.groups[group] {
                if class.is_empty() || class.windows(2).any(|pair| pair[0] >= pair[1]) {
                    return Err(RetentionError::InvalidConstraint);
                }
                let definition_class = class
                    .iter()
                    .copied()
                    .filter(|product| matches!(product, GraphNode::Definition(_)))
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                let class_index =
                    (!definition_class.is_empty()).then_some(actual_definition_classes.len());
                for &product in class.iter() {
                    if !materialization.products.contains(&product)
                        || !classified_products.insert(product)
                    {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    if let Some(class_index) = class_index
                        && matches!(product, GraphNode::Definition(_))
                        && actual_definition_class_by_definition
                            .insert(product, class_index)
                            .is_some()
                    {
                        return Err(RetentionError::InvalidConstraint);
                    }
                }
                if !definition_class.is_empty() {
                    actual_definition_classes.push(definition_class);
                }
            }
            if product_class_facts.require_complete
                && classified_products
                    .iter()
                    .copied()
                    .ne(materialization.products.iter().copied())
            {
                return Err(RetentionError::InvalidConstraint);
            }
            let local_roots = materialization
                .contributor_roots
                .iter()
                .map(|root| {
                    node_indices
                        .get(root)
                        .copied()
                        .ok_or(RetentionError::InvalidConstraint)
                })
                .collect::<Result<Vec<_>, _>>()?;
            if local_roots.iter().any(|&root| !node_has_source[root]) {
                return Err(RetentionError::InvalidConstraint);
            }
            let roots = materialization
                .retention_roots()
                .iter()
                .map(|root| {
                    node_indices
                        .get(root)
                        .copied()
                        .ok_or(RetentionError::InvalidConstraint)
                })
                .collect::<Result<Vec<_>, _>>()?;
            if roots.iter().any(|&root| !node_has_source[root]) {
                return Err(RetentionError::InvalidConstraint);
            }
            for root in roots {
                groups_by_root[root].push(group);
            }
            let contributor_class = match contributor_classes.entry(
                materialization
                    .retention_roots()
                    .to_vec()
                    .into_boxed_slice(),
            ) {
                std::collections::btree_map::Entry::Occupied(entry) => *entry.get(),
                std::collections::btree_map::Entry::Vacant(entry) => {
                    let class = contributor_class_roots.len();
                    contributor_class_roots.push(entry.key().clone());
                    entry.insert(class);
                    class
                }
            };
            contributor_class_by_group.push(contributor_class);
            producer_groups
                .entry(materialization.producer)
                .or_default()
                .push(group);
            let mut role_expansions = BTreeSet::new();
            for demand in &output_demands.groups[group] {
                for &expansion in demand
                    .dependent_expansions
                    .iter()
                    .chain(demand.required_expansions.iter())
                {
                    if !materialization
                        .products
                        .contains(&GraphNode::Expansion(expansion))
                        || !role_expansions.insert(expansion)
                    {
                        return Err(RetentionError::InvalidConstraint);
                    }
                }
                index_macro_demand_clause(
                    MacroDemandTarget::Group(group),
                    demand,
                    &mut demand_clauses,
                    &mut demand_clauses_by_carrier,
                    &mut dependent_demand_clauses_by_child,
                    &output_meaning.producer_indices,
                )?;
            }
            if output_demands.require_complete && materialization.products.iter().any(|product| {
                    matches!(product, GraphNode::Expansion(expansion) if !role_expansions.contains(expansion))
                })
            {
                return Err(RetentionError::InvalidConstraint);
            }
            for &product in &materialization.products {
                if !matches!(product, GraphNode::Expansion(expansion) if role_expansions.contains(&expansion))
                {
                    compile_trigger_groups
                        .entry(product)
                        .or_default()
                        .push(group);
                }
            }
            for requirement in &materialization.owner_requirements {
                match &requirement.effect {
                    MacroOwnerEffect::Semantic => {
                        compile_trigger_groups
                            .entry(GraphNode::Definition(requirement.owner))
                            .or_default()
                            .push(group);
                        for &member in &requirement.members {
                            compile_trigger_groups
                                .entry(GraphNode::Definition(member))
                                .or_default()
                                .push(group);
                        }
                    }
                    MacroOwnerEffect::TransparentShell { .. } => {}
                }
            }
        }
        for (&product, groups) in &output_meaning.dependent_groups_by_product {
            for &group in groups {
                if output_demands.groups[group].is_empty() {
                    compile_trigger_groups
                        .entry(product)
                        .or_default()
                        .push(group);
                }
            }
        }
        for groups in compile_trigger_groups.values_mut() {
            groups.sort_unstable();
            groups.dedup();
        }
        Ok(Self {
            contributor_dag,
            contributor_index: ValidatedContributorDag {
                node_indices,
                local_sources,
                parents,
                children,
                nodes_by_source,
                groups_by_root,
            },
            materializations,
            delegated_macro_expansions,
            product_groups,
            actual_definition_classes,
            actual_definition_class_by_definition,
            compile_trigger_groups,
            producer_groups,
            demand_clauses: demand_clauses.into_boxed_slice(),
            demand_clauses_by_carrier,
            dependent_demand_clauses_by_child,
            contributor_class_by_group,
            contributor_class_roots,
            output_meaning,
        })
    }

    #[cfg(test)]
    pub(super) fn new(
        materializations: Vec<MacroMaterialization>,
        delegated_macro_expansions: BTreeSet<ExpansionId>,
    ) -> Result<Self, RetentionError> {
        let producer_universe = materializations
            .iter()
            .map(|materialization| materialization.producer)
            .collect();
        Self::new_with_producers(
            materializations,
            delegated_macro_expansions,
            producer_universe,
        )
    }

    #[cfg(test)]
    pub(super) fn new_with_producers(
        materializations: Vec<MacroMaterialization>,
        delegated_macro_expansions: BTreeSet<ExpansionId>,
        producer_universe: BTreeSet<ExpansionId>,
    ) -> Result<Self, RetentionError> {
        let max_source = materializations
            .iter()
            .flat_map(|materialization| materialization.contributor_roots.iter())
            .map(|root| root.test_source_unit().0)
            .max();
        let source_unit_count = max_source.map_or(0, |source| source as usize + 1);
        Self::new_with_dag_and_producers(
            Arc::new(MacroContributorDag::test_source_singletons(max_source)),
            source_unit_count,
            materializations,
            delegated_macro_expansions,
            producer_universe,
        )
    }

    #[cfg(test)]
    pub(super) fn new_with_product_classes(
        materializations: Vec<MacroMaterialization>,
        product_classes: Vec<Vec<Vec<GraphNode>>>,
    ) -> Result<Self, RetentionError> {
        let producer_universe = materializations
            .iter()
            .map(|materialization| materialization.producer)
            .collect::<BTreeSet<_>>();
        let max_source = materializations
            .iter()
            .flat_map(|materialization| materialization.contributor_roots.iter())
            .map(|root| root.test_source_unit().0)
            .max();
        let source_unit_count = max_source.map_or(0, |source| source as usize + 1);
        let complete_output_meaning = ValidatedCompleteMacroOutputMeaning {
            universe: producer_universe.clone(),
            records: BTreeMap::new(),
        };
        let product_groups = macro_product_groups(&materializations)?;
        let output_meaning = MacroOutputMeaningIndex::new(
            &materializations,
            &product_groups,
            &producer_universe,
            &complete_output_meaning,
        )?;
        let product_class_facts = MacroProductClassFacts {
            groups: product_classes
                .into_iter()
                .map(|classes| {
                    classes
                        .into_iter()
                        .map(Vec::into_boxed_slice)
                        .collect::<Vec<_>>()
                        .into_boxed_slice()
                })
                .collect(),
            require_complete: true,
        };
        let output_demands = MacroOutputDemandFacts {
            groups: vec![Box::new([]); materializations.len()],
            require_complete: false,
        };
        Self::new_with_dag_and_output_meaning(
            Arc::new(MacroContributorDag::test_source_singletons(max_source)),
            source_unit_count,
            materializations,
            BTreeSet::new(),
            product_groups,
            output_meaning,
            MacroGroupFacts {
                product_classes: product_class_facts,
                output_demands,
            },
        )
    }

    #[cfg(test)]
    pub(super) fn new_with_output_demands(
        materializations: Vec<MacroMaterialization>,
        output_demands: Vec<Vec<MacroGroupDemand>>,
        producer_universe: BTreeSet<ExpansionId>,
    ) -> Result<Self, RetentionError> {
        Self::new_with_output_demands_and_triggers(
            materializations,
            output_demands,
            producer_universe,
            BTreeMap::new(),
        )
    }

    #[cfg(test)]
    pub(super) fn new_with_output_demands_and_triggers(
        materializations: Vec<MacroMaterialization>,
        output_demands: Vec<Vec<MacroGroupDemand>>,
        producer_universe: BTreeSet<ExpansionId>,
        actual_triggers: BTreeMap<ExpansionId, Vec<DefinitionId>>,
    ) -> Result<Self, RetentionError> {
        let max_source = materializations
            .iter()
            .flat_map(|materialization| materialization.contributor_roots.iter())
            .map(|root| root.test_source_unit().0)
            .max();
        let source_unit_count = max_source.map_or(0, |source| source as usize + 1);
        let complete_output_meaning = ValidatedCompleteMacroOutputMeaning {
            universe: producer_universe.clone(),
            records: actual_triggers
                .into_iter()
                .map(|(producer, definitions)| {
                    (
                        producer,
                        CompleteMacroOutputMeaningRecord {
                            intrinsic: true,
                            residual_intrinsic: true,
                            dependent_expansions: Box::new([]),
                            actual_demand_definitions: definitions.into_boxed_slice(),
                            output_demands: Box::new([]),
                        },
                    )
                })
                .collect(),
        };
        let product_groups = macro_product_groups(&materializations)?;
        let output_meaning = MacroOutputMeaningIndex::new(
            &materializations,
            &product_groups,
            &producer_universe,
            &complete_output_meaning,
        )?;
        let product_classes = singleton_product_class_facts(&materializations);
        Self::new_with_dag_and_output_meaning(
            Arc::new(MacroContributorDag::test_source_singletons(max_source)),
            source_unit_count,
            materializations,
            BTreeSet::new(),
            product_groups,
            output_meaning,
            MacroGroupFacts {
                product_classes,
                output_demands: MacroOutputDemandFacts {
                    groups: output_demands
                        .into_iter()
                        .map(Vec::into_boxed_slice)
                        .collect(),
                    require_complete: true,
                },
            },
        )
    }

    pub(super) fn group_for_product(&self, product: GraphNode) -> Option<usize> {
        self.product_groups.get(&product).copied()
    }

    #[cfg(test)]
    pub(super) fn contributor_sources_for_group(
        &self,
        group: usize,
    ) -> Result<Vec<SourceUnitId>, RetentionError> {
        let contributor_class = self
            .contributor_class_by_group
            .get(group)
            .copied()
            .ok_or(RetentionError::InvalidConstraint)?;
        self.contributor_sources_for_class_with_visits(contributor_class)
            .map(|(sources, _)| sources)
    }

    pub(super) fn contributor_class_for_group(&self, group: usize) -> Option<usize> {
        self.contributor_class_by_group.get(group).copied()
    }

    pub(super) fn contributor_sources_for_class_with_visits(
        &self,
        contributor_class: usize,
    ) -> Result<(Vec<SourceUnitId>, usize), RetentionError> {
        let roots = self
            .contributor_class_roots
            .get(contributor_class)
            .ok_or(RetentionError::InvalidConstraint)?;
        let mut seen = HashSet::new();
        let mut pending = roots
            .iter()
            .map(|root| {
                self.contributor_index
                    .node_indices
                    .get(root)
                    .copied()
                    .ok_or(RetentionError::InvalidConstraint)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut sources = BTreeSet::new();
        let mut visits = 0;
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            visits += 1;
            sources.extend(self.contributor_index.local_sources[node].iter().copied());
            pending.extend(self.contributor_index.parents[node].iter().copied());
        }
        (!sources.is_empty())
            .then(|| (sources.into_iter().collect(), visits))
            .ok_or(RetentionError::InvalidConstraint)
    }

    fn complete_contributor_nodes(&self, retained_units: &BTreeSet<SourceUnitId>) -> Vec<bool> {
        let mut complete = vec![false; self.contributor_index.parents.len()];
        for node in 0..complete.len() {
            complete[node] = self.contributor_index.local_sources[node]
                .iter()
                .all(|unit| retained_units.contains(unit))
                && self.contributor_index.parents[node]
                    .iter()
                    .all(|&parent| complete[parent]);
        }
        complete
    }
}

fn macro_product_groups(
    materializations: &[MacroMaterialization],
) -> Result<BTreeMap<GraphNode, usize>, RetentionError> {
    let mut product_groups = BTreeMap::new();
    for (group, materialization) in materializations.iter().enumerate() {
        for &product in &materialization.products {
            if product_groups.insert(product, group).is_some() {
                return Err(RetentionError::InvalidConstraint);
            }
        }
    }
    Ok(product_groups)
}

fn singleton_product_class_facts(
    materializations: &[MacroMaterialization],
) -> MacroProductClassFacts {
    MacroProductClassFacts {
        groups: materializations
            .iter()
            .map(|materialization| {
                materialization
                    .products
                    .iter()
                    .map(|&product| Box::from([product]))
                    .collect::<Vec<_>>()
                    .into_boxed_slice()
            })
            .collect(),
        require_complete: true,
    }
}

fn index_macro_demand_clause(
    target: MacroDemandTarget,
    demand: &MacroGroupDemand,
    clauses: &mut Vec<MacroDemandClause>,
    clauses_by_carrier: &mut BTreeMap<DefinitionId, Vec<usize>>,
    dependent_clauses_by_child: &mut BTreeMap<ExpansionId, Vec<usize>>,
    producer_indices: &BTreeMap<ExpansionId, usize>,
) -> Result<(), RetentionError> {
    if demand.carriers.is_empty()
        || demand.carriers.windows(2).any(|pair| pair[0] >= pair[1])
        || (demand.dependent_expansions.is_empty() && demand.required_expansions.is_empty())
        || demand
            .dependent_expansions
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || demand
            .required_expansions
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || demand
            .dependent_expansions
            .iter()
            .any(|expansion| demand.required_expansions.binary_search(expansion).is_ok())
    {
        return Err(RetentionError::InvalidConstraint);
    }
    let clause = clauses.len();
    clauses.push(MacroDemandClause {
        target,
        required_expansions: demand.required_expansions.clone(),
        opaque_dependent: demand
            .dependent_expansions
            .iter()
            .any(|child| !producer_indices.contains_key(child)),
    });
    for &carrier in &demand.carriers {
        clauses_by_carrier.entry(carrier).or_default().push(clause);
    }
    for &child in demand
        .dependent_expansions
        .iter()
        .filter(|child| producer_indices.contains_key(child))
    {
        dependent_clauses_by_child
            .entry(child)
            .or_default()
            .push(clause);
    }
    Ok(())
}

pub(super) fn outputless_macro_expansions_after_rewrite(
    macro_products: &ValidatedMacroProducts,
    retained_units: &BTreeSet<SourceUnitId>,
) -> Result<BTreeSet<ExpansionId>, RetentionError> {
    outputless_macro_expansions_after_rewrite_with_stats(macro_products, retained_units)
        .map(|(outputless, _)| outputless)
}

pub(super) fn outputless_macro_expansions_after_rewrite_with_stats(
    macro_products: &ValidatedMacroProducts,
    retained_units: &BTreeSet<SourceUnitId>,
) -> Result<(BTreeSet<ExpansionId>, MacroOutputMeaningStats), RetentionError> {
    let complete = macro_products.complete_contributor_nodes(retained_units);
    let active_groups = macro_products
        .materializations
        .iter()
        .map(|materialization| {
            materialization
                .retention_roots()
                .iter()
                .all(|root| complete[macro_products.contributor_index.node_indices[root]])
        })
        .collect::<Vec<_>>();
    macro_products
        .output_meaning
        .outputless_producers(&active_groups)
}

pub(super) fn validate_refined_macro_producers(
    source: &SourceInventory,
    graph: &DependencyGraph,
    refined_macro_definitions: &BTreeSet<SourceUnitId>,
    macro_rule_selections: &[MacroRuleSelectionRequirement],
    producer_coverage: &[MacroProducerCoverage],
) -> Result<BTreeSet<ExpansionId>, RetentionError> {
    if producer_coverage
        .windows(2)
        .any(|pair| pair[0].producer() >= pair[1].producer())
    {
        return Err(RetentionError::InvalidConstraint);
    }
    let selected_rules = macro_rule_selections
        .iter()
        .map(|selection| (selection.expansion, selection.rule))
        .collect::<BTreeMap<_, _>>();
    let mut producers = BTreeSet::new();
    for coverage in producer_coverage {
        let producer = coverage.producer();
        let Some(expansion) = graph.expansions.get(producer.0 as usize) else {
            return Err(RetentionError::InvalidConstraint);
        };
        let Some(&selected_rule) = selected_rules.get(&producer) else {
            return Err(RetentionError::InvalidConstraint);
        };
        if expansion.id != producer
            || expansion.implementation != Some(MacroImplementationKind::Declarative)
            || !macro_rule_requirement_matches(
                source,
                &graph.definitions,
                refined_macro_definitions,
                expansion,
                selected_rule,
            )
            || !producers.insert(producer)
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    Ok(producers)
}

pub(super) fn validate_macro_source_refinement_coverage(
    source: &SourceInventory,
    graph: &DependencyGraph,
    selections: &[MacroRuleSelectionRequirement],
    refined_producers: &BTreeSet<ExpansionId>,
    directly_outputless: &BTreeSet<ExpansionId>,
) -> Result<(), RetentionError> {
    let split_template_rules = source
        .macro_templates
        .iter()
        .map(|template| template.rule)
        .collect::<BTreeSet<_>>();
    let repetition_keys = source
        .macro_repetitions
        .iter()
        .map(|repetition| (repetition.invocation, repetition.rule))
        .collect::<BTreeSet<_>>();
    let mut observed_repetition_keys = BTreeSet::new();

    for selection in selections {
        let expansion = graph
            .expansions
            .get(selection.expansion.0 as usize)
            .filter(|expansion| expansion.id == selection.expansion)
            .ok_or(RetentionError::InvalidGraph)?;
        let repetition_key = expansion
            .written_invocation
            .map(|invocation| (invocation, selection.rule));
        let source_was_split = split_template_rules.contains(&selection.rule)
            || repetition_key.is_some_and(|key| repetition_keys.contains(&key));
        if source_was_split
            && !refined_producers.contains(&selection.expansion)
            && !directly_outputless.contains(&selection.expansion)
        {
            return Err(RetentionError::IncompleteMacroProductConstraints);
        }
        if let Some(key) = repetition_key
            && repetition_keys.contains(&key)
        {
            observed_repetition_keys.insert(key);
        }
    }

    if observed_repetition_keys != repetition_keys {
        return Err(RetentionError::IncompleteMacroProductConstraints);
    }
    Ok(())
}

fn lower_macro_materialization_groups_with_demands(
    groups: Vec<PendingMacroMaterializationGroup>,
) -> Result<LoweredMacroMaterializations, RetentionError> {
    let mut groups = groups
        .into_iter()
        .map(|group| {
            if group.contributor_roots.is_empty()
                || (group.products.is_empty() && group.owner_requirements.is_empty())
            {
                return Err(RetentionError::InvalidConstraint);
            }
            Ok((
                MacroMaterialization {
                    producer: group.producer,
                    products: group.products.into_iter().collect(),
                    owner_requirements: group.owner_requirements.into_iter().collect(),
                    contributor_roots: group.contributor_roots,
                    identity_cohort_root: group.identity_cohort_root,
                },
                group.product_classes.into_boxed_slice(),
                group.output_demands.into_iter().collect::<Box<[_]>>(),
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    groups.sort_by(|left, right| left.0.cmp(&right.0));
    if groups.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(RetentionError::InvalidConstraint);
    }
    let mut materializations = Vec::with_capacity(groups.len());
    let mut product_classes = Vec::with_capacity(groups.len());
    let mut output_demands = Vec::with_capacity(groups.len());
    for (materialization, classes, demands) in groups {
        materializations.push(materialization);
        product_classes.push(classes);
        output_demands.push(demands);
    }
    Ok(LoweredMacroMaterializations {
        materializations,
        product_classes,
        output_demands,
    })
}

#[cfg(test)]
pub(super) fn lower_macro_materialization_groups(
    groups: Vec<PendingMacroMaterializationGroup>,
) -> Result<Vec<MacroMaterialization>, RetentionError> {
    lower_macro_materialization_groups_with_demands(groups).map(|lowered| lowered.materializations)
}

pub(super) fn validate_macro_product_constraints(
    source: &SourceInventory,
    graph: &DependencyGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    singleton_definition_units: &[Option<SourceUnitId>],
    producer_classification: &MacroProducerClassification<'_>,
    macro_rule_selections: &[MacroRuleSelectionRequirement],
    producer_coverage: &MacroProducerCoverageInventory,
) -> Result<ValidatedMacroProducts, RetentionError> {
    let selected_rules = macro_rule_selections
        .iter()
        .map(|selection| (selection.expansion, selection.rule))
        .collect::<BTreeMap<_, _>>();
    let mut pending_materializations = Vec::new();
    let mut owner_effect_producers = BTreeSet::new();
    let mut classified_products = BTreeSet::new();
    let mut delegated_macro_expansions = BTreeSet::new();
    for coverage in producer_coverage.producers() {
        let producer_id = coverage.producer();
        if !producer_classification.refined.contains(&producer_id) {
            return Err(RetentionError::InvalidConstraint);
        }
        let producer = graph
            .expansions
            .get(producer_id.0 as usize)
            .filter(|producer| producer.id == producer_id)
            .ok_or(RetentionError::InvalidConstraint)?;
        if coverage.materialization_groups().iter().any(|group| {
            group.output_slices().is_empty()
                || group
                    .output_slices()
                    .iter()
                    .any(|slice| slice.output_ranges().is_empty())
                || group.output_slices().windows(2).any(|pair| {
                    pair[0].output_ranges()[0].start() >= pair[1].output_ranges()[0].start()
                })
        }) || coverage.materialization_groups().windows(2).any(|pair| {
            let first = pair[0]
                .output_slices()
                .iter()
                .flat_map(|slice| slice.output_ranges())
                .map(|range| range.start())
                .min();
            let second = pair[1]
                .output_slices()
                .iter()
                .flat_map(|slice| slice.output_ranges())
                .map(|range| range.start())
                .min();
            first >= second
        }) {
            return Err(RetentionError::InvalidConstraint);
        }

        let coverage_products = coverage
            .materialization_groups()
            .iter()
            .flat_map(|group| group.output_slices())
            .filter_map(|slice| slice.products())
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();

        let mut census = coverage.discarded_outputs().to_vec();
        if !census.is_empty() {
            validate_discarded_output_ranges(&census, coverage.output_token_count())?;
        }
        for group in coverage.materialization_groups() {
            let mut pending = PendingMacroMaterializationGroup {
                producer: producer_id,
                products: BTreeSet::new(),
                product_classes: Vec::new(),
                owner_requirements: BTreeSet::new(),
                contributor_roots: group.contributor_roots().to_vec().into_boxed_slice(),
                identity_cohort_root: group.identity_cohort_root(),
                output_demands: group
                    .output_demands()
                    .iter()
                    .map(|demand| MacroGroupDemand {
                        carriers: demand.carriers().into(),
                        dependent_expansions: demand.dependent_expansions().into(),
                        required_expansions: demand.required_expansions().into(),
                    })
                    .collect(),
            };
            for demand in &pending.output_demands {
                let uses_source_owner = producer
                    .source_owner
                    .is_some_and(|owner| demand.carriers.binary_search(&owner).is_ok());
                if (uses_source_owner && demand.carriers.len() != 1)
                    || demand.carriers.iter().any(|carrier| {
                        Some(*carrier) != producer.source_owner
                            && !coverage_products.contains(&GraphNode::Definition(*carrier))
                    })
                {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
            for slice in group.output_slices() {
                validate_macro_output_ranges(slice.output_ranges(), coverage.output_token_count())?;
                census.extend(slice.output_ranges().iter().copied());
                if let Some(products) = slice.products() {
                    if products.is_empty() || products.windows(2).any(|pair| pair[0] >= pair[1]) {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    validate_macro_definition_product_class(
                        graph,
                        macro_producers,
                        producer_id,
                        products,
                    )?;
                    pending
                        .product_classes
                        .push(products.to_vec().into_boxed_slice());
                    for &product in products {
                        if !macro_product_matches_producer(
                            graph,
                            macro_producers,
                            singleton_definition_units,
                            producer_id,
                            product,
                        )? || !classified_products.insert(product)
                            || !pending.products.insert(product)
                        {
                            return Err(RetentionError::InvalidConstraint);
                        }
                        if let GraphNode::Expansion(expansion) = product
                            && producer_classification.delegates_expansion_use(expansion)
                        {
                            delegated_macro_expansions.insert(expansion);
                        }
                    }
                } else if let Some((owner, members, effect)) = slice.owner_effect() {
                    let Some(source_owner) = producer.source_owner else {
                        return Err(RetentionError::IncompleteMacroProductConstraints);
                    };
                    let definition_members = validate_macro_owner_effect_members(
                        graph,
                        macro_producers,
                        producer_id,
                        owner,
                        members,
                    )?;
                    for &member in members {
                        if !macro_product_matches_producer(
                            graph,
                            macro_producers,
                            singleton_definition_units,
                            producer_id,
                            member,
                        )? || !classified_products.insert(member)
                        {
                            return Err(RetentionError::InvalidConstraint);
                        }
                    }
                    if graph
                        .definitions
                        .definitions
                        .get(owner.0 as usize)
                        .is_none_or(|definition| definition.id != owner)
                        || source_owner != owner
                        || !owner_effect_producers.insert(producer_id)
                    {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    if let MacroOwnerEffect::TransparentShell { dependent_products } = effect
                        && (!definition_members.is_empty()
                            || dependent_products.is_empty()
                            || dependent_products.windows(2).any(|pair| pair[0] >= pair[1])
                            || dependent_products
                                .iter()
                                .any(|product| !coverage_products.contains(product)))
                    {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    if !pending.owner_requirements.insert(MacroOwnerRequirement {
                        owner,
                        members: definition_members,
                        effect: effect.clone(),
                    }) {
                        return Err(RetentionError::InvalidConstraint);
                    }
                } else {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
            pending_materializations.push(pending);
        }
        validate_macro_output_census(coverage.output_token_count(), census)?;
        if coverage.output_token_count() == 0
            && (!coverage.discarded_outputs().is_empty()
                || !coverage.materialization_groups().is_empty())
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }

    let expected_products = expected_macro_products(
        graph,
        macro_producers,
        singleton_definition_units,
        producer_classification.refined,
    )?;
    if classified_products != expected_products {
        return Err(RetentionError::IncompleteMacroProductConstraints);
    }
    let lowered = lower_macro_materialization_groups_with_demands(pending_materializations)?;
    let materializations = lowered.materializations;
    let product_groups = macro_product_groups(&materializations)?;
    let output_meaning = MacroOutputMeaningIndex::new(
        &materializations,
        &product_groups,
        producer_classification.refined,
        producer_classification.complete_output_meaning,
    )?;
    let macro_products = ValidatedMacroProducts::new_with_dag_and_output_meaning(
        producer_coverage.shared_contributor_dag(),
        source.units.len(),
        materializations,
        delegated_macro_expansions,
        product_groups,
        output_meaning,
        MacroGroupFacts {
            product_classes: MacroProductClassFacts {
                groups: lowered.product_classes,
                require_complete: true,
            },
            output_demands: MacroOutputDemandFacts {
                groups: lowered.output_demands,
                require_complete: true,
            },
        },
    )?;
    validate_macro_contributor_provenance(
        source,
        graph,
        producer_classification.refined,
        &selected_rules,
        &macro_products,
    )?;

    Ok(macro_products)
}

pub(super) fn validate_macro_definition_product_class(
    graph: &DependencyGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    producer: ExpansionId,
    products: &[GraphNode],
) -> Result<(), RetentionError> {
    let mut roots = BTreeSet::new();
    for &product in products {
        let GraphNode::Definition(definition) = product else {
            continue;
        };
        let definition = graph
            .definitions
            .definitions
            .get(definition.0 as usize)
            .filter(|candidate| candidate.id == definition)
            .ok_or(RetentionError::InvalidConstraint)?;
        if macro_definition_product_role(definition) == Some(MacroDefinitionProductRole::Root) {
            roots.insert(definition.id);
        }
    }
    for &product in products {
        let GraphNode::Definition(definition) = product else {
            continue;
        };
        let definition = graph
            .definitions
            .definitions
            .get(definition.0 as usize)
            .filter(|candidate| candidate.id == definition)
            .ok_or(RetentionError::InvalidConstraint)?;
        match macro_definition_product_role(definition).ok_or(RetentionError::InvalidConstraint)? {
            MacroDefinitionProductRole::Root => {}
            MacroDefinitionProductRole::Subordinate => {
                let MacroDefinitionParent::Root(root) =
                    macro_producers.parent(producer, definition.id)?
                else {
                    return Err(RetentionError::InvalidConstraint);
                };
                if !roots.contains(&root) {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
        }
    }
    Ok(())
}

pub(super) fn validate_macro_owner_effect_members(
    graph: &DependencyGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    producer: ExpansionId,
    owner: DefinitionId,
    members: &[GraphNode],
) -> Result<Vec<DefinitionId>, RetentionError> {
    if members.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(RetentionError::InvalidConstraint);
    }
    let mut definitions = Vec::with_capacity(members.len());
    for &member in members {
        let GraphNode::Definition(definition) = member else {
            return Err(RetentionError::InvalidConstraint);
        };
        let definition = graph
            .definitions
            .definitions
            .get(definition.0 as usize)
            .filter(|candidate| candidate.id == definition)
            .ok_or(RetentionError::InvalidConstraint)?;
        if macro_definition_product_role(definition)
            != Some(MacroDefinitionProductRole::Subordinate)
            || macro_producers.parent(producer, definition.id)?
                != MacroDefinitionParent::Owner(owner)
        {
            return Err(RetentionError::InvalidConstraint);
        }
        definitions.push(definition.id);
    }
    Ok(definitions)
}

fn validate_macro_output_ranges(
    ranges: &[MacroOutputRange],
    output_token_count: u32,
) -> Result<(), RetentionError> {
    if ranges.is_empty()
        || ranges
            .iter()
            .any(|range| range.start() >= range.end() || range.end() > output_token_count)
        || ranges
            .windows(2)
            .any(|pair| pair[0].end() >= pair[1].start())
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(())
}

fn validate_discarded_output_ranges(
    ranges: &[MacroOutputRange],
    output_token_count: u32,
) -> Result<(), RetentionError> {
    if ranges.is_empty()
        || ranges
            .iter()
            .any(|range| range.start() >= range.end() || range.end() > output_token_count)
        || ranges
            .windows(2)
            .any(|pair| pair[0].end() > pair[1].start())
    {
        return Err(RetentionError::InvalidConstraint);
    }
    Ok(())
}

fn validate_macro_output_census(
    output_token_count: u32,
    mut ranges: Vec<MacroOutputRange>,
) -> Result<(), RetentionError> {
    ranges.sort();
    let mut cursor = 0;
    for range in ranges {
        if range.start() < cursor {
            return Err(RetentionError::InvalidConstraint);
        }
        if range.start() > cursor {
            return Err(RetentionError::IncompleteMacroProductConstraints);
        }
        cursor = range.end();
    }
    if cursor != output_token_count {
        return Err(RetentionError::IncompleteMacroProductConstraints);
    }
    Ok(())
}

fn expected_macro_products(
    graph: &DependencyGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    singleton_definition_units: &[Option<SourceUnitId>],
    refined_macro_producers: &BTreeSet<ExpansionId>,
) -> Result<BTreeSet<GraphNode>, RetentionError> {
    let mut expected = BTreeSet::new();
    for definition in &graph.definitions.definitions {
        if singleton_definition_units
            .get(definition.id.0 as usize)
            .copied()
            .flatten()
            .is_none()
        {
            let producer = macro_producers.producer(definition.id)?;
            if !refined_macro_producers.contains(&producer) {
                return Err(RetentionError::IncompleteMacroProductConstraints);
            }
            expected.insert(GraphNode::Definition(definition.id));
        }
    }
    for expansion in &graph.expansions {
        if !matches!(expansion.kind, ExpansionKind::Macro { .. }) {
            continue;
        }
        let Some(parent) = immediate_macro_parent(graph, expansion)? else {
            continue;
        };
        if refined_macro_producers.contains(&parent) {
            expected.insert(GraphNode::Expansion(expansion.id));
        }
    }
    Ok(expected)
}

/// Lookup-only view of the source contributors attached to one selected rule
/// or matcher invocation. `validate_source` has already established the full
/// declarative-macro source census before this index is built.
pub(super) struct MacroSourceContributorIndex {
    templates: BTreeMap<SourceUnitId, Vec<SourceUnitId>>,
    repetitions: BTreeMap<(SourceUnitId, SourceUnitId), Vec<SourceUnitId>>,
}

impl MacroSourceContributorIndex {
    pub(super) fn new(source: &SourceInventory) -> Result<Self, RetentionError> {
        let declarative_unit_kinds = source
            .declarative_unit_kinds()
            .map_err(|_| RetentionError::InvalidConstraint)?;
        let mut templates = BTreeMap::<SourceUnitId, BTreeSet<SourceUnitId>>::new();
        let mut seen_templates = BTreeSet::new();
        for template in &source.macro_templates {
            let valid_template = source
                .units
                .get(template.unit.0 as usize)
                .is_some_and(|unit| {
                    unit.id == template.unit
                        && unit.cfg_state == CfgState::Active
                        && match unit.kind {
                            WrittenUnitKind::NestedItem => {
                                declarative_unit_kinds[template.unit.0 as usize]
                                    == Some(DeclarativeSourceUnitKind::TemplateComponent)
                            }
                            WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf => {
                                declarative_unit_kinds[template.unit.0 as usize].is_none()
                            }
                            _ => false,
                        }
                });
            let valid_rule = source
                .units
                .get(template.rule.0 as usize)
                .is_some_and(|unit| {
                    unit.id == template.rule
                        && unit.cfg_state == CfgState::Active
                        && unit.kind == WrittenUnitKind::MacroRule
                });
            if !valid_template
                || !valid_rule
                || !seen_templates.insert(template.unit)
                || !templates
                    .entry(template.rule)
                    .or_default()
                    .insert(template.unit)
            {
                return Err(RetentionError::InvalidConstraint);
            }
        }

        let mut repetitions =
            BTreeMap::<(SourceUnitId, SourceUnitId), BTreeSet<SourceUnitId>>::new();
        let mut seen_elements = BTreeSet::new();
        for repetition in &source.macro_repetitions {
            let valid_invocation = source
                .units
                .get(repetition.invocation.0 as usize)
                .is_some_and(|unit| {
                    unit.id == repetition.invocation
                        && unit.cfg_state == CfgState::Active
                        && unit.kind == WrittenUnitKind::MacroInvocation
                });
            let valid_rule = source
                .units
                .get(repetition.rule.0 as usize)
                .is_some_and(|unit| {
                    unit.id == repetition.rule
                        && unit.cfg_state == CfgState::Active
                        && unit.kind == WrittenUnitKind::MacroRule
                });
            if !valid_invocation || !valid_rule {
                return Err(RetentionError::InvalidConstraint);
            }
            let elements = repetitions
                .entry((repetition.invocation, repetition.rule))
                .or_default();
            for element in &repetition.elements {
                let valid_element = source
                    .units
                    .get(element.unit.0 as usize)
                    .is_some_and(|unit| {
                        unit.id == element.unit
                            && unit.cfg_state == CfgState::Active
                            && unit.kind == WrittenUnitKind::NestedItem
                            && declarative_unit_kinds[element.unit.0 as usize]
                                == Some(DeclarativeSourceUnitKind::MatcherElement)
                            && unit.parent == Some(repetition.parent)
                    });
                if !valid_element
                    || !seen_elements.insert(element.unit)
                    || !elements.insert(element.unit)
                {
                    return Err(RetentionError::InvalidConstraint);
                }
            }
        }

        Ok(Self {
            templates: templates
                .into_iter()
                .map(|(rule, units)| (rule, units.into_iter().collect()))
                .collect(),
            repetitions: repetitions
                .into_iter()
                .map(|(key, units)| (key, units.into_iter().collect()))
                .collect(),
        })
    }

    pub(super) fn templates(&self, rule: SourceUnitId) -> &[SourceUnitId] {
        self.templates.get(&rule).map_or(&[], Vec::as_slice)
    }

    pub(super) fn repetition_elements(
        &self,
        invocation: SourceUnitId,
        rule: SourceUnitId,
    ) -> &[SourceUnitId] {
        self.repetitions
            .get(&(invocation, rule))
            .map_or(&[], Vec::as_slice)
    }
}

pub(super) struct MacroContributorProvenanceNode {
    pub(super) local: BTreeSet<SourceUnitId>,
    pub(super) parent: Option<ExpansionId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MacroContributorProvenanceRange {
    start: usize,
    end: usize,
}

pub(super) struct MacroContributorProvenanceIndex {
    producer_ranges: BTreeMap<ExpansionId, MacroContributorProvenanceRange>,
    contributor_ranges: BTreeMap<SourceUnitId, Vec<MacroContributorProvenanceRange>>,
}

impl MacroContributorProvenanceIndex {
    pub(super) fn allows(&self, producer: ExpansionId, contributor: SourceUnitId) -> Option<bool> {
        let position = self.producer_ranges.get(&producer)?.start;
        let Some(ranges) = self.contributor_ranges.get(&contributor) else {
            return Some(false);
        };
        let insertion = ranges.partition_point(|range| range.start <= position);
        Some(insertion != 0 && position < ranges[insertion - 1].end)
    }

    #[cfg(test)]
    pub(super) fn stored_range_count(&self) -> usize {
        self.contributor_ranges.values().map(Vec::len).sum()
    }

    #[cfg(test)]
    pub(super) fn producer_range_count(&self) -> usize {
        self.producer_ranges.len()
    }
}

#[derive(Default)]
pub(super) struct MacroContributorValidationStats {
    #[cfg(test)]
    pub(super) producer_visits: usize,
    #[cfg(test)]
    pub(super) materialization_visits: usize,
    #[cfg(test)]
    pub(super) dag_node_visits: usize,
}

impl MacroContributorValidationStats {
    fn visit_producer(&mut self) {
        #[cfg(test)]
        {
            self.producer_visits += 1;
        }
    }

    fn visit_materialization(&mut self) {
        #[cfg(test)]
        {
            self.materialization_visits += 1;
        }
    }

    fn visit_dag_node(&mut self) {
        #[cfg(test)]
        {
            self.dag_node_visits += 1;
        }
    }
}

fn validate_macro_contributor_provenance(
    source: &SourceInventory,
    graph: &DependencyGraph,
    refined_macro_producers: &BTreeSet<ExpansionId>,
    selected_rules: &BTreeMap<ExpansionId, SourceUnitId>,
    macro_products: &ValidatedMacroProducts,
) -> Result<(), RetentionError> {
    validate_macro_contributor_provenance_with_stats(
        source,
        graph,
        refined_macro_producers,
        selected_rules,
        macro_products,
    )
    .map(|_| ())
}

pub(super) fn validate_macro_contributor_provenance_with_stats(
    source: &SourceInventory,
    graph: &DependencyGraph,
    refined_macro_producers: &BTreeSet<ExpansionId>,
    selected_rules: &BTreeMap<ExpansionId, SourceUnitId>,
    macro_products: &ValidatedMacroProducts,
) -> Result<MacroContributorValidationStats, RetentionError> {
    let mut stats = MacroContributorValidationStats::default();
    let source_contributors = MacroSourceContributorIndex::new(source)?;
    struct ProducerBoundary {
        parent: Option<ExpansionId>,
        inherited_roots: Box<[MacroContributorSetId]>,
        selected_rule: SourceUnitId,
        written_invocation: Option<SourceUnitId>,
    }

    let mut boundaries = BTreeMap::new();
    let mut provenance_nodes = BTreeMap::new();
    for producer in macro_products.producer_groups.keys().copied() {
        stats.visit_producer();
        let expansion = graph
            .expansions
            .get(producer.0 as usize)
            .filter(|expansion| expansion.id == producer)
            .ok_or(RetentionError::InvalidConstraint)?;
        let selected_rule = selected_rules
            .get(&producer)
            .copied()
            .ok_or(RetentionError::InvalidConstraint)?;
        let mut local = BTreeSet::from([selected_rule]);
        local.extend(source_contributors.templates(selected_rule).iter().copied());
        if let Some(invocation) = expansion.written_invocation {
            local.insert(invocation);
            local.extend(
                source_contributors
                    .repetition_elements(invocation, selected_rule)
                    .iter()
                    .copied(),
            );
        }
        let parent =
            macro_contributor_provenance_parent(graph, expansion, refined_macro_producers)?;
        let inherited_roots = parent
            .map(|parent| {
                if parent == producer || !macro_products.producer_groups.contains_key(&parent) {
                    return Err(RetentionError::IncompleteMacroProductConstraints);
                }
                macro_products
                    .product_groups
                    .get(&GraphNode::Expansion(producer))
                    .and_then(|&group| macro_products.materializations.get(group))
                    .filter(|materialization| materialization.producer == parent)
                    .map(|materialization| materialization.contributor_roots.clone())
                    .ok_or(RetentionError::IncompleteMacroProductConstraints)
            })
            .transpose()?
            .unwrap_or_default();
        if boundaries
            .insert(
                producer,
                ProducerBoundary {
                    parent,
                    inherited_roots,
                    selected_rule,
                    written_invocation: expansion.written_invocation,
                },
            )
            .is_some()
        {
            return Err(RetentionError::InvalidConstraint);
        }
        if provenance_nodes
            .insert(producer, MacroContributorProvenanceNode { local, parent })
            .is_some()
        {
            return Err(RetentionError::InvalidConstraint);
        }
    }
    let provenance = resolve_macro_contributor_provenance(&provenance_nodes)?;

    for (&producer, boundary) in &boundaries {
        let mut inherited = HashSet::with_capacity(boundary.inherited_roots.len());
        for root in &boundary.inherited_roots {
            let node = macro_products
                .contributor_index
                .node_indices
                .get(root)
                .copied()
                .ok_or(RetentionError::InvalidConstraint)?;
            inherited.insert(node);
        }
        let required = if boundary.written_invocation.is_some() {
            3
        } else {
            1
        };
        let inherited_summary = boundary.parent.map_or(0, |parent| {
            let mut summary = 0;
            if provenance.allows(parent, boundary.selected_rule) == Some(true) {
                summary |= 1;
            }
            if boundary
                .written_invocation
                .is_some_and(|unit| provenance.allows(parent, unit) == Some(true))
            {
                summary |= 2;
            }
            summary
        });
        let mut summaries = HashMap::<usize, u8>::new();
        let groups = macro_products
            .producer_groups
            .get(&producer)
            .ok_or(RetentionError::InvalidConstraint)?;
        for &group in groups {
            stats.visit_materialization();
            let materialization = &macro_products.materializations[group];
            let mut group_summary = 0;
            for root in &materialization.contributor_roots {
                let root = macro_products.contributor_index.node_indices[root];
                let mut pending = vec![(root, false)];
                while let Some((node, exiting)) = pending.pop() {
                    if summaries.contains_key(&node) {
                        continue;
                    }
                    if inherited.contains(&node) {
                        stats.visit_dag_node();
                        summaries.insert(node, inherited_summary);
                        continue;
                    }
                    if !exiting {
                        pending.push((node, true));
                        pending.extend(
                            macro_products.contributor_index.parents[node]
                                .iter()
                                .rev()
                                .copied()
                                .filter(|parent| !summaries.contains_key(parent))
                                .map(|parent| (parent, false)),
                        );
                        continue;
                    }
                    let mut summary = 0;
                    for &unit in macro_products.contributor_index.local_sources[node].iter() {
                        let valid_unit = source.units.get(unit.0 as usize).is_some_and(|record| {
                            record.id == unit && record.cfg_state == CfgState::Active
                        });
                        if !valid_unit || provenance.allows(producer, unit) != Some(true) {
                            return Err(RetentionError::InvalidConstraint);
                        }
                        if unit == boundary.selected_rule {
                            summary |= 1;
                        }
                        if Some(unit) == boundary.written_invocation {
                            summary |= 2;
                        }
                    }
                    for &parent in &macro_products.contributor_index.parents[node] {
                        summary |= *summaries
                            .get(&parent)
                            .ok_or(RetentionError::InvalidConstraint)?;
                    }
                    stats.visit_dag_node();
                    summaries.insert(node, summary);
                }
                group_summary |= *summaries
                    .get(&root)
                    .ok_or(RetentionError::InvalidConstraint)?;
            }
            if group_summary & required != required {
                return Err(RetentionError::InvalidConstraint);
            }
        }
    }
    Ok(stats)
}

/// The editable source anchor and the producer-provenance root are separate
/// facts. A child discovered through a refined producer inherits that
/// producer even when rustc can also map the child to an indivisible written
/// anchor. The anchor is a root only when no refined local producer owns the
/// child occurrence.
pub(super) fn macro_contributor_provenance_parent(
    graph: &DependencyGraph,
    expansion: &ExpansionNode,
    refined_macro_producers: &BTreeSet<ExpansionId>,
) -> Result<Option<ExpansionId>, RetentionError> {
    let generation_parent =
        declarative_generation_parent(expansion.discovered_in, expansion.source_call_parent);
    let parent_state = generation_parent
        .map(|parent| {
            let candidate = graph
                .expansions
                .get(parent.0 as usize)
                .filter(|candidate| candidate.id == parent)
                .ok_or(RetentionError::InvalidGraph)?;
            if candidate.id == expansion.id {
                return Err(RetentionError::InvalidGraph);
            }
            if !matches!(candidate.kind, ExpansionKind::Macro { .. }) {
                return Ok(DeclarativeGenerationParentState::Opaque);
            }
            Ok(
                match (candidate.implementation, candidate.macro_definition) {
                    (
                        Some(MacroImplementationKind::Declarative),
                        Some(DefinitionTarget::External(_)),
                    ) => DeclarativeGenerationParentState::Opaque,
                    (
                        Some(MacroImplementationKind::Declarative),
                        Some(DefinitionTarget::Local(_)),
                    ) if refined_macro_producers.contains(&parent) => {
                        DeclarativeGenerationParentState::RefinedLocal {
                            link_complete: true,
                        }
                    }
                    (Some(MacroImplementationKind::Declarative), _) | (None, _) => {
                        DeclarativeGenerationParentState::LocalIncomplete
                    }
                    (Some(_), _) => DeclarativeGenerationParentState::Opaque,
                },
            )
        })
        .transpose()?;
    match resolve_declarative_contributor_parent(
        generation_parent,
        expansion.written_invocation.is_some(),
        parent_state,
    ) {
        DeclarativeContributorParent::Root => Ok(None),
        DeclarativeContributorParent::Parent(parent) => Ok(Some(parent)),
        DeclarativeContributorParent::Incomplete => {
            Err(RetentionError::IncompleteMacroProductConstraints)
        }
    }
}

pub(super) fn resolve_macro_contributor_provenance(
    nodes: &BTreeMap<ExpansionId, MacroContributorProvenanceNode>,
) -> Result<MacroContributorProvenanceIndex, RetentionError> {
    let mut states = BTreeMap::<ExpansionId, u8>::new();
    for &start in nodes.keys() {
        if states.get(&start) == Some(&2) {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        loop {
            match states.get(&current).copied().unwrap_or(0) {
                2 => break,
                1 => return Err(RetentionError::InvalidGraph),
                0 => {}
                _ => unreachable!("macro provenance traversal state is internal"),
            }
            let node = nodes
                .get(&current)
                .ok_or(RetentionError::IncompleteMacroProductConstraints)?;
            states.insert(current, 1);
            path.push(current);
            let Some(parent) = node.parent else {
                break;
            };
            current = parent;
        }

        for producer in path.into_iter().rev() {
            states.insert(producer, 2);
        }
    }

    let mut children = nodes
        .keys()
        .copied()
        .map(|producer| (producer, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    let mut roots = Vec::new();
    for (&producer, node) in nodes {
        if let Some(parent) = node.parent {
            children
                .get_mut(&parent)
                .ok_or(RetentionError::IncompleteMacroProductConstraints)?
                .push(producer);
        } else {
            roots.push(producer);
        }
    }

    let mut producer_ranges = BTreeMap::new();
    let mut preorder = Vec::with_capacity(nodes.len());
    let mut stack = roots
        .iter()
        .rev()
        .copied()
        .map(|producer| (producer, true))
        .collect::<Vec<_>>();
    while let Some((producer, entering)) = stack.pop() {
        if entering {
            let start = preorder.len();
            if producer_ranges
                .insert(
                    producer,
                    MacroContributorProvenanceRange { start, end: start },
                )
                .is_some()
            {
                return Err(RetentionError::InvalidGraph);
            }
            preorder.push(producer);
            stack.push((producer, false));
            for child in children
                .get(&producer)
                .ok_or(RetentionError::InvalidGraph)?
                .iter()
                .rev()
            {
                stack.push((*child, true));
            }
        } else {
            producer_ranges
                .get_mut(&producer)
                .ok_or(RetentionError::InvalidGraph)?
                .end = preorder.len();
        }
    }
    if preorder.len() != nodes.len() {
        return Err(RetentionError::InvalidGraph);
    }

    let mut contributor_ranges =
        BTreeMap::<SourceUnitId, Vec<MacroContributorProvenanceRange>>::new();
    for producer in preorder {
        let node = nodes.get(&producer).ok_or(RetentionError::InvalidGraph)?;
        let range = *producer_ranges
            .get(&producer)
            .ok_or(RetentionError::InvalidGraph)?;
        for contributor in node.local.iter().copied() {
            let ranges = contributor_ranges.entry(contributor).or_default();
            if let Some(previous) = ranges.last_mut()
                && previous.end >= range.start
            {
                previous.end = previous.end.max(range.end);
            } else {
                ranges.push(range);
            }
        }
    }

    Ok(MacroContributorProvenanceIndex {
        producer_ranges,
        contributor_ranges,
    })
}

fn macro_product_matches_producer(
    graph: &DependencyGraph,
    macro_producers: &DefinitionMacroProducerIndex,
    singleton_definition_units: &[Option<SourceUnitId>],
    producer: ExpansionId,
    product: GraphNode,
) -> Result<bool, RetentionError> {
    match product {
        GraphNode::Definition(definition) => {
            if singleton_definition_units
                .get(definition.0 as usize)
                .is_none_or(Option::is_some)
            {
                return Ok(false);
            }
            Ok(macro_producers.producer(definition)? == producer)
        }
        GraphNode::Expansion(expansion) => {
            let Some(expansion) = graph
                .expansions
                .get(expansion.0 as usize)
                .filter(|candidate| candidate.id == expansion)
            else {
                return Ok(false);
            };
            let parent = immediate_macro_parent(graph, expansion)?;
            Ok(matches!(expansion.kind, ExpansionKind::Macro { .. }) && parent == Some(producer))
        }
        GraphNode::ExternalDefinition(_) | GraphNode::Proof(_) | GraphNode::Mono(_) => Ok(false),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MacroDefinitionParent {
    Root(DefinitionId),
    Owner(DefinitionId),
}

/// Resolves the declarative-macro producer for every definition once.
///
/// Building the index records malformed facts instead of rejecting them so
/// definitions outside the refined-macro domain do not acquire a new
/// validation requirement. A queried malformed definition still fails closed.
pub(super) struct DefinitionMacroProducerIndex {
    producers: Vec<Result<ExpansionId, RetentionError>>,
    parents: Vec<Result<IndexedMacroDefinitionParent, RetentionError>>,
}

#[derive(Clone, Copy)]
struct IndexedMacroDefinitionParent {
    producer: ExpansionId,
    parent: MacroDefinitionParent,
}

impl DefinitionMacroProducerIndex {
    pub(super) fn new(graph: &DependencyGraph) -> Self {
        let definitions = &graph.definitions.definitions;
        let mut direct = vec![BTreeSet::new(); definitions.len()];
        for edge in &graph.edges {
            if edge.kind != DependencyKind::GeneratedBy {
                continue;
            }
            let GraphNode::Definition(definition) = edge.from else {
                continue;
            };
            if let Some(products) = direct.get_mut(definition.0 as usize) {
                products.insert(edge.to);
            }
        }

        // 0 is unresolved, 1 is on the current parent chain, and 2 is
        // resolved. Each compiler-generated parent link is therefore visited
        // at most once, including when many descendants share a suffix.
        let mut states = vec![0_u8; definitions.len()];
        let mut producers = vec![Err(RetentionError::InvalidGraph); definitions.len()];
        for start in 0..definitions.len() {
            if states[start] == 2 {
                continue;
            }
            let mut path = Vec::new();
            let mut current = start;
            let resolved = loop {
                match states.get(current).copied() {
                    Some(2) => break producers[current],
                    Some(1) => break Err(RetentionError::InvalidGraph),
                    Some(0) => {}
                    _ => break Err(RetentionError::IncompleteMacroProductConstraints),
                }
                states[current] = 1;
                path.push(current);

                let definition = &definitions[current];
                if definition.id.0 as usize != current {
                    break Err(RetentionError::InvalidGraph);
                }
                match definition.origin {
                    DefinitionOrigin::Expanded { .. } => {
                        let products = &direct[current];
                        break if products.len() == 1 {
                            match products.first().copied() {
                                Some(GraphNode::Expansion(producer)) => Ok(producer),
                                _ => Err(RetentionError::IncompleteMacroProductConstraints),
                            }
                        } else {
                            Err(RetentionError::IncompleteMacroProductConstraints)
                        };
                    }
                    DefinitionOrigin::CompilerGenerated { .. }
                    | DefinitionOrigin::Injected { .. } => {
                        let Some(parent) = definition.parent else {
                            break Err(RetentionError::IncompleteMacroProductConstraints);
                        };
                        let parent_index = parent.0 as usize;
                        if definitions
                            .get(parent_index)
                            .is_none_or(|definition| definition.id != parent)
                        {
                            break Err(RetentionError::IncompleteMacroProductConstraints);
                        }
                        current = parent_index;
                    }
                    DefinitionOrigin::Written { .. } => {
                        break Err(RetentionError::IncompleteMacroProductConstraints);
                    }
                }
            };
            for index in path.into_iter().rev() {
                states[index] = 2;
                producers[index] = resolved;
            }
        }
        let mut parent_states = vec![0_u8; definitions.len()];
        let mut parents: Vec<Result<IndexedMacroDefinitionParent, RetentionError>> =
            vec![Err(RetentionError::InvalidConstraint); definitions.len()];
        for start in 0..definitions.len() {
            if parent_states[start] == 2 {
                continue;
            }
            let Some(MacroDefinitionProductRole::Subordinate) =
                macro_definition_product_role(&definitions[start])
            else {
                parent_states[start] = 2;
                continue;
            };
            let producer = match producers[start] {
                Ok(producer) => producer,
                Err(error) => {
                    parent_states[start] = 2;
                    parents[start] = Err(error);
                    continue;
                }
            };

            let mut path = Vec::new();
            let mut current = start;
            let resolved = loop {
                if producers.get(current).copied() != Some(Ok(producer)) {
                    break Err(RetentionError::InvalidConstraint);
                }
                match parent_states.get(current).copied() {
                    Some(2) => {
                        break parents[current].and_then(|parent| {
                            (parent.producer == producer)
                                .then_some(parent)
                                .ok_or(RetentionError::InvalidConstraint)
                        });
                    }
                    Some(1) => break Err(RetentionError::InvalidConstraint),
                    Some(0) => {}
                    _ => break Err(RetentionError::InvalidConstraint),
                }
                parent_states[current] = 1;
                path.push(current);

                let definition = &definitions[current];
                if macro_definition_product_role(definition)
                    != Some(MacroDefinitionProductRole::Subordinate)
                {
                    break Err(RetentionError::InvalidConstraint);
                }
                let Some(parent) = definition.parent else {
                    break Err(RetentionError::InvalidConstraint);
                };
                let parent_index = parent.0 as usize;
                let Some(parent_definition) = definitions
                    .get(parent_index)
                    .filter(|definition| definition.id == parent)
                else {
                    break Err(RetentionError::InvalidConstraint);
                };
                match macro_definition_product_role(parent_definition) {
                    None => {
                        break Ok(IndexedMacroDefinitionParent {
                            producer,
                            parent: MacroDefinitionParent::Owner(parent),
                        });
                    }
                    Some(MacroDefinitionProductRole::Root) => {
                        break if producers[parent_index] == Ok(producer) {
                            Ok(IndexedMacroDefinitionParent {
                                producer,
                                parent: MacroDefinitionParent::Root(parent),
                            })
                        } else {
                            Err(RetentionError::InvalidConstraint)
                        };
                    }
                    Some(MacroDefinitionProductRole::Subordinate) => {
                        if producers[parent_index] != Ok(producer) {
                            break Err(RetentionError::InvalidConstraint);
                        }
                        current = parent_index;
                    }
                }
            };
            for index in path.into_iter().rev() {
                parent_states[index] = 2;
                parents[index] = resolved;
            }
        }
        Self { producers, parents }
    }

    pub(super) fn producer(&self, definition: DefinitionId) -> Result<ExpansionId, RetentionError> {
        self.producers
            .get(definition.0 as usize)
            .copied()
            .unwrap_or(Err(RetentionError::IncompleteMacroProductConstraints))
    }

    pub(super) fn parent(
        &self,
        producer: ExpansionId,
        definition: DefinitionId,
    ) -> Result<MacroDefinitionParent, RetentionError> {
        self.parents
            .get(definition.0 as usize)
            .copied()
            .unwrap_or(Err(RetentionError::InvalidConstraint))
            .and_then(|parent| {
                (parent.producer == producer)
                    .then_some(parent.parent)
                    .ok_or(RetentionError::InvalidConstraint)
            })
    }
}

pub(super) fn immediate_macro_parent(
    graph: &DependencyGraph,
    expansion: &ExpansionNode,
) -> Result<Option<ExpansionId>, RetentionError> {
    let Some(parent) =
        declarative_generation_parent(expansion.discovered_in, expansion.source_call_parent)
    else {
        return Ok(None);
    };
    let parent = graph
        .expansions
        .get(parent.0 as usize)
        .filter(|candidate| candidate.id == parent)
        .ok_or(RetentionError::InvalidGraph)?;
    if parent.id == expansion.id {
        return Err(RetentionError::InvalidGraph);
    }
    Ok(matches!(parent.kind, ExpansionKind::Macro { .. }).then_some(parent.id))
}
