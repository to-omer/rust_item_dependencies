use std::collections::{BTreeMap, BTreeSet};

use crate::dependency_graph::{DependencyGraph, GraphNode};
use crate::source::{SourceInventory, SourceUnitId};

use super::external::{CompilerCrateLoadCarrier, CompilerCrateLoadDisjunction};
use super::macro_products::ValidatedMacroProducts;
use super::{
    DefinitionDisjunction, MacroProductRankCache, RetentionError, SourceDisjunction,
    compiler_crate_load_carrier_rank, definition_choice_rank, require_compiler_node,
    retain_source_unit,
};

struct RankedSourceDisjunction {
    trigger: SourceUnitId,
    choices: Vec<SourceUnitId>,
    selected: SourceUnitId,
}

struct RankedCompilerDisjunction {
    trigger: Option<GraphNode>,
    choices: Vec<CompilerCrateLoadCarrier>,
    selected: CompilerCrateLoadCarrier,
}

struct RankedMemberDisjunction {
    choices: Vec<GraphNode>,
    selected: GraphNode,
}

struct MemberDisjunctionLane {
    active: Vec<bool>,
    complete: Vec<bool>,
    pending: BTreeSet<usize>,
}

impl MemberDisjunctionLane {
    fn new(count: usize) -> Self {
        Self {
            active: vec![false; count],
            complete: vec![false; count],
            pending: BTreeSet::new(),
        }
    }
}

pub(super) struct DisjunctionDemandLanes<'state> {
    pub(super) compile: &'state mut BTreeSet<GraphNode>,
    pub(super) actual: &'state mut BTreeSet<GraphNode>,
    pub(super) newly_compile: &'state mut Vec<GraphNode>,
    pub(super) newly_actual: &'state mut Vec<GraphNode>,
}

/// Delta-driven selection state for source, external-carrier, and compiler
/// member disjunctions. External carriers observe compile presence. Member
/// disjunctions independently close over compile presence and actual demand,
/// so code that remains only to make a macro expansion compilable still has a
/// structurally complete implementation. Trigger and choice reverse indexes
/// ensure each fact is revisited only when a relevant false-to-true input
/// arrives.
pub(super) struct DisjunctionClosure {
    source: Vec<RankedSourceDisjunction>,
    compiler: Vec<RankedCompilerDisjunction>,
    members: Vec<RankedMemberDisjunction>,
    source_triggers: Vec<Vec<usize>>,
    source_choices: Vec<Vec<usize>>,
    compiler_triggers: BTreeMap<GraphNode, Vec<usize>>,
    compiler_definition_choices: BTreeMap<GraphNode, Vec<usize>>,
    compiler_source_choices: Vec<Vec<usize>>,
    member_triggers: BTreeMap<GraphNode, Vec<usize>>,
    member_choices: BTreeMap<GraphNode, Vec<usize>>,
    source_active: Vec<bool>,
    compiler_active: Vec<bool>,
    compile_members: MemberDisjunctionLane,
    actual_members: MemberDisjunctionLane,
    source_complete: Vec<bool>,
    compiler_complete: Vec<bool>,
    pending_source: BTreeSet<usize>,
    pending_compiler: BTreeSet<usize>,
    seen_source: Vec<bool>,
    seen_compile: BTreeSet<GraphNode>,
    seen_actual: BTreeSet<GraphNode>,
    initialized: bool,
    #[cfg(test)]
    pub(super) fact_visits: usize,
    #[cfg(test)]
    pub(super) reverse_fact_visits: usize,
}

impl DisjunctionClosure {
    pub(super) fn new(
        source: &SourceInventory,
        graph: &DependencyGraph,
        singleton_definition_units: &[Option<SourceUnitId>],
        macro_products: &ValidatedMacroProducts,
        source_disjunctions: &[SourceDisjunction],
        compiler_disjunctions: &[CompilerCrateLoadDisjunction],
        member_disjunctions: &[DefinitionDisjunction],
    ) -> Result<Self, RetentionError> {
        let mut ranked_source = Vec::with_capacity(source_disjunctions.len());
        let mut source_triggers = vec![Vec::new(); source.units.len()];
        let mut source_choices = vec![Vec::new(); source.units.len()];
        for (index, disjunction) in source_disjunctions.iter().enumerate() {
            let selected = disjunction
                .choices
                .iter()
                .copied()
                .min_by_key(|choice| {
                    let unit = &source.units[choice.0 as usize];
                    (unit.full_range.len(), unit.full_range, unit.id)
                })
                .ok_or(RetentionError::InvalidConstraint)?;
            source_triggers[disjunction.trigger.0 as usize].push(index);
            for &choice in &disjunction.choices {
                source_choices[choice.0 as usize].push(index);
            }
            ranked_source.push(RankedSourceDisjunction {
                trigger: disjunction.trigger,
                choices: disjunction.choices.clone(),
                selected,
            });
        }

        let mut ranked_compiler = Vec::with_capacity(compiler_disjunctions.len());
        let mut macro_rank_cache = MacroProductRankCache::default();
        let mut compiler_triggers = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut compiler_definition_choices = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut compiler_source_choices = vec![Vec::new(); source.units.len()];
        for (index, disjunction) in compiler_disjunctions.iter().enumerate() {
            let mut ranked = disjunction
                .choices
                .iter()
                .copied()
                .map(|choice| {
                    Ok((
                        compiler_crate_load_carrier_rank(
                            source,
                            graph,
                            singleton_definition_units,
                            macro_products,
                            &mut macro_rank_cache,
                            choice,
                        )?,
                        choice,
                    ))
                })
                .collect::<Result<Vec<_>, RetentionError>>()?;
            ranked.sort_by(|left, right| left.0.cmp(&right.0));
            let selected = ranked
                .first()
                .map(|(_, choice)| *choice)
                .ok_or(RetentionError::InvalidConstraint)?;
            if let Some(trigger) = disjunction.trigger {
                compiler_triggers.entry(trigger).or_default().push(index);
            }
            for &choice in &disjunction.choices {
                match choice {
                    CompilerCrateLoadCarrier::Definition(definition) => {
                        compiler_definition_choices
                            .entry(GraphNode::Definition(definition))
                            .or_default()
                            .push(index);
                    }
                    CompilerCrateLoadCarrier::Source(unit) => {
                        compiler_source_choices[unit.0 as usize].push(index);
                    }
                }
            }
            ranked_compiler.push(RankedCompilerDisjunction {
                trigger: disjunction.trigger,
                choices: disjunction.choices.clone(),
                selected,
            });
        }

        let mut ranked_members = Vec::with_capacity(member_disjunctions.len());
        let mut member_triggers = BTreeMap::<GraphNode, Vec<usize>>::new();
        let mut member_choices = BTreeMap::<GraphNode, Vec<usize>>::new();
        for (index, disjunction) in member_disjunctions.iter().enumerate() {
            let trigger = GraphNode::Definition(disjunction.trigger);
            let choices = disjunction
                .choices
                .iter()
                .copied()
                .map(GraphNode::Definition)
                .collect::<Vec<_>>();
            let mut ranked = disjunction
                .choices
                .iter()
                .copied()
                .map(|choice| {
                    Ok((
                        definition_choice_rank(
                            source,
                            graph,
                            singleton_definition_units,
                            macro_products,
                            &mut macro_rank_cache,
                            choice,
                        )?,
                        GraphNode::Definition(choice),
                    ))
                })
                .collect::<Result<Vec<_>, RetentionError>>()?;
            ranked.sort_by(|left, right| left.0.cmp(&right.0));
            let selected = ranked
                .first()
                .map(|(_, choice)| *choice)
                .ok_or(RetentionError::InvalidConstraint)?;
            member_triggers.entry(trigger).or_default().push(index);
            for &choice in &choices {
                member_choices.entry(choice).or_default().push(index);
            }
            ranked_members.push(RankedMemberDisjunction { choices, selected });
        }

        Ok(Self {
            source_active: vec![false; ranked_source.len()],
            compiler_active: ranked_compiler
                .iter()
                .map(|disjunction| disjunction.trigger.is_none())
                .collect(),
            compile_members: MemberDisjunctionLane::new(ranked_members.len()),
            actual_members: MemberDisjunctionLane::new(ranked_members.len()),
            source_complete: vec![false; ranked_source.len()],
            compiler_complete: vec![false; ranked_compiler.len()],
            pending_source: BTreeSet::new(),
            pending_compiler: BTreeSet::new(),
            seen_source: vec![false; source.units.len()],
            seen_compile: BTreeSet::new(),
            seen_actual: BTreeSet::new(),
            initialized: false,
            source: ranked_source,
            compiler: ranked_compiler,
            members: ranked_members,
            source_triggers,
            source_choices,
            compiler_triggers,
            compiler_definition_choices,
            compiler_source_choices,
            member_triggers,
            member_choices,
            #[cfg(test)]
            fact_visits: 0,
            #[cfg(test)]
            reverse_fact_visits: 0,
        })
    }

    pub(super) fn seed(
        &mut self,
        compile_required: &BTreeSet<GraphNode>,
        actual_required: &BTreeSet<GraphNode>,
        retained_units: &BTreeSet<SourceUnitId>,
    ) -> Result<(), RetentionError> {
        if self.initialized {
            return Err(RetentionError::InvalidConstraint);
        }
        self.initialized = true;
        self.pending_compiler.extend(
            self.compiler
                .iter()
                .enumerate()
                .filter_map(|(index, facts)| facts.trigger.is_none().then_some(index)),
        );
        self.add_compile(compile_required.iter().copied());
        self.add_actual(actual_required.iter().copied());
        self.add_source(retained_units.iter().copied())
    }

    pub(super) fn add_compile(&mut self, nodes: impl IntoIterator<Item = GraphNode>) {
        for node in nodes {
            if !self.seen_compile.insert(node) {
                continue;
            }
            self.queue_compile_facts(node);
        }
    }

    pub(super) fn add_actual(&mut self, nodes: impl IntoIterator<Item = GraphNode>) {
        for node in nodes {
            if !self.seen_actual.insert(node) {
                continue;
            }
            self.queue_actual_facts(node);
        }
    }

    pub(super) fn add_source(
        &mut self,
        units: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<(), RetentionError> {
        for unit in units {
            let Some(seen) = self.seen_source.get_mut(unit.0 as usize) else {
                return Err(RetentionError::InvalidConstraint);
            };
            if *seen {
                continue;
            }
            *seen = true;
            for &index in &self.source_triggers[unit.0 as usize] {
                #[cfg(test)]
                {
                    self.reverse_fact_visits += 1;
                }
                self.source_active[index] = true;
                if !self.source_complete[index] {
                    self.pending_source.insert(index);
                }
            }
            for &index in &self.source_choices[unit.0 as usize] {
                #[cfg(test)]
                {
                    self.reverse_fact_visits += 1;
                }
                if !self.source_complete[index] {
                    self.pending_source.insert(index);
                }
            }
            for &index in &self.compiler_source_choices[unit.0 as usize] {
                #[cfg(test)]
                {
                    self.reverse_fact_visits += 1;
                }
                if !self.compiler_complete[index] {
                    self.pending_compiler.insert(index);
                }
            }
        }
        Ok(())
    }

    pub(super) fn select(
        &mut self,
        demand: DisjunctionDemandLanes<'_>,
        retained_units: &mut BTreeSet<SourceUnitId>,
        newly_retained: &mut Vec<SourceUnitId>,
        token_retained_deltas: &mut Vec<SourceUnitId>,
    ) -> Result<bool, RetentionError> {
        let DisjunctionDemandLanes {
            compile,
            actual,
            newly_compile,
            newly_actual,
        } = demand;
        let mut selected =
            self.select_source(retained_units, newly_retained, token_retained_deltas)?;
        selected |= self.select_compiler(
            compile,
            retained_units,
            newly_compile,
            newly_retained,
            token_retained_deltas,
        )?;
        selected |= self.select_members(compile, actual, newly_compile, newly_actual)?;
        Ok(selected)
    }

    fn queue_compile_facts(&mut self, node: GraphNode) {
        if let Some(indices) = self.compiler_triggers.get(&node) {
            for &index in indices {
                #[cfg(test)]
                {
                    self.reverse_fact_visits += 1;
                }
                self.compiler_active[index] = true;
                if !self.compiler_complete[index] {
                    self.pending_compiler.insert(index);
                }
            }
        }
        if let Some(indices) = self.compiler_definition_choices.get(&node) {
            for &index in indices {
                #[cfg(test)]
                {
                    self.reverse_fact_visits += 1;
                }
                if !self.compiler_complete[index] {
                    self.pending_compiler.insert(index);
                }
            }
        }
        queue_member_facts(
            node,
            &self.member_triggers,
            &self.member_choices,
            &mut self.compile_members,
            #[cfg(test)]
            &mut self.reverse_fact_visits,
        );
    }

    fn queue_actual_facts(&mut self, node: GraphNode) {
        queue_member_facts(
            node,
            &self.member_triggers,
            &self.member_choices,
            &mut self.actual_members,
            #[cfg(test)]
            &mut self.reverse_fact_visits,
        );
    }

    fn select_source(
        &mut self,
        retained: &mut BTreeSet<SourceUnitId>,
        newly_retained: &mut Vec<SourceUnitId>,
        token_retained_deltas: &mut Vec<SourceUnitId>,
    ) -> Result<bool, RetentionError> {
        let mut selected_any = false;
        let mut deferred = BTreeSet::new();
        let mut cursor = 0;
        while let Some(index) = self.pending_source.pop_first() {
            if index < cursor {
                deferred.insert(index);
                continue;
            }
            cursor = index + 1;
            #[cfg(test)]
            {
                self.fact_visits += 1;
            }
            if self.source_complete[index] || !self.source_active[index] {
                continue;
            }
            let facts = &self.source[index];
            if retained.contains(&facts.trigger)
                && facts.choices.iter().any(|choice| retained.contains(choice))
            {
                self.source_complete[index] = true;
                continue;
            }
            let selected = facts.selected;
            self.source_complete[index] = true;
            if !retain_source_unit(retained, newly_retained, selected) {
                return Err(RetentionError::InvalidConstraint);
            }
            token_retained_deltas.push(selected);
            self.add_source([selected])?;
            selected_any = true;
        }
        self.pending_source.extend(deferred);
        Ok(selected_any)
    }

    fn select_compiler(
        &mut self,
        compile_required: &mut BTreeSet<GraphNode>,
        retained: &mut BTreeSet<SourceUnitId>,
        newly_required: &mut Vec<GraphNode>,
        newly_retained: &mut Vec<SourceUnitId>,
        token_retained_deltas: &mut Vec<SourceUnitId>,
    ) -> Result<bool, RetentionError> {
        let mut selected_any = false;
        let mut deferred = BTreeSet::new();
        let mut cursor = 0;
        while let Some(index) = self.pending_compiler.pop_first() {
            if index < cursor {
                deferred.insert(index);
                continue;
            }
            cursor = index + 1;
            #[cfg(test)]
            {
                self.fact_visits += 1;
            }
            if self.compiler_complete[index] || !self.compiler_active[index] {
                continue;
            }
            if self.compiler[index]
                .choices
                .iter()
                .any(|choice| carrier_is_retained(*choice, compile_required, retained))
            {
                self.compiler_complete[index] = true;
                continue;
            }
            let selected = self.compiler[index].selected;
            self.compiler_complete[index] = true;
            match selected {
                CompilerCrateLoadCarrier::Definition(definition) => {
                    let node = GraphNode::Definition(definition);
                    if !require_compiler_node(compile_required, newly_required, node) {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    self.add_compile([node]);
                }
                CompilerCrateLoadCarrier::Source(unit) => {
                    if !retain_source_unit(retained, newly_retained, unit) {
                        return Err(RetentionError::InvalidConstraint);
                    }
                    token_retained_deltas.push(unit);
                    self.add_source([unit])?;
                }
            }
            selected_any = true;
        }
        self.pending_compiler.extend(deferred);
        Ok(selected_any)
    }

    fn select_members(
        &mut self,
        compile_required: &mut BTreeSet<GraphNode>,
        actual_required: &mut BTreeSet<GraphNode>,
        newly_compile_required: &mut Vec<GraphNode>,
        newly_actual_required: &mut Vec<GraphNode>,
    ) -> Result<bool, RetentionError> {
        let compile_start = newly_compile_required.len();
        let actual_start = newly_actual_required.len();
        let mut selected_any = select_member_lane(
            &self.members,
            &mut self.compile_members,
            compile_required,
            newly_compile_required,
            #[cfg(test)]
            &mut self.fact_visits,
        )?;
        selected_any |= select_member_lane(
            &self.members,
            &mut self.actual_members,
            actual_required,
            newly_actual_required,
            #[cfg(test)]
            &mut self.fact_visits,
        )?;
        let actual_deltas = newly_actual_required[actual_start..].to_vec();
        for &node in &actual_deltas {
            require_compiler_node(compile_required, newly_compile_required, node);
        }
        self.add_compile(newly_compile_required[compile_start..].to_vec());
        self.add_actual(actual_deltas);
        Ok(selected_any)
    }
}

fn queue_member_facts(
    node: GraphNode,
    triggers: &BTreeMap<GraphNode, Vec<usize>>,
    choices: &BTreeMap<GraphNode, Vec<usize>>,
    lane: &mut MemberDisjunctionLane,
    #[cfg(test)] reverse_fact_visits: &mut usize,
) {
    if let Some(indices) = triggers.get(&node) {
        for &index in indices {
            #[cfg(test)]
            {
                *reverse_fact_visits += 1;
            }
            lane.active[index] = true;
            if !lane.complete[index] {
                lane.pending.insert(index);
            }
        }
    }
    if let Some(indices) = choices.get(&node) {
        for &index in indices {
            #[cfg(test)]
            {
                *reverse_fact_visits += 1;
            }
            if !lane.complete[index] {
                lane.pending.insert(index);
            }
        }
    }
}

fn select_member_lane(
    facts: &[RankedMemberDisjunction],
    lane: &mut MemberDisjunctionLane,
    required: &mut BTreeSet<GraphNode>,
    newly_required: &mut Vec<GraphNode>,
    #[cfg(test)] fact_visits: &mut usize,
) -> Result<bool, RetentionError> {
    let mut selected_any = false;
    let mut deferred = BTreeSet::new();
    let mut cursor = 0;
    while let Some(index) = lane.pending.pop_first() {
        if index < cursor {
            deferred.insert(index);
            continue;
        }
        cursor = index + 1;
        #[cfg(test)]
        {
            *fact_visits += 1;
        }
        if lane.complete[index] || !lane.active[index] {
            continue;
        }
        if facts[index]
            .choices
            .iter()
            .any(|choice| required.contains(choice))
        {
            lane.complete[index] = true;
            continue;
        }
        let selected = facts[index].selected;
        lane.complete[index] = true;
        if !required.insert(selected) {
            return Err(RetentionError::InvalidConstraint);
        }
        newly_required.push(selected);
        selected_any = true;
    }
    lane.pending.extend(deferred);
    Ok(selected_any)
}

fn carrier_is_retained(
    carrier: CompilerCrateLoadCarrier,
    compile_required: &BTreeSet<GraphNode>,
    retained: &BTreeSet<SourceUnitId>,
) -> bool {
    match carrier {
        CompilerCrateLoadCarrier::Definition(definition) => {
            compile_required.contains(&GraphNode::Definition(definition))
        }
        CompilerCrateLoadCarrier::Source(unit) => retained.contains(&unit),
    }
}
