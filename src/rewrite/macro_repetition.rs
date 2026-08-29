use std::collections::{BTreeMap, BTreeSet};

use crate::source::syntax::ParserTokenRewriteGuard;
use crate::source::{
    ByteRange, MacroRepetitionSourceFacts, SourceInventory, SourceUnitId, WrittenUnitKind,
};

use super::{SourceRewriteError, valid_range, validate_deletion_range, validate_retention};

/// Stateful token constraints for macro repetition deletions.
///
/// The original source is tokenized once. Retention deltas select only the
/// repetitions whose parent or elements changed, and the active deletion
/// index rechecks only cohorts adjacent to those changed plans.
pub(crate) struct MacroRepetitionTokenRequirements<'source> {
    inventory: &'source SourceInventory,
    guard: Option<ParserTokenRewriteGuard<'source>>,
    inputs_by_unit: Vec<Vec<RepetitionRetentionInput>>,
    known_retained: Vec<bool>,
    pending_retained: Vec<SourceUnitId>,
    initialized: bool,
    repetitions: Vec<RepetitionDeletionState>,
    active_deletions: BTreeMap<ByteRange, ActiveMacroRepetitionDeletion>,
    components: Vec<Option<MacroRepetitionDeletionComponent>>,
    lexical_cohorts: BTreeMap<ByteRange, BTreeSet<ByteRange>>,
    #[cfg(test)]
    element_visits: usize,
    #[cfg(test)]
    cohort_element_visits: usize,
    #[cfg(test)]
    component_member_moves: usize,
    #[cfg(test)]
    full_retention_validations: usize,
}

#[derive(Clone, Copy)]
enum RepetitionRetentionInput {
    Parent { repetition: usize },
    Element { repetition: usize, element: usize },
}

struct RepetitionDeletionState {
    active: bool,
    retained_elements: Vec<bool>,
    retained_count: usize,
    unretained_runs: BTreeMap<usize, usize>,
}

struct RepetitionRetentionModel {
    retained_count: usize,
    unretained_runs: BTreeMap<usize, usize>,
}

impl RepetitionRetentionModel {
    fn from_retained_elements(
        facts: &MacroRepetitionSourceFacts,
        retained_elements: &[bool],
    ) -> Result<Self, SourceRewriteError> {
        if retained_elements.len() != facts.elements.len() {
            return Err(SourceRewriteError::InvalidInventory);
        }
        let retained_count = retained_elements
            .iter()
            .filter(|&&retained| retained)
            .count();
        Self::validate_count(facts, retained_count)?;

        let mut unretained_runs = BTreeMap::new();
        let mut run_start = None;
        for (index, &retained) in retained_elements.iter().enumerate() {
            if retained {
                if let Some(first) = run_start.take() {
                    unretained_runs.insert(first, index - 1);
                }
            } else {
                run_start.get_or_insert(index);
            }
        }
        if let Some(first) = run_start {
            unretained_runs.insert(first, retained_elements.len() - 1);
        }

        Ok(Self {
            retained_count,
            unretained_runs,
        })
    }

    fn validate_count(
        facts: &MacroRepetitionSourceFacts,
        retained_count: usize,
    ) -> Result<(), SourceRewriteError> {
        if retained_count < facts.minimum as usize
            || facts
                .maximum
                .is_some_and(|maximum| retained_count > maximum as usize)
        {
            return Err(SourceRewriteError::InvalidRetention);
        }
        Ok(())
    }
}

struct ActiveMacroRepetitionDeletion {
    repetition: usize,
    first: usize,
    last: usize,
    component: usize,
    dependency_window: ByteRange,
}

struct MacroRepetitionDeletionComponent {
    deletions: BTreeSet<ByteRange>,
}

impl<'source> MacroRepetitionTokenRequirements<'source> {
    pub(crate) fn new(inventory: &'source SourceInventory) -> Result<Self, SourceRewriteError> {
        let guard = (!inventory.macro_repetitions.is_empty())
            .then(|| ParserTokenRewriteGuard::new(&inventory.original))
            .transpose()
            .map_err(|_| SourceRewriteError::InvalidInventory)?;
        let mut inputs_by_unit = vec![Vec::new(); inventory.units.len()];
        for (repetition, facts) in inventory.macro_repetitions.iter().enumerate() {
            inputs_by_unit
                .get_mut(facts.parent.0 as usize)
                .ok_or(SourceRewriteError::InvalidInventory)?
                .push(RepetitionRetentionInput::Parent { repetition });
            for (element, facts) in facts.elements.iter().enumerate() {
                inputs_by_unit
                    .get_mut(facts.unit.0 as usize)
                    .ok_or(SourceRewriteError::InvalidInventory)?
                    .push(RepetitionRetentionInput::Element {
                        repetition,
                        element,
                    });
            }
        }
        Ok(Self {
            inventory,
            guard,
            inputs_by_unit,
            known_retained: vec![false; inventory.units.len()],
            pending_retained: Vec::new(),
            initialized: false,
            repetitions: inventory
                .macro_repetitions
                .iter()
                .map(|facts| RepetitionDeletionState {
                    active: false,
                    retained_elements: vec![false; facts.elements.len()],
                    retained_count: 0,
                    unretained_runs: BTreeMap::new(),
                })
                .collect(),
            active_deletions: BTreeMap::new(),
            components: Vec::new(),
            lexical_cohorts: BTreeMap::new(),
            #[cfg(test)]
            element_visits: 0,
            #[cfg(test)]
            cohort_element_visits: 0,
            #[cfg(test)]
            component_member_moves: 0,
            #[cfg(test)]
            full_retention_validations: 0,
        })
    }

    /// Adds one wave of token-preservation requirements.
    ///
    /// Newly required elements are processed by the next call, after the
    /// outer retention fixed point has satisfied structural and minimum-count
    /// constraints triggered by those elements.
    pub(crate) fn close(
        &mut self,
        retained: &mut BTreeSet<SourceUnitId>,
        newly_retained: &[SourceUnitId],
    ) -> Result<bool, SourceRewriteError> {
        if self.guard.is_none() {
            return Ok(false);
        }
        if !self.initialized {
            #[cfg(test)]
            {
                self.full_retention_validations += 1;
            }
            validate_retention(self.inventory, retained)?;
            let initial = newly_retained.iter().copied().collect::<BTreeSet<_>>();
            if initial.len() != newly_retained.len() || initial != *retained {
                return Err(SourceRewriteError::InvalidRetention);
            }
            self.initialized = true;
        }
        if !self.pending_retained.is_empty() {
            return Err(SourceRewriteError::InvalidRetention);
        }
        let mut pending_units = newly_retained.to_vec();
        let mut changed_repetitions = BTreeMap::<usize, BTreeSet<usize>>::new();
        while let Some(unit) = pending_units.pop() {
            let index = unit.0 as usize;
            if !retained.contains(&unit) || index >= self.known_retained.len() {
                return Err(SourceRewriteError::InvalidRetention);
            }
            if self.known_retained[index] {
                return Err(SourceRewriteError::InvalidRetention);
            }
            self.known_retained[index] = true;
            for input in &self.inputs_by_unit[index] {
                match *input {
                    RepetitionRetentionInput::Parent { repetition } => {
                        changed_repetitions.entry(repetition).or_default();
                    }
                    RepetitionRetentionInput::Element {
                        repetition,
                        element,
                    } => {
                        changed_repetitions
                            .entry(repetition)
                            .or_default()
                            .insert(element);
                    }
                }
            }
        }

        let mut dirty_components = BTreeSet::new();
        let mut dirty_lexical_cohorts = BTreeSet::new();
        for (&repetition, elements) in &changed_repetitions {
            if !self.repetitions[repetition].active {
                continue;
            }
            for &element in elements {
                self.retain_repetition_element(
                    repetition,
                    element,
                    &mut dirty_components,
                    &mut dirty_lexical_cohorts,
                )?;
            }
        }
        for (repetition, _) in changed_repetitions {
            let parent = self.inventory.macro_repetitions[repetition].parent;
            if !self.repetitions[repetition].active && self.known_retained[parent.0 as usize] {
                self.activate_repetition(
                    repetition,
                    &mut dirty_components,
                    &mut dirty_lexical_cohorts,
                )?;
            }
        }

        for component in dirty_components {
            let Some(range) = self.component_range(component) else {
                continue;
            };
            if !self
                .guard
                .as_ref()
                .expect("nonempty repetition inventories have a token guard")
                .deletion_preserves_identity(range)
            {
                for element in self.component_elements(component)? {
                    if retained.insert(element) {
                        self.pending_retained.push(element);
                    }
                }
            }
        }
        for window in dirty_lexical_cohorts {
            let Some(deletions) = self.lexical_cohorts.get(&window) else {
                continue;
            };
            let deletions = deletions.iter().copied().collect::<Vec<_>>();
            if !self
                .guard
                .as_ref()
                .expect("nonempty repetition inventories have a token guard")
                .deletions_preserve_identity(&deletions)
            {
                for element in self.deletion_elements(&deletions)? {
                    if retained.insert(element) {
                        self.pending_retained.push(element);
                    }
                }
            }
        }
        Ok(!self.pending_retained.is_empty())
    }

    pub(crate) fn take_newly_forced_units(&mut self) -> Vec<SourceUnitId> {
        std::mem::take(&mut self.pending_retained)
    }

    fn activate_repetition(
        &mut self,
        repetition: usize,
        dirty_components: &mut BTreeSet<usize>,
        dirty_lexical_cohorts: &mut BTreeSet<ByteRange>,
    ) -> Result<(), SourceRewriteError> {
        let facts = &self.inventory.macro_repetitions[repetition];
        let mut retained_elements = Vec::with_capacity(facts.elements.len());
        for element in &facts.elements {
            #[cfg(test)]
            {
                self.element_visits += 1;
            }
            let is_retained = self.known_retained[element.unit.0 as usize];
            retained_elements.push(is_retained);
        }
        let model = RepetitionRetentionModel::from_retained_elements(facts, &retained_elements)?;
        let runs = model
            .unretained_runs
            .iter()
            .map(|(&first, &last)| (first, last))
            .collect::<Vec<_>>();
        self.repetitions[repetition] = RepetitionDeletionState {
            active: true,
            retained_elements,
            retained_count: model.retained_count,
            unretained_runs: model.unretained_runs,
        };
        for (first, last) in runs {
            self.insert_active_deletion(
                repetition,
                first,
                last,
                dirty_components,
                dirty_lexical_cohorts,
            )?;
        }
        Ok(())
    }

    fn retain_repetition_element(
        &mut self,
        repetition: usize,
        element: usize,
        dirty_components: &mut BTreeSet<usize>,
        dirty_lexical_cohorts: &mut BTreeSet<ByteRange>,
    ) -> Result<(), SourceRewriteError> {
        if self.repetitions[repetition]
            .retained_elements
            .get(element)
            .copied()
            .ok_or(SourceRewriteError::InvalidInventory)?
        {
            return Ok(());
        }
        #[cfg(test)]
        {
            self.element_visits += 1;
        }
        let (first, last) = self.repetitions[repetition]
            .unretained_runs
            .range(..=element)
            .next_back()
            .map(|(first, last)| (*first, *last))
            .filter(|(_, last)| element <= *last)
            .ok_or(SourceRewriteError::InvalidInventory)?;
        self.repetitions[repetition].unretained_runs.remove(&first);
        self.repetitions[repetition].retained_elements[element] = true;
        self.repetitions[repetition].retained_count += 1;
        RepetitionRetentionModel::validate_count(
            &self.inventory.macro_repetitions[repetition],
            self.repetitions[repetition].retained_count,
        )?;
        self.remove_active_deletion(
            repetition,
            first,
            last,
            dirty_components,
            dirty_lexical_cohorts,
        )?;
        if first < element {
            self.repetitions[repetition]
                .unretained_runs
                .insert(first, element - 1);
            self.insert_active_deletion(
                repetition,
                first,
                element - 1,
                dirty_components,
                dirty_lexical_cohorts,
            )?;
        }
        if element < last {
            self.repetitions[repetition]
                .unretained_runs
                .insert(element + 1, last);
            self.insert_active_deletion(
                repetition,
                element + 1,
                last,
                dirty_components,
                dirty_lexical_cohorts,
            )?;
        }
        Ok(())
    }

    fn insert_active_deletion(
        &mut self,
        repetition: usize,
        first: usize,
        last: usize,
        dirty_components: &mut BTreeSet<usize>,
        dirty_lexical_cohorts: &mut BTreeSet<ByteRange>,
    ) -> Result<(), SourceRewriteError> {
        let range = macro_repetition_run_deletion_range(
            self.inventory,
            &self.inventory.macro_repetitions[repetition],
            first,
            last,
        )?;
        let dependency_window = self
            .guard
            .as_ref()
            .and_then(|guard| guard.deletion_dependency_window(range))
            .ok_or(SourceRewriteError::InvalidInventory)?;
        let lower = ByteRange {
            start: range.start,
            end: 0,
        };
        let previous = self
            .active_deletions
            .range(..lower)
            .next_back()
            .map(|(range, active)| (*range, active.component));
        let next = self
            .active_deletions
            .range(lower..)
            .next()
            .map(|(range, active)| (*range, active.component));
        if previous.is_some_and(|(previous, _)| previous.end > range.start)
            || next.is_some_and(|(next, _)| next.start < range.end)
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        let left = previous.filter(|(previous, _)| previous.end == range.start);
        let right = next.filter(|(next, _)| next.start == range.end);
        let component = match (left, right) {
            (None, None) => self.new_component(BTreeSet::from([range])),
            (Some((_, component)), None) | (None, Some((_, component))) => {
                self.components[component]
                    .as_mut()
                    .ok_or(SourceRewriteError::InvalidInventory)?
                    .deletions
                    .insert(range);
                component
            }
            (Some((_, left)), Some((_, right))) if left != right => {
                let (target, source) = if self.component_len(left)? >= self.component_len(right)? {
                    (left, right)
                } else {
                    (right, left)
                };
                let moved = self.components[source]
                    .take()
                    .ok_or(SourceRewriteError::InvalidInventory)?
                    .deletions;
                #[cfg(test)]
                {
                    self.component_member_moves += moved.len();
                }
                for deletion in &moved {
                    self.active_deletions
                        .get_mut(deletion)
                        .ok_or(SourceRewriteError::InvalidInventory)?
                        .component = target;
                }
                let target_component = self.components[target]
                    .as_mut()
                    .ok_or(SourceRewriteError::InvalidInventory)?;
                target_component.deletions.extend(moved);
                target_component.deletions.insert(range);
                target
            }
            (Some(_), Some(_)) => return Err(SourceRewriteError::InvalidInventory),
        };
        if self
            .active_deletions
            .insert(
                range,
                ActiveMacroRepetitionDeletion {
                    repetition,
                    first,
                    last,
                    component,
                    dependency_window,
                },
            )
            .is_some()
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        dirty_components.insert(component);
        if !self
            .lexical_cohorts
            .entry(dependency_window)
            .or_default()
            .insert(range)
        {
            return Err(SourceRewriteError::InvalidInventory);
        }
        dirty_lexical_cohorts.insert(dependency_window);
        Ok(())
    }

    fn remove_active_deletion(
        &mut self,
        repetition: usize,
        first: usize,
        last: usize,
        dirty_components: &mut BTreeSet<usize>,
        dirty_lexical_cohorts: &mut BTreeSet<ByteRange>,
    ) -> Result<(), SourceRewriteError> {
        let range = macro_repetition_run_deletion_range(
            self.inventory,
            &self.inventory.macro_repetitions[repetition],
            first,
            last,
        )?;
        let active = self
            .active_deletions
            .remove(&range)
            .ok_or(SourceRewriteError::InvalidInventory)?;
        if active.repetition != repetition || active.first != first || active.last != last {
            return Err(SourceRewriteError::InvalidInventory);
        }
        let cohort = self
            .lexical_cohorts
            .get_mut(&active.dependency_window)
            .ok_or(SourceRewriteError::InvalidInventory)?;
        if !cohort.remove(&range) {
            return Err(SourceRewriteError::InvalidInventory);
        }
        if cohort.is_empty() {
            self.lexical_cohorts.remove(&active.dependency_window);
        } else {
            dirty_lexical_cohorts.insert(active.dependency_window);
        }
        let component = self.components[active.component]
            .as_mut()
            .ok_or(SourceRewriteError::InvalidInventory)?;
        if !component.deletions.remove(&range) {
            return Err(SourceRewriteError::InvalidInventory);
        }
        if component.deletions.is_empty() {
            self.components[active.component] = None;
            return Ok(());
        }
        let left = component.deletions.range(..range).next_back().copied();
        let right = component.deletions.range(range..).next().copied();
        if let (Some(left), Some(right)) = (left, right)
            && left.end != right.start
        {
            let mut right_deletions = component.deletions.split_off(&right);
            let mut left_deletions = std::mem::take(&mut component.deletions);
            let (kept, moved) = if left_deletions.len() >= right_deletions.len() {
                (std::mem::take(&mut left_deletions), right_deletions)
            } else {
                (std::mem::take(&mut right_deletions), left_deletions)
            };
            self.components[active.component] =
                Some(MacroRepetitionDeletionComponent { deletions: kept });
            let moved_component = self.components.len();
            #[cfg(test)]
            {
                self.component_member_moves += moved.len();
            }
            for deletion in &moved {
                self.active_deletions
                    .get_mut(deletion)
                    .ok_or(SourceRewriteError::InvalidInventory)?
                    .component = moved_component;
            }
            self.components
                .push(Some(MacroRepetitionDeletionComponent { deletions: moved }));
            dirty_components.insert(moved_component);
        }
        dirty_components.insert(active.component);
        Ok(())
    }

    fn new_component(&mut self, deletions: BTreeSet<ByteRange>) -> usize {
        let id = self.components.len();
        self.components
            .push(Some(MacroRepetitionDeletionComponent { deletions }));
        id
    }

    fn component_len(&self, component: usize) -> Result<usize, SourceRewriteError> {
        self.components
            .get(component)
            .and_then(Option::as_ref)
            .map(|component| component.deletions.len())
            .ok_or(SourceRewriteError::InvalidInventory)
    }

    fn component_range(&self, component: usize) -> Option<ByteRange> {
        let component = self.components.get(component)?.as_ref()?;
        let first = component.deletions.first()?;
        let last = component.deletions.last()?;
        Some(ByteRange {
            start: first.start,
            end: last.end,
        })
    }

    fn component_elements(
        &mut self,
        component: usize,
    ) -> Result<BTreeSet<SourceUnitId>, SourceRewriteError> {
        let deletions = self
            .components
            .get(component)
            .and_then(Option::as_ref)
            .ok_or(SourceRewriteError::InvalidInventory)?
            .deletions
            .iter()
            .copied()
            .collect::<Vec<_>>();
        self.deletion_elements(&deletions)
    }

    fn deletion_elements(
        &mut self,
        deletions: &[ByteRange],
    ) -> Result<BTreeSet<SourceUnitId>, SourceRewriteError> {
        let mut elements = BTreeSet::new();
        for deletion in deletions {
            let active = self
                .active_deletions
                .get(deletion)
                .ok_or(SourceRewriteError::InvalidInventory)?;
            let facts = &self.inventory.macro_repetitions[active.repetition];
            for element in &facts.elements[active.first..=active.last] {
                #[cfg(test)]
                {
                    self.cohort_element_visits += 1;
                }
                elements.insert(element.unit);
            }
        }
        Ok(elements)
    }

    #[cfg(test)]
    pub(super) fn active_deletion_count(&self) -> usize {
        self.active_deletions.len()
    }

    #[cfg(test)]
    pub(super) fn active_deletion_ranges(&self) -> Vec<ByteRange> {
        self.active_deletions.keys().copied().collect()
    }

    #[cfg(test)]
    pub(super) fn active_component_ranges(&self) -> Vec<ByteRange> {
        let mut ranges = (0..self.components.len())
            .filter_map(|component| self.component_range(component))
            .collect::<Vec<_>>();
        ranges.sort();
        ranges
    }

    #[cfg(test)]
    pub(super) fn component_index_is_consistent(&self) -> bool {
        let active_is_indexed = self.active_deletions.iter().all(|(range, active)| {
            self.components
                .get(active.component)
                .and_then(Option::as_ref)
                .is_some_and(|component| component.deletions.contains(range))
                && self
                    .lexical_cohorts
                    .get(&active.dependency_window)
                    .is_some_and(|cohort| cohort.contains(range))
        });
        let components_are_connected =
            self.components
                .iter()
                .enumerate()
                .all(|(component_id, component)| {
                    let Some(component) = component else {
                        return true;
                    };
                    let ranges = component.deletions.iter().copied().collect::<Vec<_>>();
                    ranges.windows(2).all(|pair| pair[0].end == pair[1].start)
                        && ranges.iter().all(|range| {
                            self.active_deletions
                                .get(range)
                                .is_some_and(|active| active.component == component_id)
                        })
                });
        let cohorts_are_active = self.lexical_cohorts.iter().all(|(window, cohort)| {
            !cohort.is_empty()
                && cohort.iter().all(|range| {
                    self.active_deletions
                        .get(range)
                        .is_some_and(|active| active.dependency_window == *window)
                })
        });
        active_is_indexed && components_are_connected && cohorts_are_active
    }

    #[cfg(test)]
    pub(super) fn element_visits(&self) -> usize {
        self.element_visits
    }

    #[cfg(test)]
    pub(super) fn cohort_element_visits(&self) -> usize {
        self.cohort_element_visits
    }

    #[cfg(test)]
    pub(super) fn component_member_moves(&self) -> usize {
        self.component_member_moves
    }

    #[cfg(test)]
    pub(super) fn token_validation_bytes(&self) -> usize {
        self.guard
            .as_ref()
            .map_or(0, ParserTokenRewriteGuard::relexed_bytes)
    }

    #[cfg(test)]
    pub(super) fn token_dependency_visits(&self) -> usize {
        self.guard
            .as_ref()
            .map_or(0, ParserTokenRewriteGuard::dependency_token_visits)
    }

    #[cfg(test)]
    pub(super) fn full_retention_validations(&self) -> usize {
        self.full_retention_validations
    }
}

pub(super) fn macro_repetition_deletions(
    inventory: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
    piece_boundaries: &BTreeSet<u32>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    let mut deletions = Vec::new();
    for facts in &inventory.macro_repetitions {
        deletions.extend(plan_macro_repetition_deletions(inventory, facts, retained)?);
    }
    deletions.sort();

    let mut merged = Vec::<ByteRange>::new();
    for deletion in deletions {
        validate_deletion_range(&inventory.original, deletion, piece_boundaries)?;
        if let Some(previous) = merged.last_mut()
            && deletion.start <= previous.end
        {
            previous.end = previous.end.max(deletion.end);
        } else {
            merged.push(deletion);
        }
    }
    if !merged.is_empty() && !deletions_preserve_parser_tokens(&inventory.original, &merged) {
        return Err(SourceRewriteError::InvalidRetention);
    }
    Ok(merged)
}

#[cfg(test)]
pub(super) fn rewrite_macro_repetition(
    inventory: &SourceInventory,
    repetition: &MacroRepetitionSourceFacts,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    plan_macro_repetition_deletions(inventory, repetition, retained)
}

fn macro_repetition_run_deletion_range(
    inventory: &SourceInventory,
    repetition: &MacroRepetitionSourceFacts,
    first: usize,
    last: usize,
) -> Result<ByteRange, SourceRewriteError> {
    if first > last || last >= repetition.elements.len() {
        return Err(SourceRewriteError::InvalidInventory);
    }
    let element = |index: usize| {
        let id = repetition.elements[index].unit;
        inventory
            .units
            .get(id.0 as usize)
            .filter(|unit| unit.id == id && unit.kind == WrittenUnitKind::NestedItem)
            .ok_or(SourceRewriteError::InvalidInventory)
    };
    let first_unit = element(first)?;
    let last_unit = element(last)?;
    let mut range = if first == 0 && last + 1 == repetition.elements.len() {
        repetition.input_range
    } else {
        ByteRange {
            start: first_unit.full_range.start,
            end: last_unit.full_range.end,
        }
    };
    if first != 0 || last + 1 != repetition.elements.len() {
        if let Some(separator) = repetition.elements[last].separator_after {
            range.end = separator.end;
        } else if last + 1 == repetition.elements.len()
            && first > 0
            && let Some(separator) = repetition.elements[first - 1].separator_after
        {
            range.start = separator.start;
        }
    }
    if range.is_empty() || !valid_range(&inventory.original, range) {
        return Err(SourceRewriteError::InvalidInventory);
    }
    Ok(range)
}

fn plan_macro_repetition_deletions(
    inventory: &SourceInventory,
    repetition: &MacroRepetitionSourceFacts,
    retained: &BTreeSet<SourceUnitId>,
) -> Result<Vec<ByteRange>, SourceRewriteError> {
    if !retained.contains(&repetition.parent) {
        return Ok(Vec::new());
    }

    let retained_elements = repetition
        .elements
        .iter()
        .map(|facts| {
            inventory
                .units
                .get(facts.unit.0 as usize)
                .filter(|unit| unit.id == facts.unit && unit.kind == WrittenUnitKind::NestedItem)
                .ok_or(SourceRewriteError::InvalidInventory)
                .map(|unit| retained.contains(&unit.id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let model = RepetitionRetentionModel::from_retained_elements(repetition, &retained_elements)?;
    if model.retained_count == retained_elements.len() {
        return Ok(Vec::new());
    }

    let mut deletions = Vec::with_capacity(model.unretained_runs.len());
    for (first, last) in model.unretained_runs {
        deletions.push(macro_repetition_run_deletion_range(
            inventory, repetition, first, last,
        )?);
    }
    Ok(deletions)
}

pub(super) fn deletions_preserve_parser_tokens(source: &str, deletions: &[ByteRange]) -> bool {
    if deletions
        .windows(2)
        .any(|pair| pair[0].end >= pair[1].start)
    {
        return false;
    }
    let Ok(guard) = ParserTokenRewriteGuard::new(source) else {
        return false;
    };
    let mut cohorts = BTreeMap::<ByteRange, Vec<ByteRange>>::new();
    for &deletion in deletions {
        let Some(window) = guard.deletion_dependency_window(deletion) else {
            return false;
        };
        cohorts.entry(window).or_default().push(deletion);
    }
    cohorts
        .values()
        .all(|cohort| guard.deletions_preserve_identity(cohort))
}
