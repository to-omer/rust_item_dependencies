use std::collections::{BTreeSet, VecDeque};

use crate::source::SourceUnitId;

use super::{RetentionError, SourceRequirement, retain_source_unit};

#[derive(Clone, Copy)]
pub(super) enum SourceRequirementMode {
    Semantic,
    Compile,
}

/// Immutable reverse indexes for monotone source-retention requirements.
pub(super) struct SourceRequirementIndex {
    atomic_groups: Vec<Vec<SourceUnitId>>,
    atomic_group_by_unit: Vec<usize>,
    semantic_by_trigger: Vec<Vec<SourceUnitId>>,
    compile_by_trigger: Vec<Vec<SourceUnitId>>,
}

impl SourceRequirementIndex {
    pub(super) fn new(
        unit_count: usize,
        atomic_groups: &[Vec<SourceUnitId>],
        ancestor_requirements: &[SourceRequirement],
        shell_requirements: &[SourceRequirement],
        derive_requirements: &[SourceRequirement],
        macro_rule_requirements: &[SourceRequirement],
    ) -> Result<Self, RetentionError> {
        let mut atomic_group_by_unit = vec![usize::MAX; unit_count];
        for (group, members) in atomic_groups.iter().enumerate() {
            if members.is_empty() {
                return Err(RetentionError::InvalidConstraint);
            }
            for &member in members {
                let Some(slot) = atomic_group_by_unit.get_mut(member.0 as usize) else {
                    return Err(RetentionError::InvalidConstraint);
                };
                if *slot != usize::MAX {
                    return Err(RetentionError::InvalidConstraint);
                }
                *slot = group;
            }
        }
        if atomic_group_by_unit.contains(&usize::MAX) {
            return Err(RetentionError::InvalidConstraint);
        }

        let mut semantic_by_trigger = vec![Vec::new(); unit_count];
        let mut compile_by_trigger = vec![Vec::new(); unit_count];
        for requirement in ancestor_requirements.iter().chain(derive_requirements) {
            push_requirement(&mut semantic_by_trigger, *requirement, unit_count)?;
        }
        for requirement in ancestor_requirements
            .iter()
            .chain(shell_requirements)
            .chain(derive_requirements)
            .chain(macro_rule_requirements)
        {
            push_requirement(&mut compile_by_trigger, *requirement, unit_count)?;
        }
        for requirements in semantic_by_trigger
            .iter_mut()
            .chain(&mut compile_by_trigger)
        {
            requirements.sort_unstable();
            requirements.dedup();
        }

        Ok(Self {
            atomic_groups: atomic_groups.to_vec(),
            atomic_group_by_unit,
            semantic_by_trigger,
            compile_by_trigger,
        })
    }
}

fn push_requirement(
    by_trigger: &mut [Vec<SourceUnitId>],
    requirement: SourceRequirement,
    unit_count: usize,
) -> Result<(), RetentionError> {
    if requirement.trigger.0 as usize >= unit_count || requirement.required.0 as usize >= unit_count
    {
        return Err(RetentionError::InvalidConstraint);
    }
    by_trigger[requirement.trigger.0 as usize].push(requirement.required);
    Ok(())
}

/// Delta-driven closure for atomic source groups and directed source
/// requirements. Each retained source unit and each opened atomic group is
/// consumed once.
pub(super) struct SourceRequirementClosure<'index> {
    index: &'index SourceRequirementIndex,
    mode: SourceRequirementMode,
    initialized: bool,
    seen: Vec<bool>,
    pending: VecDeque<SourceUnitId>,
    opened_groups: Vec<bool>,
    #[cfg(test)]
    pub(super) unit_visits: usize,
    #[cfg(test)]
    pub(super) requirement_visits: usize,
    #[cfg(test)]
    pub(super) group_member_visits: usize,
}

impl<'index> SourceRequirementClosure<'index> {
    pub(super) fn new(index: &'index SourceRequirementIndex, mode: SourceRequirementMode) -> Self {
        Self {
            index,
            mode,
            initialized: false,
            seen: vec![false; index.atomic_group_by_unit.len()],
            pending: VecDeque::new(),
            opened_groups: vec![false; index.atomic_groups.len()],
            #[cfg(test)]
            unit_visits: 0,
            #[cfg(test)]
            requirement_visits: 0,
            #[cfg(test)]
            group_member_visits: 0,
        }
    }

    pub(super) fn seed(&mut self, retained: &BTreeSet<SourceUnitId>) -> Result<(), RetentionError> {
        if self.initialized {
            return Err(RetentionError::InvalidConstraint);
        }
        self.initialized = true;
        self.add(retained.iter().copied())
    }

    pub(super) fn add(
        &mut self,
        units: impl IntoIterator<Item = SourceUnitId>,
    ) -> Result<(), RetentionError> {
        for unit in units {
            let Some(seen) = self.seen.get_mut(unit.0 as usize) else {
                return Err(RetentionError::InvalidConstraint);
            };
            if !*seen {
                *seen = true;
                self.pending.push_back(unit);
            }
        }
        Ok(())
    }

    pub(super) fn close(
        &mut self,
        retained: &mut BTreeSet<SourceUnitId>,
        newly_retained: &mut Vec<SourceUnitId>,
    ) -> Result<(), RetentionError> {
        while let Some(unit) = self.pending.pop_front() {
            if !retained.contains(&unit) {
                return Err(RetentionError::InvalidConstraint);
            }
            #[cfg(test)]
            {
                self.unit_visits += 1;
            }
            let index = unit.0 as usize;
            let group = self.index.atomic_group_by_unit[index];
            if !self.opened_groups[group] {
                self.opened_groups[group] = true;
                for &member in &self.index.atomic_groups[group] {
                    #[cfg(test)]
                    {
                        self.group_member_visits += 1;
                    }
                    if retain_source_unit(retained, newly_retained, member) {
                        self.add([member])?;
                    }
                }
            }

            let requirements = match self.mode {
                SourceRequirementMode::Semantic => &self.index.semantic_by_trigger[index],
                SourceRequirementMode::Compile => &self.index.compile_by_trigger[index],
            };
            for &required in requirements {
                #[cfg(test)]
                {
                    self.requirement_visits += 1;
                }
                if retain_source_unit(retained, newly_retained, required) {
                    self.add([required])?;
                }
            }
        }
        Ok(())
    }
}
