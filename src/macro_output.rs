//! Validated compiler observations for declarative-macro output.

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::FxHashMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::unord::UnordMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_hir::def_id::LocalDefId;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{
    MacroDeclarativeExpansion, MacroInvocationOrigin, MacroOutputTokenRange, TyCtxt,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::ExpnId;

/// One half-open range in a producer's output-token ordinal space.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroOutputRange {
    pub(crate) start: u32,
    pub(crate) end: u32,
}

impl MacroOutputRange {
    pub(crate) fn len(self) -> u32 {
        self.end - self.start
    }

    pub(crate) fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub(crate) fn contains(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    pub(crate) fn start(self) -> u32 {
        self.start
    }

    pub(crate) fn end(self) -> u32 {
        self.end
    }

    #[cfg(test)]
    pub(crate) fn test_new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    #[cfg(test)]
    pub(crate) fn test_set_start(&mut self, start: u32) {
        self.start = start;
    }

    #[cfg(test)]
    pub(crate) fn test_set_end(&mut self, end: u32) {
        self.end = end;
    }
}

/// A producer's validated output-token ledger.
///
/// Construction proves, once, that every live product and discarded range is
/// within the producer output and that discarded output is either disjoint
/// from a live product or strictly nested in it. Later lowering stages may
/// classify a subset of the recorded live ranges, but cannot introduce a new
/// range that was not part of this ledger.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ValidatedMacroOutputLedger {
    output_token_count: u32,
    live_outputs: Box<[MacroOutputRange]>,
    discarded_outputs: Box<[MacroOutputRange]>,
}

impl ValidatedMacroOutputLedger {
    pub(crate) fn new(
        output_token_count: u32,
        mut live_outputs: Vec<MacroOutputRange>,
        discarded_outputs: Vec<MacroOutputRange>,
    ) -> Option<Self> {
        live_outputs.sort();
        live_outputs.dedup();
        if !laminar_output_ranges(live_outputs.iter().copied()) {
            return None;
        }
        let discarded_outputs =
            normalize_discarded_output_ranges(discarded_outputs, output_token_count)?;
        if !discarded_outputs_fit_live_products(
            &discarded_outputs,
            output_token_count,
            live_outputs.iter().copied(),
        ) {
            return None;
        }
        Some(Self {
            output_token_count,
            live_outputs: live_outputs.into_boxed_slice(),
            discarded_outputs: discarded_outputs.into_boxed_slice(),
        })
    }

    pub(crate) fn output_token_count(&self) -> u32 {
        self.output_token_count
    }

    pub(crate) fn discarded_outputs(&self) -> &[MacroOutputRange] {
        &self.discarded_outputs
    }

    pub(crate) fn contains_live_output(&self, output: MacroOutputRange) -> bool {
        self.live_outputs.binary_search(&output).is_ok()
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct ValidatedMacroDefinitionOutput {
    definition: LocalDefId,
    output: MacroOutputRange,
}

#[cfg(rust_item_dependencies_patched)]
impl ValidatedMacroDefinitionOutput {
    pub(crate) fn definition(self) -> LocalDefId {
        self.definition
    }

    pub(crate) fn output(self) -> MacroOutputRange {
        self.output
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct ValidatedMacroChildOutput {
    expansion: ExpnId,
    output: MacroOutputRange,
}

#[cfg(rust_item_dependencies_patched)]
impl ValidatedMacroChildOutput {
    pub(crate) fn expansion(self) -> ExpnId {
        self.expansion
    }

    pub(crate) fn output(self) -> MacroOutputRange {
        self.output
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Debug)]
pub(crate) struct ValidatedMacroOwnerOutput {
    intrinsic: bool,
    dependent_outputs: Box<[MacroOutputRange]>,
    required_outputs: Box<[MacroOutputRange]>,
}

#[cfg(rust_item_dependencies_patched)]
impl ValidatedMacroOwnerOutput {
    pub(crate) fn intrinsic(&self) -> bool {
        self.intrinsic
    }

    pub(crate) fn dependent_outputs(&self) -> &[MacroOutputRange] {
        &self.dependent_outputs
    }

    pub(crate) fn required_outputs(&self) -> &[MacroOutputRange] {
        &self.required_outputs
    }
}

#[cfg(rust_item_dependencies_patched)]
struct ValidatedDeclarativeOutputFacts {
    ledger: ValidatedMacroOutputLedger,
    definitions: Box<[ValidatedMacroDefinitionOutput]>,
    children: Box<[ValidatedMacroChildOutput]>,
    owner: Option<ValidatedMacroOwnerOutput>,
}

#[cfg(rust_item_dependencies_patched)]
impl ValidatedDeclarativeOutputFacts {
    fn from_declarative_expansion(expansion: &MacroDeclarativeExpansion) -> Option<Self> {
        if !expansion.output_provenance_complete {
            return None;
        }
        let output_token_count = u32::try_from(expansion.output_tokens.len()).ok()?;

        let mut seen_definitions = FxHashMap::default();
        let mut definitions = expansion
            .definitions
            .iter()
            .map(|definition| {
                let output = output_range(definition.output, output_token_count)?;
                seen_definitions
                    .insert(definition.definition, ())
                    .is_none()
                    .then_some(ValidatedMacroDefinitionOutput {
                        definition: definition.definition,
                        output,
                    })
            })
            .collect::<Option<Vec<_>>>()?;
        definitions.sort_by_key(|definition| {
            (
                definition.output,
                definition.definition.local_def_index.as_u32(),
            )
        });

        let mut seen_children = FxHashMap::default();
        let mut children = expansion
            .child_expansions
            .iter()
            .map(|child| {
                let output = output_range(child.output, output_token_count)?;
                seen_children
                    .insert(child.expansion, ())
                    .is_none()
                    .then_some(ValidatedMacroChildOutput {
                        expansion: child.expansion,
                        output,
                    })
            })
            .collect::<Option<Vec<_>>>()?;
        children.sort_by_key(|child| {
            (
                child.output,
                child.expansion.expn_hash().local_hash().as_u64(),
            )
        });

        let discarded_outputs = expansion
            .discarded_outputs
            .iter()
            .map(|&output| output_range(output, output_token_count))
            .collect::<Option<Vec<_>>>()?;
        let ledger = ValidatedMacroOutputLedger::new(
            output_token_count,
            definitions
                .iter()
                .map(|definition| definition.output)
                .chain(children.iter().map(|child| child.output))
                .collect(),
            discarded_outputs,
        )?;

        let owner = if expansion.owner_output.complete {
            let dependent_outputs = validated_role_ranges(
                &expansion.owner_output.dependent_outputs,
                output_token_count,
            )?;
            let required_outputs = validated_role_ranges(
                &expansion.owner_output.required_outputs,
                output_token_count,
            )?;
            if dependent_outputs
                .iter()
                .any(|output| required_outputs.binary_search(output).is_ok())
            {
                return None;
            }
            Some(ValidatedMacroOwnerOutput {
                intrinsic: expansion.owner_output.intrinsic,
                dependent_outputs: dependent_outputs.into_boxed_slice(),
                required_outputs: required_outputs.into_boxed_slice(),
            })
        } else {
            None
        };

        Some(Self {
            ledger,
            definitions: definitions.into_boxed_slice(),
            children: children.into_boxed_slice(),
            owner,
        })
    }
}

/// Reducer-side validation of every declarative output observation in one
/// compiler run. Invalid observations are omitted, so all later consumers fail
/// closed while sharing the same successfully validated ledger.
pub(crate) struct ValidatedDeclarativeOutputs {
    #[cfg(rust_item_dependencies_patched)]
    outputs: FxHashMap<ExpnId, ValidatedDeclarativeOutputFacts>,
}

#[cfg(not(rust_item_dependencies_patched))]
impl ValidatedDeclarativeOutputs {
    pub(crate) fn collect(_tcx: rustc_middle::ty::TyCtxt<'_>) -> Self {
        Self {}
    }
}

#[cfg(rust_item_dependencies_patched)]
impl ValidatedDeclarativeOutputs {
    pub(crate) fn collect(tcx: TyCtxt<'_>) -> Self {
        let origins = &tcx.resolutions(()).macro_invocation_origins;
        let observations = origins
            .items()
            .map(|(&expansion_id, origin)| {
                let output = origin.declarative_expansion.as_ref().and_then(|expansion| {
                    ValidatedDeclarativeOutputFacts::from_declarative_expansion(expansion)
                });
                (
                    expansion_id.expn_hash().local_hash().as_u64(),
                    expansion_id,
                    output,
                )
            })
            .into_sorted_stable_ord_by_key(|entry| &entry.0);
        let mut outputs = FxHashMap::default();
        for (_, expansion_id, output) in observations {
            if let Some(output) = output {
                outputs.insert(expansion_id, output);
            }
        }
        Self { outputs }
    }

    pub(crate) fn output<'a>(
        &'a self,
        origins: &'a UnordMap<ExpnId, MacroInvocationOrigin>,
        expansion_id: ExpnId,
    ) -> Option<ValidatedDeclarativeOutput<'a>> {
        let observation = origins.get(&expansion_id)?.declarative_expansion.as_ref()?;
        Some(ValidatedDeclarativeOutput {
            observation,
            facts: self.outputs.get(&expansion_id)?,
        })
    }

    pub(crate) fn meaning<'a>(
        &'a self,
        origins: &'a UnordMap<ExpnId, MacroInvocationOrigin>,
        expansion_id: ExpnId,
    ) -> Option<ValidatedDeclarativeOutputMeaning<'a>> {
        let output = self.output(origins, expansion_id)?;
        output
            .facts
            .owner
            .as_ref()
            .map(|_| ValidatedDeclarativeOutputMeaning(output))
    }
}

/// A declarative expansion whose output-token identity and every contributor
/// actually used by that output were observed by rustc and whose reducer-side
/// output ledger was validated.
#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(crate) struct ValidatedDeclarativeOutput<'a> {
    observation: &'a MacroDeclarativeExpansion,
    facts: &'a ValidatedDeclarativeOutputFacts,
}

#[cfg(rust_item_dependencies_patched)]
impl<'a> ValidatedDeclarativeOutput<'a> {
    pub(crate) fn observation(self) -> &'a MacroDeclarativeExpansion {
        self.observation
    }

    pub(crate) fn ledger(self) -> &'a ValidatedMacroOutputLedger {
        &self.facts.ledger
    }

    pub(crate) fn definitions(self) -> &'a [ValidatedMacroDefinitionOutput] {
        &self.facts.definitions
    }

    pub(crate) fn children(self) -> &'a [ValidatedMacroChildOutput] {
        &self.facts.children
    }
}

/// A validated declarative output whose residual semantics and direct-product
/// roles were also classified exhaustively.
#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(crate) struct ValidatedDeclarativeOutputMeaning<'a>(ValidatedDeclarativeOutput<'a>);

#[cfg(rust_item_dependencies_patched)]
impl<'a> ValidatedDeclarativeOutputMeaning<'a> {
    pub(crate) fn observation(self) -> &'a MacroDeclarativeExpansion {
        self.0.observation()
    }

    pub(crate) fn ledger(self) -> &'a ValidatedMacroOutputLedger {
        self.0.ledger()
    }

    pub(crate) fn definitions(self) -> &'a [ValidatedMacroDefinitionOutput] {
        self.0.definitions()
    }

    pub(crate) fn children(self) -> &'a [ValidatedMacroChildOutput] {
        self.0.children()
    }

    pub(crate) fn owner(self) -> &'a ValidatedMacroOwnerOutput {
        self.0
            .facts
            .owner
            .as_ref()
            .expect("validated output meaning must include owner roles")
    }
}

#[cfg(rust_item_dependencies_patched)]
fn output_range(range: MacroOutputTokenRange, output_token_count: u32) -> Option<MacroOutputRange> {
    (range.start < range.end && range.end <= output_token_count).then_some(MacroOutputRange {
        start: range.start,
        end: range.end,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn validated_role_ranges(
    ranges: &[MacroOutputTokenRange],
    output_token_count: u32,
) -> Option<Vec<MacroOutputRange>> {
    let ranges = ranges
        .iter()
        .map(|&range| output_range(range, output_token_count))
        .collect::<Option<Vec<_>>>()?;
    ranges
        .windows(2)
        .all(|pair| pair[0] < pair[1])
        .then_some(ranges)
}

pub(crate) fn normalize_discarded_output_ranges(
    mut discarded: Vec<MacroOutputRange>,
    output_token_count: u32,
) -> Option<Vec<MacroOutputRange>> {
    discarded.sort();
    let mut normalized = Vec::<MacroOutputRange>::with_capacity(discarded.len());
    for output in discarded {
        if output.start >= output.end || output.end > output_token_count {
            return None;
        }
        if let Some(previous) = normalized.last()
            && output.start < previous.end
        {
            return None;
        }
        normalized.push(output);
    }
    Some(normalized)
}

fn discarded_outputs_fit_live_products(
    discarded: &[MacroOutputRange],
    output_token_count: u32,
    live: impl IntoIterator<Item = MacroOutputRange>,
) -> bool {
    if discarded
        .iter()
        .any(|range| range.start >= range.end || range.end > output_token_count)
        || discarded.windows(2).any(|pair| pair[0].end > pair[1].start)
    {
        return false;
    }

    // Keep the original ranges as independent source-deletion candidates, but
    // validate containment against their contiguous union. Otherwise two
    // adjacent discarded ranges can jointly cover a live range while evading
    // the single-range equality check below.
    let mut contiguous = Vec::<MacroOutputRange>::with_capacity(discarded.len());
    for &range in discarded {
        if let Some(previous) = contiguous.last_mut()
            && previous.end == range.start
        {
            previous.end = range.end;
        } else {
            contiguous.push(range);
        }
    }

    live.into_iter().all(|live| {
        if live.start >= live.end || live.end > output_token_count {
            return false;
        }
        let first = discarded.partition_point(|range| range.end <= live.start);
        let end = discarded.partition_point(|range| range.start < live.end);
        if first == end {
            return true;
        }
        let first_discarded = discarded[first];
        let last_discarded = discarded[end - 1];
        let containing_union = contiguous.partition_point(|range| range.start <= live.start);
        let fully_discarded =
            containing_union > 0 && contiguous[containing_union - 1].contains(live);
        live.contains(first_discarded) && live.contains(last_discarded) && !fully_discarded
    })
}

pub(crate) fn laminar_output_ranges(ranges: impl IntoIterator<Item = MacroOutputRange>) -> bool {
    let mut ranges = ranges.into_iter().collect::<Vec<_>>();
    if ranges.iter().any(|range| range.start >= range.end) {
        return false;
    }
    ranges.sort_by_key(|range| (range.start, std::cmp::Reverse(range.end)));
    ranges.dedup();
    let mut ancestors = Vec::<MacroOutputRange>::new();
    for range in ranges {
        while ancestors
            .last()
            .is_some_and(|ancestor| ancestor.end <= range.start)
        {
            ancestors.pop();
        }
        if ancestors
            .last()
            .is_some_and(|ancestor| range.end > ancestor.end)
        {
            return false;
        }
        ancestors.push(range);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{MacroOutputRange, ValidatedMacroOutputLedger};

    #[test]
    fn adjacent_discarded_ranges_cannot_jointly_remove_a_live_output() {
        let live = MacroOutputRange { start: 1, end: 4 };
        let discarded = vec![
            MacroOutputRange { start: 1, end: 2 },
            MacroOutputRange { start: 2, end: 4 },
        ];

        assert!(ValidatedMacroOutputLedger::new(5, vec![live], discarded).is_none());
    }

    #[test]
    fn discarded_output_runs_do_not_rescan_nested_live_products() {
        const COUNT: u32 = 32_768;
        let discarded = (1..=COUNT)
            .map(|start| MacroOutputRange {
                start,
                end: start + 1,
            })
            .collect::<Vec<_>>();
        let live = (2..=COUNT + 1)
            .map(|end| MacroOutputRange { start: 0, end })
            .collect::<Vec<_>>();

        assert!(ValidatedMacroOutputLedger::new(COUNT + 1, live, discarded).is_some());
    }
}
