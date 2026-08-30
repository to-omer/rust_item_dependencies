#[cfg(rust_item_dependencies_patched)]
use std::collections::{BTreeMap, BTreeSet};

#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{MacroImplementationKind, TyCtxt};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::ExpnId;

#[cfg(rust_item_dependencies_patched)]
use crate::macro_output::ValidatedDeclarativeOutputs;
#[cfg(rust_item_dependencies_patched)]
use crate::source::syntax::{ParserTokenRewriteGuard, SourceSyntaxError, tokenize_parser_tokens};
#[cfg(rust_item_dependencies_patched)]
use crate::source::{
    ByteRange, CfgState, DeclarativeContributorParent, DeclarativeGenerationParentState,
    EditableMacroSource, MacroRuleSelectionIndex, PendingUnit, SourceError, SourceInventory,
    SourceUnitId, WrittenUnitKind, declarative_generation_parent, original_span_range,
    resolve_declarative_contributor_parent, validate_macro_rule_facts,
};

#[cfg(rust_item_dependencies_patched)]
use super::capture::{
    PendingCaptureInputFacts, TemplateCaptureObservation, capture_slot_drafts_for_rule,
};
#[cfg(rust_item_dependencies_patched)]
use super::repetition::{MatcherRepetitionDraft, PendingRepetitionFacts, matcher_repetitions};
#[cfg(rust_item_dependencies_patched)]
use super::template::{
    TemplateCandidate, blocked_range_index, classify_template_candidates, range_index_contains,
    template_candidates_for_expansion,
};
#[cfg(rust_item_dependencies_patched)]
use super::validation::{repetition_key, validate_declarative_macro_source_facts};
#[cfg(rust_item_dependencies_patched)]
use super::{
    MacroCaptureInputSourceFacts, MacroCaptureSlotSourceFacts, MacroRepetitionElementSourceFacts,
    MacroRepetitionSourceFacts, MacroTemplateSourceFacts,
};

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct PendingTemplateFacts {
    unit: u32,
    rule: u32,
}

#[cfg(rust_item_dependencies_patched)]
struct PendingCaptureSlotFacts {
    unit: u32,
    rule: u32,
    matcher_capture_range: ByteRange,
    trigger_units: Vec<u32>,
    inputs: Vec<PendingCaptureInputFacts>,
}

/// Compiler observations that are complete enough to draft source refinement.
#[cfg(rust_item_dependencies_patched)]
pub(super) struct CompilerObservations<'tcx> {
    ordered: Vec<(u64, ExpnId, &'tcx rustc_middle::ty::MacroInvocationOrigin)>,
    selected_rules: FxHashMap<ExpnId, Option<SourceUnitId>>,
    eligible: FxHashSet<ExpnId>,
    complete_rules: BTreeMap<SourceUnitId, bool>,
    candidates: BTreeSet<TemplateCandidate>,
    capture_observations: FxHashMap<ExpnId, TemplateCaptureObservation>,
}

/// Source units and compiler-backed facts before stable source IDs are assigned.
#[cfg(rust_item_dependencies_patched)]
pub(super) struct RefinementDraft {
    pending: Vec<PendingUnit>,
    templates: Vec<PendingTemplateFacts>,
    capture_slots: Vec<PendingCaptureSlotFacts>,
    repetitions: Vec<PendingRepetitionFacts>,
}

#[cfg(rust_item_dependencies_patched)]
pub(super) fn validate_refinement_inventory(
    inventory: &SourceInventory,
) -> Result<(), SourceError> {
    use super::super::{
        validate_derive_target_facts, validate_inventory, validate_ownerless_attribute_invocations,
    };

    if !inventory.macro_templates.is_empty()
        || !inventory.macro_capture_slots.is_empty()
        || !inventory.macro_repetitions.is_empty()
    {
        return Err(SourceError::InvalidInventory);
    }
    validate_inventory(&inventory.original, &inventory.units, &inventory.pieces)?;
    validate_derive_target_facts(&inventory.units, &inventory.derive_targets)?;
    validate_macro_rule_facts(&inventory.units, &inventory.macro_rules)?;
    validate_ownerless_attribute_invocations(
        &inventory.units,
        &inventory.ownerless_attribute_invocations,
    )
}

#[cfg(rust_item_dependencies_patched)]
impl<'tcx> CompilerObservations<'tcx> {
    pub(super) fn collect(
        compiler: &Compiler,
        tcx: TyCtxt<'tcx>,
        inventory: &SourceInventory,
        outputs: &ValidatedDeclarativeOutputs,
    ) -> Result<Self, SourceError> {
        let resolutions = tcx.resolutions(());
        let origins = &resolutions.macro_invocation_origins;
        let source_resolver = crate::source::EditableMacroSourceResolver::new(origins);
        let ordered = origins
            .items()
            .map(|(&expansion, origin)| {
                (
                    expansion.expn_hash().local_hash().as_u64(),
                    expansion,
                    origin,
                )
            })
            .into_sorted_stable_ord_by_key(|entry| &entry.0);
        let rule_index = inventory.macro_rule_selection_index()?;
        let implementations = ordered
            .iter()
            .map(|(_, expansion, origin)| (*expansion, origin.implementation_kind))
            .collect::<FxHashMap<_, _>>();
        let mut selected_rules = FxHashMap::default();
        for &(_, expansion_id, origin) in &ordered {
            if origin.implementation_kind != MacroImplementationKind::Declarative {
                continue;
            }
            let selected = selected_written_rule(compiler, tcx, inventory, &rule_index, origin)?;
            if selected_rules.insert(expansion_id, selected).is_some() {
                return Err(SourceError::IncompleteMacroRuleObservation);
            }
        }
        let eligible = eligible_declarative_expansions(
            compiler,
            inventory,
            outputs,
            origins,
            &source_resolver,
            &ordered,
            &implementations,
            &selected_rules,
        )?;

        // A template range is shared by every invocation selecting that rule.
        // If one invocation is incomplete, keep the whole rule unsplit.
        let mut complete_rules = BTreeMap::<SourceUnitId, bool>::new();
        let mut candidates = BTreeSet::<TemplateCandidate>::new();
        let mut blocked_repetition_contents = BTreeSet::<(SourceUnitId, ByteRange)>::new();
        let mut capture_observations = FxHashMap::<ExpnId, TemplateCaptureObservation>::default();
        let parser_tokens =
            tokenize_parser_tokens(&inventory.original).map_err(|error| match error {
                SourceSyntaxError::SourceTooLarge => SourceError::SourceTooLarge,
                SourceSyntaxError::InvalidRange | SourceSyntaxError::InvalidSyntax => {
                    SourceError::IncompleteDeclarativeMacroObservation
                }
            })?;
        let rewrite_guard =
            ParserTokenRewriteGuard::new(&inventory.original).map_err(|error| match error {
                SourceSyntaxError::SourceTooLarge => SourceError::SourceTooLarge,
                SourceSyntaxError::InvalidRange | SourceSyntaxError::InvalidSyntax => {
                    SourceError::IncompleteDeclarativeMacroObservation
                }
            })?;
        for (_, expansion_id, origin) in &ordered {
            if origin.implementation_kind != MacroImplementationKind::Declarative {
                continue;
            }
            let Some(rule) = selected_rules
                .get(expansion_id)
                .copied()
                .ok_or(SourceError::IncompleteMacroRuleObservation)?
            else {
                continue;
            };
            let complete = eligible.contains(expansion_id);
            *complete_rules.entry(rule).or_insert(true) &= complete;
            if !complete {
                continue;
            }
            let Some(expansion) = outputs.meaning(origins, *expansion_id) else {
                complete_rules.insert(rule, false);
                continue;
            };
            let Some(observed) = template_candidates_for_expansion(
                compiler,
                tcx,
                inventory,
                &parser_tokens,
                &rewrite_guard,
                rule,
                expansion,
            )?
            else {
                complete_rules.insert(rule, false);
                continue;
            };
            candidates.extend(observed.candidates);
            blocked_repetition_contents.extend(
                observed
                    .blocked_repetition_contents
                    .into_iter()
                    .map(|range| (rule, range)),
            );
            if let Some(captures) = observed.captures
                && capture_observations
                    .insert(*expansion_id, captures)
                    .is_some()
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
        }
        let blocked_repetition_contents =
            blocked_range_index(blocked_repetition_contents.into_iter())?;
        candidates.retain(|candidate| {
            complete_rules.get(&candidate.rule) == Some(&true)
                && !range_index_contains(
                    &blocked_repetition_contents,
                    candidate.rule,
                    candidate.range,
                )
        });

        Ok(Self {
            ordered,
            selected_rules,
            eligible,
            complete_rules,
            candidates,
            capture_observations,
        })
    }
}

#[cfg(rust_item_dependencies_patched)]
impl RefinementDraft {
    pub(super) fn build(
        compiler: &Compiler,
        tcx: TyCtxt<'_>,
        inventory: &SourceInventory,
        outputs: &ValidatedDeclarativeOutputs,
        observations: &CompilerObservations<'_>,
    ) -> Result<Self, SourceError> {
        use super::super::{MacroRuleSourceFacts, PendingUnit, pending_units};

        let origins = &tcx.resolutions(()).macro_invocation_origins;
        let source_resolver = crate::source::EditableMacroSourceResolver::new(origins);
        let first_refined_rules = inventory
            .macro_rules
            .iter()
            .filter_map(|facts| match facts {
                MacroRuleSourceFacts::Whole { .. } => None,
                MacroRuleSourceFacts::Refined { rules, .. } => rules.first().copied(),
            })
            .collect::<BTreeSet<_>>();
        let sole_first_rule_selections = inventory
            .macro_rules
            .iter()
            .filter_map(|facts| match facts {
                MacroRuleSourceFacts::Refined {
                    rules,
                    observed_selections,
                    ..
                } => rules.first().copied().and_then(|first| {
                    (!observed_selections.is_empty()
                        && observed_selections
                            .iter()
                            .all(|selection| *selection == first))
                    .then_some((first, observed_selections.len()))
                }),
                MacroRuleSourceFacts::Whole { .. } => None,
            })
            .collect::<BTreeMap<_, _>>();

        let (mut pending, _) = pending_units(&inventory.units);
        let mut next_temporary =
            u32::try_from(pending.len()).map_err(|_| SourceError::SourceTooLarge)?;
        let template_layout = classify_template_candidates(&observations.candidates)?;
        let mut templates = Vec::new();
        let mut template_units = BTreeMap::<(SourceUnitId, ByteRange), u32>::new();
        for (candidate, _, _) in &template_layout {
            let temporary_id = next_temporary;
            next_temporary = next_temporary
                .checked_add(1)
                .ok_or(SourceError::SourceTooLarge)?;
            if template_units
                .insert((candidate.rule, candidate.range), temporary_id)
                .is_some()
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
        }
        for (candidate, kind, parent_range) in &template_layout {
            let temporary_id = template_units[&(candidate.rule, candidate.range)];
            let parent = if let Some(range) = parent_range {
                *template_units
                    .get(&(candidate.rule, *range))
                    .ok_or(SourceError::IncompleteDeclarativeMacroObservation)?
            } else {
                candidate.rule.0
            };
            pending.push(PendingUnit {
                temporary_id,
                kind: *kind,
                full_range: candidate.range,
                parent: Some(parent),
                cfg_state: CfgState::Active,
                atomic_representative: temporary_id,
                syntax_ordinal: temporary_id,
            });
            templates.push(PendingTemplateFacts {
                unit: temporary_id,
                rule: candidate.rule.0,
            });
        }

        let mut selected_expansions_by_rule = BTreeMap::<SourceUnitId, Vec<ExpnId>>::new();
        for (_, expansion, _) in &observations.ordered {
            if let Some(Some(rule)) = observations.selected_rules.get(expansion) {
                selected_expansions_by_rule
                    .entry(*rule)
                    .or_default()
                    .push(*expansion);
            }
        }
        let mut template_candidates_by_rule =
            BTreeMap::<SourceUnitId, Vec<(ByteRange, u32)>>::new();
        for (candidate, _, _) in &template_layout {
            template_candidates_by_rule
                .entry(candidate.rule)
                .or_default()
                .push((
                    candidate.range,
                    template_units[&(candidate.rule, candidate.range)],
                ));
        }
        for candidates in template_candidates_by_rule.values_mut() {
            candidates.sort_by_key(|(range, _)| (range.start, std::cmp::Reverse(range.end)));
        }

        let mut capture_slots = Vec::new();
        for (rule, expected_selections) in sole_first_rule_selections {
            if observations.complete_rules.get(&rule) != Some(&true) {
                continue;
            }
            let Some(drafts) = capture_slot_drafts_for_rule(
                compiler,
                inventory,
                &source_resolver,
                selected_expansions_by_rule
                    .get(&rule)
                    .map(Vec::as_slice)
                    .unwrap_or_default(),
                &observations.eligible,
                &observations.capture_observations,
                template_candidates_by_rule
                    .get(&rule)
                    .map(Vec::as_slice)
                    .unwrap_or_default(),
                expected_selections,
            )?
            else {
                continue;
            };
            for draft in drafts {
                let temporary_id = next_temporary;
                next_temporary = next_temporary
                    .checked_add(1)
                    .ok_or(SourceError::SourceTooLarge)?;
                pending.push(PendingUnit {
                    temporary_id,
                    kind: WrittenUnitKind::NestedItem,
                    full_range: draft.matcher_deletion_range,
                    parent: Some(rule.0),
                    cfg_state: CfgState::Active,
                    atomic_representative: temporary_id,
                    syntax_ordinal: temporary_id,
                });
                capture_slots.push(PendingCaptureSlotFacts {
                    unit: temporary_id,
                    rule: rule.0,
                    matcher_capture_range: draft.matcher_capture_range,
                    trigger_units: draft.trigger_units,
                    inputs: draft.inputs,
                });
            }
        }

        let mut repetitions = Vec::new();
        for &(_, expansion_id, origin) in &observations.ordered {
            if origin.implementation_kind != MacroImplementationKind::Declarative
                || !observations.eligible.contains(&expansion_id)
            {
                continue;
            }
            let Some(expansion) = outputs
                .meaning(origins, expansion_id)
                .map(|validated| validated.observation())
                .filter(|expansion| expansion.complete)
            else {
                continue;
            };
            let Some(rule) = observations
                .selected_rules
                .get(&expansion_id)
                .copied()
                .ok_or(SourceError::IncompleteMacroRuleObservation)?
            else {
                continue;
            };
            if !first_refined_rules.contains(&rule) {
                // Deleting matcher input from a later rule could make an
                // earlier rule match. Template output has no such restriction.
                continue;
            }
            let Some(editable) = source_resolver.resolve(compiler, inventory, expansion_id)? else {
                continue;
            };
            let Some(exact_invocation) = editable.exact_invocation else {
                // Editing a late-parsed invocation would rewrite the enclosing
                // macro's opaque token input without its own ledger.
                continue;
            };
            let invocation = inventory
                .units
                .get(exact_invocation.0 as usize)
                .filter(|unit| {
                    unit.id == exact_invocation
                        && unit.kind == WrittenUnitKind::MacroInvocation
                        && unit.cfg_state == CfgState::Active
                })
                .ok_or(SourceError::InvalidInventory)?;
            let Some(matcher) = expansion
                .matcher
                .as_ref()
                .filter(|matcher| matcher.invocation_refinement_safe)
            else {
                continue;
            };
            let Some(observed) = matcher_repetitions(
                compiler,
                inventory,
                invocation,
                rule,
                matcher,
                next_temporary,
            )?
            else {
                continue;
            };
            let MatcherRepetitionDraft {
                units,
                facts,
                next_temporary: observed_next,
            } = observed;
            pending.extend(units);
            repetitions.extend(facts);
            next_temporary = observed_next;
        }

        Ok(Self {
            pending,
            templates,
            capture_slots,
            repetitions,
        })
    }

    pub(super) fn commit(self, inventory: &mut SourceInventory) -> Result<(), SourceError> {
        use super::super::{
            MacroRuleSourceFacts, finish_pending_units, own_lexical_pieces,
            remap_derive_target_facts, validate_derive_target_facts, validate_inventory,
            validate_ownerless_attribute_invocations,
        };

        let Self {
            pending,
            templates,
            capture_slots,
            repetitions,
        } = self;
        let (units, id_map) = finish_pending_units(pending)?;
        let derive_targets = remap_derive_target_facts(&inventory.derive_targets, &id_map)?;
        let macro_rules = inventory
            .macro_rules
            .iter()
            .map(|facts| match facts {
                MacroRuleSourceFacts::Whole { definition } => Ok(MacroRuleSourceFacts::Whole {
                    definition: id_map[&definition.0],
                }),
                MacroRuleSourceFacts::Refined {
                    definition,
                    rules,
                    observed_selections,
                } => Ok(MacroRuleSourceFacts::Refined {
                    definition: id_map[&definition.0],
                    rules: rules.iter().map(|rule| id_map[&rule.0]).collect(),
                    observed_selections: observed_selections
                        .iter()
                        .map(|rule| id_map[&rule.0])
                        .collect(),
                }),
            })
            .collect::<Result<Vec<_>, SourceError>>()?;
        let mut templates = templates
            .into_iter()
            .map(|facts| MacroTemplateSourceFacts {
                unit: id_map[&facts.unit],
                rule: id_map[&facts.rule],
            })
            .collect::<Vec<_>>();
        templates.sort();
        let mut repetitions = repetitions
            .into_iter()
            .map(|facts| MacroRepetitionSourceFacts {
                invocation: id_map[&facts.invocation],
                rule: id_map[&facts.rule],
                matcher_range: facts.matcher_range,
                parent: id_map[&facts.parent],
                repetition_path: facts.repetition_path,
                input_range: facts.input_range,
                elements: facts
                    .elements
                    .into_iter()
                    .map(|element| MacroRepetitionElementSourceFacts {
                        unit: id_map[&element.unit],
                        separator_after: element.separator_after,
                    })
                    .collect(),
                minimum: facts.minimum,
                maximum: facts.maximum,
            })
            .collect::<Vec<_>>();
        let mut capture_slots = capture_slots
            .into_iter()
            .map(|facts| MacroCaptureSlotSourceFacts {
                unit: id_map[&facts.unit],
                rule: id_map[&facts.rule],
                matcher_capture_range: facts.matcher_capture_range,
                trigger_units: facts
                    .trigger_units
                    .into_iter()
                    .map(|trigger| id_map[&trigger])
                    .collect(),
                inputs: facts
                    .inputs
                    .into_iter()
                    .map(|input| MacroCaptureInputSourceFacts {
                        invocation: id_map[&input.invocation],
                        capture_range: input.capture_range,
                        deletion_range: input.deletion_range,
                    })
                    .collect(),
            })
            .collect::<Vec<_>>();
        capture_slots.sort();
        repetitions.sort_by(|left, right| repetition_key(left).cmp(&repetition_key(right)));
        let mut ownerless_attribute_invocations = inventory
            .ownerless_attribute_invocations
            .iter()
            .map(|invocation| id_map[&invocation.0])
            .collect::<Vec<_>>();
        ownerless_attribute_invocations.sort();
        let pieces = own_lexical_pieces(&inventory.original, &units)?;
        validate_inventory(&inventory.original, &units, &pieces)?;
        validate_derive_target_facts(&units, &derive_targets)?;
        validate_ownerless_attribute_invocations(&units, &ownerless_attribute_invocations)?;
        validate_declarative_macro_source_facts(
            &inventory.original,
            &units,
            &macro_rules,
            &templates,
            &capture_slots,
            &repetitions,
        )?;

        inventory.units = units;
        inventory.pieces = pieces;
        inventory.derive_targets = derive_targets;
        inventory.macro_rules = macro_rules;
        inventory.macro_templates = templates;
        inventory.macro_capture_slots = capture_slots;
        inventory.macro_repetitions = repetitions;
        inventory.ownerless_attribute_invocations = ownerless_attribute_invocations;
        Ok(())
    }
}

#[cfg(rust_item_dependencies_patched)]
fn eligible_declarative_expansions(
    compiler: &Compiler,
    inventory: &SourceInventory,
    outputs: &ValidatedDeclarativeOutputs,
    origins: &rustc_data_structures::unord::UnordMap<
        ExpnId,
        rustc_middle::ty::MacroInvocationOrigin,
    >,
    source_resolver: &crate::source::EditableMacroSourceResolver<'_>,
    ordered: &[(u64, ExpnId, &rustc_middle::ty::MacroInvocationOrigin)],
    implementations: &FxHashMap<ExpnId, MacroImplementationKind>,
    selected_rules: &FxHashMap<ExpnId, Option<SourceUnitId>>,
) -> Result<FxHashSet<ExpnId>, SourceError> {
    let mut complete_parents = FxHashSet::default();
    let mut child_links = FxHashMap::default();
    for &(_, parent, _) in ordered {
        let Some(observation) = outputs.meaning(origins, parent) else {
            continue;
        };
        complete_parents.insert(parent);
        for child in observation.children() {
            match child_links.entry((parent, child.expansion())) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(true);
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry.insert(false);
                }
            }
        }
    }

    let mut roots = Vec::new();
    let mut children = FxHashMap::<ExpnId, Vec<ExpnId>>::default();
    for &(_, expansion_id, origin) in ordered {
        if origin.implementation_kind != MacroImplementationKind::Declarative
            || selected_rules
                .get(&expansion_id)
                .copied()
                .ok_or(SourceError::IncompleteMacroRuleObservation)?
                .is_none()
            || outputs.meaning(origins, expansion_id).is_none()
        {
            continue;
        }
        let editable = source_resolver.resolve(compiler, inventory, expansion_id)?;
        let parent = declarative_macro_parent(
            expansion_id,
            origin,
            editable,
            implementations,
            selected_rules,
            &complete_parents,
            &child_links,
        );
        match parent {
            DeclarativeContributorParent::Root => roots.push(expansion_id),
            DeclarativeContributorParent::Parent(parent) => {
                children.entry(parent).or_default().push(expansion_id);
            }
            DeclarativeContributorParent::Incomplete => {}
        }
    }

    let mut eligible = FxHashSet::default();
    let mut pending = std::collections::VecDeque::from(roots);
    while let Some(expansion) = pending.pop_front() {
        if !eligible.insert(expansion) {
            continue;
        }
        if let Some(generated) = children.get(&expansion) {
            pending.extend(generated.iter().copied());
        }
    }
    Ok(eligible)
}

#[cfg(rust_item_dependencies_patched)]
fn declarative_macro_parent(
    expansion: ExpnId,
    origin: &rustc_middle::ty::MacroInvocationOrigin,
    editable: Option<EditableMacroSource>,
    implementations: &FxHashMap<ExpnId, MacroImplementationKind>,
    selected_rules: &FxHashMap<ExpnId, Option<SourceUnitId>>,
    complete_parents: &FxHashSet<ExpnId>,
    child_links: &FxHashMap<(ExpnId, ExpnId), bool>,
) -> DeclarativeContributorParent<ExpnId> {
    let source_call = expansion.expn_data().call_site.ctxt().outer_expn();
    let discovered_in = (origin.discovered_in_expansion != ExpnId::root())
        .then_some(origin.discovered_in_expansion);
    let source_call =
        (source_call != ExpnId::root() && source_call != expansion).then_some(source_call);
    let parent = declarative_generation_parent(discovered_in, source_call);
    let parent_state = parent.map(|parent| {
        if !matches!(parent.expn_data().kind, rustc_span::ExpnKind::Macro(..)) {
            return DeclarativeGenerationParentState::Opaque;
        }
        match implementations.get(&parent) {
            Some(MacroImplementationKind::Declarative) => match parent.expn_data().macro_def_id {
                Some(definition) if !definition.is_local() => {
                    DeclarativeGenerationParentState::Opaque
                }
                Some(_) if selected_rules.get(&parent).is_some_and(Option::is_some) => {
                    DeclarativeGenerationParentState::RefinedLocal {
                        link_complete: complete_parents.contains(&parent)
                            && child_links.get(&(parent, expansion)) == Some(&true),
                    }
                }
                _ => DeclarativeGenerationParentState::LocalIncomplete,
            },
            Some(MacroImplementationKind::Builtin | MacroImplementationKind::Procedural) => {
                DeclarativeGenerationParentState::Opaque
            }
            Some(
                MacroImplementationKind::Legacy
                | MacroImplementationKind::InertAttribute
                | MacroImplementationKind::GlobDelegation,
            ) => DeclarativeGenerationParentState::Opaque,
            None => DeclarativeGenerationParentState::LocalIncomplete,
        }
    });
    resolve_declarative_contributor_parent(parent, editable.is_some(), parent_state)
}

#[cfg(rust_item_dependencies_patched)]
fn selected_written_rule(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &SourceInventory,
    rule_index: &MacroRuleSelectionIndex,
    origin: &rustc_middle::ty::MacroInvocationOrigin,
) -> Result<Option<SourceUnitId>, SourceError> {
    let Some(selection) = origin.selected_macro_rule else {
        return Ok(None);
    };
    let resolutions = tcx.resolutions(());
    if resolutions
        .expn_that_defined
        .contains_key(&selection.definition)
    {
        return Ok(None);
    }
    let rule = resolutions
        .macro_rules_definitions
        .get(&selection.definition)
        .and_then(|rules| rules.get(selection.rule_index))
        .ok_or(SourceError::IncompleteMacroRuleObservation)?;
    if rule.start_span.from_expansion() || rule.end_span.from_expansion() {
        return Ok(None);
    }
    let start = original_span_range(compiler, &inventory.offsets, rule.start_span)?;
    let end = original_span_range(compiler, &inventory.offsets, rule.end_span)?;
    let range = ByteRange {
        start: start.start,
        end: end.end,
    };
    rule_index.selected_rule(range)
}
