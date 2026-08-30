use std::collections::{BTreeMap, BTreeSet};
#[cfg(any(rust_item_dependencies_patched, test))]
use std::hash::Hash;

#[cfg(any(rust_item_dependencies_patched, test))]
use rustc_data_structures::fx::FxHashMap;
#[cfg(rust_item_dependencies_patched)]
use rustc_data_structures::fx::FxHashSet;
#[cfg(rust_item_dependencies_patched)]
use rustc_interface::interface::Compiler;
use rustc_lexer::{FrontmatterAllowed, tokenize};
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{
    MacroDeclarativeExpansion, MacroImplementationKind, MacroInputTokenRange,
    MacroMatcherObservation, MacroOutputTokenRange, MacroTranscriberComponentKind, TyCtxt,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::ExpnId;

use super::syntax::ParserTokenRewriteGuard;
#[cfg(rust_item_dependencies_patched)]
use super::syntax::SourceSyntaxError;
use super::syntax::{ParserToken, is_trivia, tokenize_parser_tokens};
use super::{
    ByteRange, CfgState, MacroRuleSourceFacts, SourceError, SourceUnitId, WrittenUnit,
    WrittenUnitKind, validate_macro_rule_facts,
};
#[cfg(rust_item_dependencies_patched)]
use super::{DeclarativeContributorParent, DeclarativeGenerationParentState};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroTemplateSourceFacts {
    pub unit: SourceUnitId,
    pub rule: SourceUnitId,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroCaptureInputSourceFacts {
    pub invocation: SourceUnitId,
    pub capture_range: ByteRange,
    pub deletion_range: ByteRange,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroCaptureSlotSourceFacts {
    pub unit: SourceUnitId,
    pub rule: SourceUnitId,
    pub matcher_capture_range: ByteRange,
    pub trigger_units: Vec<SourceUnitId>,
    pub inputs: Vec<MacroCaptureInputSourceFacts>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRepetitionElementSourceFacts {
    pub unit: SourceUnitId,
    pub separator_after: Option<ByteRange>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MacroRepetitionSourceFacts {
    pub invocation: SourceUnitId,
    pub rule: SourceUnitId,
    pub matcher_range: ByteRange,
    pub parent: SourceUnitId,
    pub repetition_path: Vec<u32>,
    pub input_range: ByteRange,
    pub elements: Vec<MacroRepetitionElementSourceFacts>,
    pub minimum: u32,
    pub maximum: Option<u32>,
}

/// A declarative expansion whose output-token identity and every contributor
/// actually used by that output were observed by rustc.
///
/// This proves definition identity and contributor provenance only. Semantic
/// output classification and source splitting require
/// `ValidatedDeclarativeOutputMeaning`.
#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(crate) struct ValidatedDeclarativeOutput<'a>(&'a MacroDeclarativeExpansion);

#[cfg(rust_item_dependencies_patched)]
impl<'a> ValidatedDeclarativeOutput<'a> {
    pub(crate) fn new(expansion: &'a MacroDeclarativeExpansion) -> Option<Self> {
        expansion
            .output_provenance_complete
            .then_some(Self(expansion))
    }

    pub(crate) fn observation(self) -> &'a MacroDeclarativeExpansion {
        self.0
    }
}

/// A validated declarative output whose residual semantics and direct-product
/// roles were also classified exhaustively. Token provenance alone remains
/// useful for definition identity, but cannot justify splitting or lowering
/// a semantic product ledger.
#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
pub(crate) struct ValidatedDeclarativeOutputMeaning<'a>(ValidatedDeclarativeOutput<'a>);

#[cfg(rust_item_dependencies_patched)]
impl<'a> ValidatedDeclarativeOutputMeaning<'a> {
    pub(crate) fn new(expansion: &'a MacroDeclarativeExpansion) -> Option<Self> {
        if !expansion.owner_output.complete {
            return None;
        }
        Some(Self(ValidatedDeclarativeOutput::new(expansion)?))
    }

    pub(crate) fn observation(self) -> &'a MacroDeclarativeExpansion {
        self.0.observation()
    }
}

/// A declarative expansion whose matcher facts are complete in addition to
/// its validated output provenance.
#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct ValidatedDeclarativeMatcher<'a>(ValidatedDeclarativeOutputMeaning<'a>);

#[cfg(rust_item_dependencies_patched)]
impl<'a> ValidatedDeclarativeMatcher<'a> {
    fn new(expansion: &'a MacroDeclarativeExpansion) -> Option<Self> {
        if !expansion.complete {
            return None;
        }
        Some(Self(ValidatedDeclarativeOutputMeaning::new(expansion)?))
    }

    fn observation(self) -> &'a MacroDeclarativeExpansion {
        self.0.observation()
    }
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TemplateCandidate {
    rule: SourceUnitId,
    range: ByteRange,
    is_use: bool,
}

#[cfg(rust_item_dependencies_patched)]
struct TemplateExpansionCandidates {
    candidates: Vec<TemplateCandidate>,
    blocked_repetition_contents: Vec<ByteRange>,
    captures: Option<TemplateCaptureObservation>,
}

#[cfg(rust_item_dependencies_patched)]
struct TemplateCaptureObservation {
    components: BTreeSet<ByteRange>,
    component_captures: BTreeMap<ByteRange, ByteRange>,
    slots: Vec<ObservedCaptureSlot>,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct ObservedCaptureSlot {
    matcher_capture_range: ByteRange,
    matcher_deletion_range: ByteRange,
    input_capture_range: ByteRange,
    input_deletion_range: ByteRange,
}

#[cfg(rust_item_dependencies_patched)]
struct CaptureSlotDraft {
    matcher_capture_range: ByteRange,
    matcher_deletion_range: ByteRange,
    trigger_units: Vec<u32>,
    inputs: Vec<PendingCaptureInputFacts>,
}

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

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct PendingCaptureInputFacts {
    invocation: u32,
    capture_range: ByteRange,
    deletion_range: ByteRange,
}

#[cfg(rust_item_dependencies_patched)]
#[derive(Clone, Copy)]
struct PendingElementFacts {
    unit: u32,
    separator_after: Option<ByteRange>,
}

#[cfg(rust_item_dependencies_patched)]
struct PendingRepetitionFacts {
    invocation: u32,
    rule: u32,
    matcher_range: ByteRange,
    parent: u32,
    repetition_path: Vec<u32>,
    input_range: ByteRange,
    elements: Vec<PendingElementFacts>,
    minimum: u32,
    maximum: Option<u32>,
}

/// Refines only source ranges whose complete correspondence to one observed
/// local declarative expansion is available. Compiler product constraints are
/// lowered separately after definition and expansion identities are known.
#[cfg(rust_item_dependencies_patched)]
pub(crate) fn refine_declarative_macros_from_compiler(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &mut super::SourceInventory,
) -> Result<(), SourceError> {
    use super::{
        MacroRuleSourceFacts, PendingUnit, finish_pending_units, own_lexical_pieces, pending_units,
        remap_derive_target_facts, validate_derive_target_facts, validate_inventory,
        validate_macro_rule_facts, validate_ownerless_attribute_invocations,
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
    )?;

    let resolutions = tcx.resolutions(());
    let origins = &resolutions.macro_invocation_origins;
    let source_resolver = super::EditableMacroSourceResolver::new(origins);
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
        &source_resolver,
        &ordered,
        &implementations,
        &selected_rules,
    )?;

    // A template range is shared by every invocation selecting that rule. If
    // even one such invocation is not completely observed, leave the whole
    // rule unsplit so that the conservative rule binding protects its source.
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
        let Some(expansion) = origin.declarative_expansion.as_ref() else {
            continue;
        };
        let observed = template_candidates_for_expansion(
            compiler,
            tcx,
            inventory,
            &parser_tokens,
            &rewrite_guard,
            rule,
            expansion,
        )?;
        let Some(observed) = observed else {
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
    let blocked_repetition_contents = blocked_range_index(blocked_repetition_contents.into_iter())?;
    candidates.retain(|candidate| {
        complete_rules.get(&candidate.rule) == Some(&true)
            && !range_index_contains(
                &blocked_repetition_contents,
                candidate.rule,
                candidate.range,
            )
    });
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
    let template_layout = classify_template_candidates(&candidates)?;
    let mut pending_templates = Vec::new();
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
        pending_templates.push(PendingTemplateFacts {
            unit: temporary_id,
            rule: candidate.rule.0,
        });
    }

    let mut selected_expansions_by_rule = BTreeMap::<SourceUnitId, Vec<ExpnId>>::new();
    for (_, expansion, _) in &ordered {
        if let Some(Some(rule)) = selected_rules.get(expansion) {
            selected_expansions_by_rule
                .entry(*rule)
                .or_default()
                .push(*expansion);
        }
    }
    let mut template_candidates_by_rule =
        BTreeMap::<SourceUnitId, Vec<(TemplateCandidate, u32)>>::new();
    for (candidate, _, _) in &template_layout {
        template_candidates_by_rule
            .entry(candidate.rule)
            .or_default()
            .push((
                *candidate,
                template_units[&(candidate.rule, candidate.range)],
            ));
    }
    for candidates in template_candidates_by_rule.values_mut() {
        candidates.sort_by_key(|(candidate, _)| {
            (
                candidate.range.start,
                std::cmp::Reverse(candidate.range.end),
            )
        });
    }

    let mut pending_capture_slots = Vec::new();
    for (rule, expected_selections) in sole_first_rule_selections {
        if complete_rules.get(&rule) != Some(&true) {
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
            &eligible,
            &capture_observations,
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
            pending_capture_slots.push(PendingCaptureSlotFacts {
                unit: temporary_id,
                rule: rule.0,
                matcher_capture_range: draft.matcher_capture_range,
                trigger_units: draft.trigger_units,
                inputs: draft.inputs,
            });
        }
    }

    let mut pending_repetitions = Vec::new();
    for (_, expansion_id, origin) in ordered {
        if origin.implementation_kind != MacroImplementationKind::Declarative {
            continue;
        }
        if !eligible.contains(&expansion_id) {
            continue;
        }
        let Some(expansion) = origin
            .declarative_expansion
            .as_ref()
            .and_then(|expansion| ValidatedDeclarativeMatcher::new(expansion))
            .map(ValidatedDeclarativeMatcher::observation)
        else {
            continue;
        };
        let Some(rule) = selected_rules
            .get(&expansion_id)
            .copied()
            .ok_or(SourceError::IncompleteMacroRuleObservation)?
        else {
            continue;
        };
        if !first_refined_rules.contains(&rule) {
            // Deleting matcher input from a later rule could make an earlier
            // rule match. Template output does not have this restriction.
            continue;
        }
        let Some(editable) = source_resolver.resolve(compiler, inventory, expansion_id)? else {
            continue;
        };
        let Some(exact_invocation) = editable.exact_invocation else {
            // A late-parsed call can have a written source anchor while being
            // contained in an enclosing macro invocation. Its template is
            // still refinable, but editing matcher input would rewrite the
            // enclosing macro's opaque token input without its own ledger.
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
        let Some(repetitions) = matcher_repetitions(
            compiler,
            inventory,
            invocation,
            rule,
            matcher,
            &mut pending,
            &mut next_temporary,
        )?
        else {
            continue;
        };
        pending_repetitions.extend(repetitions);
    }

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
    let mut templates = pending_templates
        .into_iter()
        .map(|facts| MacroTemplateSourceFacts {
            unit: id_map[&facts.unit],
            rule: id_map[&facts.rule],
        })
        .collect::<Vec<_>>();
    templates.sort();
    let mut repetitions = pending_repetitions
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
    let mut capture_slots = pending_capture_slots
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

#[cfg(rust_item_dependencies_patched)]
fn eligible_declarative_expansions(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    source_resolver: &super::EditableMacroSourceResolver<'_>,
    ordered: &[(u64, ExpnId, &rustc_middle::ty::MacroInvocationOrigin)],
    implementations: &FxHashMap<ExpnId, MacroImplementationKind>,
    selected_rules: &FxHashMap<ExpnId, Option<SourceUnitId>>,
) -> Result<FxHashSet<ExpnId>, SourceError> {
    let mut complete_parents = FxHashSet::default();
    let mut child_links = FxHashMap::default();
    for &(_, parent, origin) in ordered {
        let Some(observation) = origin
            .declarative_expansion
            .as_ref()
            .and_then(|observation| ValidatedDeclarativeOutputMeaning::new(observation))
            .map(ValidatedDeclarativeOutputMeaning::observation)
        else {
            continue;
        };
        complete_parents.insert(parent);
        for child in &observation.child_expansions {
            record_unique_valid_link(
                &mut child_links,
                parent,
                child.expansion,
                valid_output_range(child.output, observation.output_tokens.len()),
            );
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
            || origin
                .declarative_expansion
                .as_ref()
                .and_then(|expansion| ValidatedDeclarativeOutputMeaning::new(expansion))
                .is_none()
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
    editable: Option<super::EditableMacroSource>,
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
    let parent = super::declarative_generation_parent(discovered_in, source_call);
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
    super::resolve_declarative_contributor_parent(parent, editable.is_some(), parent_state)
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn record_unique_valid_link<Key: Copy + Eq + Hash>(
    links: &mut FxHashMap<(Key, Key), bool>,
    parent: Key,
    child: Key,
    valid: bool,
) {
    match links.entry((parent, child)) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(valid);
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            entry.insert(false);
        }
    }
}

#[cfg(rust_item_dependencies_patched)]
fn selected_written_rule(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &super::SourceInventory,
    rule_index: &super::MacroRuleSelectionIndex,
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
    let start = super::original_span_range(compiler, &inventory.offsets, rule.start_span)?;
    let end = super::original_span_range(compiler, &inventory.offsets, rule.end_span)?;
    let range = ByteRange {
        start: start.start,
        end: end.end,
    };
    rule_index.selected_rule(range)
}

#[cfg(rust_item_dependencies_patched)]
fn template_candidates_for_expansion(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    inventory: &super::SourceInventory,
    parser_tokens: &[ParserToken],
    rewrite_guard: &ParserTokenRewriteGuard<'_>,
    rule: SourceUnitId,
    expansion: &MacroDeclarativeExpansion,
) -> Result<Option<TemplateExpansionCandidates>, SourceError> {
    let parents = expansion
        .components
        .iter()
        .map(|component| component.parent)
        .collect::<Vec<_>>();
    let repetitions = expansion
        .components
        .iter()
        .map(|component| component.kind == MacroTranscriberComponentKind::Repetition)
        .collect::<Vec<_>>();
    let direct_repetition_outputs = expansion.output_tokens.iter().try_fold(
        vec![false; expansion.components.len()],
        |mut direct, origin| {
            if origin.component >= expansion.components.len() {
                return None;
            }
            if repetitions[origin.component] {
                direct[origin.component] = true;
            }
            Some(direct)
        },
    );
    let Some(direct_repetition_outputs) = direct_repetition_outputs else {
        return Ok(None);
    };
    let Some(repetition_output_closure) =
        component_flag_closure(&parents, &direct_repetition_outputs)
    else {
        return Ok(None);
    };
    let output_len = expansion.output_tokens.len();
    let mut products = Vec::new();
    for definition in &expansion.definitions {
        if !valid_output_range(definition.output, output_len) {
            return Ok(None);
        }
        products.push((
            definition.output,
            matches!(
                tcx.def_kind(definition.definition),
                rustc_hir::def::DefKind::Use
            ),
        ));
    }
    for child in &expansion.child_expansions {
        if !valid_output_range(child.output, output_len) {
            return Ok(None);
        }
        products.push((child.output, false));
    }
    let mut discarded_outputs = expansion.discarded_outputs.clone();
    discarded_outputs.sort_by_key(|range| (range.start, range.end));
    if !discarded_outputs_fit_live_products(&discarded_outputs, &products, output_len) {
        return Ok(None);
    }
    let mut output_ranges = products.clone();
    output_ranges.extend(
        discarded_outputs
            .iter()
            .copied()
            .map(|range| (range, false)),
    );
    if product_ranges_partially_overlap(output_ranges.iter().map(|(range, _)| *range)) {
        return Ok(None);
    }

    let rule_range = inventory
        .units
        .get(rule.0 as usize)
        .filter(|unit| unit.id == rule && unit.kind == WrittenUnitKind::MacroRule)
        .ok_or(SourceError::InvalidInventory)?
        .full_range;
    let token_ranges = template_token_source_ranges(
        compiler,
        inventory,
        rule_range,
        expansion,
        &repetition_output_closure.ancestors,
        output_ranges.iter().map(|(range, _)| *range),
    )?;
    let token_ranges = TemplateTokenRangeIndex::new(&token_ranges)?;
    let captures = capture_observation_for_expansion(
        compiler,
        inventory,
        parser_tokens,
        rewrite_guard,
        rule_range,
        expansion,
        &output_ranges,
    )?;
    let mut candidates = BTreeMap::<ByteRange, bool>::new();
    for (output, is_use) in output_ranges {
        let Some(range) = token_ranges.source_range(output.start, output.end) else {
            continue;
        };
        match candidates.entry(range) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(is_use);
            }
            std::collections::btree_map::Entry::Occupied(entry) if *entry.get() == is_use => {}
            std::collections::btree_map::Entry::Occupied(_) => return Ok(None),
        }
    }
    let mut blocked_repetition_contents = Vec::new();
    for (component, is_repetition) in repetitions.iter().copied().enumerate() {
        if !is_repetition {
            continue;
        }
        let range = match super::original_span_range(
            compiler,
            &inventory.offsets,
            expansion.components[component].span,
        ) {
            Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
            Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
            Err(error) => return Err(error),
        };
        if repetition_output_closure.descendants[component]
            || !rewrite_guard.deletion_preserves_identity(range)
        {
            blocked_repetition_contents.push(range);
            continue;
        }
        match candidates.entry(range) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(false);
            }
            std::collections::btree_map::Entry::Occupied(entry) if !*entry.get() => {}
            std::collections::btree_map::Entry::Occupied(_) => return Ok(None),
        }
    }
    Ok(Some(TemplateExpansionCandidates {
        candidates: candidates
            .into_iter()
            .map(|(range, is_use)| TemplateCandidate {
                rule,
                range,
                is_use,
            })
            .collect(),
        blocked_repetition_contents,
        captures,
    }))
}

#[cfg(rust_item_dependencies_patched)]
fn capture_observation_for_expansion(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    parser_tokens: &[ParserToken],
    rewrite_guard: &ParserTokenRewriteGuard<'_>,
    rule_range: ByteRange,
    expansion: &MacroDeclarativeExpansion,
    classified_outputs: &[(MacroOutputTokenRange, bool)],
) -> Result<Option<TemplateCaptureObservation>, SourceError> {
    let Some(matcher) = expansion
        .matcher
        .as_ref()
        .filter(|matcher| expansion.complete && matcher.invocation_refinement_safe)
    else {
        return Ok(None);
    };
    if expansion
        .components
        .iter()
        .any(|component| component.kind == MacroTranscriberComponentKind::MetaVarExpr)
    {
        return Ok(None);
    }

    let mut slots = Vec::new();
    let mut captures_by_input = BTreeMap::<(u32, u32, u32), ByteRange>::new();
    let mut fixed_separators = BTreeMap::<(u32, u32, u32), ByteRange>::new();
    let mut matcher_ranges = BTreeSet::new();
    let mut input_ranges = Vec::new();
    for capture in matcher
        .captures
        .iter()
        .filter(|capture| capture.path.is_empty())
    {
        if !capture.input.complete
            || capture.input_stream != capture.input.input_stream
            || capture.input.start >= capture.input.end
        {
            return Ok(None);
        }
        let matcher_capture_range =
            match super::original_span_range(compiler, &inventory.offsets, capture.metavar_span) {
                Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
                Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
                Err(error) => return Err(error),
            };
        let Some((matcher_deletion_range, matcher_separator)) =
            capture_deletion_layout(parser_tokens, matcher_capture_range)
        else {
            return Ok(None);
        };
        if !rule_range.contains(matcher_deletion_range)
            || !rewrite_guard.deletion_preserves_identity(matcher_deletion_range)
            || !matcher_ranges.insert(matcher_deletion_range)
        {
            return Ok(None);
        }

        let Some(input_capture_range) =
            matcher_input_source_range(compiler, inventory, matcher, capture.input)?
        else {
            return Ok(None);
        };
        if input_capture_range.is_empty() {
            return Ok(None);
        }
        let stream = &matcher.input_streams[capture.input_stream as usize];
        let input_deletion_range = if let Some(matcher_separator) = matcher_separator {
            let Some(separator_span) = stream.tokens.get(capture.input.end as usize) else {
                return Ok(None);
            };
            let Some(separator_end) = capture.input.end.checked_add(1) else {
                return Ok(None);
            };
            if fixed_separators
                .insert(
                    (capture.input_stream, capture.input.end, separator_end),
                    matcher_capture_range,
                )
                .is_some()
            {
                return Ok(None);
            }
            let input_separator =
                match super::original_span_range(compiler, &inventory.offsets, *separator_span) {
                    Ok(range) if !range.is_empty() => range,
                    Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
                    Err(error) => return Err(error),
                };
            if input_capture_range.end > input_separator.start
                || !same_single_parser_token(
                    &inventory.original,
                    matcher_separator,
                    input_separator,
                )
            {
                return Ok(None);
            }
            ByteRange {
                start: input_capture_range.start,
                end: input_separator.end,
            }
        } else {
            if capture.input.end as usize != stream.tokens.len() {
                return Ok(None);
            }
            input_capture_range
        };
        if !rewrite_guard.deletion_preserves_identity(input_deletion_range) {
            return Ok(None);
        }
        input_ranges.push((capture.input_stream, capture.input));
        if captures_by_input
            .insert(
                (capture.input_stream, capture.input.start, capture.input.end),
                matcher_capture_range,
            )
            .is_some()
        {
            return Ok(None);
        }
        slots.push(ObservedCaptureSlot {
            matcher_capture_range,
            matcher_deletion_range,
            input_capture_range,
            input_deletion_range,
        });
    }
    input_ranges.sort_by_key(|(stream, range)| (*stream, range.start, range.end));
    if input_ranges.windows(2).any(|pair| {
        pair[0].0 == pair[1].0 && pair[0].1.start < pair[1].1.end && pair[1].1.start < pair[0].1.end
    }) {
        return Ok(None);
    }
    slots.sort_by_key(|slot| slot.matcher_capture_range);

    let mut components = BTreeSet::new();
    let mut component_ranges = vec![None; expansion.components.len()];
    for (index, component) in expansion.components.iter().enumerate() {
        if component.kind != MacroTranscriberComponentKind::MetaVar {
            continue;
        }
        let range = match super::original_span_range(compiler, &inventory.offsets, component.span) {
            Ok(range) if !range.is_empty() && rule_range.contains(range) => range,
            Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
            Err(error) => return Err(error),
        };
        if !components.insert(range) {
            return Ok(None);
        }
        component_ranges[index] = Some(range);
    }

    let mut classified_delta = vec![0_i64; expansion.output_tokens.len() + 1];
    for (range, _) in classified_outputs {
        if !valid_output_range(*range, expansion.output_tokens.len()) {
            return Ok(None);
        }
        classified_delta[range.start as usize] += 1;
        classified_delta[range.end as usize] -= 1;
    }
    let mut coverage = 0_i64;
    let classified_output = classified_delta
        .into_iter()
        .take(expansion.output_tokens.len())
        .map(|delta| {
            coverage += delta;
            coverage > 0
        })
        .collect::<Vec<_>>();
    let mut component_captures = BTreeMap::new();
    for (ordinal, output) in expansion.output_tokens.iter().enumerate() {
        let Some(component) = expansion.components.get(output.component) else {
            return Ok(None);
        };
        if component.kind != MacroTranscriberComponentKind::MetaVar {
            continue;
        }
        let Some(component_range) = component_ranges[output.component] else {
            return Ok(None);
        };
        if !classified_output[ordinal] {
            return Ok(None);
        }
        let mut matched = BTreeSet::new();
        let mut separator_owners = BTreeSet::new();
        for input in &output.input_contributors {
            if !input.complete {
                return Ok(None);
            }
            let key = (input.input_stream, input.start, input.end);
            if let Some(&capture) = captures_by_input.get(&key) {
                matched.insert(capture);
            } else if let Some(&capture) = fixed_separators.get(&key) {
                separator_owners.insert(capture);
            } else {
                return Ok(None);
            }
        }
        let mut matched = matched.into_iter();
        let Some(matcher_capture_range) = matched.next() else {
            return Ok(None);
        };
        if matched.next().is_some() {
            return Ok(None);
        }
        if separator_owners
            .iter()
            .any(|owner| *owner != matcher_capture_range)
        {
            return Ok(None);
        }
        if component_captures
            .insert(component_range, matcher_capture_range)
            .is_some_and(|previous| previous != matcher_capture_range)
        {
            return Ok(None);
        }
    }

    Ok(Some(TemplateCaptureObservation {
        components,
        component_captures,
        slots,
    }))
}

fn capture_deletion_layout(
    tokens: &[ParserToken],
    capture: ByteRange,
) -> Option<(ByteRange, Option<ByteRange>)> {
    if capture.is_empty() {
        return None;
    }
    let first = tokens.partition_point(|token| token.range.end <= capture.start);
    let end = tokens.partition_point(|token| token.range.start < capture.end);
    let captured = tokens.get(first..end)?;
    if captured.first()?.range.start != capture.start
        || captured.last()?.range.end != capture.end
        || captured.iter().any(|token| !capture.contains(token.range))
    {
        return None;
    }
    let previous = tokens.get(first.checked_sub(1)?)?;
    if !matches!(previous.text.as_str(), "(" | "{" | "[" | "," | ";") {
        return None;
    }
    let next = tokens.get(end)?;
    if matches!(next.text.as_str(), "," | ";") {
        return Some((
            ByteRange {
                start: capture.start,
                end: next.range.end,
            },
            Some(next.range),
        ));
    }
    matches!(next.text.as_str(), ")" | "}" | "]").then_some((capture, None))
}

fn same_single_parser_token(source: &str, left: ByteRange, right: ByteRange) -> bool {
    let Some(left) = source.get(left.start as usize..left.end as usize) else {
        return false;
    };
    let Some(right) = source.get(right.start as usize..right.end as usize) else {
        return false;
    };
    let Ok(left) = tokenize_parser_tokens(left) else {
        return false;
    };
    let Ok(right) = tokenize_parser_tokens(right) else {
        return false;
    };
    matches!((left.as_slice(), right.as_slice()), ([left], [right]) if left.same_identity(right))
}

#[cfg(rust_item_dependencies_patched)]
fn capture_slot_drafts_for_rule(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    source_resolver: &super::EditableMacroSourceResolver<'_>,
    selected: &[ExpnId],
    eligible: &FxHashSet<ExpnId>,
    observations: &FxHashMap<ExpnId, TemplateCaptureObservation>,
    template_candidates: &[(TemplateCandidate, u32)],
    expected_selections: usize,
) -> Result<Option<Vec<CaptureSlotDraft>>, SourceError> {
    if selected.len() != expected_selections || selected.is_empty() {
        return Ok(None);
    }

    let mut invocations = BTreeSet::new();
    let mut expected_components = None;
    let mut component_captures = BTreeMap::<ByteRange, ByteRange>::new();
    let mut slots = BTreeMap::<ByteRange, (ByteRange, Vec<PendingCaptureInputFacts>)>::new();
    let mut expected_slot_ranges = None;
    for &expansion in selected {
        if !eligible.contains(&expansion) {
            return Ok(None);
        }
        let Some(observation) = observations.get(&expansion) else {
            return Ok(None);
        };
        if expected_components
            .as_ref()
            .is_some_and(|expected| expected != &observation.components)
        {
            return Ok(None);
        }
        expected_components.get_or_insert_with(|| observation.components.clone());
        for (&component, &capture) in &observation.component_captures {
            if component_captures
                .insert(component, capture)
                .is_some_and(|previous| previous != capture)
            {
                return Ok(None);
            }
        }

        let Some(editable) = source_resolver.resolve(compiler, inventory, expansion)? else {
            return Ok(None);
        };
        let Some(invocation) = editable.exact_invocation else {
            return Ok(None);
        };
        if !invocations.insert(invocation)
            || inventory
                .units
                .get(invocation.0 as usize)
                .is_none_or(|unit| {
                    unit.id != invocation
                        || unit.kind != WrittenUnitKind::MacroInvocation
                        || unit.cfg_state != CfgState::Active
                })
        {
            return Ok(None);
        }

        let slot_ranges = observation
            .slots
            .iter()
            .map(|slot| slot.matcher_capture_range)
            .collect::<BTreeSet<_>>();
        if expected_slot_ranges
            .as_ref()
            .is_some_and(|expected| expected != &slot_ranges)
        {
            return Ok(None);
        }
        expected_slot_ranges.get_or_insert(slot_ranges);
        for slot in &observation.slots {
            match slots.entry(slot.matcher_capture_range) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert((
                        slot.matcher_deletion_range,
                        vec![PendingCaptureInputFacts {
                            invocation: invocation.0,
                            capture_range: slot.input_capture_range,
                            deletion_range: slot.input_deletion_range,
                        }],
                    ));
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    if entry.get().0 != slot.matcher_deletion_range {
                        return Ok(None);
                    }
                    entry.get_mut().1.push(PendingCaptureInputFacts {
                        invocation: invocation.0,
                        capture_range: slot.input_capture_range,
                        deletion_range: slot.input_deletion_range,
                    });
                }
            }
        }
    }

    let components = expected_components.unwrap_or_default();
    if component_captures.keys().copied().collect::<BTreeSet<_>>() != components {
        return Ok(None);
    }
    let Some(component_units) = template_component_units(&components, template_candidates) else {
        return Ok(None);
    };
    let Some(mut trigger_units_by_capture) = capture_trigger_units_with_work(
        slots.keys().copied(),
        &component_captures,
        &component_units,
        || {},
    ) else {
        return Ok(None);
    };

    let mut drafts = Vec::with_capacity(slots.len());
    for (matcher_capture_range, (matcher_deletion_range, mut inputs)) in slots {
        inputs.sort_by_key(|input| input.invocation);
        let Some(trigger_units) = trigger_units_by_capture.remove(&matcher_capture_range) else {
            return Ok(None);
        };
        drafts.push(CaptureSlotDraft {
            matcher_capture_range,
            matcher_deletion_range,
            trigger_units,
            inputs,
        });
    }
    Ok(Some(drafts))
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn capture_trigger_units_with_work(
    slot_ranges: impl IntoIterator<Item = ByteRange>,
    component_captures: &BTreeMap<ByteRange, ByteRange>,
    component_units: &BTreeMap<ByteRange, u32>,
    mut visit: impl FnMut(),
) -> Option<BTreeMap<ByteRange, Vec<u32>>> {
    let mut by_capture = slot_ranges
        .into_iter()
        .map(|capture| (capture, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for (&component, &capture) in component_captures {
        visit();
        let unit = *component_units.get(&component)?;
        by_capture.get_mut(&capture)?.push(unit);
    }
    for units in by_capture.values_mut() {
        units.sort_unstable();
        units.dedup();
    }
    Some(by_capture)
}

#[cfg(rust_item_dependencies_patched)]
fn template_component_units(
    components: &BTreeSet<ByteRange>,
    candidates: &[(TemplateCandidate, u32)],
) -> Option<BTreeMap<ByteRange, u32>> {
    let components = components.iter().copied().collect::<Vec<_>>();
    if components
        .windows(2)
        .any(|pair| pair[0].end > pair[1].start)
    {
        return None;
    }

    let mut result = BTreeMap::new();
    let mut stack = Vec::<(ByteRange, u32)>::new();
    let mut candidate = 0;
    for component in components {
        while candidates
            .get(candidate)
            .is_some_and(|(candidate, _)| candidate.range.start <= component.start)
        {
            let (next, unit) = candidates[candidate];
            while stack
                .last()
                .is_some_and(|(range, _)| range.end <= next.range.start)
            {
                stack.pop();
            }
            if stack
                .last()
                .is_some_and(|(parent, _)| !parent.contains(next.range))
            {
                return None;
            }
            stack.push((next.range, unit));
            candidate += 1;
        }
        while stack
            .last()
            .is_some_and(|(range, _)| range.end <= component.start)
        {
            stack.pop();
        }
        let &(_, unit) = stack
            .last()
            .filter(|(range, _)| range.contains(component))?;
        result.insert(component, unit);
    }
    Some(result)
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct ComponentFlagClosure {
    ancestors: Vec<bool>,
    descendants: Vec<bool>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
fn component_flag_closure(
    parents: &[Option<usize>],
    marked: &[bool],
) -> Option<ComponentFlagClosure> {
    if parents.len() != marked.len() {
        return None;
    }
    // 0 is unseen, 1 is on the current parent chain, and 2 is known to reach
    // a root. Resolve the forest once and reuse its parent-before-child order
    // for the reverse descendant closure.
    let mut states = vec![0_u8; parents.len()];
    let mut ancestors = vec![false; parents.len()];
    let mut resolved = Vec::with_capacity(parents.len());
    for start in 0..parents.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = Some(start);
        let inherited = loop {
            let Some(index) = current else {
                break false;
            };
            if index >= parents.len() {
                return None;
            }
            match states[index] {
                0 => {
                    states[index] = 1;
                    path.push(index);
                    current = parents[index];
                }
                1 => return None,
                2 => break ancestors[index],
                _ => unreachable!("component traversal state is internal"),
            }
        };
        let mut inherited = inherited;
        for index in path.into_iter().rev() {
            inherited |= marked[index];
            ancestors[index] = inherited;
            states[index] = 2;
            resolved.push(index);
        }
    }
    let mut descendants = marked.to_vec();
    for index in resolved.into_iter().rev() {
        if descendants[index]
            && let Some(parent) = parents[index]
        {
            descendants[parent] = true;
        }
    }
    Some(ComponentFlagClosure {
        ancestors,
        descendants,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn blocked_range_index(
    ranges: impl IntoIterator<Item = (SourceUnitId, ByteRange)>,
) -> Result<BTreeMap<SourceUnitId, Vec<ByteRange>>, SourceError> {
    let mut by_rule = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    for (rule, range) in ranges {
        if range.is_empty() {
            return Err(SourceError::IncompleteDeclarativeMacroObservation);
        }
        by_rule.entry(rule).or_default().push(range);
    }
    for ranges in by_rule.values_mut() {
        ranges.sort_by_key(|range| (range.start, std::cmp::Reverse(range.end)));
        let mut outermost = Vec::<ByteRange>::with_capacity(ranges.len());
        for range in ranges.drain(..) {
            if outermost.last().is_some_and(|outer| outer.contains(range)) {
                continue;
            }
            if outermost
                .last()
                .is_some_and(|previous| previous.end > range.start)
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
            outermost.push(range);
        }
        *ranges = outermost;
    }
    Ok(by_rule)
}

#[cfg(rust_item_dependencies_patched)]
fn range_index_contains(
    index: &BTreeMap<SourceUnitId, Vec<ByteRange>>,
    rule: SourceUnitId,
    range: ByteRange,
) -> bool {
    let Some(ranges) = index.get(&rule) else {
        return false;
    };
    let end = ranges.partition_point(|candidate| candidate.start <= range.start);
    end > 0 && ranges[end - 1].contains(range)
}

#[cfg(test)]
fn component_repetition_ancestors(
    parents: &[Option<usize>],
    repetitions: &[bool],
) -> Option<Vec<bool>> {
    component_flag_closure(parents, repetitions).map(|closure| closure.ancestors)
}

#[cfg(any(rust_item_dependencies_patched, test))]
struct TemplateTokenRangeIndex {
    token_count: u32,
    leaf_count: usize,
    invalid_prefix: Vec<u32>,
    minimum_starts: Vec<u32>,
    maximum_ends: Vec<u32>,
}

#[cfg(any(rust_item_dependencies_patched, test))]
impl TemplateTokenRangeIndex {
    fn new(ranges: &[Option<ByteRange>]) -> Result<Self, SourceError> {
        let token_count = u32::try_from(ranges.len()).map_err(|_| SourceError::SourceTooLarge)?;
        let leaf_count = ranges
            .len()
            .max(1)
            .checked_next_power_of_two()
            .ok_or(SourceError::SourceTooLarge)?;
        let tree_len = leaf_count
            .checked_mul(2)
            .ok_or(SourceError::SourceTooLarge)?;
        let mut minimum_starts = vec![u32::MAX; tree_len];
        let mut maximum_ends = vec![0; tree_len];
        let mut invalid_prefix = Vec::with_capacity(ranges.len() + 1);
        invalid_prefix.push(0_u32);
        for (index, range) in ranges.iter().enumerate() {
            let valid = range.filter(|range| !range.is_empty());
            invalid_prefix.push(
                invalid_prefix[index]
                    .checked_add(valid.is_none() as u32)
                    .ok_or(SourceError::SourceTooLarge)?,
            );
            if let Some(range) = valid {
                minimum_starts[leaf_count + index] = range.start;
                maximum_ends[leaf_count + index] = range.end;
            }
        }
        for index in (1..leaf_count).rev() {
            minimum_starts[index] = minimum_starts[index * 2].min(minimum_starts[index * 2 + 1]);
            maximum_ends[index] = maximum_ends[index * 2].max(maximum_ends[index * 2 + 1]);
        }
        Ok(Self {
            token_count,
            leaf_count,
            invalid_prefix,
            minimum_starts,
            maximum_ends,
        })
    }

    fn source_range(&self, start: u32, end: u32) -> Option<ByteRange> {
        if start >= end
            || end > self.token_count
            || self.invalid_prefix[end as usize] != self.invalid_prefix[start as usize]
        {
            return None;
        }
        let mut left = self.leaf_count + start as usize;
        let mut right = self.leaf_count + end as usize;
        let mut minimum_start = u32::MAX;
        let mut maximum_end = 0;
        while left < right {
            if left % 2 == 1 {
                minimum_start = minimum_start.min(self.minimum_starts[left]);
                maximum_end = maximum_end.max(self.maximum_ends[left]);
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                minimum_start = minimum_start.min(self.minimum_starts[right]);
                maximum_end = maximum_end.max(self.maximum_ends[right]);
            }
            left /= 2;
            right /= 2;
        }
        (minimum_start < maximum_end).then_some(ByteRange {
            start: minimum_start,
            end: maximum_end,
        })
    }
}

#[cfg(rust_item_dependencies_patched)]
fn valid_output_range(range: MacroOutputTokenRange, output_len: usize) -> bool {
    range.start < range.end && range.end as usize <= output_len
}

#[cfg(rust_item_dependencies_patched)]
fn product_ranges_partially_overlap(ranges: impl Iterator<Item = MacroOutputTokenRange>) -> bool {
    let mut ranges = ranges.collect::<Vec<_>>();
    ranges.sort_by_key(|range| (range.start, std::cmp::Reverse(range.end)));
    let mut active = Vec::<MacroOutputTokenRange>::new();
    for range in ranges {
        while active
            .last()
            .is_some_and(|candidate| candidate.end <= range.start)
        {
            active.pop();
        }
        if active
            .last()
            .is_some_and(|candidate| range.end > candidate.end)
        {
            return true;
        }
        active.push(range);
    }
    false
}

#[cfg(rust_item_dependencies_patched)]
fn discarded_outputs_fit_live_products(
    discarded: &[MacroOutputTokenRange],
    products: &[(MacroOutputTokenRange, bool)],
    output_len: usize,
) -> bool {
    if discarded
        .iter()
        .any(|range| !valid_output_range(*range, output_len))
        || discarded.windows(2).any(|pair| pair[0].end > pair[1].start)
    {
        return false;
    }
    let mut continuous_run = Vec::with_capacity(discarded.len());
    let mut run = 0_usize;
    for (index, range) in discarded.iter().enumerate() {
        if index > 0 && discarded[index - 1].end < range.start {
            run += 1;
        }
        continuous_run.push(run);
    }

    products.iter().all(|(product, _)| {
        let first = discarded.partition_point(|range| range.end <= product.start);
        let end = discarded.partition_point(|range| range.start < product.end);
        if first == end {
            return true;
        }
        let first_discarded = discarded[first];
        let last_discarded = discarded[end - 1];
        if first_discarded.start < product.start || last_discarded.end > product.end {
            return false;
        }
        !(first_discarded.start == product.start
            && continuous_run[first] == continuous_run[end - 1]
            && last_discarded.end == product.end)
    })
}

#[cfg(rust_item_dependencies_patched)]
fn template_token_source_ranges(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    rule_range: ByteRange,
    expansion: &MacroDeclarativeExpansion,
    blocked_components: &[bool],
    product_ranges: impl Iterator<Item = MacroOutputTokenRange>,
) -> Result<Vec<Option<ByteRange>>, SourceError> {
    let mut coverage_delta = vec![0_i64; expansion.output_tokens.len() + 1];
    for range in product_ranges {
        if !valid_output_range(range, expansion.output_tokens.len()) {
            return Err(SourceError::IncompleteDeclarativeMacroObservation);
        }
        coverage_delta[range.start as usize] += 1;
        coverage_delta[range.end as usize] -= 1;
    }
    let mut coverage = 0_i64;
    expansion
        .output_tokens
        .iter()
        .enumerate()
        .map(|(index, origin)| {
            coverage += coverage_delta[index];
            if coverage == 0 {
                return Ok(None);
            }
            if blocked_components
                .get(origin.component)
                .copied()
                .unwrap_or(true)
            {
                return Ok(None);
            }
            let component = &expansion.components[origin.component];
            match super::original_span_range(compiler, &inventory.offsets, component.span) {
                Ok(range) if !range.is_empty() && rule_range.contains(range) => Ok(Some(range)),
                Ok(_) | Err(SourceError::InvalidSpan) => Ok(None),
                Err(error) => Err(error),
            }
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
type ClassifiedTemplate = (TemplateCandidate, WrittenUnitKind, Option<ByteRange>);

#[cfg(rust_item_dependencies_patched)]
fn classify_template_candidates(
    candidates: &BTreeSet<TemplateCandidate>,
) -> Result<Vec<ClassifiedTemplate>, SourceError> {
    let mut by_range = BTreeMap::<(SourceUnitId, ByteRange), bool>::new();
    for candidate in candidates {
        if by_range
            .insert((candidate.rule, candidate.range), candidate.is_use)
            .is_some()
        {
            return Err(SourceError::IncompleteDeclarativeMacroObservation);
        }
    }
    let mut candidates = by_range
        .into_iter()
        .map(|((rule, range), is_use)| TemplateCandidate {
            rule,
            range,
            is_use,
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| {
        (
            candidate.rule,
            candidate.range.start,
            std::cmp::Reverse(candidate.range.end),
        )
    });

    let mut parents = vec![None; candidates.len()];
    let mut stack = Vec::<usize>::new();
    for (index, candidate) in candidates.iter().enumerate() {
        while let Some(&ancestor) = stack.last() {
            if candidates[ancestor].rule != candidate.rule
                || candidates[ancestor].range.end <= candidate.range.start
            {
                stack.pop();
            } else {
                break;
            }
        }
        if let Some(&parent) = stack.last() {
            if candidates[parent].rule != candidate.rule
                || !candidates[parent].range.contains(candidate.range)
            {
                return Err(SourceError::IncompleteDeclarativeMacroObservation);
            }
            parents[index] = Some(parent);
        }
        stack.push(index);
    }

    let mut contains_use_descendant = vec![false; candidates.len()];
    for index in (0..candidates.len()).rev() {
        if let Some(parent) = parents[index] {
            contains_use_descendant[parent] |=
                candidates[index].is_use || contains_use_descendant[index];
        }
    }
    let mut outermost_use_ancestor = vec![None; candidates.len()];
    for index in 0..candidates.len() {
        let Some(parent) = parents[index] else {
            continue;
        };
        outermost_use_ancestor[index] =
            outermost_use_ancestor[parent].or_else(|| candidates[parent].is_use.then_some(parent));
    }

    let mut kinds = vec![None; candidates.len()];
    for (index, candidate) in candidates.iter().enumerate() {
        let containing_use_item =
            outermost_use_ancestor[index].map(|ancestor| candidates[ancestor].range);
        let contains_use_child = contains_use_descendant[index];
        let contained_by_use_child = containing_use_item.is_some();
        let kind = if candidate.is_use && contains_use_child && !contained_by_use_child {
            WrittenUnitKind::UseItem
        } else if candidate.is_use && !contains_use_child && containing_use_item.is_some() {
            kinds[index] = Some(WrittenUnitKind::UseLeaf);
            continue;
        } else if candidate.is_use && (contains_use_child || contained_by_use_child) {
            // Intermediate use-tree prefixes are represented by the enclosing
            // UseItem and the terminal leaves, matching the ordinary AST path.
            continue;
        } else {
            WrittenUnitKind::NestedItem
        };
        kinds[index] = Some(kind);
    }

    let mut nearest_emitted_ancestor = vec![None; candidates.len()];
    for index in 0..candidates.len() {
        let Some(parent) = parents[index] else {
            continue;
        };
        nearest_emitted_ancestor[index] = if kinds[parent].is_some() {
            Some(parent)
        } else {
            nearest_emitted_ancestor[parent]
        };
    }

    let mut layout = candidates
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| {
            kinds[index].map(|kind| {
                (
                    *candidate,
                    kind,
                    nearest_emitted_ancestor[index].map(|parent| candidates[parent].range),
                )
            })
        })
        .collect::<Vec<_>>();
    layout.sort_by_key(|(candidate, kind, _)| {
        (
            candidate.rule,
            candidate.range.start,
            std::cmp::Reverse(candidate.range.end),
            kind.rank(),
        )
    });
    Ok(layout)
}

#[cfg(rust_item_dependencies_patched)]
#[allow(clippy::too_many_arguments)]
fn matcher_repetitions(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    invocation: &WrittenUnit,
    rule: SourceUnitId,
    matcher: &MacroMatcherObservation,
    pending: &mut Vec<super::PendingUnit>,
    next_temporary: &mut u32,
) -> Result<Option<Vec<PendingRepetitionFacts>>, SourceError> {
    let Some(paths) = matcher_repetition_paths(matcher) else {
        return Ok(None);
    };
    if matcher.input_streams.iter().any(|stream| {
        !stream.complete
            || stream.parent_output.is_some()
            || stream.boundaries.len() != stream.tokens.len() + 1
    }) {
        return Ok(None);
    }

    let mut local_pending = Vec::new();
    let mut local_next = *next_temporary;
    let mut elements = BTreeMap::<(usize, &[usize], usize), u32>::new();
    let mut facts = Vec::new();
    let mut repetition_indices = (0..matcher.repetitions.len()).collect::<Vec<_>>();
    repetition_indices.sort_by_key(|&index| {
        (
            paths[&matcher.repetitions[index].matcher_index].len(),
            matcher.repetitions[index].matcher_index,
        )
    });

    for index in repetition_indices {
        let repetition = &matcher.repetitions[index];
        let Some(path) = paths.get(&repetition.matcher_index) else {
            return Ok(None);
        };
        let matcher_range =
            match super::original_span_range(compiler, &inventory.offsets, repetition.span) {
                Ok(range) if !range.is_empty() => range,
                Ok(_) | Err(SourceError::InvalidSpan) => return Ok(None),
                Err(error) => return Err(error),
            };
        let rule_range = inventory.units[rule.0 as usize].full_range;
        if !rule_range.contains(matcher_range) {
            return Ok(None);
        }
        for instance in &repetition.instances {
            if instance.path.len() + 1 != path.len()
                || instance.input.input_stream != repetition.input_stream
                || !instance.input.complete
            {
                return Ok(None);
            }
            let parent = match repetition.parent_matcher_index {
                None if instance.path.is_empty() => invocation.id.0,
                None => return Ok(None),
                Some(parent_matcher) => {
                    let Some((&parent_iteration, parent_path)) = instance.path.split_last() else {
                        return Ok(None);
                    };
                    let Some(&parent) =
                        elements.get(&(parent_matcher, parent_path, parent_iteration))
                    else {
                        return Ok(None);
                    };
                    parent
                }
            };
            let Some(input_range) =
                matcher_input_source_range(compiler, inventory, matcher, instance.input)?
            else {
                return Ok(None);
            };
            let mut pending_elements = Vec::new();
            let mut previous_end = None;
            for (iteration_index, iteration) in instance.iterations.iter().enumerate() {
                if iteration.path.len() != instance.path.len() + 1
                    || !iteration.path.starts_with(&instance.path)
                    || iteration.path.last() != Some(&iteration_index)
                    || iteration.body.input_stream != repetition.input_stream
                    || !iteration.body.complete
                {
                    return Ok(None);
                }
                let Some(body) =
                    matcher_input_source_range(compiler, inventory, matcher, iteration.body)?
                else {
                    return Ok(None);
                };
                if body.is_empty()
                    || !input_range.contains(body)
                    || previous_end.is_some_and(|end| end > body.start)
                {
                    return Ok(None);
                }
                let separator_after = match iteration.separator_after {
                    Some(separator) => {
                        if separator.input_stream != repetition.input_stream || !separator.complete
                        {
                            return Ok(None);
                        }
                        let Some(separator) =
                            matcher_input_source_range(compiler, inventory, matcher, separator)?
                        else {
                            return Ok(None);
                        };
                        if separator.is_empty()
                            || separator.start < body.end
                            || !input_range.contains(separator)
                        {
                            return Ok(None);
                        }
                        Some(separator)
                    }
                    None => None,
                };
                previous_end = Some(separator_after.map_or(body.end, |separator| separator.end));
                let temporary_id = local_next;
                local_next = local_next
                    .checked_add(1)
                    .ok_or(SourceError::SourceTooLarge)?;
                local_pending.push(super::PendingUnit {
                    temporary_id,
                    kind: WrittenUnitKind::NestedItem,
                    full_range: body,
                    parent: Some(parent),
                    cfg_state: CfgState::Active,
                    // An exact invocation has an independently observed
                    // matcher ledger, so each repetition element is an
                    // independent deletion unit even when the invocation
                    // itself is nested in an atomic item. Procedural-macro
                    // opaque ranges are merged again after this refinement.
                    atomic_representative: temporary_id,
                    syntax_ordinal: temporary_id,
                });
                if elements
                    .insert(
                        (
                            repetition.matcher_index,
                            instance.path.as_slice(),
                            iteration_index,
                        ),
                        temporary_id,
                    )
                    .is_some()
                {
                    return Ok(None);
                }
                pending_elements.push(PendingElementFacts {
                    unit: temporary_id,
                    separator_after,
                });
            }
            if instance
                .iterations
                .last()
                .is_some_and(|iteration| iteration.separator_after.is_some())
            {
                return Ok(None);
            }
            facts.push(PendingRepetitionFacts {
                invocation: invocation.id.0,
                rule: rule.0,
                matcher_range,
                parent,
                repetition_path: path.clone(),
                input_range,
                elements: pending_elements,
                minimum: repetition.kleene.min,
                maximum: repetition.kleene.max,
            });
        }
    }
    pending.extend(local_pending);
    *next_temporary = local_next;
    Ok(Some(facts))
}

#[cfg(rust_item_dependencies_patched)]
fn matcher_repetition_paths(
    matcher: &MacroMatcherObservation,
) -> Option<BTreeMap<usize, Vec<u32>>> {
    let repetitions = matcher
        .repetitions
        .iter()
        .map(|repetition| (repetition.matcher_index, repetition))
        .collect::<BTreeMap<_, _>>();
    if repetitions.len() != matcher.repetitions.len() {
        return None;
    }
    let mut paths = BTreeMap::<usize, Vec<u32>>::new();
    for &matcher_index in repetitions.keys() {
        if paths.contains_key(&matcher_index) {
            continue;
        }
        let mut suffix = Vec::new();
        let mut active = BTreeSet::new();
        let mut current = Some(matcher_index);
        while let Some(index) = current {
            if let Some(prefix) = paths.get(&index).cloned() {
                let mut path = prefix;
                while let Some(index) = suffix.pop() {
                    path.push(u32::try_from(index).ok()?);
                    paths.insert(index, path.clone());
                }
                break;
            }
            if !active.insert(index) {
                return None;
            }
            let repetition = repetitions.get(&index)?;
            suffix.push(index);
            current = repetition.parent_matcher_index;
        }
        if !suffix.is_empty() {
            let mut path = Vec::new();
            while let Some(index) = suffix.pop() {
                path.push(u32::try_from(index).ok()?);
                paths.insert(index, path.clone());
            }
        }
    }
    Some(paths)
}

#[cfg(rust_item_dependencies_patched)]
fn matcher_input_source_range(
    compiler: &Compiler,
    inventory: &super::SourceInventory,
    matcher: &MacroMatcherObservation,
    range: MacroInputTokenRange,
) -> Result<Option<ByteRange>, SourceError> {
    if !range.complete || range.start > range.end {
        return Ok(None);
    }
    let Some(stream) = matcher.input_streams.get(range.input_stream as usize) else {
        return Ok(None);
    };
    if !stream.complete
        || stream.parent_output.is_some()
        || stream.boundaries.len() != stream.tokens.len() + 1
        || range.end as usize > stream.tokens.len()
    {
        return Ok(None);
    }
    let start = super::original_span_range(
        compiler,
        &inventory.offsets,
        stream.boundaries[range.start as usize],
    );
    let end = super::original_span_range(
        compiler,
        &inventory.offsets,
        stream.boundaries[range.end as usize],
    );
    match (start, end) {
        (Ok(start), Ok(end)) if start.is_empty() && end.is_empty() && start.start <= end.end => {
            Ok(Some(ByteRange {
                start: start.start,
                end: end.end,
            }))
        }
        (Err(SourceError::InvalidSpan), _) | (_, Err(SourceError::InvalidSpan)) => Ok(None),
        (Err(error), _) | (_, Err(error)) => Err(error),
        _ => Ok(None),
    }
}

pub(crate) fn validate_declarative_macro_source_facts(
    original: &str,
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    repetitions: &[MacroRepetitionSourceFacts],
) -> Result<(), SourceError> {
    let census = declarative_unit_census(units)?;
    validate_macro_rule_facts(units, macro_rules)?;
    validate_refined_rule_links(units, macro_rules, templates, capture_slots, repetitions)?;
    validate_templates(units, templates, capture_slots, &census.template_units)?;
    validate_capture_slots(original, units, macro_rules, templates, capture_slots)?;
    validate_repetitions(original, units, repetitions, &census.matcher_units)
}

pub(super) fn declarative_unit_kinds(
    units: &[WrittenUnit],
) -> Result<Vec<Option<super::DeclarativeSourceUnitKind>>, SourceError> {
    Ok(declarative_unit_census(units)?.kinds)
}

struct DeclarativeUnitCensus {
    kinds: Vec<Option<super::DeclarativeSourceUnitKind>>,
    template_units: BTreeSet<SourceUnitId>,
    matcher_units: BTreeSet<SourceUnitId>,
}

#[derive(Clone, Copy)]
enum DeclarativeBoundary {
    Rule,
    Invocation,
}

fn declarative_unit_census(units: &[WrittenUnit]) -> Result<DeclarativeUnitCensus, SourceError> {
    // Resolve the nearest syntax boundary once per unit. The parser does not
    // create children inside macro token trees; those children appear only
    // when the patched observer refines a rule template or matcher input.
    let mut states = vec![0_u8; units.len()];
    let mut boundaries = vec![None; units.len()];
    for start in 0..units.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        let boundary = loop {
            match states.get(current).copied() {
                Some(2) => break boundaries[current],
                Some(1) | None => return Err(SourceError::InvalidInventory),
                Some(0) => {}
                _ => unreachable!("source ancestor traversal state is internal"),
            }
            states[current] = 1;
            path.push(current);
            let unit = &units[current];
            if unit.id.0 as usize != current {
                return Err(SourceError::InvalidInventory);
            }
            match unit.kind {
                WrittenUnitKind::MacroRule => break Some(DeclarativeBoundary::Rule),
                WrittenUnitKind::MacroInvocation => {
                    break Some(DeclarativeBoundary::Invocation);
                }
                _ => {}
            }
            let Some(parent) = unit.parent else {
                break None;
            };
            let parent_index = parent.0 as usize;
            if units.get(parent_index).is_none_or(|unit| unit.id != parent) {
                return Err(SourceError::InvalidInventory);
            }
            current = parent_index;
        };
        for index in path.into_iter().rev() {
            states[index] = 2;
            boundaries[index] = boundary;
        }
    }

    let mut kinds = vec![None; units.len()];
    let mut template_units = BTreeSet::new();
    let mut matcher_units = BTreeSet::new();
    for unit in units {
        if unit.cfg_state != CfgState::Active {
            continue;
        }
        let boundary = unit
            .parent
            .and_then(|parent| boundaries.get(parent.0 as usize).copied().flatten());
        match (boundary, unit.kind) {
            (
                Some(DeclarativeBoundary::Rule),
                WrittenUnitKind::NestedItem | WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf,
            ) => {
                template_units.insert(unit.id);
                if unit.kind == WrittenUnitKind::NestedItem {
                    kinds[unit.id.0 as usize] =
                        Some(super::DeclarativeSourceUnitKind::TemplateComponent);
                }
            }
            (Some(DeclarativeBoundary::Invocation), WrittenUnitKind::NestedItem) => {
                matcher_units.insert(unit.id);
                kinds[unit.id.0 as usize] = Some(super::DeclarativeSourceUnitKind::MatcherElement);
            }
            _ => {}
        }
    }
    Ok(DeclarativeUnitCensus {
        kinds,
        template_units,
        matcher_units,
    })
}

fn validate_refined_rule_links(
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    repetitions: &[MacroRepetitionSourceFacts],
) -> Result<(), SourceError> {
    let mut refined_rules = BTreeMap::new();
    for facts in macro_rules {
        let MacroRuleSourceFacts::Refined {
            rules,
            observed_selections,
            ..
        } = facts
        else {
            continue;
        };
        if rules.windows(2).any(|pair| {
            units[pair[0].0 as usize].full_range.start >= units[pair[1].0 as usize].full_range.start
        }) {
            return Err(SourceError::InvalidInventory);
        }
        let observed = observed_selections.iter().copied().collect::<BTreeSet<_>>();
        for (index, &rule) in rules.iter().enumerate() {
            if refined_rules
                .insert(rule, (index == 0, observed.contains(&rule)))
                .is_some()
            {
                return Err(SourceError::InvalidInventory);
            }
        }
    }

    if templates.iter().any(|template| {
        refined_rules
            .get(&template.rule)
            .is_none_or(|(_, observed)| !observed)
    }) || capture_slots.iter().any(|slot| {
        refined_rules
            .get(&slot.rule)
            .is_none_or(|(first, observed)| !first || !observed)
    }) || repetitions.iter().any(|repetition| {
        refined_rules
            .get(&repetition.rule)
            .is_none_or(|(first, observed)| !first || !observed)
    }) {
        return Err(SourceError::InvalidInventory);
    }
    Ok(())
}

fn validate_templates(
    units: &[WrittenUnit],
    templates: &[MacroTemplateSourceFacts],
    capture_slots: &[MacroCaptureSlotSourceFacts],
    expected: &BTreeSet<SourceUnitId>,
) -> Result<(), SourceError> {
    if templates.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceError::InvalidInventory);
    }

    let macro_rule_ancestors = nearest_macro_rule_ancestors(units)?;
    let mut actual = BTreeSet::new();
    for facts in templates {
        let unit = active_unit(units, facts.unit)?;
        let rule = active_unit(units, facts.rule)?;
        if !matches!(
            unit.kind,
            WrittenUnitKind::NestedItem | WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf
        ) || rule.kind != WrittenUnitKind::MacroRule
            || unit.full_range.is_empty()
            || macro_rule_ancestors[unit.id.0 as usize] != Some(rule.id)
            || !actual.insert(unit.id)
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    let capture_units = capture_slots
        .iter()
        .map(|slot| slot.unit)
        .collect::<BTreeSet<_>>();
    if capture_units.len() != capture_slots.len() || !actual.is_disjoint(&capture_units) {
        return Err(SourceError::InvalidInventory);
    }
    actual.extend(capture_units);
    (actual == *expected)
        .then_some(())
        .ok_or(SourceError::InvalidInventory)
}

fn nearest_macro_rule_ancestors(
    units: &[WrittenUnit],
) -> Result<Vec<Option<SourceUnitId>>, SourceError> {
    // 0 is unresolved, 1 is on the current parent chain, and 2 is resolved.
    let mut states = vec![0_u8; units.len()];
    let mut ancestors = vec![None; units.len()];
    for start in 0..units.len() {
        if states[start] == 2 {
            continue;
        }
        let mut path = Vec::new();
        let mut current = start;
        let ancestor = loop {
            match states.get(current).copied() {
                Some(2) => break ancestors[current],
                Some(1) | None => return Err(SourceError::InvalidInventory),
                Some(0) => {}
                _ => unreachable!("source ancestor traversal state is internal"),
            }
            states[current] = 1;
            path.push(current);
            let unit = &units[current];
            if unit.id.0 as usize != current {
                return Err(SourceError::InvalidInventory);
            }
            if unit.kind == WrittenUnitKind::MacroRule {
                break Some(unit.id);
            }
            let Some(parent) = unit.parent else {
                break None;
            };
            let parent_index = parent.0 as usize;
            if units.get(parent_index).is_none_or(|unit| unit.id != parent) {
                return Err(SourceError::InvalidInventory);
            }
            current = parent_index;
        };
        for index in path.into_iter().rev() {
            states[index] = 2;
            ancestors[index] = ancestor;
        }
    }
    Ok(ancestors)
}

fn validate_capture_slots(
    original: &str,
    units: &[WrittenUnit],
    macro_rules: &[MacroRuleSourceFacts],
    templates: &[MacroTemplateSourceFacts],
    slots: &[MacroCaptureSlotSourceFacts],
) -> Result<(), SourceError> {
    if slots.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceError::InvalidInventory);
    }
    if slots.is_empty() {
        return Ok(());
    }
    let parser_tokens =
        tokenize_parser_tokens(original).map_err(|_| SourceError::InvalidInventory)?;
    let rewrite_guard =
        ParserTokenRewriteGuard::new(original).map_err(|_| SourceError::InvalidInventory)?;
    let template_rules = templates
        .iter()
        .map(|template| (template.unit, template.rule))
        .collect::<BTreeMap<_, _>>();
    let slot_units = slots.iter().map(|slot| slot.unit).collect::<BTreeSet<_>>();
    if slot_units.len() != slots.len() {
        return Err(SourceError::InvalidInventory);
    }

    let mut rule_selection_counts = BTreeMap::new();
    for facts in macro_rules {
        let MacroRuleSourceFacts::Refined {
            rules,
            observed_selections,
            ..
        } = facts
        else {
            continue;
        };
        let Some(&first) = rules.first() else {
            return Err(SourceError::InvalidInventory);
        };
        if !observed_selections.is_empty()
            && observed_selections
                .iter()
                .all(|selection| *selection == first)
        {
            rule_selection_counts.insert(first, observed_selections.len());
        }
    }

    let mut matcher_deletions = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    let mut input_deletions = BTreeMap::<SourceUnitId, Vec<ByteRange>>::new();
    let mut invocations_by_rule = BTreeMap::<SourceUnitId, BTreeSet<SourceUnitId>>::new();
    let mut capture_order =
        BTreeMap::<(SourceUnitId, SourceUnitId), Vec<(ByteRange, ByteRange)>>::new();
    for slot in slots {
        let unit = active_unit(units, slot.unit)?;
        let rule = active_unit(units, slot.rule)?;
        let Some(&selection_count) = rule_selection_counts.get(&rule.id) else {
            return Err(SourceError::InvalidInventory);
        };
        if unit.kind != WrittenUnitKind::NestedItem
            || rule.kind != WrittenUnitKind::MacroRule
            || unit.parent != Some(rule.id)
            || slot.matcher_capture_range.is_empty()
            || !unit.full_range.contains(slot.matcher_capture_range)
            || !capture_slot_unit_shape(original, unit.full_range)
            || slot.trigger_units.windows(2).any(|pair| pair[0] >= pair[1])
            || slot.inputs.windows(2).any(|pair| pair[0] >= pair[1])
            || slot.inputs.len() != selection_count
        {
            return Err(SourceError::InvalidInventory);
        }
        let Some((matcher_deletion, matcher_separator)) =
            capture_deletion_layout(&parser_tokens, slot.matcher_capture_range)
        else {
            return Err(SourceError::InvalidInventory);
        };
        if matcher_deletion != unit.full_range
            || !rewrite_guard.deletion_preserves_identity(matcher_deletion)
        {
            return Err(SourceError::InvalidInventory);
        }
        matcher_deletions
            .entry(rule.id)
            .or_default()
            .push(matcher_deletion);

        for &trigger in &slot.trigger_units {
            let trigger = active_unit(units, trigger)?;
            if slot_units.contains(&trigger.id) || template_rules.get(&trigger.id) != Some(&rule.id)
            {
                return Err(SourceError::InvalidInventory);
            }
        }

        let mut slot_invocations = BTreeSet::new();
        for input in &slot.inputs {
            let invocation = active_unit(units, input.invocation)?;
            if invocation.kind != WrittenUnitKind::MacroInvocation
                || input.capture_range.is_empty()
                || input.deletion_range.start != input.capture_range.start
                || !input.deletion_range.contains(input.capture_range)
                || !invocation.full_range.contains(input.deletion_range)
                || !rewrite_guard.deletion_preserves_identity(input.deletion_range)
                || !slot_invocations.insert(invocation.id)
            {
                return Err(SourceError::InvalidInventory);
            }
            match matcher_separator {
                Some(separator) => {
                    if input.deletion_range == input.capture_range
                        || !same_single_parser_token(
                            original,
                            separator,
                            ByteRange {
                                start: input.capture_range.end,
                                end: input.deletion_range.end,
                            },
                        )
                    {
                        return Err(SourceError::InvalidInventory);
                    }
                }
                None if input.deletion_range != input.capture_range => {
                    return Err(SourceError::InvalidInventory);
                }
                None => {}
            }
            input_deletions
                .entry(invocation.id)
                .or_default()
                .push(input.deletion_range);
            capture_order
                .entry((rule.id, invocation.id))
                .or_default()
                .push((slot.matcher_capture_range, input.capture_range));
        }
        if invocations_by_rule
            .insert(rule.id, slot_invocations.clone())
            .is_some_and(|previous| previous != slot_invocations)
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    for captures in capture_order.values_mut() {
        captures.sort_by_key(|(matcher, _)| *matcher);
        if captures.windows(2).any(|pair| pair[0].1 >= pair[1].1) {
            return Err(SourceError::InvalidInventory);
        }
    }

    for ranges in matcher_deletions
        .values_mut()
        .chain(input_deletions.values_mut())
    {
        ranges.sort();
        if ranges
            .windows(2)
            .any(|pair| ranges_overlap(pair[0], pair[1]))
        {
            return Err(SourceError::InvalidInventory);
        }
    }
    Ok(())
}

fn capture_slot_unit_shape(source: &str, range: ByteRange) -> bool {
    let Some(source) = source.get(range.start as usize..range.end as usize) else {
        return false;
    };
    let Ok(tokens) = tokenize_parser_tokens(source) else {
        return false;
    };
    let body = match tokens.as_slice() {
        [body @ .., separator] if matches!(separator.text.as_str(), "," | ";") => body,
        body => body,
    };
    matches!(body, [dollar, _, colon, _] if dollar.text == "$" && colon.text == ":")
}

fn validate_repetitions(
    original: &str,
    units: &[WrittenUnit],
    repetitions: &[MacroRepetitionSourceFacts],
    expected_matcher_elements: &BTreeSet<SourceUnitId>,
) -> Result<(), SourceError> {
    if repetitions
        .windows(2)
        .any(|pair| repetition_key(&pair[0]) >= repetition_key(&pair[1]))
    {
        return Err(SourceError::InvalidInventory);
    }

    let expected_elements = repetitions
        .iter()
        .flat_map(|repetition| repetition.elements.iter().map(|element| element.unit))
        .collect::<BTreeSet<_>>();
    let mut actual_elements = BTreeSet::new();
    let mut element_owners = BTreeMap::new();
    let mut invocation_rules = BTreeMap::new();
    let mut matcher_identities = BTreeMap::<(SourceUnitId, &[u32]), ByteRange>::new();
    let mut sequence_inputs = Vec::new();

    for repetition in repetitions {
        let invocation = active_unit(units, repetition.invocation)?;
        let rule = active_unit(units, repetition.rule)?;
        let parent = active_unit(units, repetition.parent)?;
        if invocation.kind != WrittenUnitKind::MacroInvocation
            || rule.kind != WrittenUnitKind::MacroRule
            || !(parent.kind == WrittenUnitKind::MacroInvocation
                || expected_elements.contains(&parent.id))
            || repetition.repetition_path.is_empty()
            || repetition.minimum > 1
            || !matches!(
                (repetition.minimum, repetition.maximum),
                (0 | 1, None) | (0, Some(1))
            )
            || !valid_range(original, repetition.matcher_range)
            || repetition.matcher_range.is_empty()
            || !rule.full_range.contains(repetition.matcher_range)
            || !valid_range(original, repetition.input_range)
            || !parent.full_range.contains(repetition.input_range)
            || repetition
                .maximum
                .is_some_and(|maximum| repetition.elements.len() as u32 > maximum)
            || (repetition.elements.len() as u32) < repetition.minimum
        {
            return Err(SourceError::InvalidInventory);
        }
        if invocation_rules
            .insert(invocation.id, rule.id)
            .is_some_and(|previous| previous != rule.id)
        {
            return Err(SourceError::InvalidInventory);
        }
        let matcher_key = (rule.id, repetition.repetition_path.as_slice());
        if matcher_identities
            .insert(matcher_key, repetition.matcher_range)
            .is_some_and(|previous| previous != repetition.matcher_range)
        {
            return Err(SourceError::InvalidInventory);
        }
        sequence_inputs.push((
            invocation.id,
            parent.id,
            repetition.repetition_path.as_slice(),
            repetition.input_range,
        ));

        if repetition.parent == repetition.invocation {
            if parent.id != invocation.id {
                return Err(SourceError::InvalidInventory);
            }
        } else if !expected_elements.contains(&parent.id) {
            return Err(SourceError::InvalidInventory);
        }

        let elements = repetition
            .elements
            .iter()
            .map(|facts| active_unit(units, facts.unit))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some((first, last)) = elements.first().zip(elements.last()) {
            if repetition.input_range.start != first.full_range.start
                || repetition.input_range.end != last.full_range.end
            {
                return Err(SourceError::InvalidInventory);
            }
        } else if !repetition.input_range.is_empty() {
            return Err(SourceError::InvalidInventory);
        }

        let mut previous = None;
        let separated = repetition
            .elements
            .first()
            .and_then(|element| element.separator_after)
            .is_some();
        let mut separator_identity = None;
        for (index, (element_facts, element)) in
            repetition.elements.iter().zip(&elements).enumerate()
        {
            if element.kind != WrittenUnitKind::NestedItem
                || element.parent != Some(parent.id)
                || !actual_elements.insert(element.id)
                || !repetition.input_range.contains(element.full_range)
                || element.full_range.is_empty()
                || previous
                    .is_some_and(|previous: ByteRange| previous.end > element.full_range.start)
            {
                return Err(SourceError::InvalidInventory);
            }
            previous = Some(element.full_range);
            element_owners.insert(
                element.id,
                (
                    repetition.invocation,
                    repetition.rule,
                    repetition.repetition_path.as_slice(),
                ),
            );

            let separator = element_facts.separator_after;
            let has_following = index + 1 < repetition.elements.len();
            if separator.is_some() != (has_following && separated) {
                return Err(SourceError::InvalidInventory);
            }
            if let Some(separator) = separator {
                let next = elements
                    .get(index + 1)
                    .ok_or(SourceError::InvalidInventory)?;
                if !valid_range(original, separator)
                    || separator.is_empty()
                    || separator.start < element.full_range.end
                    || separator.end > next.full_range.start
                    || !repetition.input_range.contains(separator)
                    || !range_is_trivia(
                        original,
                        ByteRange {
                            start: element.full_range.end,
                            end: separator.start,
                        },
                    )
                    || !range_is_trivia(
                        original,
                        ByteRange {
                            start: separator.end,
                            end: next.full_range.start,
                        },
                    )
                {
                    return Err(SourceError::InvalidInventory);
                }
                let identity =
                    separator_token(original, separator).ok_or(SourceError::InvalidInventory)?;
                if separator_identity
                    .replace(identity.clone())
                    .is_some_and(|previous| previous != identity)
                {
                    return Err(SourceError::InvalidInventory);
                }
            } else if let Some(next) = elements.get(index + 1)
                && !range_is_trivia(
                    original,
                    ByteRange {
                        start: element.full_range.end,
                        end: next.full_range.start,
                    },
                )
            {
                return Err(SourceError::InvalidInventory);
            }
        }
    }

    if actual_elements != expected_elements || actual_elements != *expected_matcher_elements {
        return Err(SourceError::InvalidInventory);
    }

    for repetition in repetitions {
        if repetition.parent == repetition.invocation {
            continue;
        }
        let Some((parent_invocation, parent_rule, parent_path)) =
            element_owners.get(&repetition.parent)
        else {
            return Err(SourceError::InvalidInventory);
        };
        if *parent_invocation != repetition.invocation
            || *parent_rule != repetition.rule
            || parent_path.len() + 1 != repetition.repetition_path.len()
            || repetition.repetition_path[..parent_path.len()] != parent_path[..]
        {
            return Err(SourceError::InvalidInventory);
        }
    }

    sequence_inputs.sort_by_key(|(invocation, parent, _, range)| {
        (*invocation, *parent, range.start, range.end)
    });
    if sequence_inputs.windows(2).any(|pair| {
        pair[0].0 == pair[1].0 && pair[0].1 == pair[1].1 && ranges_overlap(pair[0].3, pair[1].3)
    }) {
        return Err(SourceError::InvalidInventory);
    }

    let mut matcher_siblings = BTreeMap::<(SourceUnitId, &[u32]), Vec<ByteRange>>::new();
    for ((rule, path), range) in &matcher_identities {
        let (_, parent_path) = path.split_last().ok_or(SourceError::InvalidInventory)?;
        if !parent_path.is_empty() {
            let parent_range = matcher_identities
                .get(&(*rule, parent_path))
                .ok_or(SourceError::InvalidInventory)?;
            if !parent_range.contains(*range) || parent_range == range {
                return Err(SourceError::InvalidInventory);
            }
        }
        matcher_siblings
            .entry((*rule, parent_path))
            .or_default()
            .push(*range);
    }
    for ranges in matcher_siblings.values_mut() {
        ranges.sort_by_key(|range| (range.start, range.end));
        if ranges
            .windows(2)
            .any(|pair| ranges_overlap(pair[0], pair[1]))
        {
            return Err(SourceError::InvalidInventory);
        }
    }
    Ok(())
}

fn repetition_key(repetition: &MacroRepetitionSourceFacts) -> (SourceUnitId, SourceUnitId, &[u32]) {
    (
        repetition.invocation,
        repetition.parent,
        &repetition.repetition_path,
    )
}

fn ranges_overlap(left: ByteRange, right: ByteRange) -> bool {
    left.start < right.end && right.start < left.end
}

fn range_is_trivia(source: &str, range: ByteRange) -> bool {
    let Some(input) = source.get(range.start as usize..range.end as usize) else {
        return false;
    };
    let mut length = 0_u32;
    for token in tokenize(input, FrontmatterAllowed::No) {
        let Some(end) = length.checked_add(token.len) else {
            return false;
        };
        length = end;
        if !is_trivia(token.kind) {
            return false;
        }
    }
    length == range.len()
}

fn separator_token(source: &str, range: ByteRange) -> Option<String> {
    let input = source.get(range.start as usize..range.end as usize)?;
    let tokens = tokenize_parser_tokens(input).ok()?;
    match tokens.as_slice() {
        [token] => Some(token.text.clone()),
        _ => None,
    }
}

fn active_unit(units: &[WrittenUnit], id: SourceUnitId) -> Result<&WrittenUnit, SourceError> {
    units
        .get(id.0 as usize)
        .filter(|unit| unit.id == id && unit.cfg_state == CfgState::Active)
        .ok_or(SourceError::InvalidInventory)
}

fn valid_range(source: &str, range: ByteRange) -> bool {
    range.start <= range.end
        && range.end as usize <= source.len()
        && source.is_char_boundary(range.start as usize)
        && source.is_char_boundary(range.end as usize)
}

#[cfg(test)]
mod tests {
    use super::super::MacroRuleSelectionIndex;
    use super::*;
    use crate::source::AtomicGroupId;

    #[cfg(rust_item_dependencies_patched)]
    fn candidate(rule: u32, start: u32, end: u32, is_use: bool) -> TemplateCandidate {
        TemplateCandidate {
            rule: SourceUnitId(rule),
            range: ByteRange { start, end },
            is_use,
        }
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn classifies_use_items_and_leaves_from_a_deep_containment_forest() {
        let mut candidates = BTreeSet::new();
        for depth in 0..128 {
            candidates.insert(candidate(1, depth, 256 - depth, true));
        }
        candidates.insert(candidate(1, 300, 310, false));
        candidates.insert(candidate(1, 320, 330, false));
        candidates.insert(candidate(1, 400, 450, false));
        candidates.insert(candidate(1, 410, 420, false));

        let layout = classify_template_candidates(&candidates).unwrap();
        let use_layout = layout
            .iter()
            .filter(|(_, kind, _)| {
                matches!(kind, WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf)
            })
            .copied()
            .collect::<Vec<_>>();

        assert_eq!(
            use_layout,
            vec![
                (candidate(1, 0, 256, true), WrittenUnitKind::UseItem, None,),
                (
                    candidate(1, 127, 129, true),
                    WrittenUnitKind::UseLeaf,
                    Some(ByteRange { start: 0, end: 256 }),
                ),
            ]
        );
        assert_eq!(
            layout
                .iter()
                .filter(|(_, kind, _)| *kind == WrittenUnitKind::NestedItem)
                .count(),
            4
        );
        assert_eq!(
            layout
                .iter()
                .find(|(candidate, _, _)| candidate.range
                    == ByteRange {
                        start: 410,
                        end: 420
                    })
                .and_then(|(_, _, parent)| *parent),
            Some(ByteRange {
                start: 400,
                end: 450
            })
        );
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn rejects_equal_and_partially_overlapping_template_candidates() {
        let equal = BTreeSet::from([candidate(1, 0, 10, false), candidate(1, 0, 10, true)]);
        assert_eq!(
            classify_template_candidates(&equal),
            Err(SourceError::IncompleteDeclarativeMacroObservation)
        );

        let partial = BTreeSet::from([candidate(1, 0, 10, false), candidate(1, 5, 15, false)]);
        assert_eq!(
            classify_template_candidates(&partial),
            Err(SourceError::IncompleteDeclarativeMacroObservation)
        );

        let siblings = BTreeSet::from([
            candidate(1, 0, 10, false),
            candidate(1, 10, 20, false),
            candidate(2, 5, 15, false),
        ]);
        assert_eq!(classify_template_candidates(&siblings).unwrap().len(), 3);
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn discarded_outputs_must_not_collectively_cover_a_live_product() {
        let range = |start, end| MacroOutputTokenRange { start, end };
        let live = [(range(0, 4), false)];

        assert!(!discarded_outputs_fit_live_products(
            &[range(0, 2), range(2, 4)],
            &live,
            4,
        ));
        assert!(!discarded_outputs_fit_live_products(
            &[range(0, 4)],
            &live,
            4,
        ));
        assert!(discarded_outputs_fit_live_products(
            &[range(1, 2), range(2, 3)],
            &live,
            4,
        ));
        assert!(discarded_outputs_fit_live_products(
            &[range(0, 1), range(2, 4)],
            &live,
            4,
        ));
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn discarded_output_runs_do_not_rescan_nested_live_products() {
        const COUNT: u32 = 32_768;
        let discarded = (1..=COUNT)
            .map(|start| MacroOutputTokenRange {
                start,
                end: start + 1,
            })
            .collect::<Vec<_>>();
        let products = (2..=COUNT + 1)
            .map(|end| (MacroOutputTokenRange { start: 0, end }, false))
            .collect::<Vec<_>>();

        assert!(discarded_outputs_fit_live_products(
            &discarded,
            &products,
            COUNT as usize + 1,
        ));
    }

    #[cfg(rust_item_dependencies_patched)]
    #[test]
    fn template_component_lookup_visits_a_large_laminar_layout_once() {
        const COUNT: u32 = 20_000;
        let components = (0..COUNT)
            .map(|index| ByteRange {
                start: index * 4 + 1,
                end: index * 4 + 2,
            })
            .collect::<BTreeSet<_>>();
        let candidates = (0..COUNT)
            .map(|index| (candidate(1, index * 4, index * 4 + 3, false), index + 10))
            .collect::<Vec<_>>();

        let resolved = template_component_units(&components, &candidates).unwrap();
        assert_eq!(resolved.len(), COUNT as usize);
        for (index, component) in components.into_iter().enumerate() {
            assert_eq!(resolved[&component], index as u32 + 10);
        }
    }

    #[test]
    fn component_repetition_ancestry_is_linear_and_fails_closed() {
        let mut parents = vec![None];
        parents.extend((1..1024).map(|index| Some(index - 1)));
        let mut repetitions = vec![false; 1024];
        repetitions[512] = true;

        let ancestry = component_repetition_ancestors(&parents, &repetitions).unwrap();
        assert!(ancestry[..512].iter().all(|repeated| !repeated));
        assert!(ancestry[512..].iter().all(|repeated| *repeated));
        let closure = component_flag_closure(&parents, &repetitions).unwrap();
        assert!(closure.descendants[..=512].iter().all(|repeated| *repeated));
        assert!(closure.descendants[513..].iter().all(|repeated| !repeated));
        assert!(component_repetition_ancestors(&parents, &repetitions[..1023]).is_none());

        let mut missing = parents.clone();
        missing[1] = Some(usize::MAX);
        assert!(component_repetition_ancestors(&missing, &repetitions).is_none());

        let mut cycle = parents;
        cycle[1] = Some(2);
        cycle[2] = Some(1);
        assert!(component_repetition_ancestors(&cycle, &repetitions).is_none());
    }

    #[test]
    fn template_token_range_index_queries_nested_equal_and_invalid_ranges() {
        let ranges = [
            Some(ByteRange { start: 10, end: 11 }),
            Some(ByteRange { start: 20, end: 22 }),
            None,
            Some(ByteRange { start: 5, end: 6 }),
            Some(ByteRange { start: 30, end: 35 }),
            Some(ByteRange { start: 40, end: 40 }),
        ];
        let index = TemplateTokenRangeIndex::new(&ranges).unwrap();
        let nested = ByteRange { start: 10, end: 22 };
        assert_eq!(index.source_range(0, 2), Some(nested));
        assert_eq!(index.source_range(0, 2), Some(nested));
        assert_eq!(
            index.source_range(3, 5),
            Some(ByteRange { start: 5, end: 35 })
        );
        assert_eq!(index.source_range(1, 3), None);
        assert_eq!(index.source_range(5, 6), None);
        assert_eq!(index.source_range(0, 0), None);
        assert_eq!(index.source_range(0, 7), None);

        let deep = (0..1024)
            .map(|index| {
                Some(ByteRange {
                    start: 2048 - index,
                    end: 4096 + index,
                })
            })
            .collect::<Vec<_>>();
        let deep = TemplateTokenRangeIndex::new(&deep).unwrap();
        assert_eq!(
            deep.source_range(0, 1024),
            Some(ByteRange {
                start: 1025,
                end: 5119,
            })
        );
    }

    #[test]
    fn nearest_macro_rule_ancestors_are_memoized_and_fail_closed() {
        let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, 1), None)];
        units.push(unit(1, WrittenUnitKind::MacroRule, (0, 1), Some(0)));
        for id in 2..1026 {
            units.push(unit(id, WrittenUnitKind::NestedItem, (0, 1), Some(id - 1)));
        }
        units.push(unit(1026, WrittenUnitKind::MacroRule, (0, 1), Some(0)));
        units.push(unit(1027, WrittenUnitKind::NestedItem, (0, 1), Some(1026)));
        units.push(unit(1028, WrittenUnitKind::Item, (0, 1), Some(0)));

        let ancestors = nearest_macro_rule_ancestors(&units).unwrap();
        assert_eq!(ancestors[0], None);
        assert_eq!(ancestors[1], Some(SourceUnitId(1)));
        assert_eq!(ancestors[1025], Some(SourceUnitId(1)));
        assert_eq!(ancestors[1026], Some(SourceUnitId(1026)));
        assert_eq!(ancestors[1027], Some(SourceUnitId(1026)));
        assert_eq!(ancestors[1028], None);

        let mut missing = units.clone();
        missing[2].parent = Some(SourceUnitId(u32::MAX));
        assert_eq!(
            nearest_macro_rule_ancestors(&missing),
            Err(SourceError::InvalidInventory)
        );

        let mut wrong_id = units.clone();
        wrong_id[2].id = SourceUnitId(99);
        assert_eq!(
            nearest_macro_rule_ancestors(&wrong_id),
            Err(SourceError::InvalidInventory)
        );

        let mut cycle = units;
        cycle[2].parent = Some(SourceUnitId(3));
        cycle[3].parent = Some(SourceUnitId(2));
        assert_eq!(
            nearest_macro_rule_ancestors(&cycle),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn macro_rule_selection_index_is_keyed_and_preserves_ambiguity() {
        let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, 4096), None)];
        units.push(unit(
            1,
            WrittenUnitKind::MacroDefinition,
            (0, 2048),
            Some(0),
        ));
        units.push(unit(
            2,
            WrittenUnitKind::MacroDefinition,
            (512, 1024),
            Some(1),
        ));
        for index in 0..1024 {
            let id = index + 3;
            let start = 2048 + index;
            units.push(unit(
                id,
                WrittenUnitKind::MacroRule,
                (start, start + 1),
                Some(0),
            ));
        }
        let facts = vec![
            MacroRuleSourceFacts::Whole {
                definition: SourceUnitId(1),
            },
            MacroRuleSourceFacts::Whole {
                definition: SourceUnitId(2),
            },
        ];
        let index = MacroRuleSelectionIndex::new(&units, &facts).unwrap();
        for offset in 0..1024 {
            assert_eq!(
                index.selected_rule(ByteRange {
                    start: 2048 + offset,
                    end: 2049 + offset,
                }),
                Ok(Some(SourceUnitId(offset + 3)))
            );
        }
        assert_eq!(
            index.selected_rule(ByteRange {
                start: 1200,
                end: 1300,
            }),
            Ok(None)
        );
        assert_eq!(
            index.selected_rule(ByteRange {
                start: 600,
                end: 700,
            }),
            Err(SourceError::IncompleteMacroRuleObservation)
        );
        assert_eq!(
            index.selected_rule(ByteRange {
                start: 3000,
                end: 3500,
            }),
            Err(SourceError::IncompleteMacroRuleObservation)
        );

        let duplicate_range = units[3].full_range;
        units.push(unit(
            u32::try_from(units.len()).unwrap(),
            WrittenUnitKind::MacroRule,
            (duplicate_range.start, duplicate_range.end),
            Some(0),
        ));
        let ambiguous = MacroRuleSelectionIndex::new(&units, &facts).unwrap();
        assert_eq!(
            ambiguous.selected_rule(duplicate_range),
            Err(SourceError::InvalidInventory)
        );

        let malformed = vec![MacroRuleSourceFacts::Whole {
            definition: SourceUnitId(u32::MAX),
        }];
        assert!(matches!(
            MacroRuleSelectionIndex::new(&units, &malformed),
            Err(SourceError::InvalidInventory)
        ));
    }

    #[test]
    fn declarative_child_links_are_indexed_once_and_require_unique_valid_facts() {
        let mut links = FxHashMap::default();
        for child in 0..1024 {
            record_unique_valid_link(&mut links, 0, child, true);
        }
        assert_eq!(links.len(), 1024);
        assert!(links.values().all(|valid| *valid));

        record_unique_valid_link(&mut links, 0, 1, true);
        record_unique_valid_link(&mut links, 0, 2, false);
        record_unique_valid_link(&mut links, 1, 3, false);
        assert_eq!(links.get(&(0, 1)), Some(&false));
        assert_eq!(links.get(&(0, 2)), Some(&false));
        assert_eq!(links.get(&(1, 3)), Some(&false));
        assert_eq!(links.get(&(1, 4)), None);
    }

    #[test]
    fn discovered_inner_macro_parent_wins_over_outer_source_context() {
        let inner_builtin_or_attribute = 7_u32;
        let outer_source_context = 3_u32;
        assert_eq!(
            crate::source::declarative_generation_parent(
                Some(inner_builtin_or_attribute),
                Some(outer_source_context),
            ),
            Some(inner_builtin_or_attribute),
        );
        assert_eq!(
            crate::source::declarative_generation_parent(None, Some(outer_source_context)),
            Some(outer_source_context),
        );
        assert_eq!(
            crate::source::resolve_declarative_contributor_parent(
                Some(inner_builtin_or_attribute),
                true,
                Some(
                    crate::source::DeclarativeGenerationParentState::RefinedLocal {
                        link_complete: true,
                    }
                ),
            ),
            crate::source::DeclarativeContributorParent::Parent(inner_builtin_or_attribute),
        );
        assert_eq!(
            crate::source::resolve_declarative_contributor_parent(
                Some(inner_builtin_or_attribute),
                true,
                Some(crate::source::DeclarativeGenerationParentState::Opaque),
            ),
            crate::source::DeclarativeContributorParent::Root,
        );
        assert_eq!(
            crate::source::resolve_declarative_contributor_parent(
                Some(inner_builtin_or_attribute),
                true,
                Some(
                    crate::source::DeclarativeGenerationParentState::RefinedLocal {
                        link_complete: false,
                    }
                ),
            ),
            crate::source::DeclarativeContributorParent::Incomplete,
        );
        assert_eq!(
            crate::source::resolve_declarative_contributor_parent(
                Some(inner_builtin_or_attribute),
                true,
                Some(crate::source::DeclarativeGenerationParentState::LocalIncomplete),
            ),
            crate::source::DeclarativeContributorParent::Incomplete,
            "an editable anchor must not hide an incomplete local declarative parent",
        );
    }

    fn unit(id: u32, kind: WrittenUnitKind, range: (u32, u32), parent: Option<u32>) -> WrittenUnit {
        WrittenUnit {
            id: SourceUnitId(id),
            kind,
            full_range: ByteRange {
                start: range.0,
                end: range.1,
            },
            parent: parent.map(SourceUnitId),
            cfg_state: CfgState::Active,
            atomic_group: AtomicGroupId(id),
            same_role_ordinal: id,
        }
    }

    fn refined_rules(
        definition: u32,
        rules: &[u32],
        observed: &[u32],
    ) -> Vec<MacroRuleSourceFacts> {
        vec![MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(definition),
            rules: rules.iter().copied().map(SourceUnitId).collect(),
            observed_selections: observed.iter().copied().map(SourceUnitId).collect(),
        }]
    }

    fn nested_layout() -> (
        String,
        Vec<WrittenUnit>,
        Vec<MacroRuleSourceFacts>,
        Vec<MacroTemplateSourceFacts>,
        Vec<MacroRepetitionSourceFacts>,
    ) {
        let mut source = " ".repeat(80);
        source.replace_range(43..44, ",");
        source.replace_range(55..56, ",");
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 80), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 30), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (5, 28), Some(1)),
            unit(3, WrittenUnitKind::NestedItem, (16, 25), Some(2)),
            unit(4, WrittenUnitKind::MacroInvocation, (31, 79), Some(0)),
            unit(5, WrittenUnitKind::NestedItem, (35, 55), Some(4)),
            unit(6, WrittenUnitKind::NestedItem, (39, 43), Some(5)),
            unit(7, WrittenUnitKind::NestedItem, (46, 50), Some(5)),
            unit(8, WrittenUnitKind::NestedItem, (58, 72), Some(4)),
        ];
        let templates = vec![MacroTemplateSourceFacts {
            unit: SourceUnitId(3),
            rule: SourceUnitId(2),
        }];
        let repetitions = vec![
            MacroRepetitionSourceFacts {
                invocation: SourceUnitId(4),
                rule: SourceUnitId(2),
                matcher_range: ByteRange { start: 6, end: 15 },
                parent: SourceUnitId(4),
                repetition_path: vec![0],
                input_range: ByteRange { start: 35, end: 72 },
                elements: vec![
                    MacroRepetitionElementSourceFacts {
                        unit: SourceUnitId(5),
                        separator_after: Some(ByteRange { start: 55, end: 56 }),
                    },
                    MacroRepetitionElementSourceFacts {
                        unit: SourceUnitId(8),
                        separator_after: None,
                    },
                ],
                minimum: 1,
                maximum: None,
            },
            MacroRepetitionSourceFacts {
                invocation: SourceUnitId(4),
                rule: SourceUnitId(2),
                matcher_range: ByteRange { start: 8, end: 12 },
                parent: SourceUnitId(5),
                repetition_path: vec![0, 1],
                input_range: ByteRange { start: 39, end: 50 },
                elements: vec![
                    MacroRepetitionElementSourceFacts {
                        unit: SourceUnitId(6),
                        separator_after: Some(ByteRange { start: 43, end: 44 }),
                    },
                    MacroRepetitionElementSourceFacts {
                        unit: SourceUnitId(7),
                        separator_after: None,
                    },
                ],
                minimum: 0,
                maximum: None,
            },
        ];
        (
            source,
            units,
            refined_rules(1, &[2], &[2]),
            templates,
            repetitions,
        )
    }

    #[test]
    fn accepts_template_and_nested_repetition_layouts() {
        let (source, units, macro_rules, templates, repetitions) = nested_layout();

        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Ok(())
        );
    }

    #[test]
    fn accepts_one_compound_parser_token_as_a_repetition_separator() {
        let (mut source, units, macro_rules, templates, mut repetitions) = nested_layout();
        source.replace_range(55..57, "=>");
        repetitions[0].elements[0].separator_after = Some(ByteRange { start: 55, end: 57 });

        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Ok(())
        );
    }

    #[test]
    fn capture_slots_require_a_complete_synchronized_layout() {
        let source = "macro_rules! m { ($a:tt,$b:tt,$c:tt) => { fn $a() {} fn $b() {} fn $c() {} } }\n\
m!( left,middle,right);\n\
m!(other,spare,unused);\n";
        let nth = |text: &str, index: usize| {
            let (start, _) = source.match_indices(text).nth(index).unwrap();
            ByteRange {
                start: start as u32,
                end: (start + text.len()) as u32,
            }
        };
        let definition = nth(
            "macro_rules! m { ($a:tt,$b:tt,$c:tt) => { fn $a() {} fn $b() {} fn $c() {} } }",
            0,
        );
        let rule = nth(
            "($a:tt,$b:tt,$c:tt) => { fn $a() {} fn $b() {} fn $c() {} }",
            0,
        );
        let matcher_a = nth("$a:tt", 0);
        let matcher_b = nth("$b:tt", 0);
        let matcher_c = nth("$c:tt", 0);
        let matcher_a_deletion = ByteRange {
            start: matcher_a.start,
            end: matcher_a.end + 1,
        };
        let matcher_b_deletion = ByteRange {
            start: matcher_b.start,
            end: matcher_b.end + 1,
        };
        let trigger_a = nth("fn $a() {}", 0);
        let trigger_b = nth("fn $b() {}", 0);
        let trigger_c = nth("fn $c() {}", 0);
        let first_invocation = nth("m!( left,middle,right);", 0);
        let second_invocation = nth("m!(other,spare,unused);", 0);
        let left = nth("left", 0);
        let middle = nth("middle", 0);
        let right = nth("right", 0);
        let other = nth("other", 0);
        let spare = nth("spare", 0);
        let unused = nth("unused", 0);
        let units = vec![
            unit(
                0,
                WrittenUnitKind::CrateRoot,
                (0, source.len() as u32),
                None,
            ),
            unit(
                1,
                WrittenUnitKind::MacroDefinition,
                (definition.start, definition.end),
                Some(0),
            ),
            unit(
                2,
                WrittenUnitKind::MacroRule,
                (rule.start, rule.end),
                Some(1),
            ),
            unit(
                3,
                WrittenUnitKind::NestedItem,
                (matcher_a_deletion.start, matcher_a_deletion.end),
                Some(2),
            ),
            unit(
                4,
                WrittenUnitKind::NestedItem,
                (matcher_b_deletion.start, matcher_b_deletion.end),
                Some(2),
            ),
            unit(
                5,
                WrittenUnitKind::NestedItem,
                (matcher_c.start, matcher_c.end),
                Some(2),
            ),
            unit(
                6,
                WrittenUnitKind::NestedItem,
                (trigger_a.start, trigger_a.end),
                Some(2),
            ),
            unit(
                7,
                WrittenUnitKind::NestedItem,
                (trigger_b.start, trigger_b.end),
                Some(2),
            ),
            unit(
                8,
                WrittenUnitKind::NestedItem,
                (trigger_c.start, trigger_c.end),
                Some(2),
            ),
            unit(
                9,
                WrittenUnitKind::MacroInvocation,
                (first_invocation.start, first_invocation.end),
                Some(0),
            ),
            unit(
                10,
                WrittenUnitKind::MacroInvocation,
                (second_invocation.start, second_invocation.end),
                Some(0),
            ),
        ];
        let macro_rules = refined_rules(1, &[2], &[2, 2]);
        let templates = (6..=8)
            .map(|unit| MacroTemplateSourceFacts {
                unit: SourceUnitId(unit),
                rule: SourceUnitId(2),
            })
            .collect::<Vec<_>>();
        let inputs = |first: ByteRange, second: ByteRange, separator: bool| {
            [(SourceUnitId(9), first), (SourceUnitId(10), second)]
                .into_iter()
                .map(|(invocation, capture_range)| MacroCaptureInputSourceFacts {
                    invocation,
                    capture_range,
                    deletion_range: ByteRange {
                        start: capture_range.start,
                        end: capture_range.end + u32::from(separator),
                    },
                })
                .collect::<Vec<_>>()
        };
        let slots = vec![
            MacroCaptureSlotSourceFacts {
                unit: SourceUnitId(3),
                rule: SourceUnitId(2),
                matcher_capture_range: matcher_a,
                trigger_units: vec![SourceUnitId(6)],
                inputs: inputs(left, other, true),
            },
            MacroCaptureSlotSourceFacts {
                unit: SourceUnitId(4),
                rule: SourceUnitId(2),
                matcher_capture_range: matcher_b,
                trigger_units: vec![SourceUnitId(7)],
                inputs: inputs(middle, spare, true),
            },
            MacroCaptureSlotSourceFacts {
                unit: SourceUnitId(5),
                rule: SourceUnitId(2),
                matcher_capture_range: matcher_c,
                trigger_units: vec![SourceUnitId(8)],
                inputs: inputs(right, unused, false),
            },
        ];

        assert_eq!(
            validate_declarative_macro_source_facts(
                source,
                &units,
                &macro_rules,
                &templates,
                &slots,
                &[],
            ),
            Ok(())
        );

        assert_eq!(
            validate_declarative_macro_source_facts(
                source,
                &units,
                &macro_rules,
                &templates,
                &slots[..1],
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );

        let mut reordered = slots.clone();
        let first_capture = reordered[0].inputs[0].capture_range;
        let first_deletion = reordered[0].inputs[0].deletion_range;
        reordered[0].inputs[0].capture_range = reordered[1].inputs[0].capture_range;
        reordered[0].inputs[0].deletion_range = reordered[1].inputs[0].deletion_range;
        reordered[1].inputs[0].capture_range = first_capture;
        reordered[1].inputs[0].deletion_range = first_deletion;
        assert_eq!(
            validate_declarative_macro_source_facts(
                source,
                &units,
                &macro_rules,
                &templates,
                &reordered,
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );

        let mut extended = slots.clone();
        extended[0].inputs[0].deletion_range.start -= 1;
        assert_eq!(
            validate_declarative_macro_source_facts(
                source,
                &units,
                &macro_rules,
                &templates,
                &extended,
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );

        let mut incomplete = slots;
        incomplete[2].inputs.pop();
        assert_eq!(
            validate_declarative_macro_source_facts(
                source,
                &units,
                &macro_rules,
                &templates,
                &incomplete,
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn capture_trigger_index_visits_each_component_once() {
        const COUNT: u32 = 20_000;
        let slots = (0..COUNT)
            .map(|index| ByteRange {
                start: index * 4,
                end: index * 4 + 1,
            })
            .collect::<Vec<_>>();
        let component_captures = slots
            .iter()
            .enumerate()
            .map(|(index, &capture)| {
                (
                    ByteRange {
                        start: COUNT * 4 + index as u32 * 2,
                        end: COUNT * 4 + index as u32 * 2 + 1,
                    },
                    capture,
                )
            })
            .collect::<BTreeMap<_, _>>();
        let component_units = component_captures
            .keys()
            .enumerate()
            .map(|(index, &component)| (component, index as u32))
            .collect::<BTreeMap<_, _>>();
        let mut visits = 0;

        let indexed =
            capture_trigger_units_with_work(slots, &component_captures, &component_units, || {
                visits += 1
            })
            .unwrap();

        assert_eq!(visits, COUNT as usize);
        assert_eq!(indexed.len(), COUNT as usize);
        assert!(indexed.values().all(|units| units.len() == 1));
    }

    #[test]
    fn templates_require_an_observed_rule_but_not_the_first_rule() {
        let source = " ".repeat(100);
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 100), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 40), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (2, 15), Some(1)),
            unit(3, WrittenUnitKind::MacroRule, (16, 38), Some(1)),
            unit(4, WrittenUnitKind::NestedItem, (25, 30), Some(3)),
        ];
        let templates = vec![MacroTemplateSourceFacts {
            unit: SourceUnitId(4),
            rule: SourceUnitId(3),
        }];
        let observed_second = refined_rules(1, &[2, 3], &[3]);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &observed_second,
                &templates,
                &[],
                &[],
            ),
            Ok(())
        );

        let unobserved_second = refined_rules(1, &[2, 3], &[2]);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &unobserved_second,
                &templates,
                &[],
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn repetitions_require_the_observed_first_rule_in_source_order() {
        let source = " ".repeat(100);
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 100), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 40), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (2, 15), Some(1)),
            unit(3, WrittenUnitKind::MacroRule, (16, 38), Some(1)),
            unit(4, WrittenUnitKind::MacroInvocation, (50, 90), Some(0)),
        ];
        let repetitions = vec![MacroRepetitionSourceFacts {
            invocation: SourceUnitId(4),
            rule: SourceUnitId(3),
            matcher_range: ByteRange { start: 20, end: 25 },
            parent: SourceUnitId(4),
            repetition_path: vec![0],
            input_range: ByteRange { start: 60, end: 60 },
            elements: Vec::new(),
            minimum: 0,
            maximum: Some(1),
        }];
        let observed_second = refined_rules(1, &[2, 3], &[3]);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &observed_second,
                &[],
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );

        let reordered = refined_rules(1, &[3, 2], &[3]);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &reordered,
                &[],
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn rejects_a_template_assigned_to_a_non_nearest_rule() {
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 100), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 60), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (5, 55), Some(1)),
            unit(3, WrittenUnitKind::MacroDefinition, (10, 50), Some(2)),
            unit(4, WrittenUnitKind::MacroRule, (15, 45), Some(3)),
            unit(5, WrittenUnitKind::NestedItem, (20, 30), Some(4)),
        ];
        let templates = vec![MacroTemplateSourceFacts {
            unit: SourceUnitId(5),
            rule: SourceUnitId(2),
        }];
        let mut macro_rules = refined_rules(1, &[2], &[2]);
        macro_rules.extend(refined_rules(3, &[4], &[4]));

        assert_eq!(
            validate_declarative_macro_source_facts(
                &" ".repeat(100),
                &units,
                &macro_rules,
                &templates,
                &[],
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn rejects_noncanonical_and_incomplete_repetition_facts() {
        let (source, units, macro_rules, templates, mut repetitions) = nested_layout();
        repetitions.swap(0, 1);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );

        let (mut source, units, macro_rules, templates, repetitions) = nested_layout();
        source.replace_range(44..45, "+");
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn rejects_last_separators_and_invalid_element_ids_without_panicking() {
        let (source, units, macro_rules, templates, mut repetitions) = nested_layout();
        repetitions[0].elements[1].separator_after = Some(ByteRange { start: 72, end: 73 });
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );

        let (source, units, macro_rules, templates, mut repetitions) = nested_layout();
        repetitions[0].elements[1].unit = SourceUnitId(u32::MAX);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn rejects_non_immediate_nested_paths_and_rule_mismatches() {
        let (source, units, macro_rules, templates, mut repetitions) = nested_layout();
        repetitions[1].repetition_path = vec![0, 1, 2];
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );

        let (source, mut units, mut macro_rules, templates, mut repetitions) = nested_layout();
        units.push(unit(9, WrittenUnitKind::MacroRule, (5, 28), Some(1)));
        let MacroRuleSourceFacts::Refined { rules, .. } = &mut macro_rules[0] else {
            unreachable!()
        };
        rules.push(SourceUnitId(9));
        repetitions[1].rule = SourceUnitId(9);
        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &templates,
                &[],
                &repetitions,
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn accepts_an_empty_optional_repetition_at_an_observed_input_point() {
        let source = " ".repeat(40);
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 40), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 15), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (2, 13), Some(1)),
            unit(3, WrittenUnitKind::MacroInvocation, (20, 39), Some(0)),
        ];
        let repetitions = vec![MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(2),
            matcher_range: ByteRange { start: 3, end: 8 },
            parent: SourceUnitId(3),
            repetition_path: vec![0],
            input_range: ByteRange { start: 24, end: 24 },
            elements: Vec::new(),
            minimum: 0,
            maximum: Some(1),
        }];
        let macro_rules = refined_rules(1, &[2], &[2]);

        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &[],
                &[],
                &repetitions,
            ),
            Ok(())
        );
    }

    #[test]
    fn rejects_overlapping_sibling_matcher_identities() {
        let source = " ".repeat(40);
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 40), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 15), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (2, 13), Some(1)),
            unit(3, WrittenUnitKind::MacroInvocation, (20, 39), Some(0)),
        ];
        let repetition = MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(2),
            matcher_range: ByteRange { start: 3, end: 8 },
            parent: SourceUnitId(3),
            repetition_path: vec![0],
            input_range: ByteRange { start: 24, end: 24 },
            elements: Vec::new(),
            minimum: 0,
            maximum: Some(1),
        };
        let mut overlapping = repetition.clone();
        overlapping.matcher_range = ByteRange { start: 6, end: 10 };
        overlapping.repetition_path = vec![1];
        let macro_rules = refined_rules(1, &[2], &[2]);

        assert_eq!(
            validate_declarative_macro_source_facts(
                &source,
                &units,
                &macro_rules,
                &[],
                &[],
                &[repetition, overlapping],
            ),
            Err(SourceError::InvalidInventory)
        );
    }

    #[test]
    fn rejects_unclassified_matcher_elements() {
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 40), None),
            unit(1, WrittenUnitKind::MacroDefinition, (0, 15), Some(0)),
            unit(2, WrittenUnitKind::MacroRule, (2, 13), Some(1)),
            unit(3, WrittenUnitKind::MacroInvocation, (20, 39), Some(0)),
            unit(4, WrittenUnitKind::NestedItem, (24, 30), Some(3)),
        ];
        let macro_rules = refined_rules(1, &[2], &[]);

        assert_eq!(
            validate_declarative_macro_source_facts(
                &" ".repeat(40),
                &units,
                &macro_rules,
                &[],
                &[],
                &[],
            ),
            Err(SourceError::InvalidInventory)
        );
    }
}
