use std::collections::BTreeMap;
#[cfg(rust_item_dependencies_patched)]
use std::collections::BTreeSet;

use crate::source::{
    AtomicGroupId, ByteRange, CfgState, MacroCaptureInputSourceFacts, MacroCaptureSlotSourceFacts,
    MacroRepetitionElementSourceFacts, MacroRepetitionSourceFacts, MacroRuleSelectionIndex,
    MacroRuleSourceFacts, MacroTemplateSourceFacts, SourceError, SourceUnitId, WrittenUnit,
    WrittenUnitKind,
};

use super::capture::capture_trigger_units_with_work;
#[cfg(rust_item_dependencies_patched)]
use super::capture::template_component_units;
#[cfg(rust_item_dependencies_patched)]
use super::template::{TemplateCandidate, classify_template_candidates};
use super::template::{
    TemplateTokenRangeIndex, component_flag_closure, component_repetition_ancestors,
};
use super::validation::{nearest_macro_rule_ancestors, validate_declarative_macro_source_facts};

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
        .filter(|(_, kind, _)| matches!(kind, WrittenUnitKind::UseItem | WrittenUnitKind::UseLeaf))
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
fn template_component_lookup_visits_a_large_laminar_layout_once() {
    const COUNT: u32 = 20_000;
    let components = (0..COUNT)
        .map(|index| ByteRange {
            start: index * 4 + 1,
            end: index * 4 + 2,
        })
        .collect::<BTreeSet<_>>();
    let candidates = (0..COUNT)
        .map(|index| {
            (
                ByteRange {
                    start: index * 4,
                    end: index * 4 + 3,
                },
                index + 10,
            )
        })
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

fn refined_rules(definition: u32, rules: &[u32], observed: &[u32]) -> Vec<MacroRuleSourceFacts> {
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
