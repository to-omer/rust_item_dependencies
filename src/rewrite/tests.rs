use std::sync::Arc;

use crate::source::{
    CfgState, DeriveAttributeSourceFacts, DeriveTargetSourceFacts,
    MacroRepetitionElementSourceFacts, MacroRepetitionSourceFacts, OriginalOffsetMap, OwnedPiece,
    PieceKind, SourceInventory, WrittenUnit,
};

use super::macro_repetition::{
    deletions_preserve_parser_tokens, macro_repetition_deletions, rewrite_macro_repetition,
};
use super::*;

#[test]
fn rewrites_nested_use_leaves_and_maps_every_retained_byte() {
    let source = "use x::{a, /* b */ b, c};\nfn dead() {}\nfn main() {}\n";
    let inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::UseItem, 0, 25, 0, 1),
            unit(WrittenUnitKind::UseLeaf, 8, 9, 1, 2),
            unit(WrittenUnitKind::UseLeaf, 19, 20, 1, 3),
            unit(WrittenUnitKind::UseLeaf, 22, 23, 1, 4),
            unit(WrittenUnitKind::Item, 26, 38, 0, 5),
            unit(WrittenUnitKind::Item, 39, 51, 0, 6),
        ],
    );
    let retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(3),
        SourceUnitId(6),
    ]);

    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(actual.source, "use x::{ /* b */ b};\n\nfn main() {}\n");
    assert_eq!(
        actual.pieces,
        vec![
            piece(0, 8, 0, 8),
            piece(8, 18, 10, 20),
            piece(18, 21, 23, 26),
            piece(21, 35, 38, 52),
        ]
    );
    assert_piece_map(&inventory.original, &actual);
}

#[test]
fn keeps_original_encoding_while_removing_nested_first_middle_and_last_leaves() {
    let source = concat!(
        "\u{feff}use crate::{α, nested::{first, /* 二 */ second, third}, glob::*};\r\n",
        "fn main() {}\r\n",
    );
    let use_range = marker(
        source,
        "use crate::{α, nested::{first, /* 二 */ second, third}, glob::*};",
    );
    let alpha = marker(source, "α");
    let first = marker(source, "first");
    let second = marker(source, "second");
    let third = marker(source, "third");
    let glob = marker(source, "glob::*");
    let main = marker(source, "fn main() {}");
    let inventory = inventory(
        source,
        &[
            unit(
                WrittenUnitKind::UseItem,
                use_range.start,
                use_range.end,
                0,
                1,
            ),
            unit(WrittenUnitKind::UseLeaf, alpha.start, alpha.end, 1, 2),
            unit(WrittenUnitKind::UseLeaf, first.start, first.end, 1, 3),
            unit(WrittenUnitKind::UseLeaf, second.start, second.end, 1, 4),
            unit(WrittenUnitKind::UseLeaf, third.start, third.end, 1, 5),
            unit(WrittenUnitKind::UseLeaf, glob.start, glob.end, 1, 6),
            unit(WrittenUnitKind::Item, main.start, main.end, 0, 7),
        ],
    );
    let retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(4),
        SourceUnitId(7),
    ]);

    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(
        actual.source,
        concat!(
            "\u{feff}use crate::{α, nested::{ /* 二 */ second}};\r\n",
            "fn main() {}\r\n",
        )
    );
    assert_piece_map(&inventory.original, &actual);
}

#[test]
fn deleting_a_use_item_deletes_every_leaf() {
    let source = "use x::{a, b};\nfn main() {}\n";
    let inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::UseItem, 0, 14, 0, 1),
            unit(WrittenUnitKind::UseLeaf, 8, 9, 1, 2),
            unit(WrittenUnitKind::UseLeaf, 11, 12, 1, 3),
            unit(WrittenUnitKind::Item, 15, 27, 0, 4),
        ],
    );
    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(4)]);

    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(actual.source, "\nfn main() {}\n");
    assert_eq!(actual.pieces, vec![piece(0, 14, 14, 28)]);

    assert_eq!(
        rewrite_source(
            &inventory,
            &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(4)])
        ),
        Err(SourceRewriteError::InvalidRetention)
    );
}

#[test]
fn preserves_or_deletes_an_empty_use_item() {
    let source = "use {};fn main(){}";
    let inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::UseItem, 0, 7, 0, 1),
            unit(WrittenUnitKind::Item, 7, 18, 0, 2),
        ],
    );

    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)]);
    let unchanged = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(unchanged.source, source);
    assert_piece_map(&inventory.original, &unchanged);

    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(2)]);
    let reduced = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(reduced.source, "fn main(){}");
    assert_eq!(reduced.pieces, vec![piece(0, 11, 7, 18)]);
    assert_piece_map(&inventory.original, &reduced);
}

#[test]
fn rejects_retention_that_splits_parents_or_atomic_groups() {
    let source = "mod m { fn f() {} }\n";
    let inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::InlineModule, 0, 19, 0, 1),
            unit(WrittenUnitKind::Item, 8, 17, 1, 2),
            unit(WrittenUnitKind::MacroInvocation, 8, 17, 2, 2),
        ],
    );
    assert_eq!(
        rewrite_source(
            &inventory,
            &BTreeSet::from([SourceUnitId(0), SourceUnitId(2), SourceUnitId(3)])
        ),
        Err(SourceRewriteError::InvalidRetention)
    );
    assert_eq!(
        rewrite_source(
            &inventory,
            &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
        ),
        Err(SourceRewriteError::InvalidRetention)
    );
}

#[test]
fn rewrites_repetition_boundaries_from_complete_input_facts() {
    let source = "a, b, c";
    let inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::MacroInvocation, 0, 7, 0, 1),
            unit(WrittenUnitKind::NestedItem, 0, 1, 1, 2),
            unit(WrittenUnitKind::NestedItem, 3, 4, 1, 3),
            unit(WrittenUnitKind::NestedItem, 6, 7, 1, 4),
        ],
    );
    let repetition = MacroRepetitionSourceFacts {
        invocation: SourceUnitId(1),
        rule: SourceUnitId(0),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(1),
        repetition_path: vec![0],
        input_range: ByteRange { start: 0, end: 7 },
        elements: vec![
            MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(2),
                separator_after: Some(ByteRange { start: 1, end: 2 }),
            },
            MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(3),
                separator_after: Some(ByteRange { start: 4, end: 5 }),
            },
            MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(4),
                separator_after: None,
            },
        ],
        minimum: 0,
        maximum: None,
    };

    let retain_middle = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(3)]);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retain_middle),
        Ok(vec![
            ByteRange { start: 0, end: 2 },
            ByteRange { start: 4, end: 7 },
        ])
    );

    let retain_edges = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(4),
    ]);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retain_edges),
        Ok(vec![ByteRange { start: 3, end: 5 }])
    );

    let retain_first = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)]);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retain_first),
        Ok(vec![ByteRange { start: 1, end: 7 }])
    );

    let retain_last = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(4)]);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retain_last),
        Ok(vec![ByteRange { start: 0, end: 5 }])
    );

    let retain_no_elements = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retain_no_elements),
        Ok(vec![ByteRange { start: 0, end: 7 }])
    );
}

#[test]
fn rejects_deleting_the_only_plus_element_and_deletes_an_optional_element() {
    let inventory = inventory(
        "only",
        &[
            unit(WrittenUnitKind::MacroInvocation, 0, 4, 0, 1),
            unit(WrittenUnitKind::NestedItem, 0, 4, 1, 2),
        ],
    );
    let mut repetition = MacroRepetitionSourceFacts {
        invocation: SourceUnitId(1),
        rule: SourceUnitId(0),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(1),
        repetition_path: vec![0],
        input_range: ByteRange { start: 0, end: 4 },
        elements: vec![MacroRepetitionElementSourceFacts {
            unit: SourceUnitId(2),
            separator_after: None,
        }],
        minimum: 1,
        maximum: None,
    };
    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);

    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retained),
        Err(SourceRewriteError::InvalidRetention)
    );

    repetition.minimum = 0;
    repetition.maximum = Some(1);
    assert_eq!(
        rewrite_macro_repetition(&inventory, &repetition, &retained),
        Ok(vec![ByteRange { start: 0, end: 4 }])
    );
}

#[test]
fn rejects_parser_token_changes_without_rejecting_spacing_or_body_owned_separators() {
    fn rewrite_unseparated(
        source: &str,
        ranges: &[(u32, u32)],
        retained_elements: &[usize],
    ) -> Result<Vec<ByteRange>, SourceRewriteError> {
        let mut children = vec![unit(
            WrittenUnitKind::MacroInvocation,
            0,
            source.len() as u32,
            0,
            1,
        )];
        children.extend(ranges.iter().enumerate().map(|(index, &(start, end))| {
            unit(WrittenUnitKind::NestedItem, start, end, 1, index as u32 + 2)
        }));
        let inventory = inventory(source, &children);
        let repetition = MacroRepetitionSourceFacts {
            invocation: SourceUnitId(1),
            rule: SourceUnitId(0),
            matcher_range: ByteRange { start: 0, end: 1 },
            parent: SourceUnitId(1),
            repetition_path: vec![0],
            input_range: ByteRange {
                start: ranges.first().unwrap().0,
                end: ranges.last().unwrap().1,
            },
            elements: (0..ranges.len())
                .map(|index| MacroRepetitionElementSourceFacts {
                    unit: SourceUnitId(index as u32 + 2),
                    separator_after: None,
                })
                .collect(),
            minimum: 0,
            maximum: None,
        };
        let mut retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);
        retained.extend(
            retained_elements
                .iter()
                .map(|index| SourceUnitId(*index as u32 + 2)),
        );
        let deletions = rewrite_macro_repetition(&inventory, &repetition, &retained)?;
        if deletions_preserve_parser_tokens(source, &deletions) {
            Ok(deletions)
        } else {
            Err(SourceRewriteError::InvalidRetention)
        }
    }

    fn deletion_preserves(source: &str, deletion: ByteRange) -> bool {
        deletions_preserve_parser_tokens(source, &[deletion])
    }

    assert_eq!(
        rewrite_unseparated("1+2", &[(0, 1), (1, 2), (2, 3)], &[0, 2]),
        Err(SourceRewriteError::InvalidRetention)
    );
    for (left, right) in [
        ("=", "="),
        ("=", ">"),
        ("<", "="),
        ("<", "<"),
        ("<", "-"),
        (">", "="),
        (">", ">"),
        ("!", "="),
        ("+", "="),
        ("-", "="),
        ("-", ">"),
        ("*", "="),
        ("/", "="),
        ("%", "="),
        ("^", "="),
        ("&", "="),
        ("&", "&"),
        ("|", "="),
        ("|", "|"),
        (".", "."),
        (":", ":"),
    ] {
        let source = format!("{left}x{right}");
        assert_eq!(
            rewrite_unseparated(&source, &[(0, 1), (1, 2), (2, 3)], &[0, 2]),
            Err(SourceRewriteError::InvalidRetention),
            "{left} and {right} must not become adjacent",
        );
    }
    for (left, right) in [(")", "("), (",", ";"), ("+", ">"), (":", "=")] {
        let source = format!("{left}x{right}");
        assert_eq!(
            rewrite_unseparated(&source, &[(0, 1), (1, 2), (2, 3)], &[0, 2]),
            Ok(vec![ByteRange { start: 1, end: 2 }]),
            "{left} and {right} do not form one parser token",
        );
    }
    assert!(!deletion_preserves("+=x", ByteRange { start: 1, end: 2 }));
    assert!(!deletion_preserves(
        "foo+\"bar\"",
        ByteRange { start: 3, end: 4 }
    ));
    assert!(!deletion_preserves(
        "#+\"bar\"",
        ByteRange { start: 1, end: 2 }
    ));
    assert!(deletion_preserves(
        "m!(a,b,c)",
        ByteRange { start: 6, end: 8 }
    ));
    assert!(deletion_preserves("-a b>", ByteRange { start: 1, end: 2 }));
    assert!(deletion_preserves("-a b>", ByteRange { start: 2, end: 4 }));
    assert!(!deletion_preserves("-a b>", ByteRange { start: 1, end: 4 }));
    assert_eq!(
        rewrite_unseparated("1 + 2", &[(0, 1), (2, 3), (4, 5)], &[0, 2]),
        Ok(vec![ByteRange { start: 2, end: 3 }])
    );
    assert_eq!(
        rewrite_unseparated("a,b,", &[(0, 2), (2, 4)], &[1]),
        Ok(vec![ByteRange { start: 0, end: 2 }])
    );
    assert_eq!(
        rewrite_unseparated(",a,b", &[(0, 2), (2, 4)], &[0]),
        Ok(vec![ByteRange { start: 2, end: 4 }])
    );
}

#[test]
fn unsafe_repetition_token_rewrite_becomes_a_retention_requirement() {
    let source = "macro_rules! m { ($($t:tt)*) => {} }\nm!(foo+\"bar\" dead);\nm!(a+x>);";
    let definition = marker(source, "macro_rules! m { ($($t:tt)*) => {} }");
    let rule = marker(source, "($($t:tt)*) => {}");
    let matcher = marker(source, "$($t:tt)*");
    let invocation = marker(source, "m!(foo+\"bar\" dead)");
    let first = marker(source, "foo");
    let middle = ByteRange {
        start: first.end,
        end: first.end + 1,
    };
    let last = marker(source, "\"bar\"");
    let same_repetition_safe = marker(source, "dead");
    let safe_invocation = marker(source, "m!(a+x>)");
    let safe_input = marker(source, "a+x>");
    let mut inventory = inventory(
        source,
        &[
            unit(
                WrittenUnitKind::MacroDefinition,
                definition.start,
                definition.end,
                0,
                1,
            ),
            unit(WrittenUnitKind::MacroRule, rule.start, rule.end, 1, 2),
            unit(
                WrittenUnitKind::MacroInvocation,
                invocation.start,
                invocation.end,
                0,
                3,
            ),
            unit(WrittenUnitKind::NestedItem, first.start, first.end, 3, 4),
            unit(WrittenUnitKind::NestedItem, middle.start, middle.end, 3, 5),
            unit(WrittenUnitKind::NestedItem, last.start, last.end, 3, 6),
            unit(
                WrittenUnitKind::NestedItem,
                same_repetition_safe.start,
                same_repetition_safe.end,
                3,
                7,
            ),
            unit(
                WrittenUnitKind::MacroInvocation,
                safe_invocation.start,
                safe_invocation.end,
                0,
                8,
            ),
            unit(
                WrittenUnitKind::NestedItem,
                safe_input.start,
                safe_input.start + 1,
                8,
                9,
            ),
            unit(
                WrittenUnitKind::NestedItem,
                safe_input.start + 1,
                safe_input.start + 2,
                8,
                10,
            ),
            unit(
                WrittenUnitKind::NestedItem,
                safe_input.start + 2,
                safe_input.start + 3,
                8,
                11,
            ),
            unit(
                WrittenUnitKind::NestedItem,
                safe_input.start + 3,
                safe_input.end,
                8,
                12,
            ),
        ],
    );
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(1),
        rules: vec![SourceUnitId(2)],
        observed_selections: vec![SourceUnitId(2), SourceUnitId(2)],
    }];
    inventory.macro_repetitions = vec![
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(2),
            matcher_range: matcher,
            parent: SourceUnitId(3),
            repetition_path: vec![0],
            input_range: ByteRange {
                start: first.start,
                end: same_repetition_safe.end,
            },
            elements: (4..=7)
                .map(|unit| MacroRepetitionElementSourceFacts {
                    unit: SourceUnitId(unit),
                    separator_after: None,
                })
                .collect(),
            minimum: 0,
            maximum: None,
        },
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(8),
            rule: SourceUnitId(2),
            matcher_range: matcher,
            parent: SourceUnitId(8),
            repetition_path: vec![0],
            input_range: safe_input,
            elements: (9..=12)
                .map(|unit| MacroRepetitionElementSourceFacts {
                    unit: SourceUnitId(unit),
                    separator_after: None,
                })
                .collect(),
            minimum: 0,
            maximum: None,
        },
    ];
    let mut retained = all_units(&inventory);
    retained.remove(&SourceUnitId(5));
    retained.remove(&SourceUnitId(7));
    retained.remove(&SourceUnitId(11));
    let initial_retained = retained.iter().copied().collect::<Vec<_>>();
    let mut token_requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();

    assert_eq!(
        rewrite_source(&inventory, &retained),
        Err(SourceRewriteError::InvalidRetention)
    );
    assert_eq!(
        token_requirements.close(&mut retained, &initial_retained),
        Ok(true)
    );
    assert!(retained.contains(&SourceUnitId(5)));
    assert!(!retained.contains(&SourceUnitId(7)));
    assert!(!retained.contains(&SourceUnitId(11)));
    assert_eq!(retained.len() + 2, inventory.units.len());
    let forced = token_requirements.take_newly_forced_units();
    assert_eq!(forced, vec![SourceUnitId(5)]);
    assert_eq!(token_requirements.close(&mut retained, &forced), Ok(false));
    assert_eq!(
        rewrite_source(&inventory, &retained).unwrap().source,
        "macro_rules! m { ($($t:tt)*) => {} }\nm!(foo+\"bar\" );\nm!(a+>);"
    );
}

#[test]
fn token_retention_returns_to_outer_fixed_point_before_activating_nested_minimum() {
    let source = "((x)) m!(foo+(x)\"bar\")";
    let definition = marker(source, "((x))");
    let inner_matcher = marker(source, "(x)");
    let invocation = marker(source, "m!(foo+(x)\"bar\")");
    let input = marker(source, "foo+(x)\"bar\"");
    let prefix = marker(source, "foo");
    let middle = marker(source, "+(x)");
    let inner = ByteRange {
        start: middle.start + 2,
        end: middle.start + 3,
    };
    let suffix = marker(source, "\"bar\"");
    let mut inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::NestedItem, prefix.start, prefix.end, 5, 1),
            unit(WrittenUnitKind::NestedItem, middle.start, middle.end, 5, 2),
            unit(WrittenUnitKind::NestedItem, inner.start, inner.end, 2, 3),
            unit(WrittenUnitKind::NestedItem, suffix.start, suffix.end, 5, 4),
            unit(
                WrittenUnitKind::MacroInvocation,
                invocation.start,
                invocation.end,
                0,
                5,
            ),
            unit(
                WrittenUnitKind::MacroDefinition,
                definition.start,
                definition.end,
                0,
                6,
            ),
            unit(
                WrittenUnitKind::MacroRule,
                definition.start,
                definition.end,
                6,
                7,
            ),
        ],
    );
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(6),
        rules: vec![SourceUnitId(7)],
        observed_selections: vec![SourceUnitId(7)],
    }];
    inventory.macro_repetitions = vec![
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(5),
            rule: SourceUnitId(7),
            matcher_range: inner_matcher,
            parent: SourceUnitId(2),
            repetition_path: vec![0, 0],
            input_range: inner,
            elements: vec![MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(3),
                separator_after: None,
            }],
            minimum: 1,
            maximum: None,
        },
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(5),
            rule: SourceUnitId(7),
            matcher_range: definition,
            parent: SourceUnitId(5),
            repetition_path: vec![0],
            input_range: input,
            elements: [SourceUnitId(1), SourceUnitId(2), SourceUnitId(4)]
                .into_iter()
                .map(|unit| MacroRepetitionElementSourceFacts {
                    unit,
                    separator_after: None,
                })
                .collect(),
            minimum: 0,
            maximum: None,
        },
    ];
    assert!(validate_inventory(&inventory).is_ok());

    let initial = [
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(4),
        SourceUnitId(5),
        SourceUnitId(6),
        SourceUnitId(7),
    ];
    let mut retained = BTreeSet::from(initial);
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();

    assert_eq!(requirements.close(&mut retained, &initial), Ok(true));
    assert!(retained.contains(&SourceUnitId(2)));
    assert!(!retained.contains(&SourceUnitId(3)));
    let forced = requirements.take_newly_forced_units();
    assert_eq!(forced, vec![SourceUnitId(2)]);

    // The outer fixed point now satisfies the nested `+` repetition's
    // source disjunction before token planning resumes.
    retained.insert(SourceUnitId(3));
    let mut next_wave = forced;
    next_wave.push(SourceUnitId(3));
    assert_eq!(requirements.close(&mut retained, &next_wave), Ok(false));
    assert_eq!(requirements.active_deletion_count(), 0);
    assert_eq!(
        rewrite_source(&inventory, &retained).unwrap().source,
        source
    );
}

#[test]
fn deep_repetition_token_fixed_point_tokenizes_source_once_and_visits_changed_facts() {
    const DEPTH: usize = 1024;
    let matcher = format!("{}x{}", "(".repeat(DEPTH - 1), ")".repeat(DEPTH - 1));
    let input = format!("{}y{}", "(".repeat(DEPTH - 1), ")".repeat(DEPTH - 1));
    let source = format!("{matcher} {input}");
    let matcher_end = matcher.len() as u32;
    let input_start = matcher_end + 1;
    let input_end = source.len() as u32;
    let mut children = vec![
        unit(WrittenUnitKind::MacroDefinition, 0, matcher_end, 0, 1),
        unit(WrittenUnitKind::MacroRule, 0, matcher_end, 1, 2),
        unit(
            WrittenUnitKind::MacroInvocation,
            input_start,
            input_end,
            0,
            3,
        ),
    ];
    children.extend((0..DEPTH).map(|depth| {
        unit(
            WrittenUnitKind::NestedItem,
            input_start + depth as u32,
            input_end - depth as u32,
            if depth == 0 { 3 } else { depth as u32 + 3 },
            depth as u32 + 4,
        )
    }));
    let mut inventory = inventory(&source, &children);
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(1),
        rules: vec![SourceUnitId(2)],
        observed_selections: vec![SourceUnitId(2)],
    }];
    inventory.macro_repetitions = (0..DEPTH)
        .map(|depth| MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(2),
            matcher_range: ByteRange {
                start: depth as u32,
                end: matcher_end - depth as u32,
            },
            parent: SourceUnitId(if depth == 0 { 3 } else { depth as u32 + 3 }),
            repetition_path: vec![0; depth + 1],
            input_range: ByteRange {
                start: input_start + depth as u32,
                end: input_end - depth as u32,
            },
            elements: vec![MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(depth as u32 + 4),
                separator_after: None,
            }],
            minimum: 0,
            maximum: None,
        })
        .collect();
    assert!(validate_inventory(&inventory).is_ok());
    let mut retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(3),
    ]);

    crate::source::syntax::reset_parser_token_rewrite_guard_build_count();
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();
    assert_eq!(
        requirements.close(
            &mut retained,
            &[
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ]
        ),
        Ok(false)
    );
    for depth in 0..DEPTH {
        let element = SourceUnitId(depth as u32 + 4);
        retained.insert(element);
        assert_eq!(requirements.close(&mut retained, &[element]), Ok(false));
    }

    assert_eq!(retained.len(), DEPTH + 4);
    assert_eq!(requirements.active_deletion_count(), 0);
    assert!(requirements.element_visits() <= DEPTH * 2);
    assert_eq!(requirements.cohort_element_visits(), 0);
    assert_eq!(requirements.component_member_moves(), 0);
    assert_eq!(requirements.full_retention_validations(), 1);
    assert_eq!(
        crate::source::syntax::parser_token_rewrite_guard_build_count(),
        1
    );
}

#[test]
fn one_large_repetition_updates_each_element_without_rescanning_its_siblings() {
    const ELEMENTS: usize = 1024;
    let input = std::iter::repeat_n("x", ELEMENTS)
        .collect::<Vec<_>>()
        .join(",");
    let source = format!("r {input}");
    let input_start = 2_u32;
    let input_end = source.len() as u32;
    let mut children = vec![
        unit(WrittenUnitKind::MacroDefinition, 0, 1, 0, 1),
        unit(WrittenUnitKind::MacroRule, 0, 1, 1, 2),
        unit(
            WrittenUnitKind::MacroInvocation,
            input_start,
            input_end,
            0,
            3,
        ),
    ];
    children.extend((0..ELEMENTS).map(|element| {
        let start = input_start + (element * 2) as u32;
        unit(
            WrittenUnitKind::NestedItem,
            start,
            start + 1,
            3,
            element as u32 + 4,
        )
    }));
    let mut inventory = inventory(&source, &children);
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(1),
        rules: vec![SourceUnitId(2)],
        observed_selections: vec![SourceUnitId(2)],
    }];
    inventory.macro_repetitions = vec![MacroRepetitionSourceFacts {
        invocation: SourceUnitId(3),
        rule: SourceUnitId(2),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(3),
        repetition_path: vec![0],
        input_range: ByteRange {
            start: input_start,
            end: input_end,
        },
        elements: (0..ELEMENTS)
            .map(|element| {
                let start = input_start + (element * 2) as u32;
                MacroRepetitionElementSourceFacts {
                    unit: SourceUnitId(element as u32 + 4),
                    separator_after: (element + 1 < ELEMENTS).then_some(ByteRange {
                        start: start + 1,
                        end: start + 2,
                    }),
                }
            })
            .collect(),
        minimum: 0,
        maximum: None,
    }];
    assert!(validate_inventory(&inventory).is_ok());
    let mut retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(3),
    ]);
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();
    assert_eq!(
        requirements.close(
            &mut retained,
            &[
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ]
        ),
        Ok(false)
    );
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);
    let order = (0..ELEMENTS).step_by(2).chain((1..ELEMENTS).step_by(2));
    for element in order {
        let unit = SourceUnitId(element as u32 + 4);
        retained.insert(unit);
        assert_eq!(requirements.close(&mut retained, &[unit]), Ok(false));
        if matches!(element, 0 | 2 | 511 | 512 | 1023) {
            assert_repetition_deletion_index_matches_static_plan(
                &inventory,
                &retained,
                &requirements,
            );
        }
    }

    assert_eq!(requirements.active_deletion_count(), 0);
    assert_eq!(requirements.element_visits(), ELEMENTS * 2);
    assert_eq!(requirements.cohort_element_visits(), 0);
    assert_eq!(requirements.component_member_moves(), 0);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);
}

#[test]
fn alternating_pound_deletions_share_one_linear_lexical_cohort() {
    const ELEMENTS: usize = 1_024;
    // Adjacent hashes are a guarded-string prefix in Rust 2024. Trivia keeps
    // these as distinct Pound tokens while the raw-prefix dependency remains
    // one logical run.
    let input = std::iter::repeat_n("#", ELEMENTS)
        .collect::<Vec<_>>()
        .join(" ");
    let source = format!("r {input}");
    let input_start = 2_u32;
    let input_end = source.len() as u32;
    let mut children = vec![
        unit(WrittenUnitKind::MacroDefinition, 0, 1, 0, 1),
        unit(WrittenUnitKind::MacroRule, 0, 1, 1, 2),
        unit(
            WrittenUnitKind::MacroInvocation,
            input_start,
            input_end,
            0,
            3,
        ),
    ];
    children.extend((0..ELEMENTS).map(|element| {
        let start = input_start + (element * 2) as u32;
        unit(
            WrittenUnitKind::NestedItem,
            start,
            start + 1,
            3,
            element as u32 + 4,
        )
    }));
    let mut inventory = inventory(&source, &children);
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(1),
        rules: vec![SourceUnitId(2)],
        observed_selections: vec![SourceUnitId(2)],
    }];
    inventory.macro_repetitions = vec![MacroRepetitionSourceFacts {
        invocation: SourceUnitId(3),
        rule: SourceUnitId(2),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(3),
        repetition_path: vec![0],
        input_range: ByteRange {
            start: input_start,
            end: input_end,
        },
        elements: (0..ELEMENTS)
            .map(|element| MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(element as u32 + 4),
                separator_after: None,
            })
            .collect(),
        minimum: 0,
        maximum: None,
    }];
    assert!(validate_inventory(&inventory).is_ok());
    let mut retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(3),
    ]);
    retained.extend(
        (1..ELEMENTS)
            .step_by(2)
            .map(|element| SourceUnitId(element as u32 + 4)),
    );
    let initial = retained.iter().copied().collect::<Vec<_>>();

    crate::source::syntax::reset_parser_token_rewrite_guard_build_count();
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();
    assert_eq!(requirements.close(&mut retained, &initial), Ok(false));

    assert_eq!(requirements.active_deletion_count(), ELEMENTS / 2);
    assert_eq!(requirements.active_component_ranges().len(), ELEMENTS / 2);
    assert_eq!(
        requirements.token_validation_bytes(),
        source.len() - ELEMENTS / 2
    );
    assert!(requirements.token_dependency_visits() <= ELEMENTS * 3 + 2);
    assert_eq!(
        crate::source::syntax::parser_token_rewrite_guard_build_count(),
        1
    );
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);
}

#[test]
fn touching_repetition_deletions_form_one_component_with_linear_member_moves() {
    const REPETITIONS: usize = 1024;
    let matcher = "()".repeat(REPETITIONS);
    let input = ";".repeat(REPETITIONS);
    let source = format!("{matcher} {input}");
    let matcher_end = matcher.len() as u32;
    let input_start = matcher_end + 1;
    let input_end = source.len() as u32;
    let spatial_order = (0..REPETITIONS)
        .step_by(2)
        .chain((1..REPETITIONS).step_by(2))
        .collect::<Vec<_>>();
    let mut children = vec![
        unit(WrittenUnitKind::MacroDefinition, 0, matcher_end, 0, 1),
        unit(WrittenUnitKind::MacroRule, 0, matcher_end, 1, 2),
        unit(
            WrittenUnitKind::MacroInvocation,
            input_start,
            input_end,
            0,
            3,
        ),
    ];
    children.extend(
        spatial_order
            .iter()
            .enumerate()
            .map(|(repetition, &position)| {
                let start = input_start + position as u32;
                unit(
                    WrittenUnitKind::NestedItem,
                    start,
                    start + 1,
                    3,
                    repetition as u32 + 4,
                )
            }),
    );
    let mut inventory = inventory(&source, &children);
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(1),
        rules: vec![SourceUnitId(2)],
        observed_selections: vec![SourceUnitId(2)],
    }];
    inventory.macro_repetitions = (0..REPETITIONS)
        .map(|repetition| {
            let position = spatial_order[repetition];
            let input = ByteRange {
                start: input_start + position as u32,
                end: input_start + position as u32 + 1,
            };
            MacroRepetitionSourceFacts {
                invocation: SourceUnitId(3),
                rule: SourceUnitId(2),
                matcher_range: ByteRange {
                    start: (repetition * 2) as u32,
                    end: (repetition * 2 + 2) as u32,
                },
                parent: SourceUnitId(3),
                repetition_path: vec![repetition as u32],
                input_range: input,
                elements: vec![MacroRepetitionElementSourceFacts {
                    unit: SourceUnitId(repetition as u32 + 4),
                    separator_after: None,
                }],
                minimum: 0,
                maximum: None,
            }
        })
        .collect();
    assert!(validate_inventory(&inventory).is_ok());
    let mut retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(3),
    ]);
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();
    assert_eq!(
        requirements.close(
            &mut retained,
            &[
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ]
        ),
        Ok(false)
    );

    assert_eq!(requirements.active_deletion_count(), REPETITIONS);
    assert_eq!(requirements.element_visits(), REPETITIONS);
    assert_eq!(requirements.cohort_element_visits(), 0);
    assert!(requirements.component_member_moves() > 0);
    assert!(requirements.component_member_moves() < REPETITIONS);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);

    let middle = SourceUnitId(
        spatial_order
            .iter()
            .position(|&position| position == REPETITIONS / 2)
            .unwrap() as u32
            + 4,
    );
    retained.insert(middle);
    assert_eq!(requirements.close(&mut retained, &[middle]), Ok(false));
    assert_eq!(requirements.active_deletion_count(), REPETITIONS - 1);
    assert_eq!(requirements.element_visits(), REPETITIONS + 1);
    assert!(requirements.component_member_moves() < REPETITIONS * 2);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);
}

#[test]
fn nested_repetition_updates_are_independent_of_fact_and_unit_order() {
    let source = "((x)) m!(a b c)";
    let definition = marker(source, "((x))");
    let matcher = marker(source, "(x)");
    let invocation = marker(source, "m!(a b c)");
    let outer = marker(source, "a b c");
    let inner = marker(source, "b");
    let mut inventory = inventory(
        source,
        &[
            unit(WrittenUnitKind::NestedItem, inner.start, inner.end, 2, 1),
            unit(WrittenUnitKind::NestedItem, outer.start, outer.end, 3, 2),
            unit(
                WrittenUnitKind::MacroInvocation,
                invocation.start,
                invocation.end,
                0,
                3,
            ),
            unit(
                WrittenUnitKind::MacroDefinition,
                definition.start,
                definition.end,
                0,
                4,
            ),
            unit(
                WrittenUnitKind::MacroRule,
                definition.start,
                definition.end,
                4,
                5,
            ),
        ],
    );
    inventory.macro_rules = vec![crate::source::MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(4),
        rules: vec![SourceUnitId(5)],
        observed_selections: vec![SourceUnitId(5)],
    }];
    inventory.macro_repetitions = vec![
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(5),
            matcher_range: matcher,
            parent: SourceUnitId(2),
            repetition_path: vec![0, 0],
            input_range: inner,
            elements: vec![MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(1),
                separator_after: None,
            }],
            minimum: 0,
            maximum: None,
        },
        MacroRepetitionSourceFacts {
            invocation: SourceUnitId(3),
            rule: SourceUnitId(5),
            matcher_range: definition,
            parent: SourceUnitId(3),
            repetition_path: vec![0],
            input_range: outer,
            elements: vec![MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(2),
                separator_after: None,
            }],
            minimum: 0,
            maximum: None,
        },
    ];
    assert!(validate_inventory(&inventory).is_ok());
    let initial = [
        SourceUnitId(0),
        SourceUnitId(3),
        SourceUnitId(4),
        SourceUnitId(5),
    ];
    let mut retained = BTreeSet::from(initial);
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();

    assert_eq!(requirements.close(&mut retained, &initial), Ok(false));
    assert_eq!(requirements.active_deletion_ranges(), vec![outer]);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);

    retained.insert(SourceUnitId(2));
    assert_eq!(
        requirements.close(&mut retained, &[SourceUnitId(2)]),
        Ok(false)
    );
    assert_eq!(requirements.active_deletion_ranges(), vec![inner]);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);

    retained.insert(SourceUnitId(1));
    assert_eq!(
        requirements.close(&mut retained, &[SourceUnitId(1)]),
        Ok(false)
    );
    assert_eq!(requirements.active_deletion_count(), 0);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained, &requirements);

    let mut retained_together = BTreeSet::from(initial);
    let mut together = MacroRepetitionTokenRequirements::new(&inventory).unwrap();
    assert_eq!(together.close(&mut retained_together, &initial), Ok(false));
    retained_together.extend([SourceUnitId(1), SourceUnitId(2)]);
    assert_eq!(
        together.close(&mut retained_together, &[SourceUnitId(1), SourceUnitId(2)]),
        Ok(false)
    );
    assert_eq!(together.active_deletion_count(), 0);
    assert_repetition_deletion_index_matches_static_plan(&inventory, &retained_together, &together);
}

#[test]
fn overlapping_active_repetition_deletions_fail_closed() {
    let source = "m!(abc)";
    let invocation = marker(source, source);
    let left = marker(source, "ab");
    let right = marker(source, "bc");
    let mut inventory = inventory(
        source,
        &[
            unit(
                WrittenUnitKind::MacroInvocation,
                invocation.start,
                invocation.end,
                0,
                1,
            ),
            unit(WrittenUnitKind::NestedItem, left.start, left.end, 1, 2),
            unit(WrittenUnitKind::NestedItem, right.start, right.end, 1, 3),
        ],
    );
    inventory.macro_repetitions = [
        (SourceUnitId(2), left, vec![0]),
        (SourceUnitId(3), right, vec![1]),
    ]
    .into_iter()
    .map(
        |(unit, range, repetition_path)| MacroRepetitionSourceFacts {
            invocation: SourceUnitId(1),
            rule: SourceUnitId(0),
            matcher_range: range,
            parent: SourceUnitId(1),
            repetition_path,
            input_range: range,
            elements: vec![MacroRepetitionElementSourceFacts {
                unit,
                separator_after: None,
            }],
            minimum: 0,
            maximum: None,
        },
    )
    .collect();
    let mut retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);
    let mut requirements = MacroRepetitionTokenRequirements::new(&inventory).unwrap();

    assert_eq!(
        requirements.close(&mut retained, &[SourceUnitId(0), SourceUnitId(1)]),
        Err(SourceRewriteError::InvalidInventory)
    );
}

#[test]
fn parser_token_fusion_outside_macro_repetition_is_checked_by_compilation() {
    let mut inactive = unit(WrittenUnitKind::InactiveCfgComponent, 1, 2, 0, 1);
    inactive.cfg_state = CfgState::Inactive;
    let inventory = inventory("|x|", &[inactive]);

    let rewritten = rewrite_source(&inventory, &BTreeSet::from([SourceUnitId(0)])).unwrap();

    assert_eq!(rewritten.source, "||");
    assert_piece_map(&inventory.original, &rewritten);
}

#[test]
fn rejects_invalid_utf8_piece_and_use_tree_boundaries() {
    let mut broken = inventory("日\n", &[unit(WrittenUnitKind::Item, 1, 3, 0, 1)]);
    assert_eq!(
        rewrite_source(&broken, &BTreeSet::from([SourceUnitId(0)])),
        Err(SourceRewriteError::InvalidInventory)
    );

    broken = inventory(
        "fn main() {}\n",
        &[unit(WrittenUnitKind::Item, 0, 12, 0, 1)],
    );
    broken.pieces.pop();
    assert_eq!(
        rewrite_source(&broken, &BTreeSet::from([SourceUnitId(0)])),
        Err(SourceRewriteError::InvalidInventory)
    );

    let malformed = inventory(
        "use x::a;\n",
        &[
            unit(WrittenUnitKind::UseItem, 0, 9, 0, 1),
            unit(WrittenUnitKind::UseLeaf, 4, 5, 1, 2),
            unit(WrittenUnitKind::UseLeaf, 7, 8, 1, 3),
        ],
    );
    assert_eq!(
        rewrite_source(
            &malformed,
            &BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
        ),
        Err(SourceRewriteError::InvalidUseTree)
    );
}

#[test]
fn an_already_rewritten_source_is_byte_identical() {
    let source = "fn main() {}\r\n// 終\r\n";
    let first =
        rewrite_source(&inventory(source, &[]), &BTreeSet::from([SourceUnitId(0)])).unwrap();
    let second = rewrite_source(
        &inventory(&first.source, &[]),
        &BTreeSet::from([SourceUnitId(0)]),
    )
    .unwrap();

    assert_eq!(first.source, source);
    assert_eq!(second.source, first.source);
    assert_eq!(
        second.pieces,
        vec![piece(0, source.len() as u32, 0, source.len() as u32)]
    );
}

#[test]
fn rewrites_first_middle_and_last_derive_elements_as_one_flat_list() {
    let source =
        "#[derive(Clone, /* keep */ core::fmt::Debug, Default,)]\nstruct S;\nfn main(){}\n";
    let mut inventory = derive_inventory(
        source,
        "#[derive(Clone, /* keep */ core::fmt::Debug, Default,)]\nstruct S;",
        "#[derive(Clone, /* keep */ core::fmt::Debug, Default,)]",
        &["Clone", "core::fmt::Debug", "Default"],
    );

    let retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(4),
        SourceUnitId(6),
    ]);
    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(
        actual.source,
        "#[derive( /* keep */ core::fmt::Debug,)]\nstruct S;\nfn main(){}\n"
    );
    assert_piece_map(&inventory.original, &actual);

    inventory.derive_targets[0] = DeriveTargetSourceFacts::Opaque {
        target: SourceUnitId(1),
        attributes: vec![DeriveAttributeSourceFacts {
            attribute: SourceUnitId(2),
            elements: vec![SourceUnitId(3), SourceUnitId(4), SourceUnitId(5)],
            directly_written: true,
        }],
        helper_candidates: Vec::new(),
    };
    for unit in &mut inventory.units[2..=5] {
        unit.atomic_group = AtomicGroupId(1);
    }
    let retained = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(3),
        SourceUnitId(4),
        SourceUnitId(5),
        SourceUnitId(6),
    ]);
    assert_eq!(
        rewrite_source(&inventory, &retained).unwrap().source,
        source
    );
}

#[test]
fn rewrites_every_nonempty_three_element_derive_subset_and_reaches_a_fixed_point() {
    let names = ["A", "B", "C"];
    for trailing_comma in [false, true] {
        let input_list = if trailing_comma { "A,B,C," } else { "A,B,C" };
        let attribute = format!("#[derive({input_list})]");
        let source = format!("{attribute}\nstruct S;\nfn main(){{}}\n");
        let target = format!("{attribute}\nstruct S;");
        let inventory = derive_inventory(&source, &target, &attribute, &names);

        for mask in 1_u8..8 {
            let kept = names
                .iter()
                .enumerate()
                .filter_map(|(index, name)| ((mask & (1 << index)) != 0).then_some(*name))
                .collect::<Vec<_>>();
            let retained_elements = (0..names.len())
                .filter(|index| (mask & (1 << index)) != 0)
                .map(|index| (0, index))
                .collect::<Vec<_>>();
            let retained = retained_derive_subset(&inventory, &retained_elements);

            let actual = rewrite_source(&inventory, &retained).unwrap();
            let mut expected_list = kept.join(",");
            if trailing_comma {
                expected_list.push(',');
            }
            let expected_attribute = format!("#[derive({expected_list})]");
            let expected = format!("{expected_attribute}\nstruct S;\nfn main(){{}}\n");
            assert_eq!(
                actual.source, expected,
                "mask {mask:03b}, trailing comma: {trailing_comma}"
            );
            assert_piece_map(&inventory.original, &actual);

            let expected_target = format!("{expected_attribute}\nstruct S;");
            let fixed_inventory =
                derive_inventory(&actual.source, &expected_target, &expected_attribute, &kept);
            let fixed = rewrite_source(&fixed_inventory, &all_units(&fixed_inventory)).unwrap();
            assert_eq!(
                fixed.source, actual.source,
                "mask {mask:03b}, trailing comma: {trailing_comma}"
            );
        }
    }
}

#[test]
fn associates_line_and_block_comments_with_the_following_derive_element() {
    let attribute = concat!(
        "#[derive(\n",
        "    First,\n",
        "    // line comment\n",
        "    Second,\n",
        "    /* block comment */ Third,\n",
        ")]",
    );
    let source = format!("{attribute}\nstruct S;\nfn main(){{}}\n");
    let target = format!("{attribute}\nstruct S;");
    let inventory = derive_inventory(&source, &target, attribute, &["First", "Second", "Third"]);

    let second =
        rewrite_source(&inventory, &retained_derive_subset(&inventory, &[(0, 1)])).unwrap();
    assert_eq!(
        second.source,
        concat!(
            "#[derive(\n",
            "    // line comment\n",
            "    Second,\n",
            ")]\n",
            "struct S;\n",
            "fn main(){}\n",
        )
    );
    assert_piece_map(&inventory.original, &second);

    let third = rewrite_source(&inventory, &retained_derive_subset(&inventory, &[(0, 2)])).unwrap();
    assert_eq!(
        third.source,
        concat!(
            "#[derive(\n",
            "    /* block comment */ Third,\n",
            ")]\n",
            "struct S;\n",
            "fn main(){}\n",
        )
    );
    assert_piece_map(&inventory.original, &third);
}

#[test]
fn rewrites_multiple_derive_attributes_independently() {
    let first_attribute = "#[derive(A, B)]";
    let second_attribute = "#[derive(C, D, E)]";
    let target = concat!("#[derive(A, B)]\n", "#[derive(C, D, E)]\n", "struct S;");
    let source = format!("{target}\nfn main(){{}}\n");
    let inventory = derive_inventory_with_attributes(
        &source,
        target,
        &[
            (first_attribute, &["A", "B"]),
            (second_attribute, &["C", "D", "E"]),
        ],
    );

    let retained = retained_derive_subset(&inventory, &[(0, 1), (1, 0), (1, 2)]);
    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(
        actual.source,
        "#[derive( B)]\n#[derive(C, E)]\nstruct S;\nfn main(){}\n"
    );
    assert_piece_map(&inventory.original, &actual);

    let mut without_first = retained;
    let first_attribute = &inventory.derive_targets[0].attributes()[0];
    without_first.remove(&first_attribute.attribute);
    for element in &first_attribute.elements {
        without_first.remove(element);
    }
    let actual = rewrite_source(&inventory, &without_first).unwrap();
    assert_eq!(actual.source, "\n#[derive(C, E)]\nstruct S;\nfn main(){}\n");
    assert_piece_map(&inventory.original, &actual);
}

#[test]
fn deletes_the_whole_derive_attribute_when_no_element_is_retained() {
    let source = "#[derive(Clone, Debug)]\nstruct S;\nfn main(){}\n";
    let inventory = derive_inventory(
        source,
        "#[derive(Clone, Debug)]\nstruct S;",
        "#[derive(Clone, Debug)]",
        &["Clone", "Debug"],
    );
    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(5)]);

    let actual = rewrite_source(&inventory, &retained).unwrap();
    assert_eq!(actual.source, "\nstruct S;\nfn main(){}\n");
    assert_piece_map(&inventory.original, &actual);

    let invalid = BTreeSet::from([
        SourceUnitId(0),
        SourceUnitId(1),
        SourceUnitId(2),
        SourceUnitId(5),
    ]);
    assert_eq!(
        rewrite_source(&inventory, &invalid),
        Err(SourceRewriteError::InvalidRetention)
    );
}

fn inventory(source: &str, children: &[WrittenUnit]) -> SourceInventory {
    let (normalized, offsets) = OriginalOffsetMap::from_source(source).unwrap();
    let mut units = vec![WrittenUnit {
        id: SourceUnitId(0),
        kind: WrittenUnitKind::CrateRoot,
        full_range: ByteRange {
            start: 0,
            end: source.len() as u32,
        },
        parent: None,
        cfg_state: CfgState::Active,
        atomic_group: AtomicGroupId(0),
        same_role_ordinal: 0,
    }];
    for mut child in children.iter().cloned() {
        child.id = SourceUnitId(units.len() as u32);
        units.push(child);
    }
    let pieces = source
        .char_indices()
        .map(|(start, value)| OwnedPiece {
            range: ByteRange {
                start: start as u32,
                end: (start + value.len_utf8()) as u32,
            },
            owner: SourceUnitId(0),
            kind: PieceKind::Trivia,
        })
        .collect();
    SourceInventory {
        original: Arc::from(source),
        normalized: Arc::from(normalized),
        offsets,
        units,
        pieces,
        derive_targets: Vec::new(),
        macro_rules: Vec::new(),
        macro_templates: Vec::new(),
        macro_repetitions: Vec::new(),
        ownerless_attribute_invocations: Vec::new(),
    }
}

fn derive_inventory(
    source: &str,
    target_marker: &str,
    attribute_marker: &str,
    element_markers: &[&str],
) -> SourceInventory {
    derive_inventory_with_attributes(
        source,
        target_marker,
        &[(attribute_marker, element_markers)],
    )
}

fn derive_inventory_with_attributes(
    source: &str,
    target_marker: &str,
    attributes: &[(&str, &[&str])],
) -> SourceInventory {
    let target = marker(source, target_marker);
    let main = marker(source, "fn main(){}");
    let mut children = vec![unit(WrittenUnitKind::Item, target.start, target.end, 0, 1)];
    let mut attribute_facts = Vec::new();
    for &(attribute_marker, element_markers) in attributes {
        let attribute = marker(source, attribute_marker);
        let attribute_id = SourceUnitId(children.len() as u32 + 1);
        children.push(unit(
            WrittenUnitKind::MacroInvocation,
            attribute.start,
            attribute.end,
            1,
            attribute_id.0,
        ));
        let mut elements = Vec::new();
        for &element_marker in element_markers {
            let element = marker(source, element_marker);
            let element_id = SourceUnitId(children.len() as u32 + 1);
            children.push(unit(
                WrittenUnitKind::MacroInvocation,
                element.start,
                element.end,
                attribute_id.0,
                element_id.0,
            ));
            elements.push(element_id);
        }
        attribute_facts.push(DeriveAttributeSourceFacts {
            attribute: attribute_id,
            elements,
            directly_written: true,
        });
    }
    let main_id = SourceUnitId(children.len() as u32 + 1);
    children.push(unit(
        WrittenUnitKind::Item,
        main.start,
        main.end,
        0,
        main_id.0,
    ));
    let mut inventory = inventory(source, &children);
    inventory.derive_targets = vec![DeriveTargetSourceFacts::Complete {
        target: SourceUnitId(1),
        attributes: attribute_facts,
        helper_candidates: Vec::new(),
        influences: Vec::new(),
        helpers: Vec::new(),
    }];
    inventory
}

fn retained_derive_subset(
    inventory: &SourceInventory,
    retained_elements: &[(usize, usize)],
) -> BTreeSet<SourceUnitId> {
    let attributes = inventory.derive_targets[0].attributes();
    let elements = attributes
        .iter()
        .flat_map(|attribute| attribute.elements.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut retained = inventory
        .units
        .iter()
        .map(|unit| unit.id)
        .filter(|unit| !elements.contains(unit))
        .collect::<BTreeSet<_>>();
    retained.extend(
        retained_elements
            .iter()
            .map(|&(attribute, element)| attributes[attribute].elements[element]),
    );
    retained
}

fn all_units(inventory: &SourceInventory) -> BTreeSet<SourceUnitId> {
    inventory.units.iter().map(|unit| unit.id).collect()
}

fn assert_repetition_deletion_index_matches_static_plan(
    inventory: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
    requirements: &MacroRepetitionTokenRequirements<'_>,
) {
    let piece_boundaries = validate_inventory(inventory).unwrap();
    let expected = macro_repetition_deletions(inventory, retained, &piece_boundaries).unwrap();
    assert_eq!(requirements.active_component_ranges(), expected);
    assert!(requirements.component_index_is_consistent());
}

fn unit(kind: WrittenUnitKind, start: u32, end: u32, parent: u32, group: u32) -> WrittenUnit {
    WrittenUnit {
        id: SourceUnitId(u32::MAX),
        kind,
        full_range: ByteRange { start, end },
        parent: Some(SourceUnitId(parent)),
        cfg_state: CfgState::Active,
        atomic_group: AtomicGroupId(group),
        same_role_ordinal: 0,
    }
}

fn marker(source: &str, marker: &str) -> ByteRange {
    let start = source.find(marker).unwrap();
    ByteRange {
        start: start as u32,
        end: (start + marker.len()) as u32,
    }
}

fn piece(
    output_start: u32,
    output_end: u32,
    original_start: u32,
    original_end: u32,
) -> SourcePiece {
    SourcePiece {
        output_range: ByteRange {
            start: output_start,
            end: output_end,
        },
        original_range: ByteRange {
            start: original_start,
            end: original_end,
        },
    }
}

fn assert_piece_map(original: &str, rewrite: &SourceRewrite) {
    let mut cursor = 0_u32;
    for piece in &rewrite.pieces {
        assert_eq!(piece.output_range.start, cursor);
        assert_eq!(piece.output_range.len(), piece.original_range.len());
        assert_eq!(
            &rewrite.source[piece.output_range.start as usize..piece.output_range.end as usize],
            &original[piece.original_range.start as usize..piece.original_range.end as usize]
        );
        cursor = piece.output_range.end;
    }
    assert_eq!(cursor as usize, rewrite.source.len());
}

#[test]
fn maps_rewritten_ranges_back_with_directional_boundary_bias() {
    let rewrite = splice(
        "aaXXbbYYYcc",
        &[
            ByteRange { start: 2, end: 4 },
            ByteRange { start: 6, end: 9 },
        ],
    )
    .unwrap();
    assert_eq!(rewrite.source, "aabbcc");

    // A range spanning the full reduced source still follows the retained
    // endpoints; only an explicitly identified crate root may include a
    // deleted prefix or suffix.
    assert_eq!(rewrite.original_range(range(0, 6)), Ok(range(0, 11)));
    // A non-empty end at a piece boundary is left-biased.
    assert_eq!(rewrite.original_range(range(1, 2)), Ok(range(1, 2)));
    // A start (and therefore an empty range) at a boundary is right-biased.
    assert_eq!(rewrite.original_range(range(2, 2)), Ok(range(4, 4)));
    assert_eq!(rewrite.original_range(range(2, 3)), Ok(range(4, 5)));
    // A range spanning multiple retained pieces maps to the original
    // envelope, including the deleted gaps between its endpoints.
    assert_eq!(rewrite.original_range(range(1, 5)), Ok(range(1, 10)));
    assert_eq!(rewrite.original_range(range(6, 6)), Ok(range(11, 11)));
}

#[test]
fn maps_crate_root_across_deleted_prefix_and_suffix() {
    let rewrite = splice(
        "XXabcYY",
        &[
            ByteRange { start: 0, end: 2 },
            ByteRange { start: 5, end: 7 },
        ],
    )
    .unwrap();
    assert_eq!(rewrite.source, "abc");
    assert_eq!(rewrite.original_range(range(0, 3)), Ok(range(2, 5)));
    assert_eq!(rewrite.original_crate_range(range(0, 3)), Ok(range(0, 7)));
    assert_eq!(rewrite.original_range(range(0, 0)), Ok(range(2, 2)));
    assert_eq!(rewrite.original_range(range(3, 3)), Ok(range(5, 5)));
}

#[test]
fn range_mapping_preserves_utf8_boundaries() {
    let rewrite = splice("éXX界", &[ByteRange { start: 2, end: 4 }]).unwrap();
    assert_eq!(rewrite.source, "é界");
    assert_eq!(rewrite.original_range(range(2, 5)), Ok(range(4, 7)));
    assert_eq!(rewrite.original_range(range(2, 2)), Ok(range(4, 4)));
    assert_eq!(
        rewrite.original_range(range(1, 2)),
        Err(SourceRewriteError::InvalidInventory)
    );
}

fn range(start: u32, end: u32) -> ByteRange {
    ByteRange { start, end }
}
