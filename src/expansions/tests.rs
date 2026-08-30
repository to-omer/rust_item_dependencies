use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};

use rustc_ast as ast;
use rustc_driver::{Callbacks, Compilation};
use rustc_feature::UnstableFeatures;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::Input;
use rustc_span::source_map::FileLoader;
use rustc_span::{FileName, RealFileName};

use super::*;
use crate::definitions::collect_definitions;
use crate::dependency_graph::{
    EvidenceOrigin, ExpansionFragmentKind, ExpansionKey, ExpansionKeyPart, MacroStyle,
};
use crate::graph::{
    Definition, DefinitionEdge, DefinitionGraph, DefinitionKey, DefinitionKeyPart, DefinitionKind,
    DefinitionOrigin, DefinitionTarget, DependencyKind as DefinitionDependencyKind,
};
use crate::macro_output::ValidatedDeclarativeOutputs;
use crate::source::{
    SourceInventory, SourceUnitIdentityKind, WrittenUnitKind, collect_source,
    refine_attribute_macros_from_compiler, refine_derive_targets_from_compiler,
    refine_macro_rules_from_compiler,
};

const FIXTURE: &str = include_str!("../../tests/fixtures/dependencies/expansion_graph.rs");

#[test]
fn outputless_macro_candidates_require_an_empty_graph_census() {
    let node = |id: u32, parent: Option<ExpansionId>| {
        let kind = ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: format!("m{id}"),
        };
        ExpansionNode {
            id: ExpansionId(id),
            key: ExpansionKey(vec![ExpansionKeyPart {
                kind: kind.clone(),
                fragment: Some(ExpansionFragmentKind::Items),
                implementation: Some(MacroImplementationKind::Declarative),
                invocation_range: None,
                node_range: None,
                target_range: None,
                macro_definition: None,
                selected_macro_rule: None,
                same_role_ordinal: 0,
            }]),
            kind,
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            discovered_in: parent,
            semantic_parent: parent,
            source_call_parent: parent,
            written_invocation: None,
            source_owner: Some(DefinitionId(0)),
            macro_definition: Some(DefinitionTarget::Local(DefinitionId(1))),
        }
    };
    let candidate = ExpansionId(0);
    let expansions = vec![node(0, None)];
    assert_eq!(
        validated_outputless_macro_expansions(&expansions, &[], &[candidate]),
        Some(BTreeSet::from([candidate]))
    );
    assert_eq!(
        validated_outputless_macro_expansions(&expansions, &[], &[]),
        Some(BTreeSet::new())
    );
    assert_eq!(
        validated_outputless_macro_expansions(&expansions, &[], &[candidate, candidate]),
        None
    );

    let generated = DependencyEdge {
        from: GraphNode::Definition(DefinitionId(2)),
        to: GraphNode::Expansion(candidate),
        kind: DependencyKind::GeneratedBy,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    };
    assert_eq!(
        validated_outputless_macro_expansions(&expansions, &[generated], &[candidate]),
        None
    );

    let child = node(1, Some(candidate));
    assert_eq!(
        validated_outputless_macro_expansions(
            &[expansions[0].clone(), child.clone()],
            &[],
            &[candidate],
        ),
        None
    );
    let parent_edge = DependencyEdge {
        from: GraphNode::Expansion(child.id),
        to: GraphNode::Expansion(candidate),
        kind: DependencyKind::ExpansionSourceCallParent,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    };
    assert_eq!(
        validated_outputless_macro_expansions(
            &[expansions[0].clone(), child],
            &[parent_edge],
            &[candidate],
        ),
        None
    );

    for implementation in [
        MacroImplementationKind::Builtin,
        MacroImplementationKind::Procedural,
    ] {
        let mut opaque_implementation = expansions.clone();
        opaque_implementation[0].implementation = Some(implementation);
        opaque_implementation[0].macro_definition = None;
        assert_eq!(
            validated_outputless_macro_expansions(&opaque_implementation, &[], &[candidate],),
            Some(BTreeSet::from([candidate]))
        );
    }

    let mut nonlocal = expansions.clone();
    nonlocal[0].implementation = Some(MacroImplementationKind::Declarative);
    nonlocal[0].macro_definition = None;
    assert_eq!(
        validated_outputless_macro_expansions(&nonlocal, &[], &[candidate]),
        Some(BTreeSet::from([candidate]))
    );

    let mut unclassified = expansions.clone();
    unclassified[0].implementation = None;
    assert_eq!(
        validated_outputless_macro_expansions(&unclassified, &[], &[candidate]),
        None
    );
}

#[test]
fn same_product_basis_definitions_share_retention_contributors() {
    let root_origin = DefinitionOrigin::Written {
        unit: SourceUnitId(0),
        unit_range: ByteRange { start: 0, end: 100 },
        anchor: ByteRange { start: 0, end: 100 },
        unit_kind: WrittenUnitKind::CrateRoot,
        unit_ordinal: 0,
    };
    let root_part = DefinitionKeyPart {
        kind: DefinitionKind::Crate,
        origin: root_origin.key(),
        name: None,
        same_role_ordinal: 0,
    };
    let root = Definition {
        id: DefinitionId(0),
        key: DefinitionKey(vec![root_part.clone()]),
        kind: DefinitionKind::Crate,
        parent: None,
        origin: root_origin,
    };
    let expanded = |id: u32, ordinal: u32| {
        let origin = DefinitionOrigin::Expanded {
            invocation: SourceUnitId(1),
            invocation_range: ByteRange { start: 10, end: 20 },
            generated_role: None,
            ordinal,
        };
        let part = DefinitionKeyPart {
            kind: DefinitionKind::Use,
            origin: origin.key(),
            name: None,
            same_role_ordinal: ordinal,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![root_part.clone(), part]),
            kind: DefinitionKind::Use,
            parent: Some(DefinitionId(0)),
            origin,
        }
    };
    let graph = DefinitionGraph::new(
        vec![root, expanded(1, 0), expanded(2, 1)],
        Vec::new(),
        vec![
            DefinitionEdge {
                from: DefinitionId(1),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DefinitionDependencyKind::Parent,
                sites: vec![ByteRange { start: 10, end: 20 }],
            },
            DefinitionEdge {
                from: DefinitionId(2),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DefinitionDependencyKind::Parent,
                sites: vec![ByteRange { start: 10, end: 20 }],
            },
        ],
    )
    .expect("test graph must be valid");
    let contributor_dag = MacroContributorDag::test_source_singletons(Some(3));
    let product_bases = vec![None, Some(Vec::new()), Some(Vec::new())];
    coalesce_definition_identity_cohorts(&mut [], &graph, &product_bases, &contributor_dag)
        .expect("an unobserved identity cohort is outside the coverage contract");
    let mut coverage = vec![MacroProducerCoverage {
        producer: ExpansionId(0),
        output_token_count: 2,
        discarded_outputs: Vec::new(),
        materialization_groups: vec![
            MacroOutputMaterializationGroup::test_new(
                vec![SourceUnitId(2)],
                vec![MacroOutputSlice {
                    output_ranges: vec![MacroOutputRange { start: 0, end: 1 }],
                    class: MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(1))]),
                }],
            ),
            MacroOutputMaterializationGroup::test_new(
                vec![SourceUnitId(3)],
                vec![MacroOutputSlice {
                    output_ranges: vec![MacroOutputRange { start: 1, end: 2 }],
                    class: MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(2))]),
                }],
            ),
        ],
    }];

    coalesce_definition_identity_cohorts(&mut coverage, &graph, &product_bases, &contributor_dag)
        .expect("same-basis products must form a conservative cohort");
    assert_eq!(
        coverage[0].materialization_groups[0].contributors(),
        vec![SourceUnitId(2), SourceUnitId(3)]
    );
    assert_eq!(coverage[0].materialization_groups.len(), 1);
    assert_eq!(coverage[0].materialization_groups[0].output_slices.len(), 2);

    let cross_producer = vec![
        MacroProducerCoverage {
            producer: ExpansionId(0),
            output_token_count: 1,
            discarded_outputs: Vec::new(),
            materialization_groups: vec![MacroOutputMaterializationGroup::test_new(
                vec![SourceUnitId(2)],
                vec![MacroOutputSlice {
                    output_ranges: vec![MacroOutputRange { start: 0, end: 1 }],
                    class: MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(1))]),
                }],
            )],
        },
        MacroProducerCoverage {
            producer: ExpansionId(1),
            output_token_count: 1,
            discarded_outputs: Vec::new(),
            materialization_groups: vec![MacroOutputMaterializationGroup::test_new(
                vec![SourceUnitId(3)],
                vec![MacroOutputSlice {
                    output_ranges: vec![MacroOutputRange { start: 0, end: 1 }],
                    class: MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(2))]),
                }],
            )],
        },
    ];
    let mut retained_cross_producer = cross_producer.clone();
    let cross_dag = coalesce_definition_identity_cohorts(
        &mut retained_cross_producer,
        &graph,
        &product_bases,
        &contributor_dag,
    )
    .expect("identity atomicity must preserve producer-local output groups");
    assert_eq!(retained_cross_producer[0].materialization_groups.len(), 1);
    assert_eq!(retained_cross_producer[1].materialization_groups.len(), 1);
    let first_gate = retained_cross_producer[0].materialization_groups[0]
        .identity_cohort_root()
        .expect("cross-producer identity needs a shared retention gate");
    assert_eq!(
        retained_cross_producer[1].materialization_groups[0].identity_cohort_root(),
        Some(first_gate)
    );
    assert_eq!(
        cross_dag.node(first_gate).unwrap().1,
        &[
            MacroContributorSetId::test_from_source_unit(SourceUnitId(2)),
            MacroContributorSetId::test_from_source_unit(SourceUnitId(3)),
        ]
    );
    assert_eq!(
        retained_cross_producer[0].materialization_groups[0].contributors(),
        vec![SourceUnitId(2)],
        "the shared gate must not replace producer-local provenance",
    );
    assert_eq!(
        retained_cross_producer[1].materialization_groups[0].contributors(),
        vec![SourceUnitId(3)],
        "the shared gate must not replace producer-local provenance",
    );

    let mut missing_member = cross_producer.clone();
    missing_member[1].materialization_groups.clear();
    assert_eq!(
        coalesce_definition_identity_cohorts(
            &mut missing_member,
            &graph,
            &product_bases,
            &contributor_dag,
        )
        .unwrap_err(),
        ExpansionError::IncompleteOrigin,
        "every member of an observed identity cohort needs a producer-local materialization"
    );

    let mut ambiguous_producer = cross_producer;
    ambiguous_producer[1].materialization_groups[0].output_slices[0].class =
        MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(1))]);
    assert_eq!(
        coalesce_definition_identity_cohorts(
            &mut ambiguous_producer,
            &graph,
            &product_bases,
            &contributor_dag,
        )
        .unwrap_err(),
        ExpansionError::IncompleteOrigin,
        "one product cannot be assigned to materializations from two producers"
    );
}

#[test]
fn identity_cohorts_form_one_shared_gate_across_a_bridging_group() {
    let root_origin = DefinitionOrigin::Written {
        unit: SourceUnitId(0),
        unit_range: ByteRange { start: 0, end: 100 },
        anchor: ByteRange { start: 0, end: 100 },
        unit_kind: WrittenUnitKind::CrateRoot,
        unit_ordinal: 0,
    };
    let root_part = DefinitionKeyPart {
        kind: DefinitionKind::Crate,
        origin: root_origin.key(),
        name: None,
        same_role_ordinal: 0,
    };
    let root = Definition {
        id: DefinitionId(0),
        key: DefinitionKey(vec![root_part.clone()]),
        kind: DefinitionKind::Crate,
        parent: None,
        origin: root_origin,
    };
    let expanded = |id: u32, name: &str| {
        let origin = DefinitionOrigin::Expanded {
            invocation: SourceUnitId(1),
            invocation_range: ByteRange { start: 10, end: 20 },
            generated_role: None,
            ordinal: id - 1,
        };
        let part = DefinitionKeyPart {
            kind: DefinitionKind::Use,
            origin: origin.key(),
            name: Some(name.to_owned()),
            same_role_ordinal: id - 1,
        };
        Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![root_part.clone(), part]),
            kind: DefinitionKind::Use,
            parent: Some(DefinitionId(0)),
            origin,
        }
    };
    let definitions = vec![
        root,
        expanded(1, "first"),
        expanded(2, "first"),
        expanded(3, "second"),
        expanded(4, "second"),
    ];
    let edges = (1..=4)
        .map(|id| DefinitionEdge {
            from: DefinitionId(id),
            to: DefinitionTarget::Local(DefinitionId(0)),
            kind: DefinitionDependencyKind::Parent,
            sites: vec![ByteRange { start: 10, end: 20 }],
        })
        .collect();
    let graph = DefinitionGraph::new(definitions, Vec::new(), edges).unwrap();
    let product_group = |source: u32, products: Vec<u32>| {
        MacroOutputMaterializationGroup::test_new(
            vec![SourceUnitId(source)],
            vec![MacroOutputSlice {
                output_ranges: vec![MacroOutputRange { start: 0, end: 1 }],
                class: MacroOutputClass::Products(
                    products
                        .into_iter()
                        .map(|id| GraphNode::Definition(DefinitionId(id)))
                        .collect(),
                ),
            }],
        )
    };
    let mut coverage = vec![
        MacroProducerCoverage::test_new(ExpansionId(0), 1, vec![product_group(1, vec![1])]),
        MacroProducerCoverage::test_new(ExpansionId(1), 1, vec![product_group(2, vec![2, 3])]),
        MacroProducerCoverage::test_new(ExpansionId(2), 1, vec![product_group(3, vec![4])]),
    ];
    let initial_dag = MacroContributorDag::test_source_singletons(Some(3));
    let product_bases = vec![
        None,
        Some(Vec::new()),
        Some(Vec::new()),
        Some(Vec::new()),
        Some(Vec::new()),
    ];
    let dag =
        coalesce_definition_identity_cohorts(&mut coverage, &graph, &product_bases, &initial_dag)
            .unwrap();

    let gates = coverage
        .iter()
        .map(|producer| producer.materialization_groups[0].identity_cohort_root())
        .collect::<Vec<_>>();
    assert!(gates.iter().all(|gate| *gate == gates[0]));
    assert!(gates[0].is_some());
    assert_eq!(dag.node_count(), initial_dag.node_count() + 1);
    assert_eq!(
        dag.node(gates[0].unwrap()).unwrap().1,
        &[
            MacroContributorSetId::test_from_source_unit(SourceUnitId(1)),
            MacroContributorSetId::test_from_source_unit(SourceUnitId(2)),
            MacroContributorSetId::test_from_source_unit(SourceUnitId(3)),
        ]
    );
}

#[test]
fn a_large_cross_producer_identity_cohort_has_linear_gate_facts() {
    const COUNT: u32 = 1_024;
    let root_origin = DefinitionOrigin::Written {
        unit: SourceUnitId(0),
        unit_range: ByteRange { start: 0, end: 100 },
        anchor: ByteRange { start: 0, end: 100 },
        unit_kind: WrittenUnitKind::CrateRoot,
        unit_ordinal: 0,
    };
    let root_part = DefinitionKeyPart {
        kind: DefinitionKind::Crate,
        origin: root_origin.key(),
        name: None,
        same_role_ordinal: 0,
    };
    let root = Definition {
        id: DefinitionId(0),
        key: DefinitionKey(vec![root_part.clone()]),
        kind: DefinitionKind::Crate,
        parent: None,
        origin: root_origin,
    };
    let mut definitions = vec![root];
    let mut edges = Vec::new();
    let mut coverage = Vec::new();
    for id in 1..=COUNT {
        let origin = DefinitionOrigin::Expanded {
            invocation: SourceUnitId(1),
            invocation_range: ByteRange { start: 10, end: 20 },
            generated_role: None,
            ordinal: id - 1,
        };
        definitions.push(Definition {
            id: DefinitionId(id),
            key: DefinitionKey(vec![
                root_part.clone(),
                DefinitionKeyPart {
                    kind: DefinitionKind::Use,
                    origin: origin.key(),
                    name: None,
                    same_role_ordinal: id - 1,
                },
            ]),
            kind: DefinitionKind::Use,
            parent: Some(DefinitionId(0)),
            origin,
        });
        edges.push(DefinitionEdge {
            from: DefinitionId(id),
            to: DefinitionTarget::Local(DefinitionId(0)),
            kind: DefinitionDependencyKind::Parent,
            sites: vec![ByteRange { start: 10, end: 20 }],
        });
        coverage.push(MacroProducerCoverage::test_new(
            ExpansionId(id - 1),
            1,
            vec![MacroOutputMaterializationGroup::test_new(
                vec![SourceUnitId(id)],
                vec![MacroOutputSlice {
                    output_ranges: vec![MacroOutputRange { start: 0, end: 1 }],
                    class: MacroOutputClass::Products(vec![GraphNode::Definition(DefinitionId(
                        id,
                    ))]),
                }],
            )],
        ));
    }
    let graph = DefinitionGraph::new(definitions, Vec::new(), edges).unwrap();
    let initial_dag = MacroContributorDag::test_source_singletons(Some(COUNT));
    let initial_facts = initial_dag.stored_fact_count();
    let mut product_bases = vec![None];
    product_bases.extend((0..COUNT).map(|_| Some(Vec::new())));
    let dag =
        coalesce_definition_identity_cohorts(&mut coverage, &graph, &product_bases, &initial_dag)
            .unwrap();

    let gate = coverage[0].materialization_groups[0]
        .identity_cohort_root()
        .unwrap();
    assert!(coverage.iter().all(|producer| {
        producer.materialization_groups.len() == 1
            && producer.materialization_groups[0].identity_cohort_root() == Some(gate)
            && producer.materialization_groups[0].contributor_roots().len() == 1
    }));
    assert_eq!(dag.node_count(), initial_dag.node_count() + 1);
    assert_eq!(dag.stored_fact_count(), initial_facts + COUNT as usize);
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ExpansionRef {
    key_depth: usize,
    kind: ExpansionKind,
    fragment: Option<ExpansionFragmentKind>,
    implementation: Option<MacroImplementationKind>,
    invocation_range: Option<ByteRange>,
    node_range: Option<ByteRange>,
    target_range: Option<ByteRange>,
    written: bool,
    owner: String,
    macro_definition: String,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum RelationRef {
    DiscoveredIn,
    SemanticParent,
    SourceCallParent,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ParentRef {
    child: ExpansionRef,
    parent: ExpansionRef,
    relation: RelationRef,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct MacroDefinitionRef {
    expansion: ExpansionRef,
    target: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ExpansionUseRef {
    owner: String,
    expansion: ExpansionRef,
    sites: Vec<ObservationSite>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct GeneratedByRef {
    definition: String,
    expansion: ExpansionRef,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GraphRef {
    expansions: BTreeSet<ExpansionRef>,
    parents: BTreeSet<ParentRef>,
    macro_definitions: BTreeSet<MacroDefinitionRef>,
    uses: BTreeSet<ExpansionUseRef>,
    generated: BTreeSet<GeneratedByRef>,
}

#[test]
fn macro_expansions_preserve_exact_ownership_and_relations() {
    let actual = inspect(FIXTURE);
    let expected = expected_graph(FIXTURE);

    assert_eq!(actual, expected);
}

#[test]
fn stacked_written_derive_attributes_are_independent_source_roots() {
    let source = concat!(
        "#[derive()]\n",
        "#[derive(Clone, Debug)]\n",
        "struct Derived;\n",
        "fn main() { let _ = Derived.clone(); }\n",
    );
    let graph = inspect(source);
    let expansion = |style, invocation| {
        let invocation = marker(source, invocation);
        graph
            .expansions
            .iter()
            .find(|expansion| {
                expansion.invocation_range == Some(invocation)
                    && matches!(
                        expansion.kind,
                        ExpansionKind::Macro {
                            style: actual,
                            ..
                        } if actual == style
                    )
            })
            .cloned()
            .expect("the macro expansion must have an exact written source")
    };
    let empty_outer = expansion(MacroStyle::Attribute, "#[derive()]");
    let populated_outer = expansion(MacroStyle::Attribute, "#[derive(Clone, Debug)]");
    let clone = expansion(MacroStyle::Derive, "Clone");
    let debug = expansion(MacroStyle::Derive, "Debug");

    for outer in [&empty_outer, &populated_outer] {
        assert_eq!(outer.key_depth, 1);
        assert!(outer.written);
        assert_eq!(outer.owner, "<none>");
        assert!(
            graph
                .parents
                .iter()
                .all(|relation| relation.child != *outer)
        );
    }
    for child in [&clone, &debug] {
        assert_eq!(child.key_depth, 2);
        assert!(child.written);
        assert_eq!(child.owner, "Derived");
        assert_eq!(
            graph
                .parents
                .iter()
                .filter(|relation| relation.child == *child)
                .map(|relation| (relation.parent.clone(), relation.relation))
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                (populated_outer.clone(), RelationRef::DiscoveredIn),
                (populated_outer.clone(), RelationRef::SemanticParent),
            ])
        );
    }
}

#[test]
fn definition_identity_survives_when_the_last_split_component_disappears() {
    const ORIGINAL: &str = "macro_rules! choose_rule {\n\
    ($one:ident) => { pub fn $one() -> u32 { 99 } };\n\
    ($($many:ident),*) => {\n\
        pub fn dead_direct() -> u32 { 123 }\n\
        pub enum Generated { $($many),* }\n\
    };\n\
}\n\
mod selected_first { choose_rule!(kept); }\n\
mod selected_second { choose_rule!(Kept, Dead); }\n\
fn main() {\n\
    assert_eq!(selected_first::kept(), 99);\n\
    let _ = selected_second::Generated::Kept;\n\
}\n";
    const REDUCED: &str = "macro_rules! choose_rule {\n\
    ($one:ident) => { pub fn $one() -> u32 { 99 } };\n\
    ($($many:ident),*) => {\n\
        pub enum Generated { $($many),* }\n\
    };\n\
}\n\
mod selected_first { choose_rule!(kept); }\n\
mod selected_second { choose_rule!(Kept, Dead); }\n\
fn main() {\n\
    assert_eq!(selected_first::kept(), 99);\n\
    let _ = selected_second::Generated::Kept;\n\
}\n";
    let original = collect(ORIGINAL);
    let reduced = collect(REDUCED);

    let producer_is_covered = |collected: &TestCollection, invocation: ByteRange| {
        let producer = collected
            .expansions
            .nodes
            .iter()
            .find(|expansion| {
                expansion
                    .key
                    .0
                    .last()
                    .is_some_and(|part| part.invocation_range == Some(invocation))
            })
            .map(|expansion| expansion.id)
            .expect("the written invocation must have one expansion");
        collected
            .expansions
            .macro_producer_coverage
            .producers()
            .iter()
            .any(|coverage| coverage.producer() == producer)
    };

    assert!(producer_is_covered(
        &original,
        marker(ORIGINAL, "choose_rule!(Kept, Dead)"),
    ));
    assert!(!producer_is_covered(
        &reduced,
        marker(REDUCED, "choose_rule!(Kept, Dead)"),
    ));
    let original_basis = definition_product_basis(&original, "Dead")
        .expect("the original producer must have an exact product basis");
    let reduced_basis = definition_product_basis(&reduced, "Dead")
        .expect("the producer must keep its exact product basis after source splitting disappears");
    assert_eq!(original_basis, reduced_basis);
    assert!(
        original_basis.is_empty(),
        "the exact product has no contributor shared by all of its tokens; observed-empty must remain distinct from missing"
    );
}

#[test]
fn late_parsed_inner_macro_inherits_its_refined_parent_component_basis() {
    let collected = collect(FIXTURE);
    let basis = definition_product_basis(&collected, "forwarded_generated")
        .expect("the late-parsed child definition must have an exact product basis");
    let parent_component = marker_in(FIXTURE, "$($tokens)*\n    };", "$tokens");
    assert!(
        basis.iter().any(|source| {
            source.kind
                == SourceUnitIdentityKind::Declarative(
                    crate::source::DeclarativeSourceUnitKind::TemplateComponent,
                )
                && source.range == parent_component
        }),
        "the exact product basis must retain the refined parent contributor",
    );
}

#[test]
fn repeated_forwarded_inputs_share_one_complete_provenance_fact() {
    const TOKENS: usize = 64;
    let expression = std::iter::repeat_n("1", TOKENS)
        .collect::<Vec<_>>()
        .join(" + ");
    let repeated = std::iter::repeat_n("$value", TOKENS)
        .collect::<Vec<_>>()
        .join(" + ");
    let source = format!(
        "macro_rules! produce {{ ($value:expr) => {{ fn forwarded_generated() -> usize {{ {repeated} }} }}; }}\n\
         macro_rules! forward {{ ($value:expr) => {{ produce!($value); }}; }}\n\
         forward!(({expression}));\n\
         fn main() {{ assert_eq!(forwarded_generated(), {}); }}\n",
        TOKENS * TOKENS,
    );

    let collected = collect(&source);
    let basis = definition_product_basis(&collected, "forwarded_generated")
        .expect("the twice-forwarded definition must retain complete provenance");
    assert!(!basis.is_empty());
}

#[test]
fn builtin_attribute_discovery_does_not_cross_the_opaque_parent_boundary() {
    let source = concat!(
        "macro_rules! dimension { () => { 1 }; }\n",
        "#[derive(Clone)]\n",
        "struct Documented([u8; dimension!()]);\n",
        "fn main() { let _ = Documented([0]).0; }\n",
    );
    let collected = collect(source);
    let graph = project_graph(&collected);
    let local_invocation = marker(source, "dimension!()");
    let local = graph
        .expansions
        .iter()
        .find(|expansion| expansion.invocation_range == Some(local_invocation))
        .expect("the nested declarative invocation must be observed");
    let discovered_parent = graph
        .parents
        .iter()
        .find(|relation| relation.child == *local && relation.relation == RelationRef::DiscoveredIn)
        .map(|relation| &relation.parent)
        .expect("the built-in attribute must be the discovery parent");

    assert!(matches!(
        discovered_parent.implementation,
        Some(MacroImplementationKind::Builtin | MacroImplementationKind::InertAttribute),
    ));
    assert!(
        graph.parents.iter().all(|relation| {
            relation.child != *local || relation.relation != RelationRef::SourceCallParent
        }),
        "the written source context must not replace the observed opaque discovery parent",
    );
    assert!(
        !local.written,
        "the opaque parent cannot lend a written anchor"
    );
    let generated_literal = marker(source, " 1 ");
    assert!(collected.source_units.iter().all(|unit| {
        unit.kind != WrittenUnitKind::NestedItem || unit.full_range != generated_literal
    }));
}

fn definition_product_basis<'a>(
    collected: &'a TestCollection,
    name: &str,
) -> Option<&'a [crate::source::MacroProductSource]> {
    let definition = collected
        .definitions
        .definitions
        .iter()
        .find(|definition| {
            definition
                .key
                .0
                .last()
                .and_then(|part| part.name.as_deref())
                == Some(name)
        })?;
    collected.product_bases[definition.id.0 as usize].as_deref()
}

fn inspect(source: &str) -> GraphRef {
    let collected = collect(source);
    project_graph(&collected)
}

fn collect(source: &str) -> TestCollection {
    let (sysroot, target) = compiler_context();
    let result = Arc::new(Mutex::new(None));
    let mut callbacks = ExpansionCallbacks {
        source: Arc::from(source),
        result: Arc::clone(&result),
        inventory: None,
        declarative_outputs: None,
    };
    let arguments = vec![
        "rust-item-dependencies-expansions".to_owned(),
        "main.rs".to_owned(),
        "--crate-name=main".to_owned(),
        "--crate-type=bin".to_owned(),
        "--edition=2024".to_owned(),
        format!("--target={target}"),
        "--sysroot".to_owned(),
        sysroot.to_string_lossy().into_owned(),
        "--emit=metadata=-".to_owned(),
    ];
    let status =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut callbacks));
    assert!(status.is_ok(), "the fixture compiler must not fail");
    result
        .lock()
        .expect("expansion result mutex is poisoned")
        .take()
        .expect("the compiler must reach analysis")
        .expect("the expansion graph must be complete")
}

struct ExpansionCallbacks {
    source: Arc<str>,
    result: Arc<Mutex<Option<Result<TestCollection, ExpansionError>>>>,
    inventory: Option<SourceInventory>,
    declarative_outputs: Option<ValidatedDeclarativeOutputs>,
}

struct TestCollection {
    definitions: crate::graph::DefinitionGraph,
    product_bases: Vec<Option<Vec<crate::source::MacroProductSource>>>,
    expansions: CollectedExpansions,
    source_units: Vec<crate::source::WrittenUnit>,
}

impl Callbacks for ExpansionCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.opts.unstable_features = UnstableFeatures::Disallow;
        let name = config
            .opts
            .file_path_mapping()
            .to_real_filename(&RealFileName::empty(), Path::new("main.rs"));
        config.input = Input::Str {
            name: FileName::Real(name),
            input: self.source.to_string(),
        };
        config.file_loader = Some(Box::new(MainSourceOnly {
            source: Arc::clone(&self.source),
        }));
        #[cfg(rust_item_dependencies_patched)]
        {
            config.observe_declarative_macro_expansions = true;
        }
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        krate: &mut ast::Crate,
    ) -> Compilation {
        self.inventory = Some(
            collect_source(compiler, krate, Arc::clone(&self.source))
                .expect("source inventory must be complete"),
        );
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        let inventory = self
            .inventory
            .as_ref()
            .expect("source inventory must survive through analysis");
        let outputs = self
            .declarative_outputs
            .as_ref()
            .expect("declarative outputs must survive through analysis");
        let value =
            collect_macro_provenance(compiler, tcx, inventory, outputs).and_then(|provenance| {
                collect_definitions(compiler, tcx, inventory, &provenance)
                    .map_err(ExpansionError::from)
                    .and_then(|mut definitions| {
                        let expansions = collect_expansions(
                            compiler,
                            tcx,
                            inventory,
                            &mut definitions,
                            &provenance,
                        )?;
                        Ok(TestCollection {
                            product_bases: definitions.product_bases().to_vec(),
                            definitions: definitions.graph,
                            expansions,
                            source_units: inventory.units.clone(),
                        })
                    })
            });
        *self
            .result
            .lock()
            .expect("expansion result mutex is poisoned") = Some(value);
        Compilation::Stop
    }

    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let declarative_outputs = ValidatedDeclarativeOutputs::collect(tcx);
        {
            let (_, krate) = tcx.resolver_for_lowering();
            let krate = krate.borrow();
            refine_attribute_macros_from_compiler(
                compiler,
                tcx,
                &krate,
                self.inventory
                    .as_mut()
                    .expect("source inventory must survive through expansion"),
            )
            .expect("attribute source inventory must be complete");
        }
        refine_derive_targets_from_compiler(
            compiler,
            tcx,
            self.inventory
                .as_mut()
                .expect("source inventory must survive through expansion"),
        )
        .expect("derive source inventory must be complete");
        refine_macro_rules_from_compiler(
            compiler,
            tcx,
            self.inventory
                .as_mut()
                .expect("source inventory must survive through expansion"),
            &declarative_outputs,
            false,
        )
        .expect("macro rule inventory must be complete");
        self.declarative_outputs = Some(declarative_outputs);
        Compilation::Continue
    }
}

struct MainSourceOnly {
    source: Arc<str>,
}

impl FileLoader for MainSourceOnly {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new("main.rs")
    }

    fn read_file(&self, path: &Path) -> std::io::Result<String> {
        if path == Path::new("main.rs") {
            Ok(self.source.to_string())
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "the fixture is single-source",
            ))
        }
    }

    fn read_binary_file(&self, path: &Path) -> std::io::Result<Arc<[u8]>> {
        if path == Path::new("main.rs") {
            Ok(Arc::from(self.source.as_bytes()))
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "the fixture is single-source",
            ))
        }
    }

    fn current_directory(&self) -> std::io::Result<PathBuf> {
        Ok(PathBuf::new())
    }
}

fn project_graph(collected: &TestCollection) -> GraphRef {
    let expansion_refs = collected
        .expansions
        .nodes
        .iter()
        .map(|node| (node.id, expansion_ref(collected, node)))
        .collect::<BTreeMap<_, _>>();
    let definition_names = collected
        .definitions
        .definitions
        .iter()
        .map(|definition| {
            (
                definition.id,
                definition_name(&collected.definitions, definition.id),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let expansions = expansion_refs.values().cloned().collect();
    let mut parents = BTreeSet::new();
    let mut macro_definitions = BTreeSet::new();
    let mut uses = BTreeSet::new();
    let mut generated = BTreeSet::new();
    for edge in &collected.expansions.edges {
        match edge.kind {
            DependencyKind::ExpansionDiscoveredIn
            | DependencyKind::ExpansionSemanticParent
            | DependencyKind::ExpansionSourceCallParent => {
                let (GraphNode::Expansion(child), GraphNode::Expansion(parent)) =
                    (edge.from, edge.to)
                else {
                    panic!("expansion relation must connect expansions");
                };
                let relation = match edge.kind {
                    DependencyKind::ExpansionDiscoveredIn => RelationRef::DiscoveredIn,
                    DependencyKind::ExpansionSemanticParent => RelationRef::SemanticParent,
                    DependencyKind::ExpansionSourceCallParent => RelationRef::SourceCallParent,
                    _ => unreachable!(),
                };
                parents.insert(ParentRef {
                    child: expansion_refs[&child].clone(),
                    parent: expansion_refs[&parent].clone(),
                    relation,
                });
            }
            DependencyKind::MacroDefinition => {
                let GraphNode::Expansion(expansion) = edge.from else {
                    panic!("macro definition source must be an expansion");
                };
                macro_definitions.insert(MacroDefinitionRef {
                    expansion: expansion_refs[&expansion].clone(),
                    target: graph_node_name(collected, edge.to),
                });
            }
            DependencyKind::ExpansionUse => {
                let (GraphNode::Definition(owner), GraphNode::Expansion(expansion)) =
                    (edge.from, edge.to)
                else {
                    panic!("expansion use must connect an owner to an expansion");
                };
                uses.insert(ExpansionUseRef {
                    owner: definition_names[&owner].clone(),
                    expansion: expansion_refs[&expansion].clone(),
                    sites: edge.sites.clone(),
                });
            }
            DependencyKind::GeneratedBy => {
                let (GraphNode::Definition(definition), GraphNode::Expansion(expansion)) =
                    (edge.from, edge.to)
                else {
                    panic!("generated definition must target an expansion");
                };
                generated.insert(GeneratedByRef {
                    definition: definition_names[&definition].clone(),
                    expansion: expansion_refs[&expansion].clone(),
                });
            }
            _ => panic!("unexpected expansion edge: {edge:?}"),
        }
    }

    GraphRef {
        expansions,
        parents,
        macro_definitions,
        uses,
        generated,
    }
}

fn expansion_ref(collected: &TestCollection, node: &ExpansionNode) -> ExpansionRef {
    let part = node.key.0.last().expect("expansion key must be nonempty");
    ExpansionRef {
        key_depth: node.key.0.len(),
        kind: node.kind.clone(),
        fragment: node.fragment,
        implementation: node.implementation,
        invocation_range: part.invocation_range,
        node_range: part.node_range,
        target_range: part.target_range,
        written: node.written_invocation.is_some(),
        owner: node.source_owner.map_or_else(
            || "<none>".to_owned(),
            |id| definition_name(&collected.definitions, id),
        ),
        macro_definition: node.macro_definition.map_or_else(
            || "<none>".to_owned(),
            |target| definition_target_name(&collected.definitions, target),
        ),
    }
}

fn graph_node_name(collected: &TestCollection, node: GraphNode) -> String {
    match node {
        GraphNode::Definition(id) => definition_name(&collected.definitions, id),
        GraphNode::ExternalDefinition(id) => collected.definitions.external_definitions
            [id.0 as usize]
            .path
            .clone(),
        _ => panic!("expected a definition node"),
    }
}

fn definition_target_name(
    graph: &crate::graph::DefinitionGraph,
    target: DefinitionTarget,
) -> String {
    match target {
        DefinitionTarget::Local(id) => definition_name(graph, id),
        DefinitionTarget::External(id) => graph.external_definitions[id.0 as usize].path.clone(),
    }
}

fn definition_name(graph: &crate::graph::DefinitionGraph, id: DefinitionId) -> String {
    let definition = &graph.definitions[id.0 as usize];
    if definition.kind == DefinitionKind::Crate {
        return "crate".to_owned();
    }
    let leaf = definition
        .key
        .0
        .last()
        .expect("definition key must be nonempty");
    leaf.name
        .clone()
        .unwrap_or_else(|| format!("{:?}@{}", definition.kind, origin_start(&definition.origin)))
}

fn origin_start(origin: &DefinitionOrigin) -> u32 {
    match origin {
        DefinitionOrigin::Written { anchor, .. } => anchor.start,
        DefinitionOrigin::Expanded {
            invocation_range, ..
        } => invocation_range.start,
        DefinitionOrigin::CompilerGenerated { ordinal, .. }
        | DefinitionOrigin::Injected { ordinal, .. } => *ordinal,
    }
}

fn expected_graph(source: &str) -> GraphRef {
    let direct = bang(source, "direct!()", "direct", "crate");
    let outer = bang(source, "outer!()", "outer", "crate");
    let nested = generated_bang(source, "nested!()", "nested", "crate");
    let forward = bang(source, "forward!(forwarded!();)", "forward", "crate");
    let mut forwarded = generated_bang(source, "forwarded!()", "forwarded", "crate");
    // The invocation is written inside `forward!`'s input even though rustc
    // expands it while processing the parent expansion.
    forwarded.written = true;
    let define_late = bang(source, "define_late!()", "define_late", "crate");
    let concat = builtin_bang(source, "concat!(late!())", "concat", "std::concat", "EAGER");
    let late_range = marker_in(source, "const EAGER: &str = concat!(late!());", "late!()");
    let late = ExpansionRef {
        key_depth: 2,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: "late".to_owned(),
        },
        fragment: Some(ExpansionFragmentKind::Expression),
        implementation: Some(MacroImplementationKind::Declarative),
        invocation_range: Some(late_range),
        node_range: Some(late_range),
        target_range: None,
        written: false,
        owner: "EAGER".to_owned(),
        macro_definition: "late".to_owned(),
    };
    let derive = ExpansionRef {
        key_depth: 1,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Attribute,
            name: "derive".to_owned(),
        },
        fragment: Some(ExpansionFragmentKind::Items),
        implementation: Some(MacroImplementationKind::Builtin),
        invocation_range: Some(marker(source, "#[derive(Clone)]")),
        node_range: Some(between(source, "#[derive(Clone)]", "struct Derived;")),
        target_range: Some(marker(source, "struct Derived;")),
        written: true,
        owner: "<none>".to_owned(),
        macro_definition: "std::derive".to_owned(),
    };
    let clone = ExpansionRef {
        key_depth: 2,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Derive,
            name: "Clone".to_owned(),
        },
        fragment: Some(ExpansionFragmentKind::Items),
        implementation: Some(MacroImplementationKind::Builtin),
        invocation_range: Some(marker(source, "Clone")),
        node_range: Some(marker(source, "struct Derived;")),
        target_range: Some(marker(source, "struct Derived;")),
        written: true,
        owner: "Derived".to_owned(),
        macro_definition: "std::clone::Clone".to_owned(),
    };

    let expansions = BTreeSet::from([
        direct.clone(),
        outer.clone(),
        nested.clone(),
        forward.clone(),
        forwarded.clone(),
        define_late.clone(),
        concat.clone(),
        late.clone(),
        derive.clone(),
        clone.clone(),
    ]);
    let parents = BTreeSet::from([
        parent(&nested, &outer, RelationRef::DiscoveredIn),
        parent(&nested, &outer, RelationRef::SemanticParent),
        parent(&nested, &outer, RelationRef::SourceCallParent),
        parent(&forwarded, &forward, RelationRef::DiscoveredIn),
        parent(&forwarded, &forward, RelationRef::SemanticParent),
        parent(&late, &concat, RelationRef::DiscoveredIn),
        parent(&clone, &derive, RelationRef::DiscoveredIn),
        parent(&clone, &derive, RelationRef::SemanticParent),
    ]);
    let macro_definitions = expansions
        .iter()
        .map(|expansion| MacroDefinitionRef {
            expansion: expansion.clone(),
            target: expansion.macro_definition.clone(),
        })
        .collect();
    let uses = expansions
        .iter()
        .filter(|expansion| expansion.owner != "<none>")
        .map(|expansion| ExpansionUseRef {
            owner: expansion.owner.clone(),
            expansion: expansion.clone(),
            sites: vec![if expansion.written {
                ObservationSite::Source(
                    expansion
                        .invocation_range
                        .expect("fixture expansion must have an invocation range"),
                )
            } else {
                ObservationSite::CompilerGenerated
            }],
        })
        .collect();
    let generated = BTreeSet::from([
        generated("direct_generated", &direct),
        generated("nested_generated", &nested),
        generated("forwarded_generated", &forwarded),
        generated("late", &define_late),
        generated("Impl@659", &clone),
        generated("clone", &clone),
        generated("'_", &clone),
    ]);

    GraphRef {
        expansions,
        parents,
        macro_definitions,
        uses,
        generated,
    }
}

fn bang(source: &str, invocation: &str, definition: &str, owner: &str) -> ExpansionRef {
    ExpansionRef {
        key_depth: 1,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: definition.to_owned(),
        },
        fragment: Some(ExpansionFragmentKind::Items),
        implementation: Some(MacroImplementationKind::Declarative),
        invocation_range: Some(marker(source, invocation)),
        node_range: Some(statement(source, invocation)),
        target_range: None,
        written: true,
        owner: owner.to_owned(),
        macro_definition: definition.to_owned(),
    }
}

fn generated_bang(source: &str, invocation: &str, definition: &str, owner: &str) -> ExpansionRef {
    ExpansionRef {
        key_depth: 2,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: definition.to_owned(),
        },
        fragment: Some(if definition == "late" {
            ExpansionFragmentKind::Expression
        } else {
            ExpansionFragmentKind::Items
        }),
        implementation: Some(MacroImplementationKind::Declarative),
        invocation_range: Some(marker(source, invocation)),
        node_range: Some(if definition == "late" {
            marker(source, invocation)
        } else {
            statement(source, invocation)
        }),
        target_range: None,
        written: false,
        owner: owner.to_owned(),
        macro_definition: definition.to_owned(),
    }
}

fn builtin_bang(
    source: &str,
    invocation: &str,
    name: &str,
    definition: &str,
    owner: &str,
) -> ExpansionRef {
    ExpansionRef {
        key_depth: 1,
        kind: ExpansionKind::Macro {
            style: MacroStyle::Bang,
            name: name.to_owned(),
        },
        fragment: Some(ExpansionFragmentKind::Expression),
        implementation: Some(MacroImplementationKind::Builtin),
        invocation_range: Some(marker(source, invocation)),
        node_range: Some(marker(source, invocation)),
        target_range: None,
        written: true,
        owner: owner.to_owned(),
        macro_definition: definition.to_owned(),
    }
}

fn parent(child: &ExpansionRef, parent: &ExpansionRef, relation: RelationRef) -> ParentRef {
    ParentRef {
        child: child.clone(),
        parent: parent.clone(),
        relation,
    }
}

fn generated(definition: &str, expansion: &ExpansionRef) -> GeneratedByRef {
    GeneratedByRef {
        definition: definition.to_owned(),
        expansion: expansion.clone(),
    }
}

fn marker(source: &str, value: &str) -> ByteRange {
    let matches = source.match_indices(value).collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "fixture marker must be unique: {value:?}");
    let (start, matched) = matches[0];
    ByteRange {
        start: start as u32,
        end: (start + matched.len()) as u32,
    }
}

fn marker_in(source: &str, container: &str, value: &str) -> ByteRange {
    let container_range = marker(source, container);
    let container = &source[container_range.start as usize..container_range.end as usize];
    let matches = container.match_indices(value).collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "fixture marker must be unique: {value:?}");
    let (relative, matched) = matches[0];
    let start = container_range.start as usize + relative;
    ByteRange {
        start: start as u32,
        end: (start + matched.len()) as u32,
    }
}

fn statement(source: &str, value: &str) -> ByteRange {
    let mut range = marker(source, value);
    if source.as_bytes().get(range.end as usize) == Some(&b';') {
        range.end += 1;
    }
    range
}

fn between(source: &str, first: &str, last: &str) -> ByteRange {
    let first = marker(source, first);
    let last = marker(source, last);
    assert!(first.end <= last.start);
    ByteRange {
        start: first.start,
        end: last.end,
    }
}

fn compiler_context() -> (PathBuf, String) {
    let rustc = env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC");
    let sysroot = Command::new(rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc must print its sysroot");
    assert!(sysroot.status.success());
    let version = Command::new(rustc)
        .arg("-Vv")
        .output()
        .expect("rustc must print its version");
    assert!(version.status.success());
    let version = String::from_utf8(version.stdout).expect("rustc version must be UTF-8");
    let target = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc version must contain its host")
        .to_owned();
    (
        PathBuf::from(
            String::from_utf8(sysroot.stdout)
                .expect("sysroot must be UTF-8")
                .trim(),
        ),
        target,
    )
}
