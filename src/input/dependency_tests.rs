use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use super::{
    Edition, SourceInput, inspect_source_with_dependencies,
    inspect_source_with_dependencies_at_original_coordinates, inspect_source_with_reduction,
};
use crate::compiler_terms::CanonicalCompilerTerm;
use crate::dependency_graph::{
    AllocationDescriptor, AllocationPathSite, AllocationRootKey, DefinitionReferenceKey,
    DependencyGraph, DependencyKind, EvidenceOrigin, GraphNode, MonoCollection, MonoDependencyKind,
    MonoId, MonoInstanceKey, MonoInstanceRole, MonoKey, ObservationSite, ProofId, ProofNodeKind,
    ProofRelationKind, RootReason, SelectionSourceKind,
};
use crate::graph::{
    DefinitionGraph, DefinitionId, DefinitionKey, DefinitionOrigin, DefinitionOriginKey,
    DefinitionTarget, GeneratedRole,
};
use crate::source::ByteRange;

const FIXTURE: &str = include_str!("../../tests/fixtures/dependencies/mono_graph.rs");
const CONST_FIXTURE: &str = include_str!("../../tests/fixtures/compiler/const_trait_function.rs");
const OPAQUE_LIFETIME_TAG_FIXTURE: &str =
    include_str!("../../tests/fixtures/dependencies/opaque_lifetime_tag.rs");
const MACRO_ASSOCIATED_CALL: &str = r#"
struct Reader;

macro_rules! implement_read {
    () => {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Ok(0)
        }
    };
}

impl std::io::Read for Reader {
    implement_read!();
}

fn main() {
    let mut reader = Reader;
    let _ = std::io::Read::read(&mut reader, &mut []);
}
"#;

const REWRITTEN_COORDINATES: &str = r#"
fn unused_prefix() -> usize { 99 }

static VALUE: usize = 7;

fn identity<T: Copy>(value: T) -> T { value }

fn main() {
    let _ = identity(VALUE);
}
"#;

const REWRITTEN_MACRO_RULE_COORDINATES: &str =
    include_str!("../../tests/fixtures/compiler/macro_rule_expansion_retention.rs");

const FULL_RANGE_REMAINING_ITEM: &str = "fn dead() {}fn main() {}";

const EXTERNAL_SYMBOL_ROOTS: &str =
    include_str!("../../tests/fixtures/retention/external_symbol_roots.input.rs");
const EXTERNAL_SYMBOL_ROOTS_EXPECTED: &str =
    include_str!("../../tests/fixtures/retention/external_symbol_roots.expected.rs");

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AllocationRef {
    root: String,
    path: Vec<(MonoDependencyKind, MonoCollection, String, u32)>,
    descriptor: &'static str,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct MonoUseRef {
    from: String,
    to: Option<String>,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
    evidence: EvidenceOrigin,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProofUseRef {
    from: String,
    target: ProofRef,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
    evidence: EvidenceOrigin,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProofRef {
    kind: &'static str,
    definitions: Vec<(ProofRelationKind, u32, String)>,
}

#[test]
fn dependency_collection_preserves_the_exact_mono_and_proof_graph() {
    let graph = inspect_fixture();

    assert_roots_and_nodes(&graph);
    assert_allocations(&graph);
    assert_mono_edges(&graph);
    assert_proofs(&graph);
}

#[test]
fn associated_consts_promoted_values_and_codegen_shims_are_exact() {
    let graph = inspect_source(CONST_FIXTURE);
    assert_const_materializations(&graph);
    assert_const_owner_edges(&graph);
    assert_const_selection_edges(&graph);
    assert_const_instance_and_proof_joins(&graph);
    assert_const_call_chains(&graph);
}

#[test]
fn macro_generated_associated_direct_call_builds_a_valid_graph() {
    let graph = inspect_source(MACRO_ASSOCIATED_CALL);
    let impl_label = anonymous_definition(MACRO_ASSOCIATED_CALL, "impl std::io::Read for Reader");
    let call_site = vec![source_site(
        MACRO_ASSOCIATED_CALL,
        "std::io::Read::read(&mut reader, &mut [])",
    )];

    let mut mono = local_mono_edges(&graph, MACRO_ASSOCIATED_CALL)
        .into_iter()
        .filter(|edge| edge.relation == MonoDependencyKind::DirectCall)
        .collect::<Vec<_>>();
    mono.sort();
    assert_eq!(
        mono,
        vec![mono_use(
            "main",
            Some(&format!("{impl_label}::read")),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            call_site.clone(),
        )]
    );

    let mut selection = local_selection_edges(&graph, MACRO_ASSOCIATED_CALL)
        .into_iter()
        .filter(|edge| edge.relation == MonoDependencyKind::DirectCall)
        .collect::<Vec<_>>();
    selection.sort();
    let mut expected = vec![
        proof_use_with_evidence(
            "main",
            obligation_proof(vec![(
                ProofRelationKind::TraitDefinition,
                0,
                "std::marker::MetaSized",
            )]),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            call_site.clone(),
            EvidenceOrigin::Derived,
        ),
        proof_use_with_evidence(
            "main",
            associated_proof(
                &format!("{impl_label}::read"),
                &impl_label,
                &impl_label,
                &[&impl_label, "std::io::Read"],
            ),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            call_site,
            EvidenceOrigin::PatchedObserver,
        ),
    ];
    expected.sort();
    assert_eq!(selection, expected);
}

#[test]
fn external_symbols_are_compiler_roots_with_their_dependencies() {
    let (sysroot, target) = compiler_context();
    let reduction = inspect_source_with_reduction(
        &SourceInput::binary(EXTERNAL_SYMBOL_ROOTS.to_owned(), Edition::Rust2024, target),
        &sysroot,
    )
    .expect("external symbols must be reducible");

    let roots = reduction
        .graph
        .roots
        .iter()
        .filter(|root| root.reason == RootReason::ExternalSymbol)
        .map(|root| {
            let GraphNode::Mono(node) = root.node else {
                panic!("external symbol roots must be monomorphic")
            };
            reduction.graph.mono_nodes[node.0 as usize]
                .materialized_definition
                .map(|target| target_label(&reduction.graph.definitions, target))
                .expect("external symbol roots must materialize definitions")
        })
        .collect::<Vec<_>>();
    assert_eq!(roots.len(), 4);
    assert!(roots.iter().any(|root| root == "exported_function"));
    assert!(roots.iter().any(|root| root == "EXPORTED_STATIC"));
    assert!(roots.iter().any(|root| root.ends_with("::method")));
    assert!(roots.iter().any(|root| root == "generated"));

    assert_eq!(reduction.rewrite.source, EXTERNAL_SYMBOL_ROOTS_EXPECTED);
}

#[test]
fn overlapping_compiler_root_reasons_do_not_duplicate_main_or_used_statics() {
    let source = concat!(
        "#[used]\n",
        "#[unsafe(export_name = \"rid_used_export\")]\n",
        "static BOTH: i32 = 1;\n",
        "\n",
        "#[unsafe(export_name = \"rid_main_body\")]\n",
        "fn main() {}\n",
    );
    let (sysroot, target) = compiler_context();
    let reduction = inspect_source_with_reduction(
        &SourceInput::binary(source.to_owned(), Edition::Rust2024, target),
        &sysroot,
    )
    .expect("overlapping compiler roots must be reducible");

    assert_eq!(reduction.rewrite.source, source);
    let mut reasons = reduction
        .graph
        .roots
        .iter()
        .map(|root| root.reason)
        .collect::<Vec<_>>();
    reasons.sort();
    assert_eq!(
        reasons,
        vec![
            RootReason::Main,
            RootReason::StartInstance,
            RootReason::UsedAttribute,
            RootReason::ExternalSymbol,
        ]
    );
}

#[test]
fn rewritten_collection_uses_original_coordinates_for_compiler_identity() {
    let (sysroot, target) = compiler_context();
    let original = inspect_source_with_reduction(
        &SourceInput::binary(
            REWRITTEN_COORDINATES.to_owned(),
            Edition::Rust2024,
            target.clone(),
        ),
        &sysroot,
    )
    .expect("the original source must reduce");
    assert!(!original.rewrite.source.contains("unused_prefix"));

    let reduced = inspect_source_with_dependencies_at_original_coordinates(
        &SourceInput::binary(original.rewrite.source.clone(), Edition::Rust2024, target),
        &sysroot,
        &original.rewrite,
    )
    .expect("the rewritten source must be observed once in original coordinates");

    let (original_main_instance, original_main_definition) = main_nodes(&original.graph);
    let (reduced_main_instance, reduced_main_definition) = main_nodes(&reduced.graph);
    let original_main =
        &original.graph.definitions.definitions[original_main_definition.0 as usize];
    let reduced_main = &reduced.graph.definitions.definitions[reduced_main_definition.0 as usize];
    assert_eq!(reduced_main.key, original_main.key);
    assert_eq!(
        reduced.graph.mono_nodes[reduced_main_instance.0 as usize].key,
        original.graph.mono_nodes[original_main_instance.0 as usize].key
    );
    for node in &reduced.graph.mono_nodes {
        assert!(
            original
                .graph
                .mono_nodes
                .iter()
                .any(|candidate| candidate.key == node.key),
            "mapped mono identity is missing from the original graph: {:?}",
            node.key
        );
    }
    assert!(reduced.graph.edges.iter().any(|edge| {
        edge.sites
            == vec![ObservationSite::Source(marker_range_nth(
                REWRITTEN_COORDINATES,
                "identity(VALUE)",
                0,
            ))]
    }));
}

#[test]
fn rewritten_macro_rule_requirements_keep_their_collected_source_ids() {
    let (sysroot, target) = compiler_context();
    let original = inspect_source_with_reduction(
        &SourceInput::binary(
            REWRITTEN_MACRO_RULE_COORDINATES.to_owned(),
            Edition::Rust2024,
            target.clone(),
        ),
        &sysroot,
    )
    .expect("the original macro source must reduce");

    let reduced = inspect_source_with_dependencies_at_original_coordinates(
        &SourceInput::binary(original.rewrite.source.clone(), Edition::Rust2024, target),
        &sysroot,
        &original.rewrite,
    )
    .expect("the reduced macro source must map compiler identities to original coordinates");

    assert!(
        reduced
            .constraints
            .macro_rule_selection_requirements
            .iter()
            .any(|requirement| {
                let selected_range = reduced.graph.expansions[requirement.expansion.0 as usize]
                    .key
                    .0
                    .last()
                    .and_then(|part| part.selected_macro_rule)
                    .expect("a selected macro rule must remain in the compiler identity");
                selected_range != reduced.source.units[requirement.rule.0 as usize].full_range
            }),
        "the fixture must exercise different compiler-identity and source-unit coordinates"
    );
}

#[test]
fn a_remaining_full_range_item_is_not_mistaken_for_the_crate_root() {
    let (sysroot, target) = compiler_context();
    let original = inspect_source_with_reduction(
        &SourceInput::binary(
            FULL_RANGE_REMAINING_ITEM.to_owned(),
            Edition::Rust2024,
            target.clone(),
        ),
        &sysroot,
    )
    .expect("the original source must reduce");
    assert_eq!(original.rewrite.source, "fn main() {}");

    let reduced = inspect_source_with_dependencies_at_original_coordinates(
        &SourceInput::binary(original.rewrite.source.clone(), Edition::Rust2024, target),
        &sysroot,
        &original.rewrite,
    )
    .expect("the remaining full-range item must map independently of the crate root");
    let (_, original_main_definition) = main_nodes(&original.graph);
    let (_, reduced_main_definition) = main_nodes(&reduced.graph);
    let original_main =
        &original.graph.definitions.definitions[original_main_definition.0 as usize];
    let reduced_main = &reduced.graph.definitions.definitions[reduced_main_definition.0 as usize];
    assert_eq!(reduced_main.key, original_main.key);
    assert_ne!(reduced_main.key.0.last(), reduced_main.key.0.first());
}

#[test]
fn hirless_opaque_lifetime_keeps_its_graph_node_without_breaking_tag_collection() {
    let (sysroot, target) = compiler_context();
    let input = SourceInput::binary(
        OPAQUE_LIFETIME_TAG_FIXTURE.to_owned(),
        Edition::Rust2024,
        target,
    );

    let first = inspect_source_with_reduction(&input, &sysroot)
        .expect("a synthetic opaque lifetime must not be queried as a HIR node");
    let second = inspect_source_with_reduction(&input, &sysroot)
        .expect("repeated opaque-lifetime analysis must succeed");

    assert_eq!(second, first);
    assert_eq!(first.tags.len(), 1);
    let (&tagged_definition, tags) = first
        .tags
        .first_key_value()
        .expect("the roots definition must keep its tag");
    assert_eq!(
        tags,
        &std::collections::BTreeSet::from(["opaque-lifetime".to_owned()])
    );
    assert!(
        first
            .retention
            .semantic_required
            .contains(&GraphNode::Definition(tagged_definition))
    );
    assert!(
        first
            .rewrite
            .source
            .contains("rust-item-dependencies:tag=opaque-lifetime")
    );
    let opaque_lifetimes = first
        .graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| {
            matches!(
                definition.origin,
                DefinitionOrigin::CompilerGenerated {
                    role: GeneratedRole::OpaqueLifetime,
                    ..
                }
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(opaque_lifetimes.len(), 1);
    assert!(opaque_lifetimes[0].parent.is_some());
}

fn inspect_source(source: &str) -> DependencyGraph {
    let (sysroot, target) = compiler_context();
    inspect_source_with_dependencies(
        &SourceInput::binary(source.to_owned(), Edition::Rust2024, target),
        &sysroot,
    )
    .expect("complete compiler observations must produce a dependency graph")
    .graph
}

fn inspect_fixture() -> DependencyGraph {
    inspect_source(FIXTURE)
}

fn main_nodes(graph: &DependencyGraph) -> (MonoId, DefinitionId) {
    let roots = graph
        .roots
        .iter()
        .filter(|root| root.reason == RootReason::Main)
        .collect::<Vec<_>>();
    let [root] = roots.as_slice() else {
        panic!("a binary graph must have exactly one main root")
    };
    let GraphNode::Mono(instance) = root.node else {
        panic!("the main root must be monomorphic")
    };
    let Some(DefinitionTarget::Local(definition)) =
        graph.mono_nodes[instance.0 as usize].materialized_definition
    else {
        panic!("the main root must materialize a local definition")
    };
    (instance, definition)
}

fn assert_const_materializations(graph: &DependencyGraph) {
    let mut actual = graph
        .mono_nodes
        .iter()
        .filter_map(|node| match node.materialized_definition {
            Some(DefinitionTarget::Local(target)) => {
                Some(definition_label(&graph.definitions, target))
            }
            _ => None,
        })
        .filter(|label| is_const_fixture_materialization(label))
        .collect::<Vec<_>>();
    actual.sort();
    let inline = format!(
        "from_inline_const::InlineConst@{}",
        marker_range_nth(
            CONST_FIXTURE,
            "const { <T as Table<A, K>>::FUNCTIONS[0] }",
            0
        )
        .start
            + 6
    );
    let two_sites = format!(
        "from_two_sites::InlineConst@{}",
        marker_range_nth(CONST_FIXTURE, "const {\n        (", 0).start + 6
    );
    let default_make = format!(
        "{}::make",
        anonymous_definition(CONST_FIXTURE, "impl Table<u16, 3> for Defaulted")
    );
    let override_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u32, 5> for Overridden");
    let multi_make = format!(
        "{}::make",
        anonymous_definition(CONST_FIXTURE, "impl Table<u8, 2> for MultiSite")
    );
    let tracked_call = format!(
        "{}::call",
        anonymous_definition(CONST_FIXTURE, "impl Tracked for TrackedImpl")
    );
    let mut expected = vec![
        "Table::FUNCTIONS".to_owned(),
        "Table::FUNCTIONS".to_owned(),
        "Tracked::FUNCTION".to_owned(),
        default_make,
        format!("{override_impl}::make"),
        format!("{override_impl}::FUNCTIONS"),
        multi_make,
        "from_inline_const".to_owned(),
        "from_inline_const".to_owned(),
        inline.clone(),
        inline,
        "tracked_pointer".to_owned(),
        format!(
            "tracked_pointer::InlineConst@{}",
            marker_range_nth(CONST_FIXTURE, "const { <T as Tracked>::FUNCTION }", 0).start + 6
        ),
        "from_two_sites".to_owned(),
        two_sites,
        "from_promoted".to_owned(),
        "from_promoted".to_owned(),
        tracked_call.clone(),
        tracked_call,
    ];
    expected.sort();
    assert_eq!(actual, expected);

    let mut materializations = graph
        .edges
        .iter()
        .filter_map(|edge| {
            if edge.kind != DependencyKind::MaterializesDefinition {
                return None;
            }
            let GraphNode::Mono(from) = edge.from else {
                return None;
            };
            let node = &graph.mono_nodes[from.0 as usize];
            let DefinitionTarget::Local(target) = node.materialized_definition? else {
                return None;
            };
            let role = definition_label(&graph.definitions, target);
            is_const_fixture_materialization(&role)
                .then(|| (role, edge.to, edge.sites.clone(), edge.evidence))
        })
        .collect::<Vec<_>>();
    materializations.sort();
    let mut expected_materializations = expected
        .into_iter()
        .map(|role| {
            let target = graph
                .definitions
                .definitions
                .iter()
                .find(|definition| definition_key_label(&definition.key) == role)
                .map(|definition| GraphNode::Definition(definition.id))
                .expect("handwritten local materialization must resolve");
            (role, target, Vec::new(), EvidenceOrigin::Derived)
        })
        .collect::<Vec<_>>();
    expected_materializations.sort();
    assert_eq!(materializations, expected_materializations);
}

fn is_const_fixture_materialization(label: &str) -> bool {
    label == "Table::FUNCTIONS"
        || label == "Tracked::FUNCTION"
        || label.starts_with("from_inline_const")
        || label.starts_with("tracked_pointer")
        || label.starts_with("from_two_sites")
        || label.starts_with("from_promoted")
        || label.starts_with(&anonymous_definition(
            CONST_FIXTURE,
            "impl Table<u16, 3> for Defaulted",
        ))
        || label.starts_with(&anonymous_definition(
            CONST_FIXTURE,
            "impl Table<u32, 5> for Overridden",
        ))
        || label.starts_with(&anonymous_definition(
            CONST_FIXTURE,
            "impl Table<u8, 2> for MultiSite",
        ))
        || label.starts_with(&anonymous_definition(
            CONST_FIXTURE,
            "impl Tracked for TrackedImpl",
        ))
        || label.contains("Unused")
}

fn assert_const_owner_edges(graph: &DependencyGraph) {
    // This projection intentionally excludes direct calls, runtime-only nodes,
    // and allocation-to-allocation traversal covered by the whole-graph test.
    let mut actual = local_mono_edges(graph, CONST_FIXTURE)
        .into_iter()
        .filter(|edge| {
            matches!(
                edge.relation,
                MonoDependencyKind::ConstAllocation | MonoDependencyKind::FunctionPointer
            ) && !edge.from.starts_with("allocation:")
        })
        .collect::<Vec<_>>();
    actual.sort();

    let inline_text = "const { <T as Table<A, K>>::FUNCTIONS[0] }";
    let inline_site = source_site(CONST_FIXTURE, inline_text);
    let inline_node = format!(
        "from_inline_const::InlineConst@{}",
        marker_range_nth(CONST_FIXTURE, inline_text, 0).start + 6
    );
    let inline_allocation = format!("allocation:from_inline_const:{inline_text}");
    let table_use = source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS");
    let override_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u32, 5> for Overridden");

    let tracked_text = "const { <T as Tracked>::FUNCTION }";
    let tracked_site = source_site(CONST_FIXTURE, tracked_text);
    let tracked_node = format!(
        "tracked_pointer::InlineConst@{}",
        marker_range_nth(CONST_FIXTURE, tracked_text, 0).start + 6
    );
    let tracked_allocation = format!("allocation:tracked_pointer:{tracked_text}");

    let multi_text = "const {\n        (\n            <T as Table<A, K>>::FUNCTIONS[0],\n            <T as Table<A, K>>::FUNCTIONS[0],\n        )\n    }";
    let multi_site = source_site(CONST_FIXTURE, multi_text);
    let multi_node = format!(
        "from_two_sites::InlineConst@{}",
        marker_range_nth(CONST_FIXTURE, multi_text, 0).start + 6
    );
    let multi_allocation = format!("allocation:from_two_sites:{multi_text}");
    let multi_uses = source_sites_after(
        CONST_FIXTURE,
        "const {\n        (",
        "<T as Table<A, K>>::FUNCTIONS",
    );

    let promoted_text = "&[(<T as Table<A, K>>::make, std::mem::size_of::<u8>())]";
    let promoted_site = source_site(CONST_FIXTURE, promoted_text);
    let promoted_allocation = format!("allocation:from_promoted:{promoted_text}");
    let default_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u16, 3> for Defaulted");
    let multi_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u8, 2> for MultiSite");
    let tracked_impl = anonymous_definition(CONST_FIXTURE, "impl Tracked for TrackedImpl");

    let mut expected = Vec::new();
    for _ in 0..2 {
        expected.push(mono_use_with_evidence(
            "from_inline_const",
            Some(&inline_node),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![inline_site.clone()],
            EvidenceOrigin::Derived,
        ));
        expected.push(mono_use(
            "from_inline_const",
            Some(&inline_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![inline_site.clone()],
        ));
        expected.push(mono_use(
            "from_inline_const",
            Some(&inline_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![inline_site.clone()],
        ));
    }
    expected.extend([
        mono_use_with_evidence(
            &inline_node,
            Some("Table::FUNCTIONS"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![table_use.clone()],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            &inline_node,
            Some(&format!("{override_impl}::FUNCTIONS")),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![table_use],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "tracked_pointer",
            Some(&tracked_node),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![tracked_site.clone()],
            EvidenceOrigin::Derived,
        ),
        mono_use(
            "tracked_pointer",
            Some(&tracked_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![tracked_site.clone()],
        ),
        mono_use(
            "tracked_pointer",
            Some(&tracked_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![tracked_site],
        ),
        mono_use_with_evidence(
            &tracked_node,
            Some("Tracked::FUNCTION"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![source_site(CONST_FIXTURE, "<T as Tracked>::FUNCTION")],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "from_two_sites",
            Some(&multi_node),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![multi_site.clone()],
            EvidenceOrigin::Derived,
        ),
        mono_use(
            "from_two_sites",
            Some(&multi_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![multi_site.clone()],
        ),
        mono_use(
            "from_two_sites",
            Some(&multi_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![multi_site],
        ),
        mono_use_with_evidence(
            &multi_node,
            Some("Table::FUNCTIONS"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            multi_uses,
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "from_promoted",
            Some("from_promoted"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![promoted_site.clone()],
            EvidenceOrigin::Derived,
        ),
        mono_use(
            "from_promoted",
            Some(&promoted_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![promoted_site.clone()],
        ),
        mono_use(
            "from_promoted",
            Some(&promoted_allocation),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![promoted_site],
        ),
        mono_use_with_evidence(
            "from_promoted",
            Some(&format!("{default_impl}::make")),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::make")],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "Table::FUNCTIONS",
            Some(&format!("{default_impl}::make")),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "Self::make")],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "Table::FUNCTIONS",
            Some(&format!("{multi_impl}::make")),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "Self::make")],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            &format!("{override_impl}::FUNCTIONS"),
            Some(&format!("{override_impl}::make")),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<Self as Table<u32, 5>>::make")],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "Tracked::FUNCTION",
            Some(&format!("{tracked_impl}::call")),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "Self::call")],
            EvidenceOrigin::Derived,
        ),
    ]);
    expected.sort();
    assert_eq!(actual, expected);
}

fn assert_const_selection_edges(graph: &DependencyGraph) {
    let default_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u16, 3> for Defaulted");
    let override_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u32, 5> for Overridden");
    let multi_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u8, 2> for MultiSite");
    let tracked_impl = anonymous_definition(CONST_FIXTURE, "impl Tracked for TrackedImpl");

    let mut projected = local_selection_edges(graph, CONST_FIXTURE)
        .into_iter()
        .filter(|edge| {
            matches!(
                edge.relation,
                MonoDependencyKind::ConstAllocation | MonoDependencyKind::FunctionPointer
            )
        })
        .collect::<Vec<_>>();
    projected.sort();
    let meta_sized = || {
        obligation_proof(vec![(
            ProofRelationKind::TraitDefinition,
            0,
            "std::marker::MetaSized",
        )])
    };
    let function_sites = |marker: &str| vec![source_site(CONST_FIXTURE, marker)];
    let mut expected = vec![
        proof_use(
            "Table::FUNCTIONS",
            associated_proof(
                "Table::FUNCTIONS",
                "Table",
                &default_impl,
                &[&default_impl, "Table"],
            ),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        ),
        proof_use(
            "Table::FUNCTIONS",
            meta_sized(),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        ),
        proof_use(
            &format!("{override_impl}::FUNCTIONS"),
            associated_proof(
                &format!("{override_impl}::FUNCTIONS"),
                &override_impl,
                &override_impl,
                &[&override_impl, "Table"],
            ),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        ),
        proof_use(
            &format!("{override_impl}::FUNCTIONS"),
            meta_sized(),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        ),
        proof_use(
            "Table::FUNCTIONS",
            associated_proof(
                "Table::FUNCTIONS",
                "Table",
                &multi_impl,
                &[&multi_impl, "Table"],
            ),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            source_sites_after(
                CONST_FIXTURE,
                "const {\n        (",
                "<T as Table<A, K>>::FUNCTIONS",
            ),
        ),
        proof_use(
            "Table::FUNCTIONS",
            meta_sized(),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            source_sites_after(
                CONST_FIXTURE,
                "const {\n        (",
                "<T as Table<A, K>>::FUNCTIONS",
            ),
        ),
        proof_use(
            "Tracked::FUNCTION",
            associated_proof(
                "Tracked::FUNCTION",
                "Tracked",
                &tracked_impl,
                &[&tracked_impl, "Tracked"],
            ),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Tracked>::FUNCTION")],
        ),
        proof_use(
            "Tracked::FUNCTION",
            meta_sized(),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Tracked>::FUNCTION")],
        ),
        proof_use(
            "from_promoted",
            associated_proof(
                &format!("{default_impl}::make"),
                &default_impl,
                &default_impl,
                &[&default_impl, "Table"],
            ),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::make")],
        ),
        proof_use(
            "from_promoted",
            meta_sized(),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::make")],
        ),
        proof_use(
            "Table::FUNCTIONS",
            associated_proof(
                &format!("{default_impl}::make"),
                &default_impl,
                &default_impl,
                &[&default_impl, "Table"],
            ),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::make"),
        ),
        proof_use(
            "Table::FUNCTIONS",
            meta_sized(),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::make"),
        ),
        proof_use(
            "Table::FUNCTIONS",
            associated_proof(
                &format!("{multi_impl}::make"),
                &multi_impl,
                &multi_impl,
                &[&multi_impl, "Table"],
            ),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::make"),
        ),
        proof_use(
            "Table::FUNCTIONS",
            meta_sized(),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::make"),
        ),
        proof_use(
            &format!("{override_impl}::FUNCTIONS"),
            associated_proof(
                &format!("{override_impl}::make"),
                &override_impl,
                &override_impl,
                &[&override_impl, "Table"],
            ),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("<Self as Table<u32, 5>>::make"),
        ),
        proof_use(
            &format!("{override_impl}::FUNCTIONS"),
            meta_sized(),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("<Self as Table<u32, 5>>::make"),
        ),
        proof_use(
            "Tracked::FUNCTION",
            associated_proof(
                &format!("{tracked_impl}::call"),
                &tracked_impl,
                &tracked_impl,
                &[&tracked_impl, "Tracked"],
            ),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::call"),
        ),
        proof_use(
            "Tracked::FUNCTION",
            meta_sized(),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            function_sites("Self::call"),
        ),
    ];
    expected.sort();
    assert_eq!(projected, expected);
}

fn assert_const_instance_and_proof_joins(graph: &DependencyGraph) {
    let mut local_const_pairs = Vec::new();
    for edge in &graph.edges {
        if edge.kind
            != (DependencyKind::Mono {
                relation: MonoDependencyKind::ConstAllocation,
                collection: MonoCollection::Used,
            })
            || edge.evidence != EvidenceOrigin::Derived
            || !edge
                .sites
                .iter()
                .any(|site| matches!(site, ObservationSite::Source(_)))
        {
            continue;
        }
        let (GraphNode::Mono(from), GraphNode::Mono(to)) = (edge.from, edge.to) else {
            continue;
        };
        let Some(from_label) = local_semantic_node_label(graph, from, CONST_FIXTURE) else {
            continue;
        };
        let Some(to_label) = local_semantic_node_label(graph, to, CONST_FIXTURE) else {
            continue;
        };
        local_const_pairs.push((from, to, from_label, to_label));
    }
    assert_eq!(local_const_pairs.len(), 9);
    for (index, (from, to, from_label, to_label)) in local_const_pairs.iter().enumerate() {
        for (other_from, other_to, other_from_label, other_to_label) in
            &local_const_pairs[index + 1..]
        {
            if instance_key(graph, *from).0 != instance_key(graph, *other_from).0
                || instance_key(graph, *to).0 != instance_key(graph, *other_to).0
            {
                continue;
            }
            assert_eq!(
                instance_key(graph, *from).1 == instance_key(graph, *other_from).1,
                instance_key(graph, *to).1 == instance_key(graph, *other_to).1,
                "owner and const-body argument partitions disagree for {from_label} -> {to_label} and {other_from_label} -> {other_to_label}"
            );
        }
    }

    let inline_owners = instance_ids(graph, "from_inline_const");
    assert_eq!(inline_owners.len(), 2);
    assert_ne!(
        instance_key(graph, inline_owners[0]).1,
        instance_key(graph, inline_owners[1]).1
    );
    let table_consts = instance_ids(graph, "Table::FUNCTIONS");
    assert_eq!(table_consts.len(), 2);
    assert_ne!(
        instance_key(graph, table_consts[0]).1,
        instance_key(graph, table_consts[1]).1
    );

    let promoted = graph
        .edges
        .iter()
        .find_map(|edge| {
            if edge.kind
                != (DependencyKind::Mono {
                    relation: MonoDependencyKind::ConstAllocation,
                    collection: MonoCollection::Used,
                })
                || edge.evidence != EvidenceOrigin::Derived
            {
                return None;
            }
            let (GraphNode::Mono(from), GraphNode::Mono(to)) = (edge.from, edge.to) else {
                return None;
            };
            (local_semantic_node_label(graph, from, CONST_FIXTURE).as_deref()
                == Some("from_promoted")
                && local_semantic_node_label(graph, to, CONST_FIXTURE).as_deref()
                    == Some("from_promoted"))
            .then_some((from, to))
        })
        .expect("the callable must reach its promoted body");
    assert_promoted_body_role(graph, promoted.0, promoted.1);

    let tracked_call = format!(
        "{}::call",
        anonymous_definition(CONST_FIXTURE, "impl Tracked for TrackedImpl")
    );
    let tracked = instance_ids(graph, &tracked_call);
    assert_eq!(tracked.len(), 2);
    assert_same_arguments_different_kinds(graph, tracked[0], tracked[1]);

    let mut associated_ids = Vec::new();
    for edge in &graph.edges {
        let DependencyKind::SelectionProof {
            relation,
            collection: MonoCollection::Mentioned,
        } = edge.kind
        else {
            continue;
        };
        if !matches!(
            relation,
            MonoDependencyKind::ConstAllocation | MonoDependencyKind::FunctionPointer
        ) || edge.evidence != EvidenceOrigin::Derived
        {
            continue;
        }
        let (GraphNode::Mono(from), GraphNode::Proof(proof)) = (edge.from, edge.to) else {
            continue;
        };
        if local_semantic_node_label(graph, from, CONST_FIXTURE).is_none() {
            continue;
        }
        let ProofNodeKind::AssociatedItem {
            raw_instance,
            codegen_instance,
            selection,
            source_kind,
            leaf: Some(leaf),
            finalizing_node: Some(finalizing),
            ..
        } = &graph.proofs[proof.0 as usize].kind
        else {
            continue;
        };
        assert_eq!(*source_kind, SelectionSourceKind::UserDefined);

        let matching = graph
            .edges
            .iter()
            .filter(|mono| {
                mono.kind
                    == (DependencyKind::Mono {
                        relation,
                        collection: if relation == MonoDependencyKind::ConstAllocation {
                            MonoCollection::Used
                        } else {
                            MonoCollection::Mentioned
                        },
                    })
                    && mono.evidence == EvidenceOrigin::Derived
                    && mono.sites == edge.sites
                    && if relation == MonoDependencyKind::ConstAllocation {
                        mono.to == GraphNode::Mono(from)
                    } else {
                        mono.from == GraphNode::Mono(from)
                    }
            })
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1);
        let endpoint = if relation == MonoDependencyKind::ConstAllocation {
            from
        } else {
            let GraphNode::Mono(target) = matching[0].to else {
                unreachable!()
            };
            target
        };
        assert_eq!(
            graph.mono_nodes[endpoint.0 as usize].materialized_definition,
            Some(*leaf)
        );

        let is_track_caller = target_label(&graph.definitions, *leaf).ends_with("::call");
        assert_eq!(raw_instance == codegen_instance, !is_track_caller);
        assert_eq!(
            graph
                .edges
                .iter()
                .filter(|relation| {
                    relation.from == GraphNode::Proof(proof)
                        && relation.to == GraphNode::Proof(*selection)
                        && relation.kind
                            == (DependencyKind::ProofRelation {
                                relation: ProofRelationKind::AssociatedSelection,
                                ordinal: 0,
                            })
                })
                .count(),
            1
        );
        let ProofNodeKind::Obligation {
            source: Some(source),
            ..
        } = &graph.proofs[selection.0 as usize].kind
        else {
            panic!("associated selection must resolve to a typed obligation")
        };
        assert_eq!(source.kind, SelectionSourceKind::UserDefined);
        assert_eq!(source.implementation, Some(finalizing.target));
        associated_ids.push((proof, edge.sites.clone()));
    }
    assert_eq!(associated_ids.len(), 9);
    assert_eq!(
        associated_ids
            .iter()
            .filter(|(_, sites)| sites.len() == 2)
            .count(),
        1
    );
    associated_ids.sort_by_key(|(id, _)| *id);
    associated_ids.dedup_by_key(|(id, _)| *id);
    assert_eq!(associated_ids.len(), 8);
}

fn assert_const_call_chains(graph: &DependencyGraph) {
    let main = only_instance(graph, "main");
    let default_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u16, 3> for Defaulted");
    let override_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u32, 5> for Overridden");
    let multi_impl = anonymous_definition(CONST_FIXTURE, "impl Table<u8, 2> for MultiSite");
    let tracked_impl = anonymous_definition(CONST_FIXTURE, "impl Tracked for TrackedImpl");

    let inline_text = "const { <T as Table<A, K>>::FUNCTIONS[0] }";
    let inline_label = format!(
        "from_inline_const::InlineConst@{}",
        marker_range_nth(CONST_FIXTURE, inline_text, 0).start + 6
    );
    let table_site = vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")];
    let default_owner = mono_step(
        graph,
        main,
        MonoDependencyKind::DirectCall,
        MonoCollection::Used,
        vec![source_site(
            CONST_FIXTURE,
            "from_inline_const::<Defaulted, u16, 3>()",
        )],
        EvidenceOrigin::PatchedObserver,
        "from_inline_const",
    );
    let default_inline = mono_step(
        graph,
        default_owner,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, inline_text)],
        EvidenceOrigin::Derived,
        &inline_label,
    );
    assert_instance_role(graph, default_owner, MonoInstanceRole::Callable);
    assert_instance_role(
        graph,
        default_inline,
        MonoInstanceRole::Const { promoted: None },
    );
    let default_const = mono_step(
        graph,
        default_inline,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        table_site.clone(),
        EvidenceOrigin::Derived,
        "Table::FUNCTIONS",
    );
    let default_const_proof = associated_proof_step(
        graph,
        default_const,
        default_const,
        MonoDependencyKind::ConstAllocation,
        table_site,
        "Table::FUNCTIONS",
        &default_impl,
        true,
    );
    let default_function = mono_step(
        graph,
        default_const,
        MonoDependencyKind::FunctionPointer,
        MonoCollection::Mentioned,
        vec![source_site(CONST_FIXTURE, "Self::make")],
        EvidenceOrigin::Derived,
        &format!("{default_impl}::make"),
    );
    associated_proof_step(
        graph,
        default_const,
        default_function,
        MonoDependencyKind::FunctionPointer,
        vec![source_site(CONST_FIXTURE, "Self::make")],
        &format!("{default_impl}::make"),
        &default_impl,
        true,
    );

    let override_owner = mono_step(
        graph,
        main,
        MonoDependencyKind::DirectCall,
        MonoCollection::Used,
        vec![source_site(
            CONST_FIXTURE,
            "from_inline_const::<Overridden, u32, 5>()",
        )],
        EvidenceOrigin::PatchedObserver,
        "from_inline_const",
    );
    let override_inline = mono_step(
        graph,
        override_owner,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, inline_text)],
        EvidenceOrigin::Derived,
        &inline_label,
    );
    let override_const_label = format!("{override_impl}::FUNCTIONS");
    assert_instance_role(graph, override_owner, MonoInstanceRole::Callable);
    assert_instance_role(
        graph,
        override_inline,
        MonoInstanceRole::Const { promoted: None },
    );
    let override_const = mono_step(
        graph,
        override_inline,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        EvidenceOrigin::Derived,
        &override_const_label,
    );
    let override_const_proof = associated_proof_step(
        graph,
        override_const,
        override_const,
        MonoDependencyKind::ConstAllocation,
        vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::FUNCTIONS")],
        &override_const_label,
        &override_impl,
        true,
    );
    let override_function = mono_step(
        graph,
        override_const,
        MonoDependencyKind::FunctionPointer,
        MonoCollection::Mentioned,
        vec![source_site(CONST_FIXTURE, "<Self as Table<u32, 5>>::make")],
        EvidenceOrigin::Derived,
        &format!("{override_impl}::make"),
    );
    associated_proof_step(
        graph,
        override_const,
        override_function,
        MonoDependencyKind::FunctionPointer,
        vec![source_site(CONST_FIXTURE, "<Self as Table<u32, 5>>::make")],
        &format!("{override_impl}::make"),
        &override_impl,
        true,
    );
    assert_ne!(default_owner, override_owner);
    assert_ne!(default_inline, override_inline);
    assert_ne!(default_const, override_const);
    assert_ne!(default_const_proof, override_const_proof);

    let multi_owner = mono_step(
        graph,
        main,
        MonoDependencyKind::DirectCall,
        MonoCollection::Used,
        vec![source_site(
            CONST_FIXTURE,
            "from_two_sites::<MultiSite, u8, 2>()",
        )],
        EvidenceOrigin::PatchedObserver,
        "from_two_sites",
    );
    let multi_text = "const {\n        (\n            <T as Table<A, K>>::FUNCTIONS[0],\n            <T as Table<A, K>>::FUNCTIONS[0],\n        )\n    }";
    let multi_inline = mono_step(
        graph,
        multi_owner,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, multi_text)],
        EvidenceOrigin::Derived,
        &format!(
            "from_two_sites::InlineConst@{}",
            marker_range_nth(CONST_FIXTURE, multi_text, 0).start + 6
        ),
    );
    let multi_sites = source_sites_after(
        CONST_FIXTURE,
        "const {\n        (",
        "<T as Table<A, K>>::FUNCTIONS",
    );
    assert_instance_role(graph, multi_owner, MonoInstanceRole::Callable);
    assert_instance_role(
        graph,
        multi_inline,
        MonoInstanceRole::Const { promoted: None },
    );
    let multi_const = mono_step(
        graph,
        multi_inline,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        multi_sites.clone(),
        EvidenceOrigin::Derived,
        "Table::FUNCTIONS",
    );
    associated_proof_step(
        graph,
        multi_const,
        multi_const,
        MonoDependencyKind::ConstAllocation,
        multi_sites,
        "Table::FUNCTIONS",
        &multi_impl,
        true,
    );
    let multi_function = mono_step(
        graph,
        multi_const,
        MonoDependencyKind::FunctionPointer,
        MonoCollection::Mentioned,
        vec![source_site(CONST_FIXTURE, "Self::make")],
        EvidenceOrigin::Derived,
        &format!("{multi_impl}::make"),
    );
    associated_proof_step(
        graph,
        multi_const,
        multi_function,
        MonoDependencyKind::FunctionPointer,
        vec![source_site(CONST_FIXTURE, "Self::make")],
        &format!("{multi_impl}::make"),
        &multi_impl,
        true,
    );
    assert_ne!(default_const, multi_const);

    let tracked_owner = mono_step(
        graph,
        main,
        MonoDependencyKind::DirectCall,
        MonoCollection::Used,
        vec![source_site(
            CONST_FIXTURE,
            "tracked_pointer::<TrackedImpl>()",
        )],
        EvidenceOrigin::PatchedObserver,
        "tracked_pointer",
    );
    let tracked_text = "const { <T as Tracked>::FUNCTION }";
    let tracked_inline = mono_step(
        graph,
        tracked_owner,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, tracked_text)],
        EvidenceOrigin::Derived,
        &format!(
            "tracked_pointer::InlineConst@{}",
            marker_range_nth(CONST_FIXTURE, tracked_text, 0).start + 6
        ),
    );
    let tracked_const = mono_step(
        graph,
        tracked_inline,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, "<T as Tracked>::FUNCTION")],
        EvidenceOrigin::Derived,
        "Tracked::FUNCTION",
    );
    assert_instance_role(graph, tracked_owner, MonoInstanceRole::Callable);
    assert_instance_role(
        graph,
        tracked_inline,
        MonoInstanceRole::Const { promoted: None },
    );
    associated_proof_step(
        graph,
        tracked_const,
        tracked_const,
        MonoDependencyKind::ConstAllocation,
        vec![source_site(CONST_FIXTURE, "<T as Tracked>::FUNCTION")],
        "Tracked::FUNCTION",
        &tracked_impl,
        true,
    );
    let tracked_function = mono_step(
        graph,
        tracked_const,
        MonoDependencyKind::FunctionPointer,
        MonoCollection::Mentioned,
        vec![source_site(CONST_FIXTURE, "Self::call")],
        EvidenceOrigin::Derived,
        &format!("{tracked_impl}::call"),
    );
    associated_proof_step(
        graph,
        tracked_const,
        tracked_function,
        MonoDependencyKind::FunctionPointer,
        vec![source_site(CONST_FIXTURE, "Self::call")],
        &format!("{tracked_impl}::call"),
        &tracked_impl,
        false,
    );

    let promoted_owner = mono_step(
        graph,
        main,
        MonoDependencyKind::DirectCall,
        MonoCollection::Used,
        vec![source_site(
            CONST_FIXTURE,
            "from_promoted::<Defaulted, u16, 3>()",
        )],
        EvidenceOrigin::PatchedObserver,
        "from_promoted",
    );
    let promoted_text = "&[(<T as Table<A, K>>::make, std::mem::size_of::<u8>())]";
    let promoted_body = mono_step(
        graph,
        promoted_owner,
        MonoDependencyKind::ConstAllocation,
        MonoCollection::Used,
        vec![source_site(CONST_FIXTURE, promoted_text)],
        EvidenceOrigin::Derived,
        "from_promoted",
    );
    assert_promoted_body_role(graph, promoted_owner, promoted_body);
    let promoted_function = mono_step(
        graph,
        promoted_body,
        MonoDependencyKind::FunctionPointer,
        MonoCollection::Mentioned,
        vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::make")],
        EvidenceOrigin::Derived,
        &format!("{default_impl}::make"),
    );
    associated_proof_step(
        graph,
        promoted_body,
        promoted_function,
        MonoDependencyKind::FunctionPointer,
        vec![source_site(CONST_FIXTURE, "<T as Table<A, K>>::make")],
        &format!("{default_impl}::make"),
        &default_impl,
        true,
    );
}

fn only_instance(graph: &DependencyGraph, label: &str) -> MonoId {
    let instances = instance_ids(graph, label);
    assert_eq!(instances.len(), 1, "expected one instance for {label}");
    instances[0]
}

fn assert_instance_role(graph: &DependencyGraph, id: MonoId, expected: MonoInstanceRole) {
    assert_eq!(*mono_instance(graph, id).1, expected);
}

fn mono_step(
    graph: &DependencyGraph,
    from: MonoId,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
    evidence: EvidenceOrigin,
    expected_target: &str,
) -> MonoId {
    let targets = graph
        .edges
        .iter()
        .filter_map(|edge| {
            (edge.from == GraphNode::Mono(from)
                && edge.kind
                    == (DependencyKind::Mono {
                        relation,
                        collection,
                    })
                && edge.sites == sites
                && edge.evidence == evidence)
                .then_some(edge.to)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        targets.len(),
        1,
        "expected one {relation:?} edge to {expected_target}"
    );
    let GraphNode::Mono(target) = targets[0] else {
        panic!("mono dependency must target a mono node")
    };
    assert_eq!(
        graph.mono_nodes[target.0 as usize]
            .materialized_definition
            .map(|definition| target_label(&graph.definitions, definition))
            .as_deref(),
        Some(expected_target)
    );
    target
}

fn associated_proof_step(
    graph: &DependencyGraph,
    from: MonoId,
    codegen_target: MonoId,
    relation: MonoDependencyKind,
    sites: Vec<ObservationSite>,
    expected_leaf: &str,
    expected_finalizing: &str,
    raw_equals_codegen: bool,
) -> ProofId {
    let proofs = graph
        .edges
        .iter()
        .filter_map(|edge| {
            if edge.from != GraphNode::Mono(from)
                || edge.kind
                    != (DependencyKind::SelectionProof {
                        relation,
                        collection: MonoCollection::Mentioned,
                    })
                || edge.sites != sites
                || edge.evidence != EvidenceOrigin::Derived
            {
                return None;
            }
            let GraphNode::Proof(proof) = edge.to else {
                panic!("selection dependency must target a proof node")
            };
            matches!(
                graph.proofs[proof.0 as usize].kind,
                ProofNodeKind::AssociatedItem { .. }
            )
            .then_some(proof)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        proofs.len(),
        1,
        "expected one {relation:?} associated proof for {expected_leaf}"
    );
    let proof = proofs[0];
    let ProofNodeKind::AssociatedItem {
        raw_instance,
        codegen_instance,
        selection,
        source_kind,
        leaf: Some(leaf),
        finalizing_node: Some(finalizing),
        ..
    } = &graph.proofs[proof.0 as usize].kind
    else {
        unreachable!()
    };
    assert_eq!(*source_kind, SelectionSourceKind::UserDefined);
    assert_eq!(target_label(&graph.definitions, *leaf), expected_leaf);
    assert_eq!(
        target_label(&graph.definitions, finalizing.target),
        expected_finalizing
    );
    assert_eq!(raw_instance == codegen_instance, raw_equals_codegen);
    if !raw_equals_codegen {
        assert_eq!(raw_instance.definition, codegen_instance.definition);
        assert_eq!(raw_instance.arguments, codegen_instance.arguments);
        assert_ne!(raw_instance.kind, codegen_instance.kind);
    }
    let (target_instance, target_role) = mono_instance(graph, codegen_target);
    assert_eq!(codegen_instance, target_instance);
    assert_eq!(
        *target_role,
        if relation == MonoDependencyKind::ConstAllocation {
            MonoInstanceRole::Const { promoted: None }
        } else {
            MonoInstanceRole::Callable
        }
    );
    assert_eq!(
        graph.mono_nodes[codegen_target.0 as usize].materialized_definition,
        Some(*leaf)
    );
    assert_eq!(
        graph
            .edges
            .iter()
            .filter(|edge| {
                edge.from == GraphNode::Proof(proof)
                    && edge.to == GraphNode::Proof(*selection)
                    && edge.kind
                        == (DependencyKind::ProofRelation {
                            relation: ProofRelationKind::AssociatedSelection,
                            ordinal: 0,
                        })
            })
            .count(),
        1
    );
    let ProofNodeKind::Obligation {
        source: Some(source),
        ..
    } = &graph.proofs[selection.0 as usize].kind
    else {
        panic!("associated selection must resolve to a typed obligation")
    };
    assert_eq!(source.kind, SelectionSourceKind::UserDefined);
    assert_eq!(source.implementation, Some(finalizing.target));
    proof
}

fn instance_ids(graph: &DependencyGraph, label: &str) -> Vec<MonoId> {
    graph
        .mono_nodes
        .iter()
        .filter_map(|node| {
            (node
                .materialized_definition
                .is_some_and(|target| target_label(&graph.definitions, target) == label))
            .then_some(node.id)
        })
        .collect()
}

fn instance_key(
    graph: &DependencyGraph,
    id: MonoId,
) -> (
    &DefinitionReferenceKey,
    &CanonicalCompilerTerm,
    &CanonicalCompilerTerm,
) {
    let (instance, _) = mono_instance(graph, id);
    (&instance.definition, &instance.arguments, &instance.kind)
}

fn mono_instance(graph: &DependencyGraph, id: MonoId) -> (&MonoInstanceKey, &MonoInstanceRole) {
    let MonoKey::Instance { instance, role } = &graph.mono_nodes[id.0 as usize].key else {
        panic!("const relations must connect instance nodes")
    };
    (instance, role)
}

fn assert_same_arguments_different_kinds(graph: &DependencyGraph, left: MonoId, right: MonoId) {
    let (left_definition, left_arguments, left_kind) = instance_key(graph, left);
    let (right_definition, right_arguments, right_kind) = instance_key(graph, right);
    assert_eq!(left_definition, right_definition);
    assert_eq!(left_arguments, right_arguments);
    assert_ne!(left_kind, right_kind);
}

fn assert_promoted_body_role(graph: &DependencyGraph, callable: MonoId, promoted: MonoId) {
    let (callable_instance, callable_role) = mono_instance(graph, callable);
    let (promoted_instance, promoted_role) = mono_instance(graph, promoted);
    assert_eq!(callable_instance, promoted_instance);
    assert_eq!(*callable_role, MonoInstanceRole::Callable);
    assert_eq!(
        *promoted_role,
        MonoInstanceRole::Const { promoted: Some(0) }
    );
}

fn assert_roots_and_nodes(graph: &DependencyGraph) {
    let mut node_counts = BTreeMap::new();
    for node in &graph.mono_nodes {
        let kind = match &node.key {
            MonoKey::Instance { .. } => "instance",
            MonoKey::Static { .. } => "static",
            MonoKey::GlobalAsm { .. } => "global-asm",
            MonoKey::VTable { .. } => "vtable",
            MonoKey::Allocation(_) => "allocation",
        };
        *node_counts.entry(kind).or_insert(0usize) += 1;
    }
    assert_eq!(
        node_counts,
        BTreeMap::from([
            ("allocation", 4),
            ("instance", 35),
            ("static", 1),
            ("vtable", 2),
        ])
    );

    let (main_instance, main_definition) = main_nodes(graph);
    let main = &graph.mono_nodes[main_instance.0 as usize];
    assert_eq!(
        main.materialized_definition
            .map(|target| target_label(&graph.definitions, target)),
        Some("main".to_owned())
    );
    assert_eq!(
        graph
            .edges
            .iter()
            .filter(|edge| {
                edge.from == GraphNode::Mono(main_instance)
                    && edge.to == GraphNode::Definition(main_definition)
                    && edge.kind == DependencyKind::MaterializesDefinition
            })
            .count(),
        1
    );

    let mut roots = graph
        .roots
        .iter()
        .filter(|root| !root.reason.is_semantic())
        .map(|root| {
            let GraphNode::Mono(node) = root.node else {
                panic!("compiler-required roots must be monomorphic")
            };
            let node = &graph.mono_nodes[node.0 as usize];
            (
                root.reason,
                node.materialized_definition
                    .map(|target| target_label(&graph.definitions, target))
                    .expect("compiler-required roots must materialize definitions"),
            )
        })
        .collect::<Vec<_>>();
    roots.sort();
    assert_eq!(
        roots,
        vec![
            (RootReason::StartInstance, "std::rt::lang_start".to_owned()),
            (RootReason::UsedAttribute, "KEEP".to_owned()),
        ]
    );

    let mut local_materializations = graph
        .mono_nodes
        .iter()
        .filter_map(|node| match node.materialized_definition {
            Some(DefinitionTarget::Local(id)) => Some(definition_label(&graph.definitions, id)),
            _ => None,
        })
        .collect::<Vec<_>>();
    local_materializations.sort();
    let mut expected = vec![
        "concrete".to_owned(),
        "concrete".to_owned(),
        "from_const".to_owned(),
        "kept_first".to_owned(),
        "kept_second".to_owned(),
        "mentioned_call".to_owned(),
        "mentioned_pointer".to_owned(),
        "dependencies".to_owned(),
        "main".to_owned(),
        "Parent::inherited".to_owned(),
        "Dispatch::invoke".to_owned(),
        "TABLE".to_owned(),
        format!(
            "{}::drop",
            anonymous_definition(FIXTURE, "impl Drop for Value")
        ),
        format!(
            "{}::selected",
            anonymous_definition(FIXTURE, "impl Object for Value")
        ),
        format!(
            "{}::invoke",
            anonymous_definition(FIXTURE, "impl Dispatch<u32> for Overridden")
        ),
        "KEEP".to_owned(),
    ];
    expected.sort();
    assert_eq!(local_materializations, expected);
    assert!(!local_materializations.iter().any(|name| name == "unseeded"));
    assert!(!local_materializations.iter().any(|name| name == "ORDINARY"));
}

fn assert_allocations(graph: &DependencyGraph) {
    let mut actual = graph
        .mono_nodes
        .iter()
        .filter_map(|node| {
            let MonoKey::Allocation(allocation) = &node.key else {
                return None;
            };
            Some(AllocationRef {
                root: allocation_root_label(graph, &allocation.root),
                path: allocation
                    .path
                    .iter()
                    .map(|part| {
                        (
                            part.relation,
                            part.collection,
                            allocation_site_label(FIXTURE, part.site),
                            part.same_role_ordinal,
                        )
                    })
                    .collect(),
                descriptor: match node
                    .allocation_observation
                    .as_ref()
                    .expect("allocation nodes must retain an observed descriptor")
                {
                    AllocationDescriptor::Memory => "memory",
                    AllocationDescriptor::Function { .. } => "function",
                    AllocationDescriptor::Static { .. } => "static",
                    AllocationDescriptor::VTable { .. } => "vtable",
                    AllocationDescriptor::TypeId { .. } => "type-id",
                },
            })
        })
        .collect::<Vec<_>>();
    actual.sort();

    let mut expected = vec![
        AllocationRef {
            root: "dependencies".to_owned(),
            path: vec![(
                MonoDependencyKind::ConstAllocation,
                MonoCollection::Used,
                "TABLE".to_owned(),
                0,
            )],
            descriptor: "memory",
        },
        AllocationRef {
            root: "dependencies".to_owned(),
            path: vec![
                (
                    MonoDependencyKind::ConstAllocation,
                    MonoCollection::Used,
                    "TABLE".to_owned(),
                    0,
                ),
                (
                    MonoDependencyKind::AllocationReference,
                    MonoCollection::Used,
                    "allocation-reference".to_owned(),
                    0,
                ),
            ],
            descriptor: "function",
        },
        AllocationRef {
            root: "KEEP".to_owned(),
            path: vec![(
                MonoDependencyKind::AllocationReference,
                MonoCollection::Used,
                "allocation-reference".to_owned(),
                0,
            )],
            descriptor: "function",
        },
        AllocationRef {
            root: "KEEP".to_owned(),
            path: vec![(
                MonoDependencyKind::AllocationReference,
                MonoCollection::Used,
                "allocation-reference".to_owned(),
                1,
            )],
            descriptor: "function",
        },
    ];
    expected.sort();
    assert_eq!(actual, expected);
}

fn assert_mono_edges(graph: &DependencyGraph) {
    let mut counts = BTreeMap::new();
    for edge in &graph.edges {
        if let DependencyKind::Mono {
            relation,
            collection,
        } = &edge.kind
        {
            *counts.entry((*relation, *collection)).or_insert(0usize) += 1;
        }
    }
    assert_eq!(
        counts,
        BTreeMap::from([
            (
                (
                    MonoDependencyKind::AllocationReference,
                    MonoCollection::Mentioned
                ),
                1
            ),
            (
                (
                    MonoDependencyKind::AllocationReference,
                    MonoCollection::Used
                ),
                3
            ),
            (
                (
                    MonoDependencyKind::ConstAllocation,
                    MonoCollection::Mentioned
                ),
                1
            ),
            (
                (MonoDependencyKind::ConstAllocation, MonoCollection::Used),
                6
            ),
            (
                (MonoDependencyKind::DirectCall, MonoCollection::Mentioned),
                2
            ),
            ((MonoDependencyKind::DirectCall, MonoCollection::Used), 21),
            ((MonoDependencyKind::DropGlue, MonoCollection::Used), 1),
            (
                (
                    MonoDependencyKind::FunctionPointer,
                    MonoCollection::Mentioned
                ),
                2
            ),
            (
                (MonoDependencyKind::FunctionPointer, MonoCollection::Used),
                3
            ),
            (
                (MonoDependencyKind::VTableConstruction, MonoCollection::Used),
                2
            ),
            ((MonoDependencyKind::VTableDrop, MonoCollection::Used), 1),
            ((MonoDependencyKind::VTableMethod, MonoCollection::Used), 4),
        ])
    );

    let mut actual = graph
        .edges
        .iter()
        .filter_map(|edge| {
            let DependencyKind::Mono {
                relation,
                collection,
            } = &edge.kind
            else {
                return None;
            };
            let (GraphNode::Mono(from), GraphNode::Mono(to)) = (edge.from, edge.to) else {
                unreachable!("mono edges must connect mono nodes")
            };
            Some(MonoUseRef {
                from: semantic_node_label(graph, from, FIXTURE)?,
                to: semantic_node_label(graph, to, FIXTURE),
                relation: *relation,
                collection: *collection,
                sites: edge.sites.clone(),
                evidence: edge.evidence,
            })
        })
        .collect::<Vec<_>>();
    actual.sort();

    let object_impl = anonymous_definition(FIXTURE, "impl Object for Value");
    let override_impl = anonymous_definition(FIXTURE, "impl Dispatch<u32> for Overridden");
    let table = "allocation:dependencies:TABLE";
    let table_function = "allocation:dependencies:TABLE/ref0";
    let keep_first = "allocation:KEEP/ref0";
    let keep_second = "allocation:KEEP/ref1";
    let mut expected = vec![
        mono_use(
            "concrete",
            Some("std::mem::size_of"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "std::mem::size_of::<T>()", 0)],
        ),
        mono_use(
            "concrete",
            Some("std::mem::size_of"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "std::mem::size_of::<T>()", 0)],
        ),
        mono_use(
            "concrete",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(
                FIXTURE,
                "std::hint::black_box(std::mem::size_of::<T>())",
            )],
        ),
        mono_use(
            "concrete",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(
                FIXTURE,
                "std::hint::black_box(std::mem::size_of::<T>())",
            )],
        ),
        mono_use(
            "dependencies",
            Some("concrete"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            source_sites(FIXTURE, "concrete::<u8>()"),
        ),
        mono_use(
            "dependencies",
            Some("concrete"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "concrete::<u16>()")],
        ),
        mono_use(
            "dependencies",
            Some("mentioned_call"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Mentioned,
            vec![source_site_nth(FIXTURE, "mentioned_call()", 1)],
        ),
        mono_use(
            "dependencies",
            Some("mentioned_pointer"),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![source_site_nth(FIXTURE, "mentioned_pointer", 1)],
        ),
        mono_use(
            "dependencies",
            Some("Dispatch::invoke"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u16>::invoke(&defaulted)")],
        ),
        mono_use(
            "dependencies",
            Some(&format!("{override_impl}::invoke")),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u32>::invoke(&overridden)")],
        ),
        mono_use(
            "dependencies",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "std::hint::black_box(TABLE)")],
        ),
        mono_use(
            "dependencies",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![
                source_site(
                    FIXTURE,
                    "std::hint::black_box(Dispatch::<u16>::invoke(&defaulted))",
                ),
                source_site(
                    FIXTURE,
                    "std::hint::black_box(Dispatch::<u32>::invoke(&overridden))",
                ),
            ],
        ),
        mono_use(
            "dependencies",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![
                source_site(FIXTURE, "std::hint::black_box(object.inherited())"),
                source_site(FIXTURE, "std::hint::black_box(object.selected())"),
            ],
        ),
        mono_use(
            "dependencies",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "std::hint::black_box(&second)")],
        ),
        mono_use(
            "dependencies",
            Some("std::hint::black_box"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Mentioned,
            vec![source_site(FIXTURE, "std::hint::black_box(pointer)")],
        ),
        mono_use(
            "dependencies",
            Some("std::ptr::drop_glue"),
            MonoDependencyKind::DropGlue,
            MonoCollection::Used,
            vec![
                ObservationSite::Source(ByteRange {
                    start: 1521,
                    end: 1522,
                }),
                ObservationSite::Source(ByteRange {
                    start: 1601,
                    end: 1602,
                }),
            ],
        ),
        mono_use(
            "dependencies",
            Some("vtable:source"),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
        ),
        mono_use(
            "dependencies",
            Some(table),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "TABLE", 1)],
        ),
        mono_use_with_evidence(
            "dependencies",
            Some("TABLE"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "TABLE", 1)],
            EvidenceOrigin::Derived,
        ),
        mono_use(
            "dependencies",
            Some(table),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Mentioned,
            vec![source_site_nth(FIXTURE, "TABLE", 1)],
        ),
        mono_use(
            "main",
            Some("dependencies"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "dependencies()", 1)],
        ),
        mono_use(
            "Dispatch::invoke",
            Some("std::mem::size_of"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site_nth(FIXTURE, "std::mem::size_of::<T>()", 1)],
        ),
        mono_use(
            &format!("{override_impl}::invoke"),
            Some("std::mem::size_of"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "std::mem::size_of::<u32>()")],
        ),
        mono_use(
            "KEEP",
            Some(keep_first),
            MonoDependencyKind::AllocationReference,
            MonoCollection::Used,
            vec![ObservationSite::AllocationOffset(0)],
        ),
        mono_use(
            "KEEP",
            Some(keep_second),
            MonoDependencyKind::AllocationReference,
            MonoCollection::Used,
            vec![ObservationSite::AllocationOffset(8)],
        ),
        mono_use(
            "vtable:source",
            Some("Parent::inherited"),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(3)],
        ),
        mono_use(
            "vtable:source",
            Some(&format!("{object_impl}::selected")),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(4)],
        ),
        mono_use(
            "vtable:source",
            Some("std::ptr::drop_glue"),
            MonoDependencyKind::VTableDrop,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(0)],
        ),
        mono_use(
            table,
            Some(table_function),
            MonoDependencyKind::AllocationReference,
            MonoCollection::Used,
            vec![ObservationSite::AllocationOffset(0)],
        ),
        mono_use(
            table,
            Some(table_function),
            MonoDependencyKind::AllocationReference,
            MonoCollection::Mentioned,
            vec![ObservationSite::AllocationOffset(0)],
        ),
        mono_use(
            table_function,
            Some("from_const"),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Used,
            vec![ObservationSite::CompilerGenerated],
        ),
        mono_use(
            table_function,
            Some("from_const"),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Mentioned,
            vec![ObservationSite::CompilerGenerated],
        ),
        mono_use(
            keep_first,
            Some("kept_first"),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Used,
            vec![ObservationSite::CompilerGenerated],
        ),
        mono_use(
            keep_second,
            Some("kept_second"),
            MonoDependencyKind::FunctionPointer,
            MonoCollection::Used,
            vec![ObservationSite::CompilerGenerated],
        ),
        mono_use_with_evidence(
            "<() as std::process::Termination>::report",
            Some("std::process::ExitCode::SUCCESS"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "std::mem::size_of",
            Some("std::mem::SizedTypeProperties::SIZE"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "std::mem::size_of",
            Some("std::mem::SizedTypeProperties::SIZE"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
            EvidenceOrigin::Derived,
        ),
        mono_use_with_evidence(
            "std::mem::size_of",
            Some("std::mem::SizedTypeProperties::SIZE"),
            MonoDependencyKind::ConstAllocation,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
            EvidenceOrigin::Derived,
        ),
        mono_use(
            "std::ops::FnOnce::call_once",
            Some("std::ops::FnOnce::call_once"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::ops::FnOnce::call_once",
            Some("std::rt::lang_start::{closure#0}"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::ptr::drop_glue",
            Some(&format!(
                "{}::drop",
                anonymous_definition(FIXTURE, "impl Drop for Value")
            )),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::rt::lang_start",
            None,
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::rt::lang_start::{closure#0}",
            Some("<() as std::process::Termination>::report"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::rt::lang_start::{closure#0}",
            Some("std::sys::backtrace::__rust_begin_short_backtrace"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
        mono_use(
            "std::sys::backtrace::__rust_begin_short_backtrace",
            Some("std::ops::FnOnce::call_once"),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![ObservationSite::ExternalSource],
        ),
    ];
    expected.sort();
    assert_eq!(actual, expected);
}

fn assert_proofs(graph: &DependencyGraph) {
    let mut proof_counts = BTreeMap::new();
    for proof in &graph.proofs {
        let kind = match &proof.kind {
            ProofNodeKind::Obligation { .. } => "obligation",
            ProofNodeKind::Projection { .. } => "projection",
            ProofNodeKind::AssociatedItem { .. } => "associated",
            ProofNodeKind::Cycle { .. } => "cycle",
        };
        *proof_counts.entry(kind).or_insert(0usize) += 1;
    }
    assert_eq!(
        proof_counts,
        BTreeMap::from([("associated", 16), ("obligation", 33), ("projection", 3)])
    );

    let mut relation_counts = BTreeMap::new();
    let mut selection_counts = BTreeMap::new();
    let mut materializations = 0usize;
    for edge in &graph.edges {
        match &edge.kind {
            DependencyKind::ProofRelation { relation, .. } => {
                *relation_counts.entry(*relation).or_insert(0usize) += 1;
            }
            DependencyKind::SelectionProof {
                relation,
                collection,
            } => {
                *selection_counts
                    .entry((*relation, *collection))
                    .or_insert(0usize) += 1;
            }
            DependencyKind::MaterializesDefinition => materializations += 1,
            _ => {}
        }
    }
    assert_eq!(materializations, 36);
    assert_eq!(
        selection_counts,
        BTreeMap::from([
            ((MonoDependencyKind::DirectCall, MonoCollection::Used), 13),
            (
                (MonoDependencyKind::VTableConstruction, MonoCollection::Used),
                9
            ),
            ((MonoDependencyKind::VTableMethod, MonoCollection::Used), 7),
            (
                (
                    MonoDependencyKind::ConstAllocation,
                    MonoCollection::Mentioned
                ),
                6
            ),
        ])
    );
    assert_eq!(
        relation_counts,
        BTreeMap::from([
            (ProofRelationKind::AssociatedDefining, 9),
            (ProofRelationKind::AssociatedFinalizing, 9),
            (ProofRelationKind::AssociatedLeaf, 9),
            (ProofRelationKind::AssociatedSelection, 16),
            (ProofRelationKind::AutoTraitProof, 7),
            (ProofRelationKind::FulfillmentNested, 3),
            (ProofRelationKind::ProjectionOwner, 3),
            (ProofRelationKind::ProjectionSelectedTrait, 2),
            (ProofRelationKind::QueryTraceRoot, 27),
            (ProofRelationKind::SelectedImpl, 10),
            (ProofRelationKind::SelectedTraitItem, 1),
            (ProofRelationKind::SpecializationAncestor, 18),
            (ProofRelationKind::TraceFulfillment, 14),
            (ProofRelationKind::TraceObligation, 41),
            (ProofRelationKind::TraceProjection, 3),
            (ProofRelationKind::TraceTraitSelection, 39),
            (ProofRelationKind::TraitDefinition, 15),
            (ProofRelationKind::TraitSelectionNested, 12),
        ])
    );

    assert_eq!(local_proof_targets(graph), expected_local_proof_targets());

    let mut local_selection_uses = graph
        .edges
        .iter()
        .filter_map(|edge| {
            let DependencyKind::SelectionProof {
                relation,
                collection,
            } = &edge.kind
            else {
                return None;
            };
            let GraphNode::Mono(from) = edge.from else {
                unreachable!("selection proof edges must start at mono nodes")
            };
            let GraphNode::Proof(target) = edge.to else {
                unreachable!("selection proof edges must end at proof nodes")
            };
            Some(ProofUseRef {
                from: local_semantic_node_label(graph, from, FIXTURE)?,
                target: proof_ref(graph, target),
                relation: *relation,
                collection: *collection,
                sites: edge.sites.clone(),
                evidence: edge.evidence,
            })
        })
        .collect::<Vec<_>>();
    local_selection_uses.sort();
    let parent_impl = anonymous_definition(FIXTURE, "impl Parent for Value");
    let object_impl = anonymous_definition(FIXTURE, "impl Object for Value");
    let default_impl = anonymous_definition(FIXTURE, "impl Dispatch<u16> for Defaulted");
    let override_impl = anonymous_definition(FIXTURE, "impl Dispatch<u32> for Overridden");
    let mut expected = vec![
        proof_use_with_evidence(
            "dependencies",
            obligation_proof(vec![(ProofRelationKind::SelectedImpl, 0, &object_impl)]),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use(
            "dependencies",
            obligation_proof(vec![(ProofRelationKind::SelectedImpl, 0, &parent_impl)]),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
        ),
        proof_use_with_evidence(
            "dependencies",
            obligation_proof(vec![(
                ProofRelationKind::AutoTraitProof,
                0,
                "std::marker::Send",
            )]),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "dependencies",
            associated_proof(
                "Dispatch::invoke",
                "Dispatch",
                &default_impl,
                &[&default_impl, "Dispatch"],
            ),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u16>::invoke(&defaulted)")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "dependencies",
            associated_proof(
                &format!("{override_impl}::invoke"),
                &override_impl,
                &override_impl,
                &[&override_impl, "Dispatch"],
            ),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u32>::invoke(&overridden)")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "dependencies",
            expected_proof("associated", Vec::new()),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "object.inherited()")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "dependencies",
            expected_proof("associated", Vec::new()),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "object.selected()")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use(
            "dependencies",
            obligation_proof(vec![(
                ProofRelationKind::TraitDefinition,
                0,
                "std::marker::MetaSized",
            )]),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u16>::invoke(&defaulted)")],
        ),
        proof_use(
            "dependencies",
            obligation_proof(vec![(
                ProofRelationKind::TraitDefinition,
                0,
                "std::marker::MetaSized",
            )]),
            MonoDependencyKind::DirectCall,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "Dispatch::<u32>::invoke(&overridden)")],
        ),
        proof_use(
            "dependencies",
            obligation_proof(vec![(
                ProofRelationKind::TraitDefinition,
                0,
                "std::marker::MetaSized",
            )]),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
        ),
        proof_use_with_evidence(
            "dependencies",
            expected_proof(
                "projection",
                vec![
                    (ProofRelationKind::SelectedImpl, 0, &object_impl),
                    (
                        ProofRelationKind::SelectedTraitItem,
                        0,
                        &format!("{object_impl}::Item"),
                    ),
                ],
            ),
            MonoDependencyKind::VTableConstruction,
            MonoCollection::Used,
            vec![source_site(FIXTURE, "&first")],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "vtable:source",
            associated_proof(
                "Parent::inherited",
                "Parent",
                &parent_impl,
                &[&parent_impl, "Parent"],
            ),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(3)],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use_with_evidence(
            "vtable:source",
            associated_proof(
                &format!("{object_impl}::selected"),
                &object_impl,
                &object_impl,
                &[&object_impl, "Object"],
            ),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(4)],
            EvidenceOrigin::PatchedObserver,
        ),
        proof_use(
            "vtable:source",
            obligation_proof(vec![(ProofRelationKind::SelectedImpl, 0, &parent_impl)]),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![ObservationSite::VTableSlot(4)],
        ),
        proof_use(
            "vtable:source",
            obligation_proof(vec![(
                ProofRelationKind::TraitDefinition,
                0,
                "std::marker::MetaSized",
            )]),
            MonoDependencyKind::VTableMethod,
            MonoCollection::Used,
            vec![
                ObservationSite::VTableSlot(3),
                ObservationSite::VTableSlot(4),
            ],
        ),
    ];
    expected.sort();
    assert_eq!(local_selection_uses, expected);
}

fn expected_local_proof_targets() -> BTreeMap<(ProofRelationKind, String), usize> {
    let drop_impl = anonymous_definition(FIXTURE, "impl Drop for Value");
    let parent_impl = anonymous_definition(FIXTURE, "impl Parent for Value");
    let object_impl = anonymous_definition(FIXTURE, "impl Object for Value");
    let default_impl = anonymous_definition(FIXTURE, "impl Dispatch<u16> for Defaulted");
    let override_impl = anonymous_definition(FIXTURE, "impl Dispatch<u32> for Overridden");
    BTreeMap::from([
        (
            (
                ProofRelationKind::AssociatedLeaf,
                "Dispatch::invoke".to_owned(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedLeaf,
                format!("{drop_impl}::drop"),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedLeaf,
                format!("{object_impl}::selected"),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedLeaf,
                format!("{override_impl}::invoke"),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedLeaf,
                "Parent::inherited".to_owned(),
            ),
            1,
        ),
        (
            (ProofRelationKind::AssociatedDefining, "Dispatch".to_owned()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedDefining, drop_impl.clone()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedDefining, object_impl.clone()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedDefining, override_impl.clone()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedDefining, "Parent".to_owned()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedFinalizing, drop_impl.clone()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedFinalizing, parent_impl.clone()),
            1,
        ),
        (
            (ProofRelationKind::AssociatedFinalizing, object_impl.clone()),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedFinalizing,
                default_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::AssociatedFinalizing,
                override_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                "Dispatch".to_owned(),
            ),
            2,
        ),
        (
            (ProofRelationKind::SpecializationAncestor, drop_impl.clone()),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                parent_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                object_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                default_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                override_impl.clone(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                "Object".to_owned(),
            ),
            1,
        ),
        (
            (
                ProofRelationKind::SpecializationAncestor,
                "Parent".to_owned(),
            ),
            1,
        ),
        ((ProofRelationKind::SelectedImpl, drop_impl), 1),
        ((ProofRelationKind::SelectedImpl, parent_impl), 1),
        ((ProofRelationKind::SelectedImpl, object_impl.clone()), 2),
        ((ProofRelationKind::SelectedImpl, default_impl), 1),
        ((ProofRelationKind::SelectedImpl, override_impl), 1),
        (
            (
                ProofRelationKind::SelectedTraitItem,
                format!("{object_impl}::Item"),
            ),
            1,
        ),
        ((ProofRelationKind::TraitDefinition, "Object".to_owned()), 1),
        ((ProofRelationKind::TraitDefinition, "Parent".to_owned()), 1),
    ])
}

fn local_proof_targets(graph: &DependencyGraph) -> BTreeMap<(ProofRelationKind, String), usize> {
    let mut result = BTreeMap::new();
    for edge in &graph.edges {
        let DependencyKind::ProofRelation { relation, .. } = &edge.kind else {
            continue;
        };
        let GraphNode::Definition(id) = edge.to else {
            continue;
        };
        *result
            .entry((*relation, definition_label(&graph.definitions, id)))
            .or_insert(0usize) += 1;
    }
    result
}

fn local_mono_edges(graph: &DependencyGraph, source: &str) -> Vec<MonoUseRef> {
    graph
        .edges
        .iter()
        .filter_map(|edge| {
            let DependencyKind::Mono {
                relation,
                collection,
            } = &edge.kind
            else {
                return None;
            };
            let (GraphNode::Mono(from), GraphNode::Mono(to)) = (edge.from, edge.to) else {
                unreachable!("mono edges must connect mono nodes")
            };
            Some(MonoUseRef {
                from: local_semantic_node_label(graph, from, source)?,
                to: semantic_node_label(graph, to, source),
                relation: *relation,
                collection: *collection,
                sites: edge.sites.clone(),
                evidence: edge.evidence,
            })
        })
        .collect()
}

fn local_selection_edges(graph: &DependencyGraph, source: &str) -> Vec<ProofUseRef> {
    graph
        .edges
        .iter()
        .filter_map(|edge| {
            let DependencyKind::SelectionProof {
                relation,
                collection,
            } = &edge.kind
            else {
                return None;
            };
            let GraphNode::Mono(from) = edge.from else {
                unreachable!("selection proof edges must start at mono nodes")
            };
            let GraphNode::Proof(target) = edge.to else {
                unreachable!("selection proof edges must end at proof nodes")
            };
            Some(ProofUseRef {
                from: local_semantic_node_label(graph, from, source)?,
                target: proof_ref(graph, target),
                relation: *relation,
                collection: *collection,
                sites: edge.sites.clone(),
                evidence: edge.evidence,
            })
        })
        .collect()
}

fn proof_ref(graph: &DependencyGraph, id: ProofId) -> ProofRef {
    let kind = match &graph.proofs[id.0 as usize].kind {
        ProofNodeKind::Obligation { .. } => "obligation",
        ProofNodeKind::Projection { .. } => "projection",
        ProofNodeKind::AssociatedItem { .. } => "associated",
        ProofNodeKind::Cycle { .. } => "cycle",
    };
    let mut definitions = graph
        .edges
        .iter()
        .filter_map(|edge| {
            if edge.from != GraphNode::Proof(id) {
                return None;
            }
            let DependencyKind::ProofRelation { relation, ordinal } = &edge.kind else {
                return None;
            };
            let label = match edge.to {
                GraphNode::Definition(target) => definition_label(&graph.definitions, target),
                GraphNode::ExternalDefinition(target) => graph.definitions.external_definitions
                    [target.0 as usize]
                    .path
                    .clone(),
                _ => return None,
            };
            Some((*relation, *ordinal, label))
        })
        .collect::<Vec<_>>();
    definitions.sort();
    ProofRef { kind, definitions }
}

fn obligation_proof(definitions: Vec<(ProofRelationKind, u32, &str)>) -> ProofRef {
    expected_proof("obligation", definitions)
}

fn associated_proof(leaf: &str, defining: &str, finalizing: &str, ancestors: &[&str]) -> ProofRef {
    let mut definitions = vec![
        (ProofRelationKind::AssociatedLeaf, 0, leaf),
        (ProofRelationKind::AssociatedDefining, 0, defining),
        (ProofRelationKind::AssociatedFinalizing, 0, finalizing),
    ];
    definitions.extend(ancestors.iter().enumerate().map(|(ordinal, target)| {
        (
            ProofRelationKind::SpecializationAncestor,
            ordinal as u32,
            *target,
        )
    }));
    expected_proof("associated", definitions)
}

fn expected_proof(
    kind: &'static str,
    definitions: Vec<(ProofRelationKind, u32, &str)>,
) -> ProofRef {
    let mut definitions = definitions
        .into_iter()
        .map(|(relation, ordinal, target)| (relation, ordinal, target.to_owned()))
        .collect::<Vec<_>>();
    definitions.sort();
    ProofRef { kind, definitions }
}

fn proof_use(
    from: &str,
    target: ProofRef,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
) -> ProofUseRef {
    proof_use_with_evidence(
        from,
        target,
        relation,
        collection,
        sites,
        EvidenceOrigin::Derived,
    )
}

fn proof_use_with_evidence(
    from: &str,
    target: ProofRef,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
    evidence: EvidenceOrigin,
) -> ProofUseRef {
    ProofUseRef {
        from: from.to_owned(),
        target,
        relation,
        collection,
        sites,
        evidence,
    }
}

fn local_semantic_node_label(graph: &DependencyGraph, id: MonoId, source: &str) -> Option<String> {
    let node = &graph.mono_nodes[id.0 as usize];
    if let Some(DefinitionTarget::Local(definition)) = node.materialized_definition {
        return Some(definition_label(&graph.definitions, definition));
    }
    match &node.key {
        MonoKey::VTable { .. }
            if graph.edges.iter().any(|edge| {
                edge.to == GraphNode::Mono(id)
                    && edge
                        .sites
                        .iter()
                        .any(|site| matches!(site, ObservationSite::Source(_)))
            }) =>
        {
            Some("vtable:source".to_owned())
        }
        MonoKey::Allocation(allocation) if allocation_root_is_local(&allocation.root) => {
            Some(allocation_node_label(graph, allocation, source))
        }
        _ => None,
    }
}

fn semantic_node_label(graph: &DependencyGraph, id: MonoId, source: &str) -> Option<String> {
    let node = &graph.mono_nodes[id.0 as usize];
    if let Some(definition) = node.materialized_definition {
        return Some(target_label(&graph.definitions, definition));
    }
    match &node.key {
        MonoKey::VTable { .. }
            if graph.edges.iter().any(|edge| {
                edge.to == GraphNode::Mono(id)
                    && edge
                        .sites
                        .iter()
                        .any(|site| matches!(site, ObservationSite::Source(_)))
            }) =>
        {
            Some("vtable:source".to_owned())
        }
        MonoKey::Allocation(allocation) if allocation_root_is_local(&allocation.root) => {
            Some(allocation_node_label(graph, allocation, source))
        }
        _ => None,
    }
}

fn allocation_node_label(
    graph: &DependencyGraph,
    allocation: &crate::dependency_graph::AllocationKey,
    source: &str,
) -> String {
    let mut label = format!(
        "allocation:{}",
        allocation_root_label(graph, &allocation.root)
    );
    for part in &allocation.path {
        match part.site {
            AllocationPathSite::Source(range) => {
                label.push(':');
                label.push_str(source_slice(source, range));
            }
            AllocationPathSite::AllocationReference => {
                label.push_str(&format!("/ref{}", part.same_role_ordinal));
            }
            AllocationPathSite::ExternalSource => label.push_str(":external"),
            AllocationPathSite::CompilerGenerated => label.push_str(":generated"),
        }
    }
    label
}

fn allocation_root_is_local(root: &AllocationRootKey) -> bool {
    matches!(
        root,
        AllocationRootKey::Instance {
            instance: MonoInstanceKey {
                definition: DefinitionReferenceKey::Local(_),
                ..
            },
            ..
        } | AllocationRootKey::Static(_)
    )
}

fn allocation_root_label(graph: &DependencyGraph, root: &AllocationRootKey) -> String {
    match root {
        AllocationRootKey::Instance { instance, .. } => {
            definition_reference_label(&graph.definitions, &instance.definition)
        }
        AllocationRootKey::Static(definition) => definition_key_label(definition),
        AllocationRootKey::VTable { .. } => "vtable".to_owned(),
    }
}

fn allocation_site_label(source: &str, site: AllocationPathSite) -> String {
    match site {
        AllocationPathSite::Source(range) => source_slice(source, range).to_owned(),
        AllocationPathSite::ExternalSource => "external-source".to_owned(),
        AllocationPathSite::AllocationReference => "allocation-reference".to_owned(),
        AllocationPathSite::CompilerGenerated => "compiler-generated".to_owned(),
    }
}

fn definition_reference_label(
    graph: &DefinitionGraph,
    reference: &DefinitionReferenceKey,
) -> String {
    match reference {
        DefinitionReferenceKey::Local(key) => definition_key_label(key),
        DefinitionReferenceKey::External(key) => graph
            .external_definitions
            .iter()
            .find(|definition| definition.key == *key)
            .expect("external definition keys must resolve")
            .path
            .clone(),
    }
}

fn target_label(graph: &DefinitionGraph, target: DefinitionTarget) -> String {
    match target {
        DefinitionTarget::Local(id) => definition_label(graph, id),
        DefinitionTarget::External(id) => graph.external_definitions[id.0 as usize].path.clone(),
    }
}

fn definition_label(graph: &DefinitionGraph, id: DefinitionId) -> String {
    definition_key_label(&graph.definitions[id.0 as usize].key)
}

fn definition_key_label(key: &DefinitionKey) -> String {
    key.0
        .iter()
        .skip(1)
        .map(|part| {
            part.name.clone().unwrap_or_else(|| {
                let anchor = match &part.origin {
                    DefinitionOriginKey::Written { anchor, .. } => anchor.start.to_string(),
                    DefinitionOriginKey::Expanded {
                        invocation_range, ..
                    } => invocation_range.start.to_string(),
                    DefinitionOriginKey::CompilerGenerated { role } => {
                        format!("generated-{role:?}")
                    }
                    DefinitionOriginKey::Injected { role } => format!("injected-{role:?}"),
                };
                format!("{:?}@{anchor}", part.kind)
            })
        })
        .collect::<Vec<_>>()
        .join("::")
}

fn anonymous_definition(source: &str, marker: &str) -> String {
    format!("Impl@{}", marker_range_nth(source, marker, 0).start)
}

fn mono_use(
    from: &str,
    to: Option<&str>,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
) -> MonoUseRef {
    mono_use_with_evidence(
        from,
        to,
        relation,
        collection,
        sites,
        EvidenceOrigin::PatchedObserver,
    )
}

fn mono_use_with_evidence(
    from: &str,
    to: Option<&str>,
    relation: MonoDependencyKind,
    collection: MonoCollection,
    sites: Vec<ObservationSite>,
    evidence: EvidenceOrigin,
) -> MonoUseRef {
    MonoUseRef {
        from: from.to_owned(),
        to: to.map(str::to_owned),
        relation,
        collection,
        sites,
        evidence,
    }
}

fn source_site(source: &str, marker: &str) -> ObservationSite {
    source_site_nth(source, marker, 0)
}

fn source_site_nth(source: &str, marker: &str, occurrence: usize) -> ObservationSite {
    ObservationSite::Source(marker_range_nth(source, marker, occurrence))
}

fn source_sites(source: &str, marker: &str) -> Vec<ObservationSite> {
    source
        .match_indices(marker)
        .map(|(start, _)| {
            ObservationSite::Source(ByteRange {
                start: start as u32,
                end: (start + marker.len()) as u32,
            })
        })
        .collect()
}

fn source_sites_after(source: &str, anchor: &str, marker: &str) -> Vec<ObservationSite> {
    let start = marker_range_nth(source, anchor, 0).start as usize;
    source[start..]
        .match_indices(marker)
        .map(|(offset, _)| {
            let start = start + offset;
            ObservationSite::Source(ByteRange {
                start: start as u32,
                end: (start + marker.len()) as u32,
            })
        })
        .collect()
}

fn marker_range_nth(source: &str, marker: &str, occurrence: usize) -> ByteRange {
    let start = source
        .match_indices(marker)
        .nth(occurrence)
        .unwrap_or_else(|| panic!("missing source marker {marker:?} occurrence {occurrence}"))
        .0;
    ByteRange {
        start: start as u32,
        end: (start + marker.len()) as u32,
    }
}

fn source_slice(source: &str, range: ByteRange) -> &str {
    &source[range.start as usize..range.end as usize]
}

fn compiler_context() -> (PathBuf, String) {
    let rustc = env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC");
    let sysroot = rustc_output(rustc, &["--print", "sysroot"]);
    let version = rustc_output(rustc, &["-Vv"]);
    let target = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc -Vv must report a host")
        .to_owned();
    (PathBuf::from(sysroot.trim()), target)
}

fn rustc_output(rustc: &str, arguments: &[&str]) -> String {
    let output = Command::new(rustc)
        .args(arguments)
        .output()
        .expect("rustc query must start");
    assert!(output.status.success(), "rustc query failed");
    String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
}
