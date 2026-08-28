use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use crate::compiler_terms::CanonicalCompilerTerm;
use crate::dependency_graph::{
    AstPassKind, DefinitionReferenceKey, DependencyEdge, EvidenceOrigin, ExpansionFragmentKind,
    ExpansionId, ExpansionKey, ExpansionKeyPart, ExpansionKind, ExpansionNode, MacroStyle,
    MonoInstanceKey, MonoInstanceRole, MonoKey, MonoNode, ObservationSite, RootReason, RootRecord,
};
use crate::expansions::MacroOutputSlice;
use crate::graph::{
    Definition, DefinitionEdge, DefinitionGraph, DefinitionKey, DefinitionKeyPart,
    DependencyKind as DefinitionDependencyKind, ExternalDefinition, ExternalDefinitionId,
    ExternalDefinitionKey, GeneratedRole, InjectedRole,
};
use crate::source::{
    AtomicGroupId, ByteRange, DeriveAttributeSourceFacts, DeriveHelperSourceFacts,
    DeriveSourceRequirement, DeriveTargetSourceFacts, MacroRepetitionElementSourceFacts,
    MacroRepetitionSourceFacts, MacroRuleSourceFacts, MacroTemplateSourceFacts, OriginalOffsetMap,
    SourceInventory, WrittenUnit,
};

use super::macro_products::MacroGroupDemand;
use super::*;
use crate::dependency_graph::MonoId;

fn macro_graph(graph: &DependencyGraph) -> &DependencyGraph {
    graph
}

fn unit(
    id: u32,
    kind: WrittenUnitKind,
    range: (u32, u32),
    parent: Option<u32>,
    group: u32,
) -> WrittenUnit {
    WrittenUnit {
        id: SourceUnitId(id),
        kind,
        full_range: ByteRange {
            start: range.0,
            end: range.1,
        },
        parent: parent.map(SourceUnitId),
        cfg_state: CfgState::Active,
        atomic_group: AtomicGroupId(group),
        same_role_ordinal: id.saturating_sub(1),
    }
}

fn output_range(start: u32, end: u32) -> MacroOutputRange {
    MacroOutputRange::test_new(start, end)
}

fn source_with_token(len: usize, range: (usize, usize)) -> String {
    let mut source = vec![b' '; len];
    source[range.0..range.1].fill(b'x');
    String::from_utf8(source).unwrap()
}

fn contributor_roots(contributors: Vec<SourceUnitId>) -> Box<[MacroContributorSetId]> {
    contributors
        .into_iter()
        .map(MacroContributorSetId::test_from_source_unit)
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

fn products_group(
    output_ranges: Vec<MacroOutputRange>,
    products: Vec<GraphNode>,
    contributors: Vec<SourceUnitId>,
) -> MacroOutputMaterializationGroup {
    MacroOutputMaterializationGroup::test_new(
        contributors,
        vec![MacroOutputSlice::test_new_products(output_ranges, products)],
    )
}

fn owner_effect_group(
    output_ranges: Vec<MacroOutputRange>,
    owner: DefinitionId,
    contributors: Vec<SourceUnitId>,
) -> MacroOutputMaterializationGroup {
    MacroOutputMaterializationGroup::test_new(
        contributors,
        vec![MacroOutputSlice::test_new_owner_effect(
            output_ranges,
            owner,
        )],
    )
}

fn macro_group_demand(
    carriers: Vec<DefinitionId>,
    dependent_expansions: Vec<ExpansionId>,
    required_expansions: Vec<ExpansionId>,
) -> MacroGroupDemand {
    MacroGroupDemand {
        carriers: carriers.into_boxed_slice(),
        dependent_expansions: dependent_expansions.into_boxed_slice(),
        required_expansions: required_expansions.into_boxed_slice(),
    }
}

fn complete_meaning_with_source_owner(
    producer: ExpansionId,
    residual_intrinsic: bool,
    dependent_expansions: Vec<ExpansionId>,
    source_owner: DefinitionId,
) -> MacroCompleteOutputMeaning {
    let mut meaning = MacroCompleteOutputMeaning::test_new(
        producer,
        residual_intrinsic,
        dependent_expansions.clone(),
    );
    meaning.test_set_actual_demand(
        residual_intrinsic,
        residual_intrinsic
            .then_some(source_owner)
            .into_iter()
            .collect(),
        (!dependent_expansions.is_empty())
            .then(|| (vec![source_owner], dependent_expansions, Vec::new()))
            .into_iter()
            .collect(),
    );
    meaning
}

fn complete_meaning(
    producer: ExpansionId,
    intrinsic: bool,
    residual_intrinsic: bool,
    dependent_expansions: Vec<ExpansionId>,
    actual_demand_definitions: Vec<DefinitionId>,
    output_demands: Vec<(Vec<DefinitionId>, Vec<ExpansionId>, Vec<ExpansionId>)>,
) -> MacroCompleteOutputMeaning {
    let mut meaning =
        MacroCompleteOutputMeaning::test_new(producer, intrinsic, dependent_expansions);
    meaning.test_set_actual_demand(
        residual_intrinsic,
        actual_demand_definitions,
        output_demands,
    );
    meaning
}

fn set_complete_meaning(
    constraints: &mut SourceConstraints,
    meanings: Vec<MacroCompleteOutputMeaning>,
) {
    constraints
        .declarative_macros
        .as_mut()
        .expect("complete test constraints include declarative macro facts")
        .complete_output_meaning = MacroCompleteOutputMeaningInventory::test_new(meanings);
}

fn coverage(
    producer: ExpansionId,
    output_token_count: u32,
    materialization_groups: Vec<MacroOutputMaterializationGroup>,
) -> MacroProducerCoverage {
    MacroProducerCoverage::test_new(producer, output_token_count, materialization_groups)
}

struct CoverageMut<'a> {
    inventory: &'a mut MacroProducerCoverageInventory,
    complete_output_meaning: &'a mut MacroCompleteOutputMeaningInventory,
    producers: Vec<MacroProducerCoverage>,
}

impl Deref for CoverageMut<'_> {
    type Target = Vec<MacroProducerCoverage>;

    fn deref(&self) -> &Self::Target {
        &self.producers
    }
}

impl DerefMut for CoverageMut<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.producers
    }
}

impl Drop for CoverageMut<'_> {
    fn drop(&mut self) {
        if self.complete_output_meaning.producers().is_empty() {
            let mut meanings = Vec::new();
            for coverage in &self.producers {
                if coverage.output_token_count() == 0 {
                    continue;
                }
                let mut intrinsic = false;
                let mut dependencies = BTreeSet::new();
                for slice in coverage
                    .materialization_groups()
                    .iter()
                    .flat_map(|group| group.output_slices())
                {
                    if let Some(products) = slice.products() {
                        for &product in products {
                            match product {
                                GraphNode::Expansion(expansion) => {
                                    dependencies.insert(expansion);
                                }
                                GraphNode::Definition(_)
                                | GraphNode::ExternalDefinition(_)
                                | GraphNode::Proof(_)
                                | GraphNode::Mono(_) => intrinsic = true,
                            }
                        }
                    } else if let Some((_, _, effect)) = slice.owner_effect() {
                        match effect {
                            MacroOwnerEffect::Semantic => intrinsic = true,
                            MacroOwnerEffect::TransparentShell { dependent_products } => {
                                for &product in dependent_products {
                                    match product {
                                        GraphNode::Expansion(expansion) => {
                                            dependencies.insert(expansion);
                                        }
                                        GraphNode::Definition(_)
                                        | GraphNode::ExternalDefinition(_)
                                        | GraphNode::Proof(_)
                                        | GraphNode::Mono(_) => intrinsic = true,
                                    }
                                }
                            }
                        }
                    }
                }
                if !intrinsic && dependencies.is_empty() {
                    intrinsic = true;
                }
                meanings.push(MacroCompleteOutputMeaning::test_new(
                    coverage.producer(),
                    intrinsic,
                    dependencies.into_iter().collect(),
                ));
            }
            meanings.sort();
            *self.complete_output_meaning = MacroCompleteOutputMeaningInventory::test_new(meanings);
        }
        *self.inventory =
            MacroProducerCoverageInventory::test_new(std::mem::take(&mut self.producers));
    }
}

fn coverage_mut(constraints: &mut SourceConstraints) -> CoverageMut<'_> {
    let declarative_macros = constraints
        .declarative_macros
        .as_mut()
        .expect("complete test constraints include declarative macro facts");
    CoverageMut {
        producers: declarative_macros.producer_coverage.producers().to_vec(),
        inventory: &mut declarative_macros.producer_coverage,
        complete_output_meaning: &mut declarative_macros.complete_output_meaning,
    }
}

fn outputless_mut(constraints: &mut SourceConstraints) -> &mut Vec<ExpansionId> {
    &mut constraints
        .declarative_macros
        .as_mut()
        .expect("complete test constraints include declarative macro facts")
        .outputless_expansions
}

fn close_validated_retention_constraints(
    macro_products: &ValidatedMacroProducts,
    compiler_members: Option<&ValidatedCompilerMemberConstraints>,
    compile_required: &mut BTreeSet<GraphNode>,
    retained_units: &mut BTreeSet<SourceUnitId>,
) {
    let mut closure = RetentionClosure::new(macro_products, compiler_members);
    let mut newly_required = Vec::new();
    let mut actual_required = compile_required.clone();
    let mut newly_actual = Vec::new();
    let mut newly_retained_units = Vec::new();
    closure
        .seed(compile_required, &actual_required, retained_units)
        .unwrap();
    closure.close(
        compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        retained_units,
        &mut newly_retained_units,
    );
}

fn close_compiler_reachability(
    graph: &DependencyGraph,
    source: &SourceInventory,
    retained: &BTreeSet<SourceUnitId>,
    materialized: &BTreeSet<ExpansionId>,
    mut reachable: BTreeSet<GraphNode>,
) -> Result<BTreeSet<GraphNode>, RetentionError> {
    let source_sites = SourceSiteOwnerIndex::new(source)?;
    let index = CompilerReachabilityIndex::new(source, &source_sites, graph, materialized)?;
    let mut closure = CompilerReachabilityClosure::new(&index);
    closure.seed(&reachable, retained)?;
    let mut newly_reachable = Vec::new();
    closure.close(&mut reachable, &mut newly_reachable)?;
    Ok(reachable)
}

#[test]
fn compiler_reachability_keeps_presence_and_actual_demand_as_separate_lanes() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index = CompilerReachabilityIndex::new(&inventory, &source_sites, &graph, &BTreeSet::new())
        .unwrap();
    let trigger = GraphNode::Definition(DefinitionId(1));
    let target = GraphNode::Definition(DefinitionId(0));
    let mut compile_present = BTreeSet::from([trigger]);
    let mut newly_present = Vec::new();
    let mut presence = CompilerReachabilityClosure::new(&index);
    presence.seed(&compile_present, &BTreeSet::new()).unwrap();
    presence
        .close(&mut compile_present, &mut newly_present)
        .unwrap();

    let mut actual_required = BTreeSet::new();
    let mut newly_actual = Vec::new();
    let mut actual = CompilerReachabilityClosure::new(&index);
    actual.seed(&actual_required, &BTreeSet::new()).unwrap();
    actual
        .close(&mut actual_required, &mut newly_actual)
        .unwrap();
    assert!(compile_present.contains(&target));
    assert!(!actual_required.contains(&target));

    actual_required.insert(trigger);
    newly_actual.push(trigger);
    actual.add_reachable([trigger]);
    actual
        .close(&mut actual_required, &mut newly_actual)
        .unwrap();
    mirror_actual_nodes_into_compile(&newly_actual, &mut compile_present, &mut newly_present);
    assert!(actual_required.contains(&target));
    assert!(compile_present.is_superset(&actual_required));
}

#[test]
fn compiler_member_requirement_materializes_compile_presence_without_semantic_demand() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 48), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 12), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (16, 32), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Impl, &units[2], Some(0), "impl"),
        ],
        Vec::new(),
    );
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints
        .compiler_members
        .requirements
        .push(DefinitionRequirement {
            trigger: DefinitionId(0),
            required: DefinitionId(2),
        });

    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();

    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Definition(DefinitionId(0)))
    );
    assert!(retention.retained_units.contains(&SourceUnitId(0)));
    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Definition(DefinitionId(2)))
    );
    assert!(retention.retained_units.contains(&SourceUnitId(2)));
    assert!(
        !retention
            .semantic_required
            .contains(&GraphNode::Definition(DefinitionId(2)))
    );
}

fn tied_source_site_reachability_fixture()
-> (SourceInventory, Vec<Definition>, ByteRange, ByteRange) {
    let source = "x".repeat(24);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 24), None, 0),
        unit(1, WrittenUnitKind::Item, (1, 20), Some(0), 1),
        unit(2, WrittenUnitKind::NestedItem, (4, 12), Some(1), 2),
        unit(3, WrittenUnitKind::NestedItem, (5, 13), Some(1), 3),
        unit(4, WrittenUnitKind::MacroInvocation, (21, 22), Some(0), 4),
    ];
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
    ];
    (
        inventory(&source, units),
        definitions,
        ByteRange { start: 6, end: 10 },
        ByteRange { start: 21, end: 22 },
    )
}

fn rule_selections(constraints: &SourceConstraints) -> &[MacroRuleSelectionRequirement] {
    &constraints
        .declarative_macros
        .as_ref()
        .expect("complete test constraints include declarative macro facts")
        .rule_selections
}

fn inventory(source: &str, units: Vec<WrittenUnit>) -> SourceInventory {
    let (normalized, offsets) = OriginalOffsetMap::from_source(source).unwrap();
    SourceInventory {
        original: Arc::from(source),
        normalized: Arc::from(normalized),
        offsets,
        units,
        pieces: Vec::new(),
        derive_targets: Vec::new(),
        macro_rules: Vec::new(),
        macro_templates: Vec::new(),
        macro_repetitions: Vec::new(),
        ownerless_attribute_invocations: Vec::new(),
    }
}

fn written_definition(
    id: u32,
    kind: DefinitionKind,
    unit: &WrittenUnit,
    parent: Option<u32>,
    name: &str,
) -> Definition {
    let origin = DefinitionOrigin::Written {
        unit: unit.id,
        unit_range: unit.full_range,
        anchor: ByteRange {
            start: unit.full_range.start,
            end: unit.full_range.start,
        },
        unit_kind: unit.kind,
        unit_ordinal: unit.same_role_ordinal,
    };
    Definition {
        id: DefinitionId(id),
        key: DefinitionKey(vec![DefinitionKeyPart {
            kind,
            origin: origin.key(),
            name: Some(name.to_owned()),
            same_role_ordinal: 0,
        }]),
        kind,
        parent: parent.map(DefinitionId),
        origin,
    }
}

fn expanded_definition(
    id: u32,
    kind: DefinitionKind,
    invocation: &WrittenUnit,
    parent: Option<u32>,
    name: &str,
) -> Definition {
    let origin = DefinitionOrigin::Expanded {
        invocation: invocation.id,
        invocation_range: invocation.full_range,
        generated_role: None,
        ordinal: id,
    };
    Definition {
        id: DefinitionId(id),
        key: DefinitionKey(vec![DefinitionKeyPart {
            kind,
            origin: origin.key(),
            name: Some(name.to_owned()),
            same_role_ordinal: id,
        }]),
        kind,
        parent: parent.map(DefinitionId),
        origin,
    }
}

fn compiler_generated_definition(id: u32, parent: u32) -> Definition {
    let origin = DefinitionOrigin::CompilerGenerated {
        role: GeneratedRole::OpaqueType,
        ordinal: id,
    };
    Definition {
        id: DefinitionId(id),
        key: DefinitionKey(vec![DefinitionKeyPart {
            kind: DefinitionKind::OpaqueType,
            origin: origin.key(),
            name: None,
            same_role_ordinal: id,
        }]),
        kind: DefinitionKind::OpaqueType,
        parent: Some(DefinitionId(parent)),
        origin,
    }
}

fn injected_definition(id: u32, parent: u32) -> Definition {
    let origin = DefinitionOrigin::Injected {
        role: InjectedRole::PreludeImport,
        ordinal: 0,
    };
    Definition {
        id: DefinitionId(id),
        key: DefinitionKey(vec![DefinitionKeyPart {
            kind: DefinitionKind::Use,
            origin: origin.key(),
            name: None,
            same_role_ordinal: 0,
        }]),
        kind: DefinitionKind::Use,
        parent: Some(DefinitionId(parent)),
        origin,
    }
}

fn edge(from: GraphNode, to: GraphNode) -> DependencyEdge {
    let materialization = matches!(from, GraphNode::Mono(_))
        && matches!(
            to,
            GraphNode::Definition(_) | GraphNode::ExternalDefinition(_)
        );
    DependencyEdge {
        from,
        to,
        kind: if materialization {
            DependencyKind::MaterializesDefinition
        } else {
            DependencyKind::Definition(DefinitionDependencyKind::ValuePath)
        },
        sites: (!materialization)
            .then_some(ObservationSite::CompilerGenerated)
            .into_iter()
            .collect(),
        evidence: EvidenceOrigin::Compiler,
    }
}

fn opaque_source_edge(
    from: u32,
    to: u32,
    sites: impl IntoIterator<Item = ByteRange>,
) -> DefinitionEdge {
    DefinitionEdge {
        from: DefinitionId(from),
        to: DefinitionTarget::Local(DefinitionId(to)),
        kind: DefinitionDependencyKind::OpaqueSource,
        sites: sites.into_iter().collect(),
    }
}

fn graph(definitions: Vec<Definition>, mut edges: Vec<DependencyEdge>) -> DependencyGraph {
    let main = definitions
        .iter()
        .find(|definition| {
            definition
                .key
                .0
                .last()
                .and_then(|part| part.name.as_deref())
                == Some("main")
        })
        .unwrap();
    let main_id = main.id;
    let main_key = main.key.clone();
    let term = CanonicalCompilerTerm {
        schema_version: 1,
        bytes: vec![1],
    };
    let main_instance = MonoInstanceKey {
        definition: DefinitionReferenceKey::Local(main_key),
        arguments: term.clone(),
        kind: term.clone(),
    };
    let start_instance = MonoInstanceKey {
        definition: DefinitionReferenceKey::Local(definitions[0].key.clone()),
        arguments: term.clone(),
        kind: term,
    };
    let mono_nodes = vec![
        MonoNode {
            id: MonoId(0),
            key: MonoKey::Instance {
                instance: main_instance,
                role: MonoInstanceRole::Callable,
            },
            materialized_definition: Some(crate::graph::DefinitionTarget::Local(main_id)),
            allocation_observation: None,
        },
        MonoNode {
            id: MonoId(1),
            key: MonoKey::Instance {
                instance: start_instance,
                role: MonoInstanceRole::Callable,
            },
            materialized_definition: None,
            allocation_observation: None,
        },
    ];
    edges.push(edge(
        GraphNode::Mono(MonoId(0)),
        GraphNode::Definition(main_id),
    ));
    DependencyGraph {
        definitions: DefinitionGraph {
            definitions,
            external_definitions: Vec::new(),
            edges: Vec::new(),
        },
        expansions: Vec::new(),
        proofs: Vec::new(),
        mono_nodes,
        edges,
        roots: vec![
            RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::Main,
            },
            RootRecord {
                node: GraphNode::Mono(MonoId(1)),
                reason: RootReason::StartInstance,
            },
        ],
    }
}

fn add_macro_expansion(
    graph: &mut DependencyGraph,
    invocation: &WrittenUnit,
    owner: DefinitionId,
    products: impl IntoIterator<Item = DefinitionId>,
) -> ExpansionId {
    let id = ExpansionId(graph.expansions.len() as u32);
    let kind = ExpansionKind::Macro {
        style: MacroStyle::Bang,
        name: format!("macro_{}", id.0),
    };
    graph.expansions.push(ExpansionNode {
        id,
        key: ExpansionKey(vec![ExpansionKeyPart {
            kind: kind.clone(),
            fragment: Some(ExpansionFragmentKind::Items),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: Some(invocation.full_range),
            node_range: Some(invocation.full_range),
            target_range: None,
            macro_definition: None,
            selected_macro_rule: None,
            same_role_ordinal: id.0,
        }]),
        kind,
        fragment: Some(ExpansionFragmentKind::Items),
        implementation: Some(MacroImplementationKind::Declarative),
        discovered_in: None,
        semantic_parent: None,
        source_call_parent: None,
        written_invocation: Some(invocation.id),
        source_owner: Some(owner),
        macro_definition: None,
    });
    graph.edges.push(DependencyEdge {
        from: GraphNode::Definition(owner),
        to: GraphNode::Expansion(id),
        kind: DependencyKind::ExpansionUse,
        sites: vec![ObservationSite::Source(invocation.full_range)],
        evidence: EvidenceOrigin::Compiler,
    });
    graph
        .edges
        .extend(products.into_iter().map(|product| DependencyEdge {
            from: GraphNode::Definition(product),
            to: GraphNode::Expansion(id),
            kind: DependencyKind::GeneratedBy,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        }));
    id
}

fn test_expansion_node(
    id: u32,
    written_invocation: Option<SourceUnitId>,
    discovered_in: Option<u32>,
    semantic_parent: Option<u32>,
    source_call_parent: Option<u32>,
) -> ExpansionNode {
    let kind = ExpansionKind::Macro {
        style: MacroStyle::Bang,
        name: format!("expansion_{id}"),
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
            same_role_ordinal: id,
        }]),
        kind,
        fragment: Some(ExpansionFragmentKind::Items),
        implementation: Some(MacroImplementationKind::Declarative),
        discovered_in: discovered_in.map(ExpansionId),
        semantic_parent: semantic_parent.map(ExpansionId),
        source_call_parent: source_call_parent.map(ExpansionId),
        written_invocation,
        source_owner: Some(DefinitionId(1)),
        macro_definition: None,
    }
}

fn complete_macro_meaning_graph(parents: &[Option<u32>]) -> DependencyGraph {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 30), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroDefinition, (11, 29), Some(0), 2),
    ];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Macro, &units[2], Some(0), "m"),
        ],
        Vec::new(),
    );
    let definition = DefinitionTarget::Local(DefinitionId(2));
    let definition_key =
        DefinitionReferenceKey::Local(graph.definitions.definitions[2].key.clone());
    graph.expansions = parents
        .iter()
        .enumerate()
        .map(|(id, &parent)| {
            let mut expansion = test_expansion_node(id as u32, None, None, None, parent);
            expansion.macro_definition = Some(definition);
            expansion.key.0[0].macro_definition = Some(definition_key.clone());
            expansion
        })
        .collect();
    graph
}

fn compiler_expansion_use(from: DefinitionId, to: ExpansionId) -> DependencyEdge {
    DependencyEdge {
        from: GraphNode::Definition(from),
        to: GraphNode::Expansion(to),
        kind: DependencyKind::ExpansionUse,
        sites: vec![ObservationSite::CompilerGenerated],
        evidence: EvidenceOrigin::Compiler,
    }
}

fn complete_constraints(source: &SourceInventory, graph: &DependencyGraph) -> SourceConstraints {
    let mut constraints = SourceConstraints::from_source(source);
    constraints.member_containers = graph
        .definitions
        .definitions
        .iter()
        .filter_map(|definition| {
            matches!(
                definition.kind,
                DefinitionKind::Trait | DefinitionKind::Impl
            )
            .then(|| match &definition.origin {
                DefinitionOrigin::Written { unit, .. } => Some(*unit),
                _ => None,
            })
            .flatten()
        })
        .collect();
    constraints.classified_members = source
        .units
        .iter()
        .filter(|unit| {
            matches!(
                unit.kind,
                WrittenUnitKind::TraitMember | WrittenUnitKind::ImplMember
            ) && unit.cfg_state == CfgState::Active
        })
        .map(|unit| unit.id)
        .collect();
    constraints.compiler_members.classified_members = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| {
            matches!(
                definition.kind,
                DefinitionKind::AssociatedType
                    | DefinitionKind::AssociatedFunction
                    | DefinitionKind::AssociatedConst
            ) && matches!(
                definition.origin,
                DefinitionOrigin::Written { .. } | DefinitionOrigin::Expanded { .. }
            )
        })
        .map(|definition| definition.id)
        .collect();
    constraints.compiler_members.classified_implementations = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::Impl)
        .map(|definition| definition.id)
        .collect();
    constraints.external_crates.loaded_crates = graph
        .definitions
        .external_definitions
        .iter()
        .map(|definition| definition.key.crate_identity)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|crate_identity| ExternalCrateDependency {
            crate_identity,
            kind: ExternalDependencyKind::Unconditional,
        })
        .collect();
    constraints.external_crates.bindings = graph
        .definitions
        .definitions
        .iter()
        .filter(|definition| definition.kind == DefinitionKind::ExternCrate)
        .map(|definition| ExternalCrateBinding {
            definition: definition.id,
            target: ExternalCrateBindingTarget::SelfCrate,
        })
        .collect();
    let declarative_macros = collect_declarative_macro_constraints(
        source,
        &graph.definitions,
        &graph.expansions,
        MacroProducerCoverageInventory::test_new(Vec::new()),
        MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
        Vec::new(),
    )
    .unwrap();
    constraints
        .set_declarative_macro_constraints(declarative_macros)
        .unwrap();
    constraints
}

fn external_dependency(
    crate_identity: u64,
    kind: ExternalDependencyKind,
) -> ExternalCrateDependency {
    ExternalCrateDependency {
        crate_identity,
        kind,
    }
}

fn external_load(
    direct: ExternalCrateDependency,
    closure: impl IntoIterator<Item = ExternalCrateDependency>,
) -> ExternalCrateLoad {
    ExternalCrateLoad {
        direct,
        closure: closure.into_iter().collect(),
    }
}

#[test]
fn opaque_source_preservation_depends_on_owner_reachability() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let mut inactive = unit(4, WrittenUnitKind::Item, (31, 40), Some(0), 4);
    inactive.cfg_state = CfgState::Inactive;
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
        inactive,
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(2, DefinitionKind::Function, &units[2], Some(0), "unused_a"),
        written_definition(3, DefinitionKind::Function, &units[3], Some(0), "unused_b"),
    ];
    for (trigger, site, expected) in [
        (
            1,
            ByteRange { start: 3, end: 8 },
            BTreeSet::from([
                SourceUnitId(0),
                SourceUnitId(1),
                SourceUnitId(2),
                SourceUnitId(3),
            ]),
        ),
        (
            2,
            ByteRange { start: 13, end: 18 },
            BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
        ),
    ] {
        let mut graph = graph(
            definitions.clone(),
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        graph.definitions.edges = vec![opaque_source_edge(trigger, 0, [site])];

        let retention = compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        )
        .unwrap();

        assert_eq!(retention.retained_units, expected, "trigger {trigger}");
    }
}

#[test]
fn opaque_source_edges_require_the_crate_target_and_source_evidence() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
    ];

    for opaque_edge in [
        opaque_source_edge(1, 1, [ByteRange { start: 3, end: 8 }]),
        opaque_source_edge(1, 0, []),
        opaque_source_edge(1, 0, [ByteRange { start: 20, end: 21 }]),
        opaque_source_edge(1, 0, [ByteRange { start: 33, end: 34 }]),
    ] {
        let mut graph = graph(
            definitions.clone(),
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        graph.definitions.edges = vec![opaque_edge];

        assert_eq!(
            compute_retention(
                &inventory,
                &graph,
                &complete_constraints(&inventory, &graph),
            ),
            Err(RetentionError::IncompleteOpaqueSourceConstraints)
        );
    }
}

#[test]
fn retained_macro_products_reenter_the_compiler_closure() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "first"),
        expanded_definition(3, DefinitionKind::Function, &units[2], Some(0), "sibling"),
        written_definition(4, DefinitionKind::Struct, &units[3], Some(0), "dependency"),
        compiler_generated_definition(5, 4),
        compiler_generated_definition(6, 2),
    ];
    let mut graph = graph(
        definitions,
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(3)),
                GraphNode::Definition(DefinitionId(5)),
            ),
        ],
    );
    add_macro_expansion(
        &mut graph,
        &units[2],
        DefinitionId(1),
        [DefinitionId(2), DefinitionId(3)],
    );
    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert_eq!(
        retention.retained_units,
        BTreeSet::from([
            SourceUnitId(0),
            SourceUnitId(1),
            SourceUnitId(2),
            SourceUnitId(3),
        ])
    );
    assert_eq!(
        retention.compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
            GraphNode::Definition(DefinitionId(3)),
            GraphNode::Definition(DefinitionId(4)),
            GraphNode::Definition(DefinitionId(5)),
            GraphNode::Definition(DefinitionId(6)),
            GraphNode::Expansion(ExpansionId(0)),
            GraphNode::Mono(MonoId(0)),
            GraphNode::Mono(MonoId(1)),
        ])
    );
}

#[test]
fn macro_materialization_requires_all_contributors_in_both_directions() {
    let first_product = GraphNode::Definition(DefinitionId(2));
    let second_product = GraphNode::Definition(DefinitionId(3));
    let materialization = MacroMaterialization {
        producer: ExpansionId(0),
        products: vec![first_product, second_product],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(2), SourceUnitId(3)]),
    };
    let macro_products =
        ValidatedMacroProducts::new(vec![materialization], BTreeSet::new()).unwrap();

    let mut compile_required = BTreeSet::from([second_product]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(
        retained_units,
        BTreeSet::from([SourceUnitId(2), SourceUnitId(3)])
    );

    compile_required.clear();
    retained_units = BTreeSet::from([SourceUnitId(2)]);
    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut actual_required = BTreeSet::new();
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained_units = Vec::new();
    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained_units,
    );
    assert!(compile_required.is_empty());

    retained_units.insert(SourceUnitId(3));
    closure.add_source([SourceUnitId(3)]);
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained_units,
    );
    assert_eq!(
        compile_required,
        BTreeSet::from([first_product, second_product])
    );
}

#[test]
fn every_macro_materialization_root_must_resolve_to_a_source() {
    let (dag, empty, source) =
        crate::expansions::MacroContributorDag::test_empty_and_source_root(SourceUnitId(0));
    let materialization = |roots: Vec<MacroContributorSetId>| MacroMaterialization {
        producer: ExpansionId(0),
        products: vec![GraphNode::Definition(DefinitionId(0))],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: roots.into_boxed_slice(),
    };
    let validate = |roots| {
        ValidatedMacroProducts::new_with_dag(
            Arc::new(dag.clone()),
            1,
            vec![materialization(roots)],
            BTreeSet::new(),
        )
    };

    assert!(validate(vec![source]).is_ok());
    assert!(matches!(
        validate(vec![empty]),
        Err(RetentionError::InvalidConstraint)
    ));
    assert!(matches!(
        validate(vec![empty, source]),
        Err(RetentionError::InvalidConstraint)
    ));
}

#[test]
fn explicit_materialization_group_lowers_all_members_without_pointer_identity() {
    const COUNT: u32 = 1_024;
    let contributors = (0..COUNT).map(SourceUnitId).collect::<Vec<_>>();
    let groups = vec![PendingMacroMaterializationGroup {
        producer: ExpansionId(0),
        products: (0..COUNT)
            .map(|index| GraphNode::Definition(DefinitionId(index)))
            .collect(),
        product_classes: (0..COUNT)
            .map(|index| Box::from([GraphNode::Definition(DefinitionId(index))]))
            .collect(),
        owner_requirements: BTreeSet::from([MacroOwnerRequirement {
            owner: DefinitionId(COUNT),
            members: vec![DefinitionId(COUNT + 1)],
            effect: MacroOwnerEffect::Semantic,
        }]),
        identity_cohort_root: None,
        output_demands: BTreeSet::new(),
        contributor_roots: contributor_roots(contributors.clone()),
    }];

    let materializations = lower_macro_materialization_groups(groups).unwrap();
    assert_eq!(materializations.len(), 1);
    assert_eq!(materializations[0].products.len(), COUNT as usize);
    assert_eq!(materializations[0].owner_requirements.len(), 1);
    assert_eq!(
        materializations[0]
            .contributor_roots
            .iter()
            .map(|root| root.test_source_unit())
            .collect::<Vec<_>>(),
        contributors,
    );
    let validated = ValidatedMacroProducts::new(materializations.clone(), BTreeSet::new()).unwrap();
    assert_eq!(validated.product_groups.len(), COUNT as usize);
    assert_eq!(
        validated.contributor_sources_for_group(0).unwrap(),
        contributors
    );
    for definition in (0..COUNT).rev() {
        assert_eq!(
            validated.group_for_product(GraphNode::Definition(DefinitionId(definition))),
            Some(0),
        );
    }
    assert_eq!(
        validated.group_for_product(GraphNode::Definition(DefinitionId(COUNT))),
        None
    );

    let owner = GraphNode::Definition(DefinitionId(COUNT));
    let owner_member = GraphNode::Definition(DefinitionId(COUNT + 1));
    let mut compile_required =
        BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT - 1)), owner]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &validated,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(retained_units.len(), COUNT as usize);
    assert_eq!(compile_required.len(), COUNT as usize + 2);
    assert!(compile_required.contains(&owner_member));

    let equal_contributor_groups = lower_macro_materialization_groups(vec![
        PendingMacroMaterializationGroup {
            producer: ExpansionId(0),
            products: BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT + 2))]),
            product_classes: vec![Box::from([GraphNode::Definition(DefinitionId(COUNT + 2))])],
            owner_requirements: BTreeSet::new(),
            identity_cohort_root: None,
            output_demands: BTreeSet::new(),
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
        PendingMacroMaterializationGroup {
            producer: ExpansionId(0),
            products: BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT + 3))]),
            product_classes: vec![Box::from([GraphNode::Definition(DefinitionId(COUNT + 3))])],
            owner_requirements: BTreeSet::new(),
            identity_cohort_root: None,
            output_demands: BTreeSet::new(),
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ])
    .unwrap();
    assert_eq!(
        equal_contributor_groups.len(),
        2,
        "equal contributor values do not replace explicit group membership"
    );

    let left_product = GraphNode::Definition(DefinitionId(COUNT + 4));
    let right_product = GraphNode::Definition(DefinitionId(COUNT + 5));
    let independent_producers = lower_macro_materialization_groups(vec![
        PendingMacroMaterializationGroup {
            producer: ExpansionId(0),
            products: BTreeSet::from([left_product]),
            product_classes: vec![Box::from([left_product])],
            owner_requirements: BTreeSet::new(),
            identity_cohort_root: None,
            output_demands: BTreeSet::new(),
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
        PendingMacroMaterializationGroup {
            producer: ExpansionId(1),
            products: BTreeSet::from([right_product]),
            product_classes: vec![Box::from([right_product])],
            owner_requirements: BTreeSet::new(),
            identity_cohort_root: None,
            output_demands: BTreeSet::new(),
            contributor_roots: contributor_roots(vec![SourceUnitId(2)]),
        },
    ])
    .unwrap();
    let independent_producers =
        ValidatedMacroProducts::new(independent_producers, BTreeSet::new()).unwrap();
    let mut one_required = BTreeSet::from([left_product]);
    let mut one_retained = BTreeSet::new();
    close_validated_retention_constraints(
        &independent_producers,
        None,
        &mut one_required,
        &mut one_retained,
    );
    assert_eq!(one_retained, BTreeSet::from([SourceUnitId(1)]));
    assert!(!one_required.contains(&right_product));

    let mut duplicate = materializations;
    duplicate.push(MacroMaterialization {
        producer: ExpansionId(COUNT),
        products: vec![GraphNode::Definition(DefinitionId(0))],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(COUNT)]),
    });
    assert!(matches!(
        ValidatedMacroProducts::new(duplicate.clone(), BTreeSet::new()),
        Err(RetentionError::InvalidConstraint)
    ));
    duplicate[1].products.clear();
    duplicate[1].owner_requirements.clear();
    assert!(matches!(
        ValidatedMacroProducts::new(duplicate[1..].to_vec(), BTreeSet::new()),
        Err(RetentionError::InvalidConstraint)
    ));
    duplicate[1].products = vec![
        GraphNode::Definition(DefinitionId(1)),
        GraphNode::Definition(DefinitionId(1)),
    ];
    assert!(matches!(
        ValidatedMacroProducts::new(duplicate[1..].to_vec(), BTreeSet::new()),
        Err(RetentionError::InvalidConstraint)
    ));
}

#[test]
fn shared_identity_gate_is_atomic_without_replacing_local_provenance() {
    let sources = [SourceUnitId(0), SourceUnitId(1)];
    let (dag, identity_root) = MacroContributorDag::test_source_union(&sources);
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![GraphNode::Definition(DefinitionId(0))],
            owner_requirements: Vec::new(),
            contributor_roots: contributor_roots(vec![sources[0]]),
            identity_cohort_root: Some(identity_root),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Definition(DefinitionId(1))],
            owner_requirements: Vec::new(),
            contributor_roots: contributor_roots(vec![sources[1]]),
            identity_cohort_root: Some(identity_root),
        },
    ];
    let macro_products = ValidatedMacroProducts::new_with_dag(
        Arc::new(dag),
        sources.len(),
        materializations,
        BTreeSet::new(),
    )
    .unwrap();

    assert_eq!(
        macro_products.contributor_class_for_group(0),
        macro_products.contributor_class_for_group(1),
        "rank calculation must share the one gate instead of flattening it per group",
    );

    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(0))]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(retained_units, BTreeSet::from(sources));
    assert_eq!(
        compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
        ])
    );

    compile_required.clear();
    retained_units = BTreeSet::from(sources);
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(
        compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
        ])
    );

    compile_required.clear();
    retained_units = BTreeSet::from([sources[0]]);
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert!(compile_required.is_empty());
}

#[test]
fn independent_macro_groups_and_rank_queries_visit_only_reachable_dag_facts() {
    const COUNT: u32 = 1_024;
    let source = "x".repeat(COUNT as usize);
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, COUNT), None, 0)];
    units.extend((1..COUNT).map(|id| unit(id, WrittenUnitKind::Item, (id - 1, id), Some(0), id)));
    let inventory = inventory(&source, units.clone());
    let mut definitions = vec![written_definition(
        0,
        DefinitionKind::Crate,
        &units[0],
        None,
        "crate",
    )];
    definitions.extend((1..COUNT).map(|id| {
        written_definition(
            id,
            DefinitionKind::Function,
            &units[id as usize],
            Some(0),
            if id + 1 == COUNT { "main" } else { "item" },
        )
    }));
    let graph = graph(definitions, Vec::new());
    let macro_products = ValidatedMacroProducts::new(
        (0..COUNT)
            .map(|index| MacroMaterialization {
                producer: ExpansionId(index),
                products: vec![GraphNode::Definition(DefinitionId(index))],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: contributor_roots(vec![SourceUnitId(index)]),
            })
            .collect(),
        BTreeSet::new(),
    )
    .unwrap();
    let mut rank_cache = MacroProductRankCache::default();
    let singleton_units = vec![None; COUNT as usize];
    for definition in 0..COUNT {
        definition_choice_rank(
            &inventory,
            &graph,
            &singleton_units,
            &macro_products,
            &mut rank_cache,
            DefinitionId(definition),
        )
        .unwrap();
    }

    assert_eq!(rank_cache.contributor_classes.len(), COUNT as usize);
    assert_eq!(rank_cache.rank_queries, COUNT as usize);
    assert_eq!(rank_cache.contributor_class_misses, COUNT as usize);
    assert_eq!(rank_cache.dag_node_visits, COUNT as usize);
}

#[test]
fn shared_deep_macro_rank_is_materialized_once_for_many_groups_and_choices() {
    const DEPTH: u32 = 1_024;
    const CHOICES: u32 = 1_024;
    let source = "x".repeat(DEPTH as usize);
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, DEPTH), None, 0)];
    units.extend((1..DEPTH).map(|id| unit(id, WrittenUnitKind::Item, (id - 1, id), Some(0), id)));
    let inventory = inventory(&source, units.clone());
    let mut definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
    ];
    definitions.extend((0..CHOICES).map(|choice| {
        expanded_definition(
            choice + 2,
            DefinitionKind::Function,
            &units[1],
            Some(0),
            "generated",
        )
    }));
    let graph = graph(definitions, Vec::new());
    let (dag, root) = crate::expansions::MacroContributorDag::test_source_chain(DEPTH);
    let macro_products = ValidatedMacroProducts::new_with_dag(
        Arc::new(dag),
        DEPTH as usize,
        (0..CHOICES)
            .map(|choice| MacroMaterialization {
                producer: ExpansionId(choice),
                products: vec![GraphNode::Definition(DefinitionId(choice + 2))],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: vec![root].into_boxed_slice(),
            })
            .collect(),
        BTreeSet::new(),
    )
    .unwrap();
    let mut rank_cache = MacroProductRankCache::default();
    let singleton_units = vec![None; graph.definitions.definitions.len()];
    for choice in 0..CHOICES {
        let (_, ranges, _) = definition_choice_rank(
            &inventory,
            &graph,
            &singleton_units,
            &macro_products,
            &mut rank_cache,
            DefinitionId(choice + 2),
        )
        .unwrap();
        assert_eq!(ranges.len(), DEPTH as usize);
    }

    assert_eq!(rank_cache.contributor_classes.len(), 1);
    assert_eq!(rank_cache.rank_queries, CHOICES as usize);
    assert_eq!(rank_cache.contributor_class_misses, 1);
    assert_eq!(rank_cache.dag_node_visits, DEPTH as usize);
}

#[test]
fn independent_macro_producers_validate_only_their_reachable_dag_facts() {
    const COUNT: u32 = 1_024;
    let source = "x".repeat(COUNT as usize + 2);
    let mut units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, COUNT + 2), None, 0),
        unit(1, WrittenUnitKind::MacroRule, (0, 1), Some(0), 1),
    ];
    units.extend((0..COUNT).map(|producer| {
        let id = producer + 2;
        unit(
            id,
            WrittenUnitKind::MacroInvocation,
            (id - 1, id),
            Some(0),
            id,
        )
    }));
    let inventory = inventory(&source, units.clone());
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[0], Some(0), "main"),
        ],
        Vec::new(),
    );
    graph.expansions = (0..COUNT)
        .map(|producer| {
            test_expansion_node(producer, Some(SourceUnitId(producer + 2)), None, None, None)
        })
        .collect();
    let selected_rules = (0..COUNT)
        .map(|producer| (ExpansionId(producer), SourceUnitId(1)))
        .collect::<BTreeMap<_, _>>();
    let refined = (0..COUNT).map(ExpansionId).collect::<BTreeSet<_>>();
    let macro_products = ValidatedMacroProducts::new(
        (0..COUNT)
            .map(|producer| MacroMaterialization {
                producer: ExpansionId(producer),
                products: vec![GraphNode::Expansion(ExpansionId(producer))],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: contributor_roots(vec![
                    SourceUnitId(1),
                    SourceUnitId(producer + 2),
                ]),
            })
            .collect(),
        BTreeSet::new(),
    )
    .unwrap();

    let stats = validate_macro_contributor_provenance_with_stats(
        &inventory,
        macro_graph(&graph),
        &refined,
        &selected_rules,
        &macro_products,
    )
    .unwrap();

    assert_eq!(stats.producer_visits, COUNT as usize);
    assert_eq!(stats.materialization_visits, COUNT as usize);
    assert_eq!(stats.dag_node_visits, 2 * COUNT as usize);
}

#[test]
fn compiler_closure_delegates_only_refined_classified_macro_expansions() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let refined_child = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[refined_child.0 as usize].fragment = Some(ExpansionFragmentKind::Expression);
    graph.expansions[refined_child.0 as usize].key.0[0].fragment =
        Some(ExpansionFragmentKind::Expression);
    let opaque_child = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[opaque_child.0 as usize].fragment = Some(ExpansionFragmentKind::Statements);
    graph.expansions[opaque_child.0 as usize].implementation =
        Some(MacroImplementationKind::Builtin);
    graph.expansions[opaque_child.0 as usize].key.0[0].fragment =
        Some(ExpansionFragmentKind::Statements);
    graph.expansions[opaque_child.0 as usize].key.0[0].implementation =
        Some(MacroImplementationKind::Builtin);
    let root = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    let mut retained = BTreeSet::from([SourceUnitId(2)]);

    let ordinary = close_compiler_reachability(
        &graph,
        &inventory,
        &retained,
        &BTreeSet::new(),
        root.clone(),
    )
    .unwrap();
    assert!(ordinary.contains(&GraphNode::Expansion(refined_child)));
    assert!(ordinary.contains(&GraphNode::Expansion(opaque_child)));

    let mut delegated = close_compiler_reachability(
        &graph,
        &inventory,
        &retained,
        &BTreeSet::from([refined_child]),
        root,
    )
    .unwrap();
    assert!(!delegated.contains(&GraphNode::Expansion(refined_child)));
    assert!(
        delegated.contains(&GraphNode::Expansion(opaque_child)),
        "an unrefined built-in child keeps its ordinary ExpansionUse carrier"
    );

    let materialization = MacroMaterialization {
        producer: ExpansionId(1),
        products: vec![GraphNode::Expansion(refined_child)],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(1), SourceUnitId(2)]),
    };
    let macro_products =
        ValidatedMacroProducts::new(vec![materialization], BTreeSet::new()).unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut actual_required = delegated.clone();
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained_units = Vec::new();
    closure
        .seed(&delegated, &actual_required, &retained)
        .unwrap();
    closure.close(
        &mut delegated,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained,
        &mut newly_retained_units,
    );
    assert!(!delegated.contains(&GraphNode::Expansion(refined_child)));
    assert!(delegated.contains(&GraphNode::Expansion(opaque_child)));

    retained.insert(SourceUnitId(1));
    closure.add_source([SourceUnitId(1)]);
    closure.close(
        &mut delegated,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained,
        &mut newly_retained_units,
    );
    assert!(delegated.contains(&GraphNode::Expansion(refined_child)));
    assert!(delegated.contains(&GraphNode::Expansion(opaque_child)));
}

#[test]
fn macro_classification_delegates_only_refined_or_directly_empty_expansions() {
    let graph = complete_macro_meaning_graph(&[None, Some(0), Some(1)]);
    let inventory = MacroCompleteOutputMeaningInventory::test_new(vec![
        complete_meaning_with_source_owner(
            ExpansionId(0),
            false,
            vec![ExpansionId(1)],
            DefinitionId(1),
        ),
        complete_meaning_with_source_owner(
            ExpansionId(1),
            false,
            vec![ExpansionId(2)],
            DefinitionId(1),
        ),
    ]);
    let outputless = BTreeSet::from([ExpansionId(2)]);
    let meaning =
        validate_complete_macro_output_meaning(macro_graph(&graph), &inventory, &outputless)
            .unwrap();
    let refined = BTreeSet::from([ExpansionId(0)]);
    let classification = MacroProducerClassification::new(&refined, &meaning);

    assert!(classification.delegates_expansion_use(ExpansionId(0)));
    assert!(classification.delegates_expansion_use(ExpansionId(2)));
    assert!(
        !classification.delegates_expansion_use(ExpansionId(1)),
        "a complete meaning census alone cannot replace precise source materialization",
    );
}

#[test]
fn partial_tied_site_is_rejected_only_after_its_source_node_becomes_reachable() {
    let (inventory, definitions, tied_site, _) = tied_source_site_reachability_fixture();
    let graph = graph(
        definitions,
        vec![DependencyEdge {
            from: GraphNode::Definition(DefinitionId(1)),
            to: GraphNode::Definition(DefinitionId(0)),
            kind: DependencyKind::Definition(DefinitionDependencyKind::ValuePath),
            sites: vec![ObservationSite::Source(tied_site)],
            evidence: EvidenceOrigin::Compiler,
        }],
    );
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index = CompilerReachabilityIndex::new(&inventory, &source_sites, &graph, &BTreeSet::new())
        .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::new();
    closure
        .seed(&reachable, &BTreeSet::from([SourceUnitId(2)]))
        .unwrap();
    assert_eq!(closure.close(&mut reachable, &mut Vec::new()), Ok(()));

    reachable.insert(GraphNode::Definition(DefinitionId(1)));
    closure.add_reachable([GraphNode::Definition(DefinitionId(1))]);
    assert_eq!(
        closure.close(&mut reachable, &mut Vec::new()),
        Err(RetentionError::InvalidGraph),
        "a reachable conditional edge must reject disagreement between tied source owners",
    );
}

#[test]
fn partial_tied_site_waits_for_the_target_expansion_component_gate() {
    let (inventory, definitions, tied_site, _) = tied_source_site_reachability_fixture();
    let mut graph = graph(
        definitions,
        vec![DependencyEdge {
            from: GraphNode::Definition(DefinitionId(1)),
            to: GraphNode::Expansion(ExpansionId(0)),
            kind: DependencyKind::ExpansionUse,
            sites: vec![ObservationSite::Source(tied_site)],
            evidence: EvidenceOrigin::Compiler,
        }],
    );
    graph.expansions = vec![test_expansion_node(
        0,
        Some(SourceUnitId(4)),
        None,
        None,
        None,
    )];
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index = CompilerReachabilityIndex::new(&inventory, &source_sites, &graph, &BTreeSet::new())
        .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    closure
        .seed(&reachable, &BTreeSet::from([SourceUnitId(2)]))
        .unwrap();
    assert_eq!(closure.close(&mut reachable, &mut Vec::new()), Ok(()));
    assert!(!reachable.contains(&GraphNode::Expansion(ExpansionId(0))));

    closure.add_sources([SourceUnitId(4)]).unwrap();
    assert_eq!(
        closure.close(&mut reachable, &mut Vec::new()),
        Err(RetentionError::InvalidGraph),
        "the partial site is evaluated once the target component can survive",
    );
}

#[test]
fn one_open_source_site_satisfies_an_edge_even_when_an_alternative_is_partial() {
    let (inventory, definitions, tied_site, open_site) = tied_source_site_reachability_fixture();
    let graph = graph(
        definitions,
        vec![DependencyEdge {
            from: GraphNode::Definition(DefinitionId(1)),
            to: GraphNode::Definition(DefinitionId(0)),
            kind: DependencyKind::Definition(DefinitionDependencyKind::ValuePath),
            sites: vec![
                ObservationSite::Source(tied_site),
                ObservationSite::Source(open_site),
            ],
            evidence: EvidenceOrigin::Compiler,
        }],
    );
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index = CompilerReachabilityIndex::new(&inventory, &source_sites, &graph, &BTreeSet::new())
        .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    closure
        .seed(
            &reachable,
            &BTreeSet::from([SourceUnitId(2), SourceUnitId(4)]),
        )
        .unwrap();

    assert_eq!(closure.close(&mut reachable, &mut Vec::new()), Ok(()));
    assert!(reachable.contains(&GraphNode::Definition(DefinitionId(0))));
}

#[test]
fn compiler_reachability_preserves_expansion_scc_greatest_fixed_point() {
    let source = "x".repeat(32);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::MacroInvocation, (1, 2), Some(0), 1),
    ];
    let inventory = inventory(&source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[0], Some(0), "main"),
    ];
    let root = GraphNode::Definition(DefinitionId(1));

    let mut source_free = graph(
        definitions.clone(),
        vec![compiler_expansion_use(DefinitionId(1), ExpansionId(0))],
    );
    source_free.expansions = vec![
        test_expansion_node(0, None, Some(1), None, None),
        test_expansion_node(1, None, None, Some(0), None),
    ];
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index =
        CompilerReachabilityIndex::new(&inventory, &source_sites, &source_free, &BTreeSet::new())
            .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([root]);
    closure.seed(&reachable, &BTreeSet::new()).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    assert!(
        reachable.contains(&GraphNode::Expansion(ExpansionId(0))),
        "a source-free cycle formed by distinct parent relations is a surviving SCC",
    );

    let mut written_cycle = source_free.clone();
    written_cycle.expansions[0].written_invocation = Some(SourceUnitId(1));
    let index =
        CompilerReachabilityIndex::new(&inventory, &source_sites, &written_cycle, &BTreeSet::new())
            .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([root]);
    closure.seed(&reachable, &BTreeSet::new()).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    assert!(!reachable.contains(&GraphNode::Expansion(ExpansionId(0))));
    closure.add_sources([SourceUnitId(1)]).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    assert!(
        reachable.contains(&GraphNode::Expansion(ExpansionId(0))),
        "one written gate controls every member of its SCC",
    );

    let mut external_parent = graph(
        definitions,
        vec![compiler_expansion_use(DefinitionId(1), ExpansionId(0))],
    );
    external_parent.expansions = vec![
        test_expansion_node(0, None, Some(1), Some(2), None),
        test_expansion_node(1, None, None, Some(0), None),
        test_expansion_node(2, Some(SourceUnitId(1)), None, None, None),
    ];
    let index = CompilerReachabilityIndex::new(
        &inventory,
        &source_sites,
        &external_parent,
        &BTreeSet::new(),
    )
    .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([root]);
    closure.seed(&reachable, &BTreeSet::new()).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    assert!(!reachable.contains(&GraphNode::Expansion(ExpansionId(0))));
    closure.add_sources([SourceUnitId(1)]).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    assert!(
        reachable.contains(&GraphNode::Expansion(ExpansionId(0))),
        "an external parent component propagates survival to the whole child SCC",
    );
}

#[test]
fn compiler_reachability_visits_nodes_edges_and_sites_once_per_gate() {
    const COUNT: u32 = 1_024;
    let source = "x".repeat(COUNT as usize);
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, COUNT), None, 0)];
    units.extend((1..=COUNT).map(|id| unit(id, WrittenUnitKind::Item, (id - 1, id), Some(0), id)));
    let inventory = inventory(&source, units.clone());
    let mut definitions = vec![written_definition(
        0,
        DefinitionKind::Crate,
        &units[0],
        None,
        "crate",
    )];
    definitions.extend((1..=COUNT).map(|id| {
        written_definition(
            id,
            DefinitionKind::Function,
            &units[id as usize],
            Some(0),
            if id == COUNT { "main" } else { "item" },
        )
    }));
    let edges = (2..=COUNT)
        .map(|from| DependencyEdge {
            from: GraphNode::Definition(DefinitionId(from)),
            to: GraphNode::Definition(DefinitionId(from - 1)),
            kind: DependencyKind::Definition(DefinitionDependencyKind::ValuePath),
            sites: vec![ObservationSite::Source(
                units[(from - 1) as usize].full_range,
            )],
            evidence: EvidenceOrigin::Compiler,
        })
        .collect::<Vec<_>>();
    let graph = graph(definitions, edges);
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let index = CompilerReachabilityIndex::new(&inventory, &source_sites, &graph, &BTreeSet::new())
        .unwrap();
    let mut closure = CompilerReachabilityClosure::new(&index);
    let mut reachable = BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT))]);
    closure.seed(&reachable, &BTreeSet::new()).unwrap();
    closure.close(&mut reachable, &mut Vec::new()).unwrap();
    for source in (1..COUNT).rev() {
        closure.add_sources([SourceUnitId(source)]).unwrap();
        closure.close(&mut reachable, &mut Vec::new()).unwrap();
    }

    assert_eq!(reachable.len(), COUNT as usize);
    assert_eq!(closure.node_visits, COUNT as usize);
    assert_eq!(closure.site_owner_visits, COUNT as usize - 1);
    assert_eq!(closure.edge_visits, (COUNT as usize - 1) * 2);
    assert_eq!(closure.component_fact_visits, 0);
}

#[test]
fn macro_owner_requirement_keeps_contributors_and_materializes_members() {
    let member = GraphNode::Definition(DefinitionId(2));
    let owner = DefinitionId(1);
    let materialization = MacroMaterialization {
        producer: ExpansionId(0),
        products: Vec::new(),
        owner_requirements: vec![MacroOwnerRequirement {
            owner,
            members: vec![DefinitionId(2)],
            effect: MacroOwnerEffect::Semantic,
        }],
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(2)]),
    };
    let macro_products =
        ValidatedMacroProducts::new(vec![materialization], BTreeSet::new()).unwrap();
    let mut compile_required = BTreeSet::new();
    let mut retained_units = BTreeSet::from([SourceUnitId(2)]);

    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert!(!compile_required.contains(&GraphNode::Definition(owner)));
    assert!(!compile_required.contains(&member));

    compile_required = BTreeSet::from([member]);
    retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(2)]));
    assert!(!compile_required.contains(&GraphNode::Definition(owner)));

    compile_required = BTreeSet::from([GraphNode::Definition(owner)]);
    retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(2)]));
    assert!(compile_required.contains(&member));
}

#[test]
fn transparent_owner_shell_uses_the_same_product_dependency_for_meaning_and_source() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(0),
            products: Vec::new(),
            owner_requirements: vec![MacroOwnerRequirement {
                owner: DefinitionId(0),
                members: Vec::new(),
                effect: MacroOwnerEffect::TransparentShell {
                    dependent_products: vec![child],
                },
            }],
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: Vec::new(),
            owner_requirements: vec![MacroOwnerRequirement {
                owner: DefinitionId(1),
                members: Vec::new(),
                effect: MacroOwnerEffect::Semantic,
            }],
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(2)]),
        },
    ];
    let producers = BTreeSet::from([ExpansionId(0), ExpansionId(1)]);
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();

    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(0))]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert!(
        retained_units.is_empty(),
        "the owner alone does not open a proven shell"
    );

    compile_required = BTreeSet::from([child]);
    retained_units = BTreeSet::from([SourceUnitId(2)]);
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(
        retained_units,
        BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)]),
        "one meaningful child opens both its product syntax and transparent shell"
    );
    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &retained_units).unwrap(),
        BTreeSet::new()
    );
}

#[test]
fn transparent_owner_shell_follows_a_definition_product_without_becoming_intrinsic() {
    let definition = GraphNode::Definition(DefinitionId(2));
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![definition],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(0),
            products: Vec::new(),
            owner_requirements: vec![MacroOwnerRequirement {
                owner: DefinitionId(0),
                members: Vec::new(),
                effect: MacroOwnerEffect::TransparentShell {
                    dependent_products: vec![definition],
                },
            }],
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ];
    let macro_products = ValidatedMacroProducts::new(materializations, BTreeSet::new()).unwrap();

    let mut compile_required = BTreeSet::from([definition]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(
        retained_units,
        BTreeSet::from([SourceUnitId(0), SourceUnitId(1)])
    );
    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &retained_units).unwrap(),
        BTreeSet::new()
    );
    assert_eq!(
        outputless_macro_expansions_after_rewrite(
            &macro_products,
            &BTreeSet::from([SourceUnitId(1)])
        )
        .unwrap(),
        BTreeSet::from([ExpansionId(0)]),
        "a shell without its definition dependency is not meaningful"
    );
}

#[test]
fn transparent_owner_shell_rejects_unclassified_members_and_dependencies() {
    let transparent = |members, dependent_products| MacroMaterialization {
        producer: ExpansionId(0),
        products: Vec::new(),
        owner_requirements: vec![MacroOwnerRequirement {
            owner: DefinitionId(0),
            members,
            effect: MacroOwnerEffect::TransparentShell { dependent_products },
        }],
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
    };

    assert!(matches!(
        ValidatedMacroProducts::new(
            vec![transparent(
                vec![DefinitionId(1)],
                vec![GraphNode::Definition(DefinitionId(1))]
            )],
            BTreeSet::new()
        ),
        Err(RetentionError::InvalidConstraint)
    ));
    assert!(matches!(
        ValidatedMacroProducts::new(
            vec![transparent(
                Vec::new(),
                vec![GraphNode::Definition(DefinitionId(1))]
            )],
            BTreeSet::new()
        ),
        Err(RetentionError::InvalidConstraint)
    ));
}

#[test]
fn only_validated_outputless_macro_facts_are_excluded() {
    let source = "x".repeat(80);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 80), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::MacroDefinition, (21, 70), Some(0), 3),
        unit(4, WrittenUnitKind::MacroRule, (30, 69), Some(3), 4),
        unit(5, WrittenUnitKind::NestedItem, (40, 50), Some(4), 5),
    ];
    let mut inventory = inventory(&source, units.clone());
    inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(3),
        rules: vec![SourceUnitId(4)],
        observed_selections: vec![SourceUnitId(4)],
    }];
    inventory.macro_templates = vec![MacroTemplateSourceFacts {
        unit: SourceUnitId(5),
        rule: SourceUnitId(4),
    }];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Macro, &units[3], Some(0), "m"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let producer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[producer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(2)));
    graph.expansions[producer.0 as usize].key.0[0].macro_definition = Some(
        DefinitionReferenceKey::Local(graph.definitions.definitions[2].key.clone()),
    );
    graph.expansions[producer.0 as usize].key.0[0].selected_macro_rule = Some(units[4].full_range);
    graph.edges.push(DependencyEdge {
        from: GraphNode::Expansion(producer),
        to: GraphNode::Definition(DefinitionId(2)),
        kind: DependencyKind::MacroDefinition,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });

    assert_eq!(
        compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints),
        "a split source needs either output coverage or a direct-empty fact",
    );

    let mut structurally_empty = complete_constraints(&inventory, &graph);
    *outputless_mut(&mut structurally_empty) = vec![producer];
    assert_eq!(
        compute_retention(&inventory, &graph, &structurally_empty)
            .unwrap()
            .outputless_macro_expansions,
        BTreeSet::from([producer])
    );

    let mut empty = complete_constraints(&inventory, &graph);
    *coverage_mut(&mut empty) = vec![coverage(producer, 0, Vec::new())];
    *outputless_mut(&mut empty) = vec![producer];
    assert_eq!(
        compute_retention(&inventory, &graph, &empty),
        Err(RetentionError::InvalidConstraint),
        "direct empty output is a seed, not a zero-token materialization ledger",
    );

    let mut owner_effect = complete_constraints(&inventory, &graph);
    *coverage_mut(&mut owner_effect) = vec![coverage(
        producer,
        1,
        vec![owner_effect_group(
            vec![output_range(0, 1)],
            DefinitionId(1),
            vec![SourceUnitId(2), SourceUnitId(4)],
        )],
    )];
    set_complete_meaning(
        &mut owner_effect,
        vec![complete_meaning(
            producer,
            true,
            true,
            Vec::new(),
            vec![DefinitionId(1)],
            Vec::new(),
        )],
    );
    assert!(
        compute_retention(&inventory, &graph, &owner_effect)
            .unwrap()
            .outputless_macro_expansions
            .is_empty()
    );

    let mut inconsistent = owner_effect.clone();
    *outputless_mut(&mut inconsistent) = vec![producer];
    assert_eq!(
        compute_retention(&inventory, &graph, &inconsistent),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn macro_definition_classes_follow_the_nearest_root_or_source_owner() {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "first"),
            expanded_definition(3, DefinitionKind::Closure, &units[2], Some(2), "closure"),
            expanded_definition(4, DefinitionKind::Function, &units[2], Some(0), "second"),
            expanded_definition(
                5,
                DefinitionKind::AnonymousConst,
                &units[2],
                Some(1),
                "owner_member",
            ),
        ],
        vec![],
    );
    let producer = add_macro_expansion(
        &mut graph,
        &units[2],
        DefinitionId(1),
        (2..=5).map(DefinitionId),
    );
    let first_class = vec![
        GraphNode::Definition(DefinitionId(2)),
        GraphNode::Definition(DefinitionId(3)),
    ];
    let owner_members = vec![GraphNode::Definition(DefinitionId(5))];
    let macro_producers = DefinitionMacroProducerIndex::new(macro_graph(&graph));

    assert_eq!(
        validate_macro_definition_product_class(
            macro_graph(&graph),
            &macro_producers,
            producer,
            &first_class,
        ),
        Ok(())
    );
    assert_eq!(
        validate_macro_owner_effect_members(
            macro_graph(&graph),
            &macro_producers,
            producer,
            DefinitionId(1),
            &owner_members,
        ),
        Ok(vec![DefinitionId(5)])
    );

    let mut different_root = graph.clone();
    different_root.definitions.definitions[3].parent = Some(DefinitionId(4));
    let different_root_producers = DefinitionMacroProducerIndex::new(macro_graph(&different_root));
    assert_eq!(
        validate_macro_definition_product_class(
            macro_graph(&different_root),
            &different_root_producers,
            producer,
            &first_class,
        ),
        Err(RetentionError::InvalidConstraint)
    );
    let second_class = vec![
        GraphNode::Definition(DefinitionId(3)),
        GraphNode::Definition(DefinitionId(4)),
    ];
    assert_eq!(
        validate_macro_definition_product_class(
            macro_graph(&different_root),
            &different_root_producers,
            producer,
            &second_class,
        ),
        Ok(())
    );

    let owner_in_products = vec![
        GraphNode::Definition(DefinitionId(2)),
        GraphNode::Definition(DefinitionId(5)),
    ];
    assert_eq!(
        validate_macro_definition_product_class(
            macro_graph(&graph),
            &macro_producers,
            producer,
            &owner_in_products,
        ),
        Err(RetentionError::InvalidConstraint)
    );

    let rooted_in_owner = vec![
        GraphNode::Definition(DefinitionId(3)),
        GraphNode::Definition(DefinitionId(5)),
    ];
    assert_eq!(
        validate_macro_owner_effect_members(
            macro_graph(&graph),
            &macro_producers,
            producer,
            DefinitionId(1),
            &rooted_in_owner,
        ),
        Err(RetentionError::InvalidConstraint)
    );
    assert_eq!(
        validate_macro_owner_effect_members(
            macro_graph(&graph),
            &macro_producers,
            producer,
            DefinitionId(1),
            &[
                GraphNode::Definition(DefinitionId(5)),
                GraphNode::Definition(DefinitionId(5)),
            ],
        ),
        Err(RetentionError::InvalidConstraint)
    );

    let mut cross_producer = different_root;
    let other = add_macro_expansion(&mut cross_producer, &units[2], DefinitionId(1), []);
    let edge = cross_producer
        .edges
        .iter_mut()
        .find(|edge| {
            edge.from == GraphNode::Definition(DefinitionId(4))
                && edge.kind == DependencyKind::GeneratedBy
        })
        .unwrap();
    edge.to = GraphNode::Expansion(other);
    let cross_producer_index = DefinitionMacroProducerIndex::new(macro_graph(&cross_producer));
    assert_eq!(
        validate_macro_definition_product_class(
            macro_graph(&cross_producer),
            &cross_producer_index,
            producer,
            &second_class,
        ),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn definition_macro_producer_index_resolves_shared_parent_chains_once() {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let mut definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "root"),
    ];
    for id in 3..1027 {
        definitions.push(compiler_generated_definition(id, id - 1));
    }
    let mut graph = graph(definitions, vec![]);
    let producer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), [DefinitionId(2)]);

    let index = DefinitionMacroProducerIndex::new(macro_graph(&graph));
    for id in 2..1027 {
        assert_eq!(index.producer(DefinitionId(id)), Ok(producer));
    }
    assert_eq!(
        index.parent(producer, DefinitionId(1026)),
        Ok(MacroDefinitionParent::Root(DefinitionId(2)))
    );
}

#[test]
fn definition_macro_producer_index_preserves_fail_closed_boundaries() {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "root"),
        compiler_generated_definition(3, 2),
        compiler_generated_definition(4, 3),
        injected_definition(5, 4),
    ];
    let mut graph = graph(definitions, vec![]);
    let producer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), [DefinitionId(2)]);
    let generated_by = graph
        .edges
        .iter()
        .find(|edge| {
            edge.from == GraphNode::Definition(DefinitionId(2))
                && edge.kind == DependencyKind::GeneratedBy
        })
        .unwrap()
        .clone();

    let mut duplicate = graph.clone();
    duplicate.edges.push(generated_by.clone());
    let index = DefinitionMacroProducerIndex::new(macro_graph(&duplicate));
    assert_eq!(index.producer(DefinitionId(5)), Ok(producer));

    let mut ambiguous = graph.clone();
    let other = add_macro_expansion(&mut ambiguous, &units[2], DefinitionId(1), []);
    ambiguous.edges.push(DependencyEdge {
        to: GraphNode::Expansion(other),
        ..generated_by.clone()
    });
    assert_eq!(
        DefinitionMacroProducerIndex::new(macro_graph(&ambiguous)).producer(DefinitionId(2)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut non_expansion = graph.clone();
    non_expansion
        .edges
        .iter_mut()
        .find(|edge| {
            edge.from == GraphNode::Definition(DefinitionId(2))
                && edge.kind == DependencyKind::GeneratedBy
        })
        .unwrap()
        .to = GraphNode::Definition(DefinitionId(0));
    assert_eq!(
        DefinitionMacroProducerIndex::new(macro_graph(&non_expansion)).producer(DefinitionId(2)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut missing = graph.clone();
    missing.edges.retain(|edge| {
        edge.from != GraphNode::Definition(DefinitionId(2))
            || edge.kind != DependencyKind::GeneratedBy
    });
    assert_eq!(
        DefinitionMacroProducerIndex::new(macro_graph(&missing)).producer(DefinitionId(3)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut missing_parent = graph.clone();
    missing_parent.definitions.definitions[3].parent = None;
    assert_eq!(
        DefinitionMacroProducerIndex::new(macro_graph(&missing_parent)).producer(DefinitionId(3)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut non_expanded_parent = graph.clone();
    non_expanded_parent.definitions.definitions[3].parent = Some(DefinitionId(1));
    assert_eq!(
        DefinitionMacroProducerIndex::new(macro_graph(&non_expanded_parent))
            .producer(DefinitionId(3)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut cycle = graph;
    cycle.definitions.definitions[3].parent = Some(DefinitionId(4));
    cycle.definitions.definitions[4].parent = Some(DefinitionId(3));
    let index = DefinitionMacroProducerIndex::new(macro_graph(&cycle));
    assert_eq!(
        index.producer(DefinitionId(3)),
        Err(RetentionError::InvalidGraph)
    );
    assert_eq!(
        index.parent(producer, DefinitionId(4)),
        Err(RetentionError::InvalidGraph)
    );
    assert_eq!(
        index.producer(DefinitionId(1)),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );
}

#[test]
fn macro_products_use_the_immediate_observed_macro_parent() {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![],
    );
    let outer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let immediate = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let child = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let ast_pass = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[ast_pass.0 as usize].kind =
        ExpansionKind::AstPass(AstPassKind::StandardImports);

    graph.expansions[child.0 as usize].discovered_in = Some(immediate);
    graph.expansions[child.0 as usize].source_call_parent = Some(outer);
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Ok(Some(immediate))
    );

    graph.expansions[child.0 as usize].discovered_in = Some(outer);
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Ok(Some(outer))
    );

    graph.expansions[child.0 as usize].discovered_in = None;
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Ok(Some(outer))
    );

    graph.expansions[child.0 as usize].discovered_in = Some(ast_pass);
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Ok(None),
        "a recorded non-macro discovery parent is authoritative; the source-call relation is not a fallback"
    );

    graph.expansions[child.0 as usize].discovered_in = Some(ExpansionId(99));
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Err(RetentionError::InvalidGraph)
    );

    graph.expansions[child.0 as usize].discovered_in = Some(child);
    assert_eq!(
        immediate_macro_parent(macro_graph(&graph), &graph.expansions[child.0 as usize]),
        Err(RetentionError::InvalidGraph)
    );
}

#[test]
fn macro_provenance_parent_is_independent_of_the_editable_anchor() {
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
    ];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![],
    );
    let outer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let child = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);

    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[outer.0 as usize],
            &BTreeSet::from([outer]),
        ),
        Ok(None),
        "an anchored producer without a refined parent is a provenance root"
    );

    graph.expansions[outer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(1)));
    graph.expansions[child.0 as usize].written_invocation = None;
    graph.expansions[child.0 as usize].source_call_parent = Some(outer);
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([outer, child]),
        ),
        Ok(Some(outer)),
        "a generated child inherits its refined producer"
    );

    graph.expansions[child.0 as usize].written_invocation = Some(units[2].id);
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([outer, child]),
        ),
        Ok(Some(outer)),
        "an indivisible anchor does not erase an observed refined parent"
    );

    graph.expansions[outer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(1)));
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints),
        "a missing local-parent ledger does not turn the child anchor into a root"
    );

    graph.expansions[outer.0 as usize].macro_definition = None;
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints),
        "an unclassified declarative parent is not assumed to be external"
    );

    graph.expansions[outer.0 as usize].implementation = None;
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints),
        "a macro parent with an unknown implementation is not an opaque boundary"
    );
    graph.expansions[outer.0 as usize].implementation = Some(MacroImplementationKind::Declarative);

    graph.expansions[outer.0 as usize].macro_definition =
        Some(DefinitionTarget::External(ExternalDefinitionId(0)));
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Ok(None),
        "an external parent stops at the indivisible written anchor"
    );

    graph.expansions[outer.0 as usize].kind = ExpansionKind::AstPass(AstPassKind::StandardImports);
    graph.expansions[outer.0 as usize].implementation = None;
    graph.expansions[outer.0 as usize].macro_definition = None;
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Ok(None),
        "a recorded non-macro parent is an opaque boundary at the written anchor"
    );

    graph.expansions[child.0 as usize].written_invocation = None;
    graph.expansions[child.0 as usize].source_call_parent = None;
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    graph.expansions[child.0 as usize].source_call_parent = Some(child);
    assert_eq!(
        macro_contributor_provenance_parent(
            macro_graph(&graph),
            &graph.expansions[child.0 as usize],
            &BTreeSet::from([child]),
        ),
        Err(RetentionError::InvalidGraph)
    );
}

#[test]
fn owner_effect_contributors_can_materialize_an_item_expansion() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let materialization = MacroMaterialization {
        producer: ExpansionId(0),
        products: vec![child],
        owner_requirements: vec![MacroOwnerRequirement {
            owner: DefinitionId(1),
            members: Vec::new(),
            effect: MacroOwnerEffect::Semantic,
        }],
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(2), SourceUnitId(3)]),
    };
    let macro_products =
        ValidatedMacroProducts::new(vec![materialization], BTreeSet::new()).unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    let mut retained_units = BTreeSet::new();

    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert_eq!(
        retained_units,
        BTreeSet::from([SourceUnitId(2), SourceUnitId(3)])
    );

    assert!(compile_required.contains(&child));
}

#[test]
fn producer_is_outputless_only_when_no_output_group_survives_the_rewrite() {
    let materialization =
        |producer: u32, product: u32, contributors: Vec<SourceUnitId>| MacroMaterialization {
            producer: ExpansionId(producer),
            products: vec![GraphNode::Definition(DefinitionId(product))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(contributors),
        };
    let materializations = vec![
        materialization(0, 0, vec![SourceUnitId(1), SourceUnitId(2)]),
        materialization(0, 1, vec![SourceUnitId(1), SourceUnitId(3)]),
        materialization(1, 2, vec![SourceUnitId(4)]),
    ];
    let macro_products = ValidatedMacroProducts::new(materializations, BTreeSet::new()).unwrap();
    let retained = BTreeSet::from([SourceUnitId(1), SourceUnitId(3)]);

    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &retained).unwrap(),
        BTreeSet::from([ExpansionId(1)]),
        "one surviving output group keeps the producer observable"
    );
}

#[test]
fn control_only_macro_products_are_outputless_transitively_and_do_not_retain_their_sources() {
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![GraphNode::Expansion(ExpansionId(1))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Expansion(ExpansionId(2))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ];
    let producers = (0..=2).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();
    let retained = BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]);

    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &retained).unwrap(),
        BTreeSet::from([ExpansionId(0), ExpansionId(1), ExpansionId(2)])
    );

    let mut compile_required = BTreeSet::from([GraphNode::Expansion(ExpansionId(1))]);
    let mut retained_units = BTreeSet::new();
    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );
    assert!(retained_units.is_empty());
}

#[test]
fn materialized_outputless_child_stays_compile_only_without_reopening_its_contributors() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Definition(DefinitionId(0))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ];
    let producers = BTreeSet::from([ExpansionId(0), ExpansionId(1)]);
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut compile_required = BTreeSet::new();
    let mut actual_required = BTreeSet::new();
    let mut retained_units = BTreeSet::from([SourceUnitId(0)]);
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(compile_required.contains(&child));
    assert!(!compile_required.contains(&GraphNode::Definition(DefinitionId(0))));
    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(0)]));
}

#[test]
fn a_known_outputless_generated_child_delegates_its_use_and_keeps_its_rule_compile_only() {
    let source = "x".repeat(160);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 160), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 20), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (10, 19), Some(1), 1),
        unit(3, WrittenUnitKind::MacroDefinition, (21, 70), Some(0), 3),
        unit(4, WrittenUnitKind::MacroRule, (30, 69), Some(3), 4),
        unit(5, WrittenUnitKind::NestedItem, (40, 50), Some(4), 4),
        unit(6, WrittenUnitKind::MacroDefinition, (71, 120), Some(0), 6),
        unit(7, WrittenUnitKind::MacroRule, (80, 119), Some(6), 7),
    ];
    let mut inventory = inventory(&source, units.clone());
    inventory.macro_rules = vec![
        MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(3),
            rules: vec![SourceUnitId(4)],
            observed_selections: vec![SourceUnitId(4)],
        },
        MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(6),
            rules: vec![SourceUnitId(7)],
            observed_selections: vec![SourceUnitId(7)],
        },
    ];
    inventory.macro_templates = vec![MacroTemplateSourceFacts {
        unit: SourceUnitId(5),
        rule: SourceUnitId(4),
    }];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Macro, &units[3], Some(0), "outer"),
            written_definition(3, DefinitionKind::Macro, &units[6], Some(0), "inner"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let outer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[outer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(2)));
    graph.expansions[outer.0 as usize].key.0[0].macro_definition = Some(
        DefinitionReferenceKey::Local(graph.definitions.definitions[2].key.clone()),
    );
    graph.expansions[outer.0 as usize].key.0[0].selected_macro_rule = Some(units[4].full_range);
    graph.edges.push(DependencyEdge {
        from: GraphNode::Expansion(outer),
        to: GraphNode::Definition(DefinitionId(2)),
        kind: DependencyKind::MacroDefinition,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });

    let child = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let outer_key = graph.expansions[outer.0 as usize].key.0[0].clone();
    let child_node = &mut graph.expansions[child.0 as usize];
    child_node.written_invocation = None;
    child_node.source_call_parent = Some(outer);
    child_node.macro_definition = Some(DefinitionTarget::Local(DefinitionId(3)));
    child_node.key.0.insert(0, outer_key);
    child_node.key.0[1].macro_definition = Some(DefinitionReferenceKey::Local(
        graph.definitions.definitions[3].key.clone(),
    ));
    child_node.key.0[1].selected_macro_rule = Some(units[7].full_range);
    graph.edges.iter_mut().for_each(|edge| {
        if edge.kind == DependencyKind::ExpansionUse && edge.to == GraphNode::Expansion(child) {
            edge.sites = vec![ObservationSite::CompilerGenerated];
        }
    });
    graph.edges.extend([
        DependencyEdge {
            from: GraphNode::Expansion(child),
            to: GraphNode::Expansion(outer),
            kind: DependencyKind::ExpansionSourceCallParent,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
        DependencyEdge {
            from: GraphNode::Expansion(child),
            to: GraphNode::Definition(DefinitionId(3)),
            kind: DependencyKind::MacroDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
    ]);

    let mut constraints = complete_constraints(&inventory, &graph);
    *coverage_mut(&mut constraints) = vec![coverage(
        outer,
        1,
        vec![products_group(
            vec![output_range(0, 1)],
            vec![GraphNode::Expansion(child)],
            vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)],
        )],
    )];
    coverage_mut(&mut constraints)[0].test_materialization_groups_mut()[0]
        .test_set_output_demands(vec![(vec![DefinitionId(1)], vec![child], Vec::new())]);
    *outputless_mut(&mut constraints) = vec![child];
    set_complete_meaning(
        &mut constraints,
        vec![complete_meaning_with_source_owner(
            outer,
            false,
            vec![child],
            DefinitionId(1),
        )],
    );

    let definition_units = definition_source_units(&inventory, &graph).unwrap();
    let validated = validate_constraints(&inventory, &graph, &definition_units, &constraints)
        .expect("the producer ledger and outputless child form complete constraints");
    assert_eq!(
        validated.macro_products.delegated_macro_expansions,
        BTreeSet::from([child]),
        "only the classified child delegates its ordinary ExpansionUse"
    );

    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Expansion(child))
    );
    assert!(retention.retained_units.contains(&SourceUnitId(7)));
    assert_eq!(
        retention.outputless_macro_expansions,
        BTreeSet::from([outer, child])
    );
    assert_eq!(
        outputless_macro_expansions_in_complete_source(&graph, &constraints).unwrap(),
        BTreeSet::from([outer, child]),
        "the reduced-source snapshot applies the same transitive outputless closure",
    );
}

#[test]
fn macro_output_meaning_preserves_intrinsic_owner_opaque_and_multiple_outputs() {
    let definition_leaf = MacroMaterialization {
        producer: ExpansionId(2),
        products: vec![GraphNode::Definition(DefinitionId(0))],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(2)]),
    };
    let owner_leaf = MacroMaterialization {
        producer: ExpansionId(3),
        products: Vec::new(),
        owner_requirements: vec![MacroOwnerRequirement {
            owner: DefinitionId(1),
            members: Vec::new(),
            effect: MacroOwnerEffect::Semantic,
        }],
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(3)]),
    };
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![
                GraphNode::Expansion(ExpansionId(1)),
                GraphNode::Expansion(ExpansionId(2)),
            ],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        definition_leaf,
        owner_leaf,
        MacroMaterialization {
            producer: ExpansionId(5),
            products: vec![GraphNode::Expansion(ExpansionId(99))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(4)]),
        },
    ];
    let producers = (0..=5).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();
    let retained = (0..=4).map(SourceUnitId).collect();

    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &retained).unwrap(),
        BTreeSet::from([ExpansionId(1), ExpansionId(4)]),
        "a definition, owner effect, one meaningful child, or an unclassified child is observable"
    );
}

#[test]
fn removed_leaf_output_makes_its_control_chain_outputless() {
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![GraphNode::Expansion(ExpansionId(1))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Definition(DefinitionId(0))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ];
    let producers = (0..=1).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();

    assert_eq!(
        outputless_macro_expansions_after_rewrite(
            &macro_products,
            &BTreeSet::from([SourceUnitId(0), SourceUnitId(1)]),
        )
        .unwrap(),
        BTreeSet::new()
    );
    assert_eq!(
        outputless_macro_expansions_after_rewrite(
            &macro_products,
            &BTreeSet::from([SourceUnitId(0)]),
        )
        .unwrap(),
        BTreeSet::from([ExpansionId(0), ExpansionId(1)])
    );
}

#[test]
fn disappearing_leaf_output_collapses_its_parent_chain_in_one_retention_pass() {
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![GraphNode::Expansion(ExpansionId(1))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Definition(DefinitionId(0))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: vec![GraphNode::Expansion(ExpansionId(2))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(2)]),
        },
    ];
    let producers = (0..=2).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();

    let reduce = || {
        let mut compile_required = BTreeSet::from([GraphNode::Expansion(ExpansionId(1))]);
        let mut retained_units = BTreeSet::from([SourceUnitId(2)]);
        close_validated_retention_constraints(
            &macro_products,
            None,
            &mut compile_required,
            &mut retained_units,
        );
        (compile_required, retained_units)
    };
    let first = reduce();
    assert_eq!(first.1, BTreeSet::from([SourceUnitId(2)]));
    assert!(!first.0.contains(&GraphNode::Definition(DefinitionId(0))));
    assert_eq!(
        outputless_macro_expansions_after_rewrite(&macro_products, &first.1).unwrap(),
        BTreeSet::from([ExpansionId(0), ExpansionId(1), ExpansionId(2)])
    );
}

#[test]
fn complete_output_meaning_finds_an_unrefined_transparent_control_chain() {
    let graph = complete_macro_meaning_graph(&[None, Some(0)]);
    let inventory =
        MacroCompleteOutputMeaningInventory::test_new(vec![complete_meaning_with_source_owner(
            ExpansionId(0),
            false,
            vec![ExpansionId(1)],
            DefinitionId(1),
        )]);
    let directly_outputless = BTreeSet::from([ExpansionId(1)]);
    let validated = validate_complete_macro_output_meaning(
        macro_graph(&graph),
        &inventory,
        &directly_outputless,
    )
    .unwrap();

    assert_eq!(
        outputless_complete_macro_outputs(&validated).unwrap(),
        BTreeSet::from([ExpansionId(0), ExpansionId(1)]),
        "complete output meaning is independent of editing coverage",
    );
}

#[test]
fn complete_output_meaning_preserves_intrinsic_and_opaque_children() {
    let mut graph = complete_macro_meaning_graph(&[None, Some(0)]);
    graph.expansions[1].implementation = Some(MacroImplementationKind::Builtin);
    graph.expansions[1].key.0[0].implementation = Some(MacroImplementationKind::Builtin);
    graph.expansions[1].macro_definition = None;
    graph.expansions[1].key.0[0].macro_definition = None;
    let directly_outputless = BTreeSet::from([ExpansionId(1)]);
    let intrinsic =
        MacroCompleteOutputMeaningInventory::test_new(vec![complete_meaning_with_source_owner(
            ExpansionId(0),
            true,
            vec![ExpansionId(1)],
            DefinitionId(1),
        )]);
    let intrinsic = validate_complete_macro_output_meaning(
        macro_graph(&graph),
        &intrinsic,
        &directly_outputless,
    )
    .unwrap();
    assert_eq!(
        outputless_complete_macro_outputs(&intrinsic).unwrap(),
        BTreeSet::from([ExpansionId(1)]),
        "a definition or semantic owner output makes its producer meaningful",
    );

    let opaque_child =
        MacroCompleteOutputMeaningInventory::test_new(vec![complete_meaning_with_source_owner(
            ExpansionId(0),
            false,
            vec![ExpansionId(1)],
            DefinitionId(1),
        )]);
    let opaque_child = validate_complete_macro_output_meaning(
        macro_graph(&graph),
        &opaque_child,
        &BTreeSet::new(),
    )
    .unwrap();
    assert!(
        outputless_complete_macro_outputs(&opaque_child)
            .unwrap()
            .is_empty(),
        "a child outside the complete meaning universe is opaque, not empty",
    );
}

#[test]
fn incomplete_empty_output_is_not_an_outputless_seed() {
    let graph = complete_macro_meaning_graph(&[None]);
    let validated = validate_complete_macro_output_meaning(
        macro_graph(&graph),
        &MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
        &BTreeSet::new(),
    )
    .unwrap();

    assert!(
        outputless_complete_macro_outputs(&validated)
            .unwrap()
            .is_empty(),
        "absence from both complete censuses is not evidence of empty output",
    );
}

#[test]
fn complete_output_meaning_walks_a_deep_chain_linearly() {
    const COUNT: u32 = 1_024;
    let parents = (0..COUNT)
        .map(|producer| producer.checked_sub(1))
        .collect::<Vec<_>>();
    let graph = complete_macro_meaning_graph(&parents);
    let inventory = MacroCompleteOutputMeaningInventory::test_new(
        (0..COUNT)
            .map(|producer| {
                let child = (producer + 1 < COUNT).then(|| ExpansionId(producer + 1));
                complete_meaning_with_source_owner(
                    ExpansionId(producer),
                    child.is_none(),
                    child.into_iter().collect(),
                    DefinitionId(1),
                )
            })
            .collect(),
    );
    let validated =
        validate_complete_macro_output_meaning(macro_graph(&graph), &inventory, &BTreeSet::new())
            .unwrap();
    let (outputless, stats) = outputless_complete_macro_outputs_with_stats(&validated).unwrap();

    assert!(outputless.is_empty());
    assert_eq!(stats.index_visits, 2 * COUNT as usize - 1);
    assert_eq!(stats.dependency_visits, COUNT as usize - 1);
    assert_eq!(stats.producer_activations, COUNT as usize);
}

#[test]
fn meaning_activation_reprocesses_one_consumed_compile_trigger_once() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let materializations = vec![
        MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        },
        MacroMaterialization {
            producer: ExpansionId(1),
            products: Vec::new(),
            owner_requirements: vec![MacroOwnerRequirement {
                owner: DefinitionId(0),
                members: Vec::new(),
                effect: MacroOwnerEffect::Semantic,
            }],
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
        },
    ];
    let producers = BTreeSet::from([ExpansionId(0), ExpansionId(1)]);
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut compile_required = BTreeSet::from([child]);
    let mut actual_required = compile_required.clone();
    let mut retained_units = BTreeSet::from([SourceUnitId(1)]);
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(retained_units.contains(&SourceUnitId(0)));
    assert_eq!(
        closure.compile_trigger_visits, 1,
        "the false-before-true child trigger is reopened exactly once"
    );
}

#[test]
fn required_child_output_opens_from_its_container_demand() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let macro_products = ValidatedMacroProducts::new_with_output_demands(
        vec![MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        }],
        vec![vec![macro_group_demand(
            vec![DefinitionId(0)],
            Vec::new(),
            vec![ExpansionId(1)],
        )]],
        BTreeSet::from([ExpansionId(0), ExpansionId(1)]),
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(0))]);
    let mut retained_units = BTreeSet::new();

    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );

    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(0)]));
    assert!(compile_required.contains(&child));
}

#[test]
fn dependent_child_output_requires_container_and_actual_child_demand_in_either_order() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let macro_products = ValidatedMacroProducts::new_with_output_demands_and_triggers(
        vec![MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        }],
        vec![vec![macro_group_demand(
            vec![DefinitionId(0)],
            vec![ExpansionId(1)],
            Vec::new(),
        )]],
        BTreeSet::from([ExpansionId(0), ExpansionId(1)]),
        BTreeMap::from([(ExpansionId(1), vec![DefinitionId(1)])]),
    )
    .unwrap();

    for initial in [
        vec![
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
        ],
        vec![
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        ],
    ] {
        let mut closure = RetentionClosure::new(&macro_products, None);
        let mut compile_required = BTreeSet::new();
        let mut actual_required = BTreeSet::new();
        let mut retained_units = BTreeSet::new();
        let mut newly_required = Vec::new();
        let mut newly_actual = Vec::new();
        let mut newly_retained = Vec::new();
        closure
            .seed(&compile_required, &actual_required, &retained_units)
            .unwrap();
        for trigger in initial {
            compile_required.insert(trigger);
            actual_required.insert(trigger);
            closure.add_presence([trigger]);
            let GraphNode::Definition(definition) = trigger else {
                unreachable!("test triggers are definitions")
            };
            closure.add_actual_definitions([definition]);
            closure.close(
                &mut compile_required,
                &mut newly_required,
                &mut actual_required,
                &mut newly_actual,
                &mut retained_units,
                &mut newly_retained,
            );
            if compile_required.len() == 1 {
                assert!(retained_units.is_empty());
            }
        }
        assert_eq!(retained_units, BTreeSet::from([SourceUnitId(0)]));
    }
}

#[test]
fn demanded_container_activates_a_dependent_child_with_residual_semantics() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let macro_products = ValidatedMacroProducts::new_with_output_demands_and_triggers(
        vec![MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![child],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        }],
        vec![vec![macro_group_demand(
            vec![DefinitionId(0)],
            vec![ExpansionId(1)],
            Vec::new(),
        )]],
        BTreeSet::from([ExpansionId(0), ExpansionId(1)]),
        BTreeMap::from([(ExpansionId(1), vec![DefinitionId(0)])]),
    )
    .unwrap();
    let carrier = GraphNode::Definition(DefinitionId(0));
    let mut compile_present = BTreeSet::from([carrier]);
    let mut actual_required = compile_present.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut closure = RetentionClosure::new(&macro_products, None);
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(actual_required.contains(&child));
    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(0)]));
}

#[test]
fn potential_child_meaning_does_not_bootstrap_actual_demand() {
    let child = GraphNode::Expansion(ExpansionId(1));
    let macro_products = ValidatedMacroProducts::new_with_output_demands(
        vec![
            MacroMaterialization {
                producer: ExpansionId(0),
                products: vec![child],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
            },
            MacroMaterialization {
                producer: ExpansionId(1),
                products: vec![GraphNode::Definition(DefinitionId(1))],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: contributor_roots(vec![SourceUnitId(1)]),
            },
        ],
        vec![
            vec![macro_group_demand(
                vec![DefinitionId(0)],
                vec![ExpansionId(1)],
                Vec::new(),
            )],
            Vec::new(),
        ],
        BTreeSet::from([ExpansionId(0), ExpansionId(1)]),
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(0))]);
    let mut retained_units = BTreeSet::from([SourceUnitId(1)]);

    close_validated_retention_constraints(
        &macro_products,
        None,
        &mut compile_required,
        &mut retained_units,
    );

    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(1)]));
    assert!(!compile_required.contains(&child));
}

#[test]
fn materialized_presence_upgrades_to_actual_demand_only_after_an_independent_trigger() {
    let generated = GraphNode::Definition(DefinitionId(1));
    let producer = GraphNode::Expansion(ExpansionId(0));
    let macro_products = ValidatedMacroProducts::new_with_output_demands_and_triggers(
        vec![MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![generated],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        }],
        vec![Vec::new()],
        BTreeSet::from([ExpansionId(0)]),
        BTreeMap::from([(ExpansionId(0), vec![DefinitionId(1)])]),
    )
    .unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut compile_present = BTreeSet::new();
    let mut actual_required = BTreeSet::new();
    let mut retained_units = BTreeSet::from([SourceUnitId(0)]);
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(compile_present.contains(&generated));
    assert!(!actual_required.contains(&generated));
    assert!(!actual_required.contains(&producer));

    actual_required.insert(generated);
    closure.add_actual_definitions([DefinitionId(1)]);
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(actual_required.contains(&producer));
    assert!(compile_present.is_superset(&actual_required));
}

#[test]
fn actual_macro_demand_must_already_have_compiler_presence() {
    let macro_products = ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    assert_eq!(
        closure.seed(
            &BTreeSet::new(),
            &BTreeSet::from([GraphNode::Definition(DefinitionId(0))]),
            &BTreeSet::new(),
        ),
        Err(RetentionError::InvalidConstraint),
    );
}

#[test]
fn compile_presence_and_actual_demand_close_member_constraints_independently() {
    let root = GraphNode::Definition(DefinitionId(1));
    let subordinate = GraphNode::Definition(DefinitionId(2));
    let independent_sibling = GraphNode::Definition(DefinitionId(3));
    let implementation = GraphNode::Definition(DefinitionId(4));
    let materialization = MacroMaterialization {
        producer: ExpansionId(0),
        products: vec![root, subordinate, independent_sibling],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
    };
    let product_classes = vec![vec![vec![root, subordinate], vec![independent_sibling]]];
    let macro_products = ValidatedMacroProducts::new_with_product_classes(
        vec![materialization.clone()],
        product_classes.clone(),
    )
    .unwrap();
    let compiler_members = ValidatedCompilerMemberConstraints {
        requirements_by_trigger: BTreeMap::from([(DefinitionId(2), vec![DefinitionId(4)])]),
        conditional_requirements: Vec::new(),
        conditional_by_trigger: BTreeMap::new(),
        disjunctions: Vec::new(),
    };
    let mut compile_present = BTreeSet::from([root]);
    let mut actual_required = compile_present.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut closure = RetentionClosure::new(&macro_products, Some(&compiler_members));
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert!(actual_required.contains(&subordinate));
    assert!(actual_required.contains(&implementation));
    assert!(!actual_required.contains(&independent_sibling));
    assert!(compile_present.contains(&independent_sibling));

    let macro_products = ValidatedMacroProducts::new_with_product_classes(
        vec![materialization.clone()],
        product_classes,
    )
    .unwrap();
    let mut compile_present = BTreeSet::new();
    let mut actual_required = BTreeSet::new();
    let mut retained_units = BTreeSet::from([SourceUnitId(0)]);
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut closure = RetentionClosure::new(&macro_products, Some(&compiler_members));
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert_eq!(
        compile_present,
        BTreeSet::from([root, subordinate, independent_sibling, implementation])
    );
    assert!(actual_required.is_empty());

    assert!(matches!(
        ValidatedMacroProducts::new_with_product_classes(
            vec![materialization.clone()],
            vec![vec![vec![root, subordinate]]],
        ),
        Err(RetentionError::InvalidConstraint)
    ));
    assert!(matches!(
        ValidatedMacroProducts::new_with_product_classes(
            vec![materialization],
            vec![vec![
                vec![root, subordinate],
                vec![subordinate, independent_sibling]
            ]],
        ),
        Err(RetentionError::InvalidConstraint)
    ));
}

#[test]
fn required_child_demand_does_not_actualize_atomic_sibling_outputs() {
    let required = GraphNode::Expansion(ExpansionId(1));
    let dependent_sibling = GraphNode::Expansion(ExpansionId(3));
    let definition_sibling = GraphNode::Definition(DefinitionId(2));
    let indirectly_triggered = GraphNode::Expansion(ExpansionId(2));
    let macro_products = ValidatedMacroProducts::new_with_output_demands_and_triggers(
        vec![MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![definition_sibling, required, dependent_sibling],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        }],
        vec![vec![
            macro_group_demand(vec![DefinitionId(0)], Vec::new(), vec![ExpansionId(1)]),
            macro_group_demand(vec![DefinitionId(0)], vec![ExpansionId(3)], Vec::new()),
        ]],
        BTreeSet::from([
            ExpansionId(0),
            ExpansionId(1),
            ExpansionId(2),
            ExpansionId(3),
        ]),
        BTreeMap::from([(ExpansionId(2), vec![DefinitionId(2)])]),
    )
    .unwrap();
    let mut closure = RetentionClosure::new(&macro_products, None);
    let carrier = GraphNode::Definition(DefinitionId(0));
    let mut compile_present = BTreeSet::from([carrier]);
    let mut actual_required = compile_present.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert_eq!(retained_units, BTreeSet::from([SourceUnitId(0)]));
    assert!(compile_present.contains(&required));
    assert!(compile_present.contains(&dependent_sibling));
    assert!(compile_present.contains(&definition_sibling));
    assert!(actual_required.contains(&required));
    assert!(!actual_required.contains(&dependent_sibling));
    assert!(!actual_required.contains(&definition_sibling));
    assert!(!actual_required.contains(&indirectly_triggered));
}

#[test]
fn required_child_demand_visits_each_clause_once() {
    const COUNT: u32 = 1_024;
    let materializations = (0..COUNT)
        .map(|index| MacroMaterialization {
            producer: ExpansionId(0),
            products: vec![GraphNode::Expansion(ExpansionId(index + 1))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(index)]),
        })
        .collect::<Vec<_>>();
    let output_demands = (0..COUNT)
        .map(|index| {
            vec![macro_group_demand(
                vec![DefinitionId(0)],
                Vec::new(),
                vec![ExpansionId(index + 1)],
            )]
        })
        .collect();
    let producer_universe = (0..=COUNT).map(ExpansionId).collect();
    let macro_products = ValidatedMacroProducts::new_with_output_demands(
        materializations,
        output_demands,
        producer_universe,
    )
    .unwrap();
    let carrier = GraphNode::Definition(DefinitionId(0));
    let mut compile_present = BTreeSet::from([carrier]);
    let mut actual_required = compile_present.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut closure = RetentionClosure::new(&macro_products, None);
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert_eq!(retained_units.len(), COUNT as usize);
    assert!(
        (1..=COUNT)
            .all(|child| { actual_required.contains(&GraphNode::Expansion(ExpansionId(child))) })
    );
    assert_eq!(closure.demand_fact_visits, COUNT as usize);
}

#[test]
fn macro_output_meaning_walks_each_group_and_dependency_once() {
    const COUNT: u32 = 1_024;
    let mut materializations = (0..COUNT - 1)
        .map(|producer| MacroMaterialization {
            producer: ExpansionId(producer),
            products: vec![GraphNode::Expansion(ExpansionId(producer + 1))],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
        })
        .collect::<Vec<_>>();
    materializations.push(MacroMaterialization {
        producer: ExpansionId(COUNT - 1),
        products: vec![GraphNode::Definition(DefinitionId(0))],
        owner_requirements: Vec::new(),
        identity_cohort_root: None,
        contributor_roots: contributor_roots(vec![SourceUnitId(0)]),
    });
    let producers = (0..COUNT).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();

    let (outputless, stats) = outputless_macro_expansions_after_rewrite_with_stats(
        &macro_products,
        &BTreeSet::from([SourceUnitId(0)]),
    )
    .unwrap();
    assert!(outputless.is_empty());
    assert_eq!(stats.group_visits, COUNT as usize);
    assert_eq!(stats.dependency_visits, COUNT as usize - 1);
    assert_eq!(stats.producer_activations, COUNT as usize);

    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut compile_required = BTreeSet::new();
    let mut actual_required = BTreeSet::new();
    let mut retained_units = BTreeSet::from([SourceUnitId(0)]);
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );
    assert_eq!(
        closure.output_meaning_fact_visits,
        2 * COUNT as usize - 1,
        "each group and child dependency is consumed once"
    );
}

#[test]
fn transparent_shell_dependencies_visit_each_shared_reverse_fact_once() {
    const COUNT: u32 = 1_024;
    let mut materializations = Vec::with_capacity(2 * COUNT as usize);
    for producer in 0..COUNT {
        let definition = GraphNode::Definition(DefinitionId(producer));
        materializations.push(MacroMaterialization {
            producer: ExpansionId(producer),
            products: vec![definition],
            owner_requirements: Vec::new(),
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(2 * producer)]),
        });
        materializations.push(MacroMaterialization {
            producer: ExpansionId(producer),
            products: Vec::new(),
            owner_requirements: vec![MacroOwnerRequirement {
                owner: DefinitionId(COUNT + producer),
                members: Vec::new(),
                effect: MacroOwnerEffect::TransparentShell {
                    dependent_products: vec![definition],
                },
            }],
            identity_cohort_root: None,
            contributor_roots: contributor_roots(vec![SourceUnitId(2 * producer + 1)]),
        });
    }
    let producers = (0..COUNT).map(ExpansionId).collect();
    let macro_products =
        ValidatedMacroProducts::new_with_producers(materializations, BTreeSet::new(), producers)
            .unwrap();
    let all_sources = (0..2 * COUNT).map(SourceUnitId).collect();

    let (outputless, stats) =
        outputless_macro_expansions_after_rewrite_with_stats(&macro_products, &all_sources)
            .unwrap();
    assert!(outputless.is_empty());
    assert_eq!(stats.group_visits, 2 * COUNT as usize);
    assert_eq!(stats.dependency_visits, COUNT as usize);
    assert_eq!(stats.producer_activations, COUNT as usize);

    let mut closure = RetentionClosure::new(&macro_products, None);
    let mut compile_required = (0..COUNT)
        .map(|definition| GraphNode::Definition(DefinitionId(definition)))
        .collect::<BTreeSet<_>>();
    let mut actual_required = compile_required.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );
    assert_eq!(retained_units, all_sources);
    assert_eq!(closure.compile_trigger_visits, 2 * COUNT as usize);
}

#[test]
fn macro_product_validation_rejects_missing_duplicate_and_cross_kind_facts() {
    let source = source_with_token(96, (12, 18));
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 96), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::MacroDefinition, (21, 80), Some(0), 3),
        unit(4, WrittenUnitKind::MacroRule, (30, 79), Some(3), 4),
        unit(5, WrittenUnitKind::NestedItem, (40, 50), Some(4), 5),
        unit(6, WrittenUnitKind::Item, (81, 90), Some(0), 6),
        unit(7, WrittenUnitKind::NestedItem, (12, 18), Some(2), 7),
    ];
    let mut inventory = inventory(&source, units.clone());
    inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(3),
        rules: vec![SourceUnitId(4)],
        observed_selections: vec![SourceUnitId(4)],
    }];
    inventory.macro_templates = vec![MacroTemplateSourceFacts {
        unit: SourceUnitId(5),
        rule: SourceUnitId(4),
    }];
    inventory.macro_repetitions = vec![MacroRepetitionSourceFacts {
        invocation: SourceUnitId(2),
        rule: SourceUnitId(4),
        matcher_range: ByteRange { start: 31, end: 32 },
        parent: SourceUnitId(2),
        repetition_path: vec![0],
        input_range: ByteRange { start: 12, end: 18 },
        elements: vec![MacroRepetitionElementSourceFacts {
            unit: SourceUnitId(7),
            separator_after: None,
        }],
        minimum: 0,
        maximum: None,
    }];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "output"),
            written_definition(3, DefinitionKind::Macro, &units[3], Some(0), "m"),
        ],
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );
    let producer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), [DefinitionId(2)]);
    graph.expansions[producer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(3)));
    graph.expansions[producer.0 as usize].key.0[0].macro_definition = Some(
        DefinitionReferenceKey::Local(graph.definitions.definitions[3].key.clone()),
    );
    graph.expansions[producer.0 as usize].key.0[0].selected_macro_rule = Some(units[4].full_range);
    graph.edges.push(DependencyEdge {
        from: GraphNode::Expansion(producer),
        to: GraphNode::Definition(DefinitionId(3)),
        kind: DependencyKind::MacroDefinition,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });

    assert_eq!(
        compute_retention(
            &inventory,
            &graph,
            &complete_constraints(&inventory, &graph),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut constraints = complete_constraints(&inventory, &graph);
    let product = GraphNode::Definition(DefinitionId(2));
    let contributors = vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)];
    *coverage_mut(&mut constraints) = vec![coverage(
        producer,
        1,
        vec![products_group(
            vec![output_range(0, 1)],
            vec![product],
            contributors,
        )],
    )];
    set_complete_meaning(
        &mut constraints,
        vec![complete_meaning(
            producer,
            true,
            false,
            Vec::new(),
            vec![DefinitionId(2)],
            Vec::new(),
        )],
    );
    let result = compute_retention(&inventory, &graph, &constraints);
    assert!(result.is_ok(), "{result:?}");

    let mut transparent_shell = complete_constraints(&inventory, &graph);
    *coverage_mut(&mut transparent_shell) = vec![coverage(
        producer,
        2,
        vec![
            products_group(
                vec![output_range(0, 1)],
                vec![product],
                vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)],
            ),
            owner_effect_group(
                vec![output_range(1, 2)],
                DefinitionId(1),
                vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)],
            ),
        ],
    )];
    set_complete_meaning(
        &mut transparent_shell,
        vec![complete_meaning(
            producer,
            true,
            false,
            Vec::new(),
            vec![DefinitionId(2)],
            Vec::new(),
        )],
    );
    coverage_mut(&mut transparent_shell)[0]
        .test_single_slice_group_mut(1)
        .test_set_transparent_owner_effect(vec![product]);
    let result = compute_retention(&inventory, &graph, &transparent_shell);
    assert!(result.is_ok(), "{result:?}");

    coverage_mut(&mut transparent_shell)[0]
        .test_single_slice_group_mut(1)
        .test_set_transparent_owner_effect(vec![GraphNode::Definition(DefinitionId(99))]);
    assert_eq!(
        compute_retention(&inventory, &graph, &transparent_shell),
        Err(RetentionError::InvalidConstraint),
        "a published transparent dependency must name a classified output product",
    );

    let mut repetition_only = inventory.clone();
    repetition_only.macro_templates.clear();
    assert_eq!(
        validate_macro_source_refinement_coverage(
            &repetition_only,
            macro_graph(&graph),
            rule_selections(&constraints),
            &BTreeSet::new(),
            &BTreeSet::new(),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut repeated_graph = graph.clone();
    let repeated_producer = ExpansionId(repeated_graph.expansions.len() as u32);
    let mut repeated = repeated_graph.expansions[producer.0 as usize].clone();
    repeated.id = repeated_producer;
    repeated_graph.expansions.push(repeated);
    let repeated_selections = vec![
        MacroRuleSelectionRequirement {
            expansion: producer,
            rule: SourceUnitId(4),
        },
        MacroRuleSelectionRequirement {
            expansion: repeated_producer,
            rule: SourceUnitId(4),
        },
    ];
    assert_eq!(
        validate_macro_source_refinement_coverage(
            &inventory,
            macro_graph(&repeated_graph),
            &repeated_selections,
            &BTreeSet::from([producer]),
            &BTreeSet::new(),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );
    assert_eq!(
        validate_macro_source_refinement_coverage(
            &repetition_only,
            macro_graph(&repeated_graph),
            &repeated_selections,
            &BTreeSet::from([producer]),
            &BTreeSet::new(),
        ),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut generated_shell = constraints.clone();
    let base_contributors = vec![SourceUnitId(2), SourceUnitId(4)];
    coverage_mut(&mut generated_shell)[0].test_materialization_groups_mut()[0]
        .test_set_contributors(base_contributors);
    assert!(compute_retention(&inventory, &graph, &generated_shell).is_ok());

    let mut missing_contributor = constraints.clone();
    coverage_mut(&mut missing_contributor)[0].test_materialization_groups_mut()[0]
        .test_set_contributors(vec![SourceUnitId(2), SourceUnitId(5)]);
    assert_eq!(
        compute_retention(&inventory, &graph, &missing_contributor),
        Err(RetentionError::InvalidConstraint)
    );

    let mut duplicate_contributor = constraints.clone();
    coverage_mut(&mut duplicate_contributor)[0].test_materialization_groups_mut()[0]
        .test_set_contributors(vec![
            SourceUnitId(2),
            SourceUnitId(4),
            SourceUnitId(5),
            SourceUnitId(5),
        ]);
    assert_eq!(
        compute_retention(&inventory, &graph, &duplicate_contributor),
        Err(RetentionError::InvalidConstraint)
    );

    let mut cross_kind = constraints.clone();
    {
        let mut coverage = coverage_mut(&mut cross_kind);
        let group = &mut coverage[0].test_materialization_groups_mut()[0];
        let mut contributors = group.contributors();
        contributors[2] = SourceUnitId(6);
        group.test_set_contributors(contributors);
    }
    assert_eq!(
        compute_retention(&inventory, &graph, &cross_kind),
        Err(RetentionError::InvalidConstraint)
    );

    let mut duplicate_product = constraints.clone();
    coverage_mut(&mut duplicate_product)[0]
        .test_single_slice_group_mut(0)
        .test_set_products(vec![product, product]);
    assert_eq!(
        compute_retention(&inventory, &graph, &duplicate_product),
        Err(RetentionError::InvalidConstraint)
    );

    let mut duplicate_producer = constraints.clone();
    let duplicate = coverage_mut(&mut duplicate_producer)[0].clone();
    coverage_mut(&mut duplicate_producer).push(duplicate);
    assert_eq!(
        compute_retention(&inventory, &graph, &duplicate_producer),
        Err(RetentionError::InvalidConstraint)
    );

    let mut gap = constraints.clone();
    coverage_mut(&mut gap)[0].test_set_output_token_count(3);
    coverage_mut(&mut gap)[0]
        .test_materialization_groups_mut()
        .push(owner_effect_group(
            vec![output_range(2, 3)],
            DefinitionId(1),
            vec![SourceUnitId(2), SourceUnitId(4)],
        ));
    assert_eq!(
        compute_retention(&inventory, &graph, &gap),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut overlap = gap.clone();
    coverage_mut(&mut overlap)[0]
        .test_single_slice_group_mut(0)
        .test_output_ranges_mut()[0]
        .test_set_end(2);
    coverage_mut(&mut overlap)[0]
        .test_single_slice_group_mut(1)
        .test_output_ranges_mut()[0]
        .test_set_start(1);
    assert_eq!(
        compute_retention(&inventory, &graph, &overlap),
        Err(RetentionError::InvalidConstraint)
    );

    let mut missing_output = constraints;
    coverage_mut(&mut missing_output)[0]
        .test_materialization_groups_mut()
        .clear();
    assert_eq!(
        compute_retention(&inventory, &graph, &missing_output),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut shared_range_graph = graph.clone();
    let use_leaf = DefinitionId(shared_range_graph.definitions.definitions.len() as u32);
    shared_range_graph
        .definitions
        .definitions
        .push(expanded_definition(
            use_leaf.0,
            DefinitionKind::Use,
            &units[2],
            Some(0),
            "use_leaf",
        ));
    shared_range_graph.edges.push(DependencyEdge {
        from: GraphNode::Definition(use_leaf),
        to: GraphNode::Expansion(producer),
        kind: DependencyKind::GeneratedBy,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });
    let mut shared_range = complete_constraints(&inventory, &shared_range_graph);
    *coverage_mut(&mut shared_range) = vec![coverage(
        producer,
        1,
        vec![products_group(
            vec![output_range(0, 1)],
            vec![product, GraphNode::Definition(use_leaf)],
            vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)],
        )],
    )];
    set_complete_meaning(
        &mut shared_range,
        vec![complete_meaning(
            producer,
            true,
            false,
            Vec::new(),
            vec![DefinitionId(2), use_leaf],
            Vec::new(),
        )],
    );
    assert!(compute_retention(&inventory, &shared_range_graph, &shared_range).is_ok());

    coverage_mut(&mut shared_range)[0]
        .test_single_slice_group_mut(0)
        .test_set_products(vec![product]);
    assert_eq!(
        compute_retention(&inventory, &shared_range_graph, &shared_range),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );
}

#[test]
fn generated_macro_products_inherit_their_parent_product_provenance() {
    let source = source_with_token(180, (12, 18));
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 180), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::MacroDefinition, (21, 70), Some(0), 3),
        unit(4, WrittenUnitKind::MacroRule, (30, 69), Some(3), 4),
        unit(5, WrittenUnitKind::NestedItem, (40, 50), Some(4), 5),
        unit(6, WrittenUnitKind::MacroDefinition, (71, 120), Some(0), 6),
        unit(7, WrittenUnitKind::MacroRule, (80, 119), Some(6), 7),
        unit(8, WrittenUnitKind::NestedItem, (90, 100), Some(7), 8),
        unit(9, WrittenUnitKind::NestedItem, (12, 18), Some(2), 9),
        unit(10, WrittenUnitKind::Item, (121, 130), Some(0), 10),
    ];
    let mut inventory = inventory(&source, units.clone());
    inventory.macro_rules = vec![
        MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(3),
            rules: vec![SourceUnitId(4)],
            observed_selections: vec![SourceUnitId(4)],
        },
        MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(6),
            rules: vec![SourceUnitId(7)],
            observed_selections: vec![SourceUnitId(7)],
        },
    ];
    inventory.macro_templates = vec![
        MacroTemplateSourceFacts {
            unit: SourceUnitId(5),
            rule: SourceUnitId(4),
        },
        MacroTemplateSourceFacts {
            unit: SourceUnitId(8),
            rule: SourceUnitId(7),
        },
    ];
    inventory.macro_repetitions = vec![MacroRepetitionSourceFacts {
        invocation: SourceUnitId(2),
        rule: SourceUnitId(4),
        matcher_range: ByteRange { start: 31, end: 32 },
        parent: SourceUnitId(2),
        repetition_path: vec![0],
        input_range: ByteRange { start: 12, end: 18 },
        elements: vec![MacroRepetitionElementSourceFacts {
            unit: SourceUnitId(9),
            separator_after: None,
        }],
        minimum: 0,
        maximum: None,
    }];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            expanded_definition(2, DefinitionKind::Function, &units[2], Some(0), "output"),
            written_definition(3, DefinitionKind::Macro, &units[3], Some(0), "outer"),
            written_definition(4, DefinitionKind::Macro, &units[6], Some(0), "inner"),
            written_definition(
                5,
                DefinitionKind::Function,
                &units[10],
                Some(0),
                "unused_owner",
            ),
        ],
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );
    let outer = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    graph.expansions[outer.0 as usize].macro_definition =
        Some(DefinitionTarget::Local(DefinitionId(3)));
    graph.expansions[outer.0 as usize].key.0[0].macro_definition = Some(
        DefinitionReferenceKey::Local(graph.definitions.definitions[3].key.clone()),
    );
    graph.expansions[outer.0 as usize].key.0[0].selected_macro_rule = Some(units[4].full_range);
    graph.edges.push(DependencyEdge {
        from: GraphNode::Expansion(outer),
        to: GraphNode::Definition(DefinitionId(3)),
        kind: DependencyKind::MacroDefinition,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });

    let inner = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), [DefinitionId(2)]);
    let outer_key = graph.expansions[outer.0 as usize].key.0[0].clone();
    let inner_node = &mut graph.expansions[inner.0 as usize];
    inner_node.written_invocation = None;
    inner_node.source_call_parent = Some(outer);
    inner_node.macro_definition = Some(DefinitionTarget::Local(DefinitionId(4)));
    inner_node.key.0.insert(0, outer_key);
    inner_node.key.0[1].macro_definition = Some(DefinitionReferenceKey::Local(
        graph.definitions.definitions[4].key.clone(),
    ));
    inner_node.key.0[1].selected_macro_rule = Some(units[7].full_range);
    graph.edges.extend([
        DependencyEdge {
            from: GraphNode::Expansion(inner),
            to: GraphNode::Expansion(outer),
            kind: DependencyKind::ExpansionSourceCallParent,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
        DependencyEdge {
            from: GraphNode::Expansion(inner),
            to: GraphNode::Definition(DefinitionId(4)),
            kind: DependencyKind::MacroDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
    ]);
    let ast_pass = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
    let ast_pass_node = &mut graph.expansions[ast_pass.0 as usize];
    ast_pass_node.kind = ExpansionKind::AstPass(AstPassKind::StandardImports);
    ast_pass_node.key.0[0].kind = ast_pass_node.kind.clone();
    ast_pass_node.implementation = None;
    ast_pass_node.key.0[0].implementation = None;
    ast_pass_node.source_call_parent = Some(outer);
    graph.edges.push(DependencyEdge {
        from: GraphNode::Expansion(ast_pass),
        to: GraphNode::Expansion(outer),
        kind: DependencyKind::ExpansionSourceCallParent,
        sites: Vec::new(),
        evidence: EvidenceOrigin::Compiler,
    });

    let outer_contributors = vec![SourceUnitId(2), SourceUnitId(4), SourceUnitId(5)];
    let inner_contributors = vec![
        SourceUnitId(2),
        SourceUnitId(4),
        SourceUnitId(5),
        SourceUnitId(7),
        SourceUnitId(8),
        SourceUnitId(9),
    ];
    let mut constraints = complete_constraints(&inventory, &graph);
    *coverage_mut(&mut constraints) = vec![
        coverage(
            outer,
            4,
            vec![
                owner_effect_group(
                    vec![output_range(0, 1), output_range(3, 4)],
                    DefinitionId(1),
                    outer_contributors.clone(),
                ),
                products_group(
                    vec![output_range(1, 3)],
                    vec![GraphNode::Expansion(inner)],
                    outer_contributors,
                ),
            ],
        ),
        coverage(
            inner,
            1,
            vec![products_group(
                vec![output_range(0, 1)],
                vec![GraphNode::Definition(DefinitionId(2))],
                inner_contributors,
            )],
        ),
    ];
    coverage_mut(&mut constraints)[0].test_materialization_groups_mut()[1]
        .test_set_output_demands(vec![(vec![DefinitionId(1)], vec![inner], Vec::new())]);
    set_complete_meaning(
        &mut constraints,
        vec![
            complete_meaning(
                outer,
                true,
                true,
                vec![inner],
                vec![DefinitionId(1)],
                vec![(vec![DefinitionId(1)], vec![inner], Vec::new())],
            ),
            complete_meaning(
                inner,
                true,
                false,
                Vec::new(),
                vec![DefinitionId(2)],
                Vec::new(),
            ),
        ],
    );
    let result = compute_retention(&inventory, &graph, &constraints);
    assert!(result.is_ok(), "{result:?}");

    let mut unrefined_child = constraints.clone();
    coverage_mut(&mut unrefined_child).pop();
    assert_eq!(
        compute_retention(&inventory, &graph, &unrefined_child),
        Err(RetentionError::IncompleteMacroProductConstraints)
    );

    let mut wrong_owner = constraints.clone();
    coverage_mut(&mut wrong_owner)[0]
        .test_single_slice_group_mut(0)
        .test_set_owner_effect(DefinitionId(5));
    assert_eq!(
        compute_retention(&inventory, &graph, &wrong_owner),
        Err(RetentionError::InvalidConstraint)
    );

    let mut missing_source_owner = graph.clone();
    missing_source_owner.expansions[outer.0 as usize].source_owner = None;
    assert_eq!(
        compute_retention(&inventory, &missing_source_owner, &constraints),
        Err(RetentionError::InvalidConstraint)
    );

    let mut missing_child_product = constraints.clone();
    coverage_mut(&mut missing_child_product)[0]
        .test_single_slice_group_mut(1)
        .test_set_owner_effect(DefinitionId(1));
    assert_eq!(
        compute_retention(&inventory, &graph, &missing_child_product),
        Err(RetentionError::InvalidConstraint)
    );

    let mut ast_pass_product = constraints.clone();
    coverage_mut(&mut ast_pass_product)[0]
        .test_single_slice_group_mut(1)
        .test_set_products(vec![GraphNode::Expansion(ast_pass)]);
    assert_eq!(
        compute_retention(&inventory, &graph, &ast_pass_product),
        Err(RetentionError::InvalidConstraint)
    );

    let mut partial_inherited = constraints.clone();
    {
        let mut coverage = coverage_mut(&mut partial_inherited);
        let group = &mut coverage[1].test_materialization_groups_mut()[0];
        let mut contributors = group.contributors();
        contributors.retain(|unit| *unit != SourceUnitId(5));
        group.test_set_contributors(contributors);
    }
    assert!(compute_retention(&inventory, &graph, &partial_inherited).is_ok());

    let mut written_child_graph = graph.clone();
    written_child_graph.expansions[inner.0 as usize].written_invocation = Some(SourceUnitId(2));
    let mut written_child_constraints = constraints.clone();
    coverage_mut(&mut written_child_constraints)[1].test_materialization_groups_mut()[0]
        .test_set_contributors(vec![SourceUnitId(2), SourceUnitId(7), SourceUnitId(8)]);
    assert!(
        compute_retention(&inventory, &written_child_graph, &written_child_constraints).is_ok()
    );

    {
        let mut coverage = coverage_mut(&mut written_child_constraints);
        let group = &mut coverage[1].test_materialization_groups_mut()[0];
        let mut contributors = group.contributors();
        contributors.push(SourceUnitId(5));
        contributors.sort();
        group.test_set_contributors(contributors);
    }
    assert!(
        compute_retention(&inventory, &written_child_graph, &written_child_constraints).is_ok()
    );

    let mut unrelated = constraints;
    {
        let mut coverage = coverage_mut(&mut unrelated);
        let group = &mut coverage[1].test_materialization_groups_mut()[0];
        let mut contributors = group.contributors();
        contributors.push(SourceUnitId(10));
        group.test_set_contributors(contributors);
    }
    assert_eq!(
        compute_retention(&inventory, &graph, &unrelated),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn nonempty_macro_repetition_adds_a_source_disjunction() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 48), None, 0),
        unit(1, WrittenUnitKind::MacroRule, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (11, 40), Some(0), 2),
        unit(3, WrittenUnitKind::NestedItem, (12, 20), Some(2), 3),
        unit(4, WrittenUnitKind::NestedItem, (22, 30), Some(2), 4),
    ];
    let mut inventory = inventory(source, units);
    inventory.macro_repetitions = vec![MacroRepetitionSourceFacts {
        invocation: SourceUnitId(2),
        rule: SourceUnitId(1),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(2),
        repetition_path: vec![0],
        input_range: ByteRange { start: 11, end: 40 },
        elements: vec![
            MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(3),
                separator_after: Some(ByteRange { start: 20, end: 21 }),
            },
            MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(4),
                separator_after: None,
            },
        ],
        minimum: 1,
        maximum: None,
    }];

    let constraints = SourceConstraints::from_source(&inventory);
    assert_eq!(
        constraints.disjunctions,
        vec![SourceDisjunction {
            trigger: SourceUnitId(2),
            choices: vec![SourceUnitId(3), SourceUnitId(4)],
        }]
    );

    inventory.macro_repetitions[0].minimum = 0;
    assert!(
        SourceConstraints::from_source(&inventory)
            .disjunctions
            .is_empty()
    );
}

#[test]
fn declarative_macro_observer_snapshot_is_attached_atomically_once() {
    let inventory = inventory(
        "x",
        vec![unit(0, WrittenUnitKind::CrateRoot, (0, 1), None, 0)],
    );
    let mut constraints = SourceConstraints::from_source(&inventory);

    let empty = DeclarativeMacroConstraints {
        rule_selections: Vec::new(),
        producer_coverage: MacroProducerCoverageInventory::test_new(Vec::new()),
        complete_output_meaning: MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
        outputless_expansions: Vec::new(),
    };
    assert_eq!(
        constraints.set_declarative_macro_constraints(empty.clone()),
        Ok(())
    );
    assert_eq!(
        constraints.set_declarative_macro_constraints(empty),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn source_site_uses_the_deepest_equal_range_owner() {
    let source = "fn main(){}";
    let inventory = inventory(
        source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 11), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 11), Some(0), 1),
        ],
    );
    let site = crate::source::ByteRange { start: 3, end: 7 };
    let source_sites = SourceSiteOwnerIndex::new(&inventory).unwrap();

    assert_eq!(
        source_site_is_retained(&source_sites, &BTreeSet::from([SourceUnitId(1)]), site),
        Ok(true)
    );
    assert_eq!(
        source_site_is_retained(&source_sites, &BTreeSet::from([SourceUnitId(0)]), site),
        Ok(false)
    );
}

#[test]
fn source_site_index_preserves_smallest_deepest_ties_and_inactive_units() {
    let source = "x".repeat(24);
    let mut inactive = unit(4, WrittenUnitKind::Item, (6, 10), Some(1), 4);
    inactive.cfg_state = CfgState::Inactive;
    let inventory = inventory(
        &source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 24), None, 0),
            unit(1, WrittenUnitKind::Item, (1, 20), Some(0), 1),
            unit(2, WrittenUnitKind::NestedItem, (4, 12), Some(1), 2),
            unit(3, WrittenUnitKind::NestedItem, (5, 13), Some(1), 3),
            inactive,
            unit(5, WrittenUnitKind::Item, (4, 12), Some(0), 5),
        ],
    );
    let index = SourceSiteOwnerIndex::new(&inventory).unwrap();

    assert_eq!(
        index.owners(ByteRange { start: 6, end: 10 }),
        Ok(vec![SourceUnitId(2), SourceUnitId(3)]),
        "crossing equal-length ranges tie, the shallower equal range loses, and inactive units do not own sites",
    );
    assert_eq!(
        source_site_is_retained(
            &index,
            &BTreeSet::from([SourceUnitId(2)]),
            ByteRange { start: 6, end: 10 },
        ),
        Err(RetentionError::InvalidGraph),
        "tied owners cannot disagree about retention",
    );
    assert_eq!(
        source_site_owner(&index, ByteRange { start: 6, end: 10 }),
        Err(RetentionError::IncompleteMemberConstraints),
        "a single-owner consumer rejects an ambiguous tie",
    );
    assert_eq!(
        index.owners(ByteRange { start: 2, end: 3 }),
        Ok(vec![SourceUnitId(1)]),
        "the smallest containing range wins",
    );
}

#[test]
fn source_site_index_rejects_invalid_parent_forests() {
    let source = "xxxx";
    let missing_parent = inventory(
        source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 4), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 1), Some(9), 1),
        ],
    );
    assert!(matches!(
        SourceSiteOwnerIndex::new(&missing_parent),
        Err(RetentionError::InvalidGraph)
    ));

    let cycle = inventory(
        source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 4), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 2), Some(2), 1),
            unit(2, WrittenUnitKind::NestedItem, (0, 2), Some(1), 2),
        ],
    );
    assert!(matches!(
        SourceSiteOwnerIndex::new(&cycle),
        Err(RetentionError::InvalidGraph)
    ));
}

#[test]
fn source_site_index_allows_an_empty_active_inventory_until_queried() {
    let mut root = unit(0, WrittenUnitKind::CrateRoot, (0, 1), None, 0);
    root.cfg_state = CfgState::Inactive;
    let inventory = inventory("x", vec![root]);
    let index = SourceSiteOwnerIndex::new(&inventory).unwrap();

    assert_eq!(
        index.owners(ByteRange { start: 0, end: 1 }),
        Err(RetentionError::InvalidGraph)
    );
}

#[test]
fn source_site_index_uses_byte_ranges_for_utf8_source() {
    let source = "αβγ";
    let inventory = inventory(
        source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 6), None, 0),
            unit(1, WrittenUnitKind::Item, (2, 6), Some(0), 1),
        ],
    );
    let index = SourceSiteOwnerIndex::new(&inventory).unwrap();

    assert_eq!(
        index.owners(ByteRange { start: 2, end: 4 }),
        Ok(vec![SourceUnitId(1)])
    );
}

#[test]
fn source_site_index_matches_the_naive_owner_definition_for_every_site() {
    fn naive_owners(source: &SourceInventory, site: ByteRange) -> Vec<SourceUnitId> {
        let candidates = source
            .units
            .iter()
            .filter(|unit| unit.cfg_state == CfgState::Active && unit.full_range.contains(site))
            .collect::<Vec<_>>();
        let smallest = candidates.iter().map(|unit| unit.full_range.len()).min();
        let mut ranked = candidates
            .into_iter()
            .filter(|unit| Some(unit.full_range.len()) == smallest)
            .map(|unit| {
                let mut depth = 0_u32;
                let mut parent = unit.parent;
                while let Some(id) = parent {
                    depth += 1;
                    parent = source.units[id.0 as usize].parent;
                }
                (unit.id, depth)
            })
            .collect::<Vec<_>>();
        let deepest = ranked.iter().map(|(_, depth)| *depth).max();
        ranked.retain(|(_, depth)| Some(*depth) == deepest);
        ranked.into_iter().map(|(unit, _)| unit).collect()
    }

    let source = "x".repeat(12);
    let mut inactive = unit(7, WrittenUnitKind::NestedItem, (5, 7), Some(3), 7);
    inactive.cfg_state = CfgState::Inactive;
    let inventory = inventory(
        &source,
        vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 12), None, 0),
            unit(1, WrittenUnitKind::Item, (0, 8), Some(0), 1),
            unit(2, WrittenUnitKind::Item, (4, 12), Some(0), 2),
            unit(3, WrittenUnitKind::NestedItem, (2, 8), Some(1), 3),
            unit(4, WrittenUnitKind::Item, (3, 9), Some(0), 4),
            unit(5, WrittenUnitKind::Item, (2, 8), Some(0), 5),
            unit(6, WrittenUnitKind::NestedItem, (2, 8), Some(1), 6),
            inactive,
            unit(8, WrittenUnitKind::NestedItem, (6, 6), Some(3), 8),
            unit(9, WrittenUnitKind::NestedItem, (6, 6), Some(6), 9),
        ],
    );
    let index = SourceSiteOwnerIndex::new(&inventory).unwrap();

    for start in 0..=12 {
        for end in start..=12 {
            let site = ByteRange { start, end };
            assert_eq!(index.owners(site).unwrap(), naive_owners(&inventory, site));
        }
    }
}

#[test]
fn source_site_index_does_not_rescan_disjoint_units_per_site() {
    const COUNT: u32 = 1_024;
    let source = "x".repeat(COUNT as usize);
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, COUNT), None, 0)];
    units.extend((0..COUNT).map(|start| {
        unit(
            start + 1,
            WrittenUnitKind::Item,
            (start, start + 1),
            Some(0),
            start + 1,
        )
    }));
    let inventory = inventory(&source, units);
    let index = SourceSiteOwnerIndex::new(&inventory).unwrap();
    let mut tree_node_visits = 0;
    let mut owner_visits = 0;
    for start in 0..COUNT {
        let (owners, work) = index
            .test_query(ByteRange {
                start,
                end: start + 1,
            })
            .unwrap();
        assert_eq!(owners, vec![SourceUnitId(start + 1)]);
        tree_node_visits += work.tree_node_visits;
        owner_visits += work.owner_visits;
    }

    assert_eq!(index.test_build_unit_visits(), COUNT as usize + 1);
    assert!(index.test_build_tree_node_visits() <= (COUNT as usize + 1) * 32);
    assert_eq!(owner_visits, COUNT as usize);
    assert!(tree_node_visits <= COUNT as usize * 32);
}

#[test]
fn compiler_roots_do_not_pollute_semantic_requirements() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(
            2,
            DefinitionKind::Static,
            &units[2],
            Some(0),
            "compiler_root",
        ),
        written_definition(3, DefinitionKind::Function, &units[3], Some(0), "entry"),
    ];
    let mut graph = graph(
        definitions,
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let compiler_root = MonoId(graph.mono_nodes.len() as u32);
    graph.mono_nodes.push(MonoNode {
        id: compiler_root,
        key: MonoKey::Static {
            definition: graph.definitions.definitions[2].key.clone(),
        },
        materialized_definition: Some(crate::graph::DefinitionTarget::Local(DefinitionId(2))),
        allocation_observation: None,
    });
    graph.roots.push(RootRecord {
        node: GraphNode::Mono(compiler_root),
        reason: RootReason::UsedAttribute,
    });
    graph.roots.push(RootRecord {
        node: GraphNode::Definition(DefinitionId(3)),
        reason: RootReason::ExplicitEntry,
    });
    graph.edges.push(edge(
        GraphNode::Mono(compiler_root),
        GraphNode::Definition(DefinitionId(2)),
    ));
    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert_eq!(
        retention.semantic_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(3)),
            GraphNode::Mono(MonoId(0)),
        ])
    );
    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Definition(DefinitionId(2)))
    );
}

#[test]
fn a_reexport_definition_root_retains_a_generic_function_without_a_mono_node() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 40), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (21, 30), Some(0), 3),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "generic"),
        written_definition(2, DefinitionKind::Use, &units[2], Some(0), "export"),
        written_definition(3, DefinitionKind::Function, &units[3], Some(0), "unused"),
    ];
    let graph = DependencyGraph::new(
        DefinitionGraph {
            definitions,
            external_definitions: Vec::new(),
            edges: Vec::new(),
        },
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![
            edge(
                GraphNode::Definition(DefinitionId(2)),
                GraphNode::Definition(DefinitionId(1)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(2)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
        ],
        vec![RootRecord {
            node: GraphNode::Definition(DefinitionId(2)),
            reason: RootReason::ExplicitEntry,
        }],
    )
    .unwrap();
    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert!(graph.mono_nodes.is_empty());
    assert_eq!(
        retention.semantic_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ])
    );
    assert_eq!(
        retention.retained_units,
        BTreeSet::from([SourceUnitId(0), SourceUnitId(1), SourceUnitId(2)])
    );
}

#[test]
fn native_link_definition_roots_are_compile_only() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 20), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(
            2,
            DefinitionKind::ForeignModule,
            &units[2],
            Some(0),
            "linked",
        ),
    ];
    let mut graph = graph(
        definitions,
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    graph.roots.push(RootRecord {
        node: GraphNode::Definition(DefinitionId(2)),
        reason: RootReason::NativeLink,
    });

    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert_eq!(
        retention.semantic_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(0)),
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Mono(MonoId(0)),
        ])
    );
    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Definition(DefinitionId(2)))
    );
    assert!(retention.retained_units.contains(&SourceUnitId(2)));
}

#[test]
fn disjunction_uses_shortest_member_then_source_order() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 5), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (6, 60), Some(0), 2),
        unit(3, WrittenUnitKind::ImplMember, (10, 20), Some(2), 3),
        unit(4, WrittenUnitKind::ImplMember, (21, 26), Some(2), 4),
        unit(5, WrittenUnitKind::ImplMember, (30, 35), Some(2), 5),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(2, DefinitionKind::Impl, &units[2], Some(0), "impl"),
        written_definition(
            3,
            DefinitionKind::AssociatedFunction,
            &units[3],
            Some(2),
            "long",
        ),
        written_definition(
            4,
            DefinitionKind::AssociatedFunction,
            &units[4],
            Some(2),
            "first_short",
        ),
        written_definition(
            5,
            DefinitionKind::AssociatedFunction,
            &units[5],
            Some(2),
            "second_short",
        ),
    ];
    let graph = graph(
        definitions,
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints
        .compiler_members
        .disjunctions
        .push(DefinitionDisjunction {
            trigger: DefinitionId(2),
            choices: vec![DefinitionId(5), DefinitionId(3), DefinitionId(4)],
        });
    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();

    assert_eq!(
        retention.retained_units,
        BTreeSet::from([
            SourceUnitId(0),
            SourceUnitId(1),
            SourceUnitId(2),
            SourceUnitId(4),
        ])
    );
}

fn disjunction_lane_fixture() -> (
    SourceInventory,
    DependencyGraph,
    Vec<Option<SourceUnitId>>,
    ValidatedMacroProducts,
) {
    let source = "x".repeat(80);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 80), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 16), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (17, 40), Some(0), 3),
        unit(4, WrittenUnitKind::Item, (41, 42), Some(0), 4),
    ];
    let inventory = inventory(&source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Function, &units[2], Some(0), "short"),
            written_definition(3, DefinitionKind::Function, &units[3], Some(0), "long"),
        ],
        Vec::new(),
    );
    (
        inventory,
        graph,
        vec![
            Some(SourceUnitId(0)),
            Some(SourceUnitId(1)),
            Some(SourceUnitId(2)),
            Some(SourceUnitId(3)),
        ],
        ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap(),
    )
}

#[test]
fn compile_only_carrier_satisfies_compiler_disjunction_without_selecting_source() {
    let (inventory, graph, singleton_units, macro_products) = disjunction_lane_fixture();
    let mut closure = DisjunctionClosure::new(
        &inventory,
        &graph,
        &singleton_units,
        &macro_products,
        &[],
        &[CompilerCrateLoadDisjunction {
            trigger: Some(GraphNode::Definition(DefinitionId(1))),
            choices: vec![
                CompilerCrateLoadCarrier::Definition(DefinitionId(2)),
                CompilerCrateLoadCarrier::Source(SourceUnitId(4)),
            ],
        }],
        &[],
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([
        GraphNode::Definition(DefinitionId(1)),
        GraphNode::Definition(DefinitionId(2)),
    ]);
    let mut actual_required = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    let mut retained = BTreeSet::new();
    closure
        .seed(&compile_required, &actual_required, &retained)
        .unwrap();

    let mut newly_compile = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut token_deltas = Vec::new();
    assert!(
        !closure
            .select(
                DisjunctionDemandLanes {
                    compile: &mut compile_required,
                    actual: &mut actual_required,
                    newly_compile: &mut newly_compile,
                    newly_actual: &mut newly_actual,
                },
                &mut retained,
                &mut newly_retained,
                &mut token_deltas,
            )
            .unwrap()
    );
    assert_eq!(
        compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ])
    );
    assert_eq!(
        actual_required,
        BTreeSet::from([GraphNode::Definition(DefinitionId(1))])
    );
    assert!(retained.is_empty());
    assert!(newly_compile.is_empty());
    assert!(newly_actual.is_empty());
    assert!(newly_retained.is_empty());
    assert!(token_deltas.is_empty());
}

#[test]
fn member_disjunction_closes_compile_and_actual_lanes_independently() {
    let (inventory, graph, singleton_units, macro_products) = disjunction_lane_fixture();
    let mut closure = DisjunctionClosure::new(
        &inventory,
        &graph,
        &singleton_units,
        &macro_products,
        &[],
        &[],
        &[DefinitionDisjunction {
            trigger: DefinitionId(1),
            choices: vec![DefinitionId(2), DefinitionId(3)],
        }],
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(1))]);
    let mut actual_required = BTreeSet::new();
    let mut retained = BTreeSet::new();
    closure
        .seed(&compile_required, &actual_required, &retained)
        .unwrap();

    let mut newly_compile = Vec::new();
    assert!(
        closure
            .select(
                DisjunctionDemandLanes {
                    compile: &mut compile_required,
                    actual: &mut actual_required,
                    newly_compile: &mut newly_compile,
                    newly_actual: &mut Vec::new(),
                },
                &mut retained,
                &mut Vec::new(),
                &mut Vec::new(),
            )
            .unwrap()
    );
    assert_eq!(
        compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ])
    );
    assert_eq!(newly_compile, vec![GraphNode::Definition(DefinitionId(2))]);
    assert!(actual_required.is_empty());

    assert!(actual_required.insert(GraphNode::Definition(DefinitionId(1))));
    closure.add_actual([GraphNode::Definition(DefinitionId(1))]);

    let mut newly_compile = Vec::new();
    let mut newly_actual = Vec::new();
    assert!(
        closure
            .select(
                DisjunctionDemandLanes {
                    compile: &mut compile_required,
                    actual: &mut actual_required,
                    newly_compile: &mut newly_compile,
                    newly_actual: &mut newly_actual,
                },
                &mut retained,
                &mut Vec::new(),
                &mut Vec::new(),
            )
            .unwrap()
    );
    assert_eq!(
        compile_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ])
    );
    assert_eq!(
        actual_required,
        BTreeSet::from([
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(2)),
        ])
    );
    assert!(newly_compile.is_empty());
    assert_eq!(newly_actual, vec![GraphNode::Definition(DefinitionId(2))]);
}

#[test]
fn compiler_disjunction_is_independent_of_trigger_and_source_delta_order() {
    for source_first in [false, true] {
        let (inventory, graph, singleton_units, macro_products) = disjunction_lane_fixture();
        let mut closure = DisjunctionClosure::new(
            &inventory,
            &graph,
            &singleton_units,
            &macro_products,
            &[],
            &[CompilerCrateLoadDisjunction {
                trigger: Some(GraphNode::Definition(DefinitionId(1))),
                choices: vec![CompilerCrateLoadCarrier::Source(SourceUnitId(4))],
            }],
            &[],
        )
        .unwrap();
        let mut compile_required = BTreeSet::new();
        let mut actual_required = BTreeSet::new();
        let mut retained = BTreeSet::new();
        closure
            .seed(&compile_required, &actual_required, &retained)
            .unwrap();

        if source_first {
            assert!(retained.insert(SourceUnitId(4)));
            closure.add_source([SourceUnitId(4)]).unwrap();
            assert!(compile_required.insert(GraphNode::Definition(DefinitionId(1))));
            closure.add_compile([GraphNode::Definition(DefinitionId(1))]);
        } else {
            assert!(compile_required.insert(GraphNode::Definition(DefinitionId(1))));
            closure.add_compile([GraphNode::Definition(DefinitionId(1))]);
            assert!(retained.insert(SourceUnitId(4)));
            closure.add_source([SourceUnitId(4)]).unwrap();
        }

        let mut newly_compile = Vec::new();
        let mut newly_actual = Vec::new();
        let mut newly_retained = Vec::new();
        let mut token_deltas = Vec::new();
        assert!(
            !closure
                .select(
                    DisjunctionDemandLanes {
                        compile: &mut compile_required,
                        actual: &mut actual_required,
                        newly_compile: &mut newly_compile,
                        newly_actual: &mut newly_actual,
                    },
                    &mut retained,
                    &mut newly_retained,
                    &mut token_deltas,
                )
                .unwrap()
        );
        assert_eq!(
            compile_required,
            BTreeSet::from([GraphNode::Definition(DefinitionId(1))])
        );
        assert!(actual_required.is_empty());
        assert_eq!(retained, BTreeSet::from([SourceUnitId(4)]));
        assert!(newly_compile.is_empty());
        assert!(newly_actual.is_empty());
        assert!(newly_retained.is_empty());
        assert!(token_deltas.is_empty());
    }
}

#[test]
fn source_disjunction_is_independent_of_gate_and_choice_delta_order() {
    for choice_first in [false, true] {
        let (inventory, graph, singleton_units, macro_products) = disjunction_lane_fixture();
        let mut closure = DisjunctionClosure::new(
            &inventory,
            &graph,
            &singleton_units,
            &macro_products,
            &[SourceDisjunction {
                trigger: SourceUnitId(1),
                choices: vec![SourceUnitId(4)],
            }],
            &[],
            &[],
        )
        .unwrap();
        let mut compile_required = BTreeSet::new();
        let mut actual_required = BTreeSet::new();
        let mut retained = BTreeSet::new();
        closure
            .seed(&compile_required, &actual_required, &retained)
            .unwrap();

        for unit in if choice_first {
            [SourceUnitId(4), SourceUnitId(1)]
        } else {
            [SourceUnitId(1), SourceUnitId(4)]
        } {
            assert!(retained.insert(unit));
            closure.add_source([unit]).unwrap();
        }

        let mut newly_retained = Vec::new();
        let mut token_deltas = Vec::new();
        assert!(
            !closure
                .select(
                    DisjunctionDemandLanes {
                        compile: &mut compile_required,
                        actual: &mut actual_required,
                        newly_compile: &mut Vec::new(),
                        newly_actual: &mut Vec::new(),
                    },
                    &mut retained,
                    &mut newly_retained,
                    &mut token_deltas,
                )
                .unwrap()
        );
        assert!(compile_required.is_empty());
        assert!(actual_required.is_empty());
        assert_eq!(retained, BTreeSet::from([SourceUnitId(1), SourceUnitId(4)]));
        assert!(newly_retained.is_empty());
        assert!(token_deltas.is_empty());
    }
}

#[test]
fn disjunction_closures_visit_reverse_chains_once_across_waves() {
    const COUNT: u32 = 1_024;
    let source = "x".repeat(COUNT as usize + 1);
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, COUNT + 1), None, 0)];
    units.extend((1..=COUNT).map(|id| unit(id, WrittenUnitKind::Item, (id, id + 1), Some(0), id)));
    let inventory = inventory(&source, units.clone());
    let mut definitions = vec![written_definition(
        0,
        DefinitionKind::Crate,
        &units[0],
        None,
        "crate",
    )];
    definitions.extend((1..=COUNT).map(|id| {
        written_definition(
            id,
            DefinitionKind::Function,
            &units[id as usize],
            Some(0),
            if id == COUNT { "main" } else { "item" },
        )
    }));
    let graph = graph(definitions, Vec::new());
    let singleton_units = (0..=COUNT)
        .map(|id| Some(SourceUnitId(id)))
        .collect::<Vec<_>>();
    let macro_products = ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap();

    let source_disjunctions = (1..=COUNT)
        .map(|trigger| SourceDisjunction {
            trigger: SourceUnitId(trigger),
            choices: vec![SourceUnitId(trigger - 1)],
        })
        .collect::<Vec<_>>();
    let mut source_closure = DisjunctionClosure::new(
        &inventory,
        &graph,
        &singleton_units,
        &macro_products,
        &source_disjunctions,
        &[],
        &[],
    )
    .unwrap();
    let mut compile_required = BTreeSet::new();
    let mut actual_required = BTreeSet::new();
    let mut retained = BTreeSet::from([SourceUnitId(COUNT)]);
    source_closure
        .seed(&compile_required, &actual_required, &retained)
        .unwrap();
    loop {
        let mut required_delta = Vec::new();
        let mut retained_delta = Vec::new();
        if !source_closure
            .select(
                DisjunctionDemandLanes {
                    compile: &mut compile_required,
                    actual: &mut actual_required,
                    newly_compile: &mut required_delta,
                    newly_actual: &mut Vec::new(),
                },
                &mut retained,
                &mut retained_delta,
                &mut Vec::new(),
            )
            .unwrap()
        {
            break;
        }
    }
    assert_eq!(retained.len(), COUNT as usize + 1);
    assert_eq!(source_closure.fact_visits, COUNT as usize);
    assert_eq!(source_closure.reverse_fact_visits, 2 * COUNT as usize);

    let compiler_disjunctions = (1..=COUNT)
        .map(|trigger| CompilerCrateLoadDisjunction {
            trigger: Some(GraphNode::Definition(DefinitionId(trigger))),
            choices: vec![CompilerCrateLoadCarrier::Definition(DefinitionId(
                trigger - 1,
            ))],
        })
        .collect::<Vec<_>>();
    let mut compiler_closure = DisjunctionClosure::new(
        &inventory,
        &graph,
        &singleton_units,
        &macro_products,
        &[],
        &compiler_disjunctions,
        &[],
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT))]);
    let mut actual_required = BTreeSet::new();
    let mut retained = BTreeSet::new();
    compiler_closure
        .seed(&compile_required, &actual_required, &retained)
        .unwrap();
    while compiler_closure
        .select(
            DisjunctionDemandLanes {
                compile: &mut compile_required,
                actual: &mut actual_required,
                newly_compile: &mut Vec::new(),
                newly_actual: &mut Vec::new(),
            },
            &mut retained,
            &mut Vec::new(),
            &mut Vec::new(),
        )
        .unwrap()
    {}
    assert_eq!(compile_required.len(), COUNT as usize + 1);
    assert_eq!(compiler_closure.fact_visits, COUNT as usize);
    assert_eq!(compiler_closure.reverse_fact_visits, 2 * COUNT as usize);

    let member_disjunctions = (1..=COUNT)
        .map(|trigger| DefinitionDisjunction {
            trigger: DefinitionId(trigger),
            choices: vec![DefinitionId(trigger - 1)],
        })
        .collect::<Vec<_>>();
    let mut member_closure = DisjunctionClosure::new(
        &inventory,
        &graph,
        &singleton_units,
        &macro_products,
        &[],
        &[],
        &member_disjunctions,
    )
    .unwrap();
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT))]);
    let mut actual_required = compile_required.clone();
    let mut retained = BTreeSet::new();
    member_closure
        .seed(&compile_required, &actual_required, &retained)
        .unwrap();
    while member_closure
        .select(
            DisjunctionDemandLanes {
                compile: &mut compile_required,
                actual: &mut actual_required,
                newly_compile: &mut Vec::new(),
                newly_actual: &mut Vec::new(),
            },
            &mut retained,
            &mut Vec::new(),
            &mut Vec::new(),
        )
        .unwrap()
    {}
    assert_eq!(compile_required.len(), COUNT as usize + 1);
    assert_eq!(actual_required, compile_required);
    assert_eq!(member_closure.fact_visits, 2 * COUNT as usize);
    assert_eq!(member_closure.reverse_fact_visits, 4 * COUNT as usize);
}

#[test]
fn conditional_member_requirement_needs_both_inputs() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 5), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (6, 30), Some(0), 2),
        unit(3, WrittenUnitKind::TraitMember, (10, 15), Some(2), 3),
        unit(4, WrittenUnitKind::Item, (31, 60), Some(0), 4),
        unit(5, WrittenUnitKind::ImplMember, (40, 50), Some(4), 5),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(2, DefinitionKind::Trait, &units[2], Some(0), "trait"),
        written_definition(
            3,
            DefinitionKind::AssociatedType,
            &units[3],
            Some(2),
            "required",
        ),
        written_definition(4, DefinitionKind::Impl, &units[4], Some(0), "impl"),
        written_definition(
            5,
            DefinitionKind::AssociatedType,
            &units[5],
            Some(4),
            "implementation",
        ),
    ];
    let conditional = ConditionalDefinitionRequirement {
        left: DefinitionId(4),
        right: DefinitionId(3),
        required: DefinitionId(5),
    };

    for (edges, expected_member) in [
        (
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(4)),
            )],
            false,
        ),
        (
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(3)),
            )],
            false,
        ),
        (
            vec![
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(3)),
                ),
                edge(
                    GraphNode::Definition(DefinitionId(1)),
                    GraphNode::Definition(DefinitionId(4)),
                ),
            ],
            true,
        ),
    ] {
        let graph = graph(definitions.clone(), edges);
        let mut constraints = complete_constraints(&inventory, &graph);
        constraints
            .compiler_members
            .conditional_requirements
            .push(conditional);
        let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
        assert_eq!(
            retention.retained_units.contains(&SourceUnitId(5)),
            expected_member
        );
    }
}

#[test]
fn compiler_member_constraints_do_not_collapse_shared_macro_source() {
    let requirement = ConditionalDefinitionRequirement {
        left: DefinitionId(2),
        right: DefinitionId(3),
        required: DefinitionId(4),
    };
    let macro_products = ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap();
    let compiler_members = ValidatedCompilerMemberConstraints {
        requirements_by_trigger: BTreeMap::new(),
        conditional_requirements: vec![requirement],
        conditional_by_trigger: BTreeMap::from([
            (requirement.left, vec![(0, 1)]),
            (requirement.right, vec![(0, 2)]),
        ]),
        disjunctions: Vec::new(),
    };

    for (definitions, expected_member) in [
        (
            BTreeSet::from([GraphNode::Definition(DefinitionId(2))]),
            false,
        ),
        (
            BTreeSet::from([GraphNode::Definition(DefinitionId(3))]),
            false,
        ),
        (
            BTreeSet::from([
                GraphNode::Definition(DefinitionId(2)),
                GraphNode::Definition(DefinitionId(3)),
            ]),
            true,
        ),
    ] {
        // All three products may map to the same written macro invocation.
        // Their compiler identities, rather than that shared source unit,
        // are the operands of the completeness relation.
        let mut required = definitions;
        let mut retained_units = BTreeSet::new();
        close_validated_retention_constraints(
            &macro_products,
            Some(&compiler_members),
            &mut required,
            &mut retained_units,
        );
        assert_eq!(
            required.contains(&GraphNode::Definition(DefinitionId(4))),
            expected_member
        );
    }
}

#[test]
fn direct_and_conditional_member_requirements_close_each_demand_lane() {
    let direct = DefinitionRequirement {
        trigger: DefinitionId(1),
        required: DefinitionId(2),
    };
    let conditional = ConditionalDefinitionRequirement {
        left: DefinitionId(2),
        right: DefinitionId(3),
        required: DefinitionId(4),
    };
    let macro_products = ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap();
    let compiler_members = ValidatedCompilerMemberConstraints {
        requirements_by_trigger: BTreeMap::from([(direct.trigger, vec![direct.required])]),
        conditional_requirements: vec![conditional],
        conditional_by_trigger: BTreeMap::from([
            (conditional.left, vec![(0, 1)]),
            (conditional.right, vec![(0, 2)]),
        ]),
        disjunctions: Vec::new(),
    };
    let trigger = GraphNode::Definition(direct.trigger);
    let right = GraphNode::Definition(conditional.right);
    let direct_requirement = GraphNode::Definition(direct.required);
    let conditional_requirement = GraphNode::Definition(conditional.required);
    let mut compile_present = BTreeSet::from([trigger, right]);
    let mut actual_required = BTreeSet::new();
    let mut retained_units = BTreeSet::new();
    let mut newly_present = Vec::new();
    let mut newly_actual = Vec::new();
    let mut newly_retained = Vec::new();
    let mut closure = RetentionClosure::new(&macro_products, Some(&compiler_members));
    closure
        .seed(&compile_present, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert_eq!(
        compile_present,
        BTreeSet::from([trigger, right, direct_requirement, conditional_requirement])
    );
    assert!(actual_required.is_empty());
    assert_eq!(closure.compile_member_fact_visits, 3);
    assert_eq!(closure.actual_member_fact_visits, 0);

    actual_required.extend([trigger, right]);
    closure.add_actual([trigger, right]);
    closure.close(
        &mut compile_present,
        &mut newly_present,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained,
    );

    assert_eq!(actual_required, compile_present);
    assert_eq!(closure.compile_member_fact_visits, 3);
    assert_eq!(closure.actual_member_fact_visits, 3);
}

#[test]
fn macro_and_member_reverse_chains_visit_each_indexed_fact_once() {
    const COUNT: u32 = 1_024;
    let macro_products = ValidatedMacroProducts::new(
        (0..COUNT)
            .map(|index| MacroMaterialization {
                producer: ExpansionId(index),
                products: vec![GraphNode::Definition(DefinitionId(index))],
                owner_requirements: Vec::new(),
                identity_cohort_root: None,
                contributor_roots: contributor_roots(vec![SourceUnitId(index)]),
            })
            .collect(),
        BTreeSet::new(),
    )
    .unwrap();
    let requirements = (1..COUNT)
        .map(|trigger| DefinitionRequirement {
            trigger: DefinitionId(trigger),
            required: DefinitionId(trigger - 1),
        })
        .collect::<Vec<_>>();
    let compiler_members = ValidatedCompilerMemberConstraints {
        requirements_by_trigger: requirements.iter().fold(
            BTreeMap::<DefinitionId, Vec<DefinitionId>>::new(),
            |mut index, requirement| {
                index
                    .entry(requirement.trigger)
                    .or_default()
                    .push(requirement.required);
                index
            },
        ),
        conditional_requirements: Vec::new(),
        conditional_by_trigger: BTreeMap::new(),
        disjunctions: Vec::new(),
    };
    let mut closure = RetentionClosure::new(&macro_products, Some(&compiler_members));
    let mut compile_required = BTreeSet::from([GraphNode::Definition(DefinitionId(COUNT - 1))]);
    let mut actual_required = compile_required.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_retained_units = Vec::new();
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();

    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained_units,
    );

    assert_eq!(compile_required.len(), COUNT as usize);
    assert_eq!(retained_units.len(), COUNT as usize);
    assert_eq!(closure.compile_member_fact_visits, COUNT as usize - 1);
    assert_eq!(closure.actual_member_fact_visits, COUNT as usize - 1);
    assert_eq!(
        closure.macro_fact_visits,
        COUNT as usize * 4,
        "each trigger, local source, source gate, and materialization root is visited once",
    );
}

#[test]
fn conditional_member_reverse_chain_visits_each_operand_once() {
    const COUNT: u32 = 1_024;
    const COMMON: DefinitionId = DefinitionId(COUNT);
    let macro_products = ValidatedMacroProducts::new(Vec::new(), BTreeSet::new()).unwrap();
    let conditional_requirements = (1..COUNT)
        .map(|left| ConditionalDefinitionRequirement {
            left: DefinitionId(left),
            right: COMMON,
            required: DefinitionId(left - 1),
        })
        .collect::<Vec<_>>();
    let mut conditional_by_trigger = BTreeMap::<DefinitionId, Vec<(usize, u8)>>::new();
    for (index, requirement) in conditional_requirements.iter().enumerate() {
        conditional_by_trigger
            .entry(requirement.left)
            .or_default()
            .push((index, 1));
        conditional_by_trigger
            .entry(requirement.right)
            .or_default()
            .push((index, 2));
    }
    let compiler_members = ValidatedCompilerMemberConstraints {
        requirements_by_trigger: BTreeMap::new(),
        conditional_requirements,
        conditional_by_trigger,
        disjunctions: Vec::new(),
    };
    let mut closure = RetentionClosure::new(&macro_products, Some(&compiler_members));
    let mut compile_required = BTreeSet::from([
        GraphNode::Definition(DefinitionId(COUNT - 1)),
        GraphNode::Definition(COMMON),
    ]);
    let mut actual_required = compile_required.clone();
    let mut retained_units = BTreeSet::new();
    let mut newly_retained_units = Vec::new();
    let mut newly_required = Vec::new();
    let mut newly_actual = Vec::new();

    closure
        .seed(&compile_required, &actual_required, &retained_units)
        .unwrap();
    closure.close(
        &mut compile_required,
        &mut newly_required,
        &mut actual_required,
        &mut newly_actual,
        &mut retained_units,
        &mut newly_retained_units,
    );

    assert_eq!(compile_required.len(), COUNT as usize + 1);
    assert_eq!(closure.compile_member_fact_visits, (COUNT as usize - 1) * 2);
    assert_eq!(closure.actual_member_fact_visits, (COUNT as usize - 1) * 2);
}

#[test]
fn compiler_member_constraint_census_and_structure_fail_closed() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 5), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (6, 30), Some(0), 2),
        unit(3, WrittenUnitKind::TraitMember, (10, 15), Some(2), 3),
        unit(4, WrittenUnitKind::Item, (31, 60), Some(0), 4),
        unit(5, WrittenUnitKind::ImplMember, (40, 50), Some(4), 5),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Trait, &units[2], Some(0), "trait"),
            written_definition(
                3,
                DefinitionKind::AssociatedFunction,
                &units[3],
                Some(2),
                "required",
            ),
            written_definition(4, DefinitionKind::Impl, &units[4], Some(0), "impl"),
            written_definition(
                5,
                DefinitionKind::AssociatedFunction,
                &units[5],
                Some(4),
                "implementation",
            ),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );

    let mut missing = complete_constraints(&inventory, &graph);
    missing.compiler_members.classified_members.pop();
    assert_eq!(
        compute_retention(&inventory, &graph, &missing),
        Err(RetentionError::IncompleteMemberConstraints)
    );

    let mut wrong_parent = complete_constraints(&inventory, &graph);
    wrong_parent
        .compiler_members
        .conditional_requirements
        .push(ConditionalDefinitionRequirement {
            left: DefinitionId(4),
            right: DefinitionId(3),
            required: DefinitionId(3),
        });
    assert_eq!(
        compute_retention(&inventory, &graph, &wrong_parent),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn atomicity_and_an_empty_impl_shell_are_retained() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::MacroInvocation, (2, 4), Some(1), 1),
        unit(3, WrittenUnitKind::Item, (11, 20), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(2, DefinitionKind::Impl, &units[3], Some(0), "empty_impl"),
    ];
    let graph = graph(
        definitions,
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );
    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert_eq!(
        retention.retained_units,
        BTreeSet::from([
            SourceUnitId(0),
            SourceUnitId(1),
            SourceUnitId(2),
            SourceUnitId(3),
        ])
    );
}

#[test]
fn source_requirement_closure_visits_each_fact_once_across_incremental_waves() {
    const COUNT: u32 = 1_024;
    let unit_count = COUNT as usize * 2;
    let groups = (0..unit_count)
        .map(|unit| vec![SourceUnitId(unit as u32)])
        .collect::<Vec<_>>();
    let requirements = (0..COUNT)
        .map(|trigger| SourceRequirement {
            trigger: SourceUnitId(trigger),
            required: SourceUnitId(COUNT + trigger),
        })
        .collect::<Vec<_>>();
    let index =
        SourceRequirementIndex::new(unit_count, &groups, &requirements, &[], &[], &[]).unwrap();
    let mut closure = SourceRequirementClosure::new(&index, SourceRequirementMode::Compile);
    let mut retained = BTreeSet::new();
    let mut newly_retained = Vec::new();
    closure.seed(&retained).unwrap();
    for trigger in 0..COUNT {
        let trigger = SourceUnitId(trigger);
        retained.insert(trigger);
        closure.add([trigger]).unwrap();
        closure.close(&mut retained, &mut newly_retained).unwrap();
    }

    assert_eq!(retained.len(), unit_count);
    assert_eq!(closure.unit_visits, unit_count);
    assert_eq!(closure.requirement_visits, COUNT as usize);
    assert_eq!(closure.group_member_visits, unit_count);
}

#[test]
fn invalid_constraints_and_missing_member_coverage_fail_closed() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 10), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (11, 30), Some(0), 2),
        unit(3, WrittenUnitKind::TraitMember, (15, 20), Some(2), 3),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Trait, &units[2], Some(0), "trait"),
            written_definition(
                3,
                DefinitionKind::AssociatedFunction,
                &units[3],
                Some(2),
                "member",
            ),
        ],
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );

    let mut missing = SourceConstraints::from_source(&inventory);
    assert_eq!(
        compute_retention(&inventory, &graph, &missing),
        Err(RetentionError::IncompleteMacroProductConstraints),
        "an absent declarative-macro snapshot is not an empty observation"
    );
    missing
        .set_declarative_macro_constraints(DeclarativeMacroConstraints {
            rule_selections: Vec::new(),
            producer_coverage: MacroProducerCoverageInventory::test_new(Vec::new()),
            complete_output_meaning: MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
            outputless_expansions: Vec::new(),
        })
        .unwrap();
    assert_eq!(
        compute_retention(&inventory, &graph, &missing),
        Err(RetentionError::IncompleteMemberConstraints)
    );

    let mut invalid = complete_constraints(&inventory, &graph);
    invalid
        .compiler_members
        .requirements
        .push(DefinitionRequirement {
            trigger: DefinitionId(3),
            required: DefinitionId(99),
        });
    assert_eq!(
        compute_retention(&inventory, &graph, &invalid),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn retained_derive_outputs_close_over_influences_and_helper_attributes() {
    let source = "x".repeat(128);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 128), None, 0),
        unit(1, WrittenUnitKind::Item, (100, 120), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 90), Some(0), 2),
        unit(3, WrittenUnitKind::MacroInvocation, (0, 30), Some(2), 3),
        unit(4, WrittenUnitKind::MacroInvocation, (9, 14), Some(3), 4),
        unit(5, WrittenUnitKind::MacroInvocation, (16, 23), Some(3), 5),
        unit(6, WrittenUnitKind::MacroInvocation, (40, 50), Some(2), 6),
    ];
    let mut inventory = inventory(&source, units.clone());
    inventory.derive_targets = vec![DeriveTargetSourceFacts::Complete {
        target: SourceUnitId(2),
        attributes: vec![DeriveAttributeSourceFacts {
            attribute: SourceUnitId(3),
            elements: vec![SourceUnitId(4), SourceUnitId(5)],
            directly_written: true,
        }],
        helper_candidates: vec![units[6].full_range],
        influences: vec![DeriveSourceRequirement {
            trigger: SourceUnitId(4),
            required: SourceUnitId(5),
        }],
        helpers: vec![DeriveHelperSourceFacts {
            attribute: SourceUnitId(6),
            provider: SourceUnitId(5),
        }],
    }];

    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            expanded_definition(
                2,
                DefinitionKind::Function,
                &units[4],
                Some(0),
                "derived_output",
            ),
        ],
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );
    add_macro_expansion(&mut graph, &units[4], DefinitionId(1), [DefinitionId(2)]);
    let constraints = complete_constraints(&inventory, &graph);

    assert_eq!(
        constraints
            .derive_requirements
            .iter()
            .copied()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([
            SourceRequirement {
                trigger: SourceUnitId(4),
                required: SourceUnitId(5),
            },
            SourceRequirement {
                trigger: SourceUnitId(5),
                required: SourceUnitId(6),
            },
            SourceRequirement {
                trigger: SourceUnitId(6),
                required: SourceUnitId(5),
            },
        ])
    );
    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(retention.retained_units.contains(&SourceUnitId(4)));
    assert!(retention.retained_units.contains(&SourceUnitId(5)));
    assert!(retention.retained_units.contains(&SourceUnitId(6)));

    let mut incomplete = constraints.clone();
    incomplete.derive_requirements.pop();
    assert_eq!(
        compute_retention(&inventory, &graph, &incomplete),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn reachable_macro_expansion_requires_only_its_selected_rule() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (24, 32), Some(0), 1),
        unit(2, WrittenUnitKind::MacroDefinition, (0, 23), Some(0), 2),
        unit(3, WrittenUnitKind::MacroRule, (5, 12), Some(2), 3),
        unit(4, WrittenUnitKind::MacroRule, (13, 22), Some(2), 4),
    ];
    let mut inventory = inventory(source, units.clone());
    inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(2),
        rules: vec![SourceUnitId(3), SourceUnitId(4)],
        observed_selections: vec![SourceUnitId(3), SourceUnitId(3)],
    }];
    let mut graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Macro, &units[2], Some(0), "m"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let expansion_kind = ExpansionKind::Macro {
        style: MacroStyle::Bang,
        name: "m".into(),
    };
    graph.expansions.push(ExpansionNode {
        id: ExpansionId(0),
        key: ExpansionKey(vec![ExpansionKeyPart {
            kind: expansion_kind.clone(),
            fragment: Some(ExpansionFragmentKind::Expression),
            implementation: Some(MacroImplementationKind::Declarative),
            invocation_range: Some(ByteRange { start: 24, end: 25 }),
            node_range: Some(ByteRange { start: 24, end: 25 }),
            target_range: None,
            macro_definition: Some(DefinitionReferenceKey::Local(
                graph.definitions.definitions[2].key.clone(),
            )),
            selected_macro_rule: Some(units[3].full_range),
            same_role_ordinal: 0,
        }]),
        kind: expansion_kind,
        fragment: Some(ExpansionFragmentKind::Expression),
        implementation: Some(MacroImplementationKind::Declarative),
        discovered_in: None,
        semantic_parent: None,
        source_call_parent: None,
        written_invocation: None,
        source_owner: Some(DefinitionId(1)),
        macro_definition: Some(DefinitionTarget::Local(DefinitionId(2))),
    });
    let mut repeated_expansion = graph.expansions[0].clone();
    repeated_expansion.id = ExpansionId(1);
    repeated_expansion.key.0[0].invocation_range = Some(ByteRange { start: 25, end: 26 });
    repeated_expansion.key.0[0].node_range = Some(ByteRange { start: 25, end: 26 });
    repeated_expansion.key.0[0].same_role_ordinal = 1;
    graph.expansions.push(repeated_expansion);
    graph.edges.extend([
        DependencyEdge {
            from: GraphNode::Definition(DefinitionId(1)),
            to: GraphNode::Expansion(ExpansionId(0)),
            kind: DependencyKind::ExpansionUse,
            sites: vec![ObservationSite::CompilerGenerated],
            evidence: EvidenceOrigin::Compiler,
        },
        DependencyEdge {
            from: GraphNode::Expansion(ExpansionId(0)),
            to: GraphNode::Definition(DefinitionId(2)),
            kind: DependencyKind::MacroDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
        DependencyEdge {
            from: GraphNode::Definition(DefinitionId(1)),
            to: GraphNode::Expansion(ExpansionId(1)),
            kind: DependencyKind::ExpansionUse,
            sites: vec![ObservationSite::CompilerGenerated],
            evidence: EvidenceOrigin::Compiler,
        },
        DependencyEdge {
            from: GraphNode::Expansion(ExpansionId(1)),
            to: GraphNode::Definition(DefinitionId(2)),
            kind: DependencyKind::MacroDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        },
    ]);

    let mut missing_selection_graph = graph.clone();
    missing_selection_graph.expansions[0].key.0[0].selected_macro_rule = None;
    assert_eq!(
        collect_declarative_macro_constraints(
            &inventory,
            &missing_selection_graph.definitions,
            &missing_selection_graph.expansions,
            MacroProducerCoverageInventory::test_new(Vec::new()),
            MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
            Vec::new(),
        ),
        Err(RetentionError::InvalidConstraint),
        "every in-scope expansion needs a collected rule selection"
    );

    let mut missing_definition_graph = graph.clone();
    missing_definition_graph.expansions[1].macro_definition = None;
    missing_definition_graph.expansions[1].key.0[0].macro_definition = None;
    assert_eq!(
        collect_declarative_macro_constraints(
            &inventory,
            &missing_definition_graph.definitions,
            &missing_definition_graph.expansions,
            MacroProducerCoverageInventory::test_new(Vec::new()),
            MacroCompleteOutputMeaningInventory::test_new(Vec::new()),
            Vec::new(),
        ),
        Err(RetentionError::InvalidConstraint),
        "coverage must not depend on the macro-definition relation being present"
    );

    let constraints = complete_constraints(&inventory, &graph);
    assert_eq!(
        constraints.macro_rule_selections().unwrap(),
        vec![
            MacroRuleSelectionRequirement {
                expansion: ExpansionId(0),
                rule: SourceUnitId(3),
            },
            MacroRuleSelectionRequirement {
                expansion: ExpansionId(1),
                rule: SourceUnitId(3),
            },
        ]
    );
    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(retention.retained_units.contains(&SourceUnitId(2)));
    assert!(retention.retained_units.contains(&SourceUnitId(3)));
    assert!(!retention.retained_units.contains(&SourceUnitId(4)));

    let mut missing_repeated_selection = constraints.clone();
    missing_repeated_selection
        .declarative_macros
        .as_mut()
        .unwrap()
        .rule_selections
        .pop();
    assert_eq!(
        compute_retention(&inventory, &graph, &missing_repeated_selection),
        Err(RetentionError::InvalidConstraint),
        "every expansion must keep its own selection even when the rule is shared"
    );

    let mut normalized_graph = graph.clone();
    for expansion in &mut normalized_graph.expansions {
        expansion.key.0[0].selected_macro_rule = Some(ByteRange { start: 6, end: 13 });
    }
    let normalized_retention =
        compute_retention(&inventory, &normalized_graph, &constraints).unwrap();
    assert_eq!(normalized_retention, retention);

    let mut orphaned_graph = graph.clone();
    orphaned_graph.edges.retain(|edge| {
        !(edge.from == GraphNode::Definition(DefinitionId(1))
            && matches!(edge.to, GraphNode::Expansion(_)))
    });
    orphaned_graph.edges.push(edge(
        GraphNode::Definition(DefinitionId(1)),
        GraphNode::Definition(DefinitionId(2)),
    ));
    let orphaned = compute_retention(&inventory, &orphaned_graph, &constraints).unwrap();
    assert!(orphaned.retained_units.contains(&SourceUnitId(2)));
    assert!(orphaned.retained_units.contains(&SourceUnitId(3)));
    assert!(!orphaned.retained_units.contains(&SourceUnitId(4)));
}

#[test]
fn a_written_outputless_invocation_keeps_its_rule_only_while_its_source_site_survives() {
    fn run(invocation_group: u32) -> Retention {
        let source = "x".repeat(64);
        let units = vec![
            unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
            unit(1, WrittenUnitKind::Item, (32, 64), Some(0), 1),
            unit(
                2,
                WrittenUnitKind::MacroInvocation,
                (40, 41),
                Some(1),
                invocation_group,
            ),
            unit(3, WrittenUnitKind::MacroDefinition, (0, 31), Some(0), 3),
            unit(4, WrittenUnitKind::MacroRule, (5, 30), Some(3), 4),
        ];
        let mut inventory = inventory(&source, units.clone());
        inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
            definition: SourceUnitId(3),
            rules: vec![SourceUnitId(4)],
            observed_selections: vec![SourceUnitId(4)],
        }];
        let mut graph = graph(
            vec![
                written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
                written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
                written_definition(2, DefinitionKind::Macro, &units[3], Some(0), "m"),
            ],
            vec![edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            )],
        );
        let expansion = add_macro_expansion(&mut graph, &units[2], DefinitionId(1), []);
        graph.expansions[expansion.0 as usize].macro_definition =
            Some(DefinitionTarget::Local(DefinitionId(2)));
        graph.expansions[expansion.0 as usize].key.0[0].macro_definition = Some(
            DefinitionReferenceKey::Local(graph.definitions.definitions[2].key.clone()),
        );
        graph.expansions[expansion.0 as usize].key.0[0].selected_macro_rule =
            Some(units[4].full_range);
        graph.edges.push(DependencyEdge {
            from: GraphNode::Expansion(expansion),
            to: GraphNode::Definition(DefinitionId(2)),
            kind: DependencyKind::MacroDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Compiler,
        });
        let mut constraints = complete_constraints(&inventory, &graph);
        *outputless_mut(&mut constraints) = vec![expansion];
        compute_retention(&inventory, &graph, &constraints).unwrap()
    }

    let retained = run(1);
    assert!(retained.retained_units.contains(&SourceUnitId(2)));
    assert!(retained.retained_units.contains(&SourceUnitId(3)));
    assert!(retained.retained_units.contains(&SourceUnitId(4)));
    assert!(
        retained
            .compile_required
            .contains(&GraphNode::Expansion(ExpansionId(0)))
    );

    let removed = run(2);
    assert!(!removed.retained_units.contains(&SourceUnitId(2)));
    assert!(!removed.retained_units.contains(&SourceUnitId(3)));
    assert!(!removed.retained_units.contains(&SourceUnitId(4)));
    assert!(
        !removed
            .compile_required
            .contains(&GraphNode::Expansion(ExpansionId(0)))
    );
}

#[test]
fn retained_unobserved_macro_definition_keeps_one_rule() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (24, 32), Some(0), 1),
        unit(2, WrittenUnitKind::MacroDefinition, (0, 23), Some(0), 2),
        unit(3, WrittenUnitKind::MacroRule, (5, 12), Some(2), 3),
        unit(4, WrittenUnitKind::MacroRule, (13, 22), Some(2), 4),
    ];
    let mut inventory = inventory(source, units.clone());
    inventory.macro_rules = vec![MacroRuleSourceFacts::Refined {
        definition: SourceUnitId(2),
        rules: vec![SourceUnitId(3), SourceUnitId(4)],
        observed_selections: Vec::new(),
    }];
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Macro, &units[2], Some(0), "m"),
        ],
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(2)),
            ),
        ],
    );

    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();
    assert!(retention.retained_units.contains(&SourceUnitId(2)));
    assert!(retention.retained_units.contains(&SourceUnitId(3)));
    assert!(!retention.retained_units.contains(&SourceUnitId(4)));

    let mut missing = complete_constraints(&inventory, &graph);
    missing.disjunctions.clear();
    assert_eq!(
        compute_retention(&inventory, &graph, &missing),
        Err(RetentionError::InvalidConstraint)
    );
}

#[test]
fn compiler_generated_load_keeps_the_source_of_its_external_condition() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (48, 64), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 32), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(
                2,
                DefinitionKind::Function,
                &units[2],
                Some(0),
                "loads_need",
            ),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let needs = external_dependency(10, ExternalDependencyKind::MacrosOnly);
    let runtime = external_dependency(20, ExternalDependencyKind::Conditional);
    let needs_load = external_load(needs, [needs]);
    let runtime_load = external_load(runtime, [runtime]);
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![needs, runtime];
    constraints.external_crates.activations = vec![ExternalCrateActivation {
        source: Some(SourceUnitId(2)),
        load: needs_load.clone(),
    }];
    constraints.external_crates.compiler_generated_activations =
        vec![CompilerGeneratedCrateActivation {
            load: runtime_load,
            condition: Some(needs.crate_identity),
        }];
    constraints.external_crates.providers = vec![ExternalMetadataProvider {
        crate_identity: runtime.crate_identity,
        kind: ExternalMetadataProviderKind::PanicRuntime,
    }];

    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(retention.retained_units.contains(&SourceUnitId(2)));

    constraints
        .external_crates
        .activations
        .push(ExternalCrateActivation {
            source: None,
            load: needs_load,
        });
    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(!retention.retained_units.contains(&SourceUnitId(2)));
}

#[test]
fn external_crate_bindings_remain_definition_domain_carriers() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 48), None, 0),
        unit(1, WrittenUnitKind::Item, (32, 48), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 24), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(
                2,
                DefinitionKind::ExternCrate,
                &units[2],
                Some(0),
                "runtime",
            ),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let dependency = external_dependency(10, ExternalDependencyKind::Unconditional);
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![dependency];
    constraints.external_crates.bindings = vec![ExternalCrateBinding {
        definition: DefinitionId(2),
        target: ExternalCrateBindingTarget::External(external_load(dependency, [dependency])),
    }];
    constraints.external_crates.providers = vec![ExternalMetadataProvider {
        crate_identity: dependency.crate_identity,
        kind: ExternalMetadataProviderKind::PanicRuntime,
    }];

    assert_eq!(
        validate_external_crate_facts(
            &inventory,
            &graph,
            &definition_source_units(&inventory, &graph).unwrap(),
            &constraints.external_crates,
        )
        .unwrap(),
        vec![CompilerCrateLoadDisjunction {
            trigger: None,
            choices: vec![CompilerCrateLoadCarrier::Definition(DefinitionId(2))],
        }]
    );
}

#[test]
fn compiler_metadata_requirements_keep_their_external_source() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (48, 64), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 32), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(
                2,
                DefinitionKind::Function,
                &units[2],
                Some(0),
                "loads_need",
            ),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let dependency = external_dependency(10, ExternalDependencyKind::Unconditional);
    let load = external_load(dependency, [dependency]);

    for kind in [
        ExternalMetadataRequirementKind::Allocator,
        ExternalMetadataRequirementKind::PanicRuntime,
    ] {
        let mut constraints = complete_constraints(&inventory, &graph);
        constraints.external_crates.loaded_crates = vec![dependency];
        constraints.external_crates.activations = vec![ExternalCrateActivation {
            source: Some(SourceUnitId(2)),
            load: load.clone(),
        }];
        constraints.external_crates.requirements = vec![ExternalMetadataRequirement {
            crate_identity: dependency.crate_identity,
            kind,
        }];

        let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
        assert!(retention.retained_units.contains(&SourceUnitId(2)));

        constraints
            .external_crates
            .activations
            .push(ExternalCrateActivation {
                source: None,
                load: load.clone(),
            });
        let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
        assert!(!retention.retained_units.contains(&SourceUnitId(2)));
    }
}

#[test]
fn compiler_metadata_requirement_uses_one_smallest_carrier() {
    let source = "x".repeat(80);
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 80), None, 0),
        unit(1, WrittenUnitKind::Item, (60, 80), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 40), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (41, 55), Some(0), 3),
    ];
    let inventory = inventory(&source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Function, &units[2], Some(0), "large"),
            written_definition(3, DefinitionKind::Function, &units[3], Some(0), "small"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let large = external_dependency(10, ExternalDependencyKind::Unconditional);
    let small = external_dependency(20, ExternalDependencyKind::MacrosOnly);
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![large, small];
    constraints.external_crates.activations = vec![
        ExternalCrateActivation {
            source: Some(SourceUnitId(2)),
            load: external_load(large, [large]),
        },
        ExternalCrateActivation {
            source: Some(SourceUnitId(3)),
            load: external_load(small, [small]),
        },
    ];
    constraints.external_crates.requirements = vec![
        ExternalMetadataRequirement {
            crate_identity: large.crate_identity,
            kind: ExternalMetadataRequirementKind::Allocator,
        },
        ExternalMetadataRequirement {
            crate_identity: small.crate_identity,
            kind: ExternalMetadataRequirementKind::Allocator,
        },
    ];

    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(!retention.retained_units.contains(&SourceUnitId(2)));
    assert!(retention.retained_units.contains(&SourceUnitId(3)));

    constraints.external_crates.local_requirements = vec![LocalMetadataRequirement {
        source: None,
        kind: ExternalMetadataRequirementKind::Allocator,
    }];
    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(!retention.retained_units.contains(&SourceUnitId(2)));
    assert!(!retention.retained_units.contains(&SourceUnitId(3)));
}

#[test]
fn provider_choice_preserves_the_required_dependency_kind() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (48, 64), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 20), Some(0), 2),
        unit(3, WrittenUnitKind::Item, (21, 40), Some(0), 3),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Function, &units[2], Some(0), "weak"),
            written_definition(3, DefinitionKind::Function, &units[3], Some(0), "strong"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let provider = external_dependency(10, ExternalDependencyKind::Unconditional);
    let weak = external_dependency(20, ExternalDependencyKind::MacrosOnly);
    let strong = external_dependency(30, ExternalDependencyKind::Unconditional);
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![provider, weak, strong];
    constraints.external_crates.activations = vec![
        ExternalCrateActivation {
            source: Some(SourceUnitId(2)),
            load: external_load(
                weak,
                [
                    weak,
                    external_dependency(10, ExternalDependencyKind::MacrosOnly),
                ],
            ),
        },
        ExternalCrateActivation {
            source: Some(SourceUnitId(3)),
            load: external_load(strong, [strong, provider]),
        },
    ];
    constraints.external_crates.providers = vec![ExternalMetadataProvider {
        crate_identity: provider.crate_identity,
        kind: ExternalMetadataProviderKind::GlobalAllocator,
    }];

    let retention = compute_retention(&inventory, &graph, &constraints).unwrap();
    assert!(!retention.retained_units.contains(&SourceUnitId(2)));
    assert!(retention.retained_units.contains(&SourceUnitId(3)));
}

#[test]
fn external_compiler_root_selects_a_source_only_when_reached() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 64), None, 0),
        unit(1, WrittenUnitKind::Item, (48, 64), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 32), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        written_definition(2, DefinitionKind::Function, &units[2], Some(0), "load"),
    ];
    let external = ExternalDefinition {
        id: ExternalDefinitionId(0),
        key: ExternalDefinitionKey {
            crate_identity: 10,
            crate_name: "external".to_owned(),
            def_path_hash: [1; 16],
        },
        path: "external::entry".to_owned(),
    };
    let mut live_graph = graph(
        definitions.clone(),
        vec![
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::Definition(DefinitionId(0)),
            ),
            edge(
                GraphNode::Definition(DefinitionId(1)),
                GraphNode::ExternalDefinition(ExternalDefinitionId(0)),
            ),
        ],
    );
    live_graph.definitions.external_definitions = vec![external.clone()];
    let load = external_dependency(10, ExternalDependencyKind::Unconditional);
    let mut constraints = complete_constraints(&inventory, &live_graph);
    constraints.external_crates.activations = vec![ExternalCrateActivation {
        source: Some(SourceUnitId(2)),
        load: external_load(load, [load]),
    }];

    let retention = compute_retention(&inventory, &live_graph, &constraints).unwrap();
    assert!(retention.retained_units.contains(&SourceUnitId(2)));

    let mut dead_graph = graph(
        definitions,
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    dead_graph.definitions.external_definitions = vec![external];
    let dead_retention = compute_retention(&inventory, &dead_graph, &constraints).unwrap();
    assert!(!dead_retention.retained_units.contains(&SourceUnitId(2)));
}

#[test]
fn missing_external_activation_is_an_observation_gap() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (16, 32), Some(0), 1),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![external_dependency(
        10,
        ExternalDependencyKind::Unconditional,
    )];
    constraints.external_crates.providers = vec![ExternalMetadataProvider {
        crate_identity: 10,
        kind: ExternalMetadataProviderKind::CompilerBuiltins,
    }];
    assert_eq!(
        compute_retention(&inventory, &graph, &constraints),
        Err(RetentionError::IncompleteExternalCrateConstraints)
    );
}

#[test]
fn removable_user_external_native_link_metadata_is_rejected() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 48), None, 0),
        unit(1, WrittenUnitKind::Item, (32, 48), Some(0), 1),
        unit(2, WrittenUnitKind::Item, (0, 24), Some(0), 2),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            written_definition(2, DefinitionKind::Function, &units[2], Some(0), "load"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let dependency = external_dependency(10, ExternalDependencyKind::Unconditional);
    let load = external_load(dependency, [dependency]);
    let mut constraints = complete_constraints(&inventory, &graph);
    constraints.external_crates.loaded_crates = vec![dependency];
    constraints.external_crates.activations = vec![ExternalCrateActivation {
        source: Some(SourceUnitId(2)),
        load: load.clone(),
    }];
    constraints.external_crates.providers = vec![ExternalMetadataProvider {
        crate_identity: dependency.crate_identity,
        kind: ExternalMetadataProviderKind::ExternalNativeLink,
    }];

    assert!(compute_retention(&inventory, &graph, &constraints).is_ok());

    constraints.external_crates.user_artifact_crates = vec![dependency.crate_identity];
    assert_eq!(
        compute_retention(&inventory, &graph, &constraints),
        Err(RetentionError::UnsupportedExternalNativeLink)
    );

    constraints.external_crates.activations[0].source = Some(SourceUnitId(0));
    assert!(compute_retention(&inventory, &graph, &constraints).is_ok());

    constraints.external_crates.activations[0].source = None;
    assert!(compute_retention(&inventory, &graph, &constraints).is_ok());
}

#[test]
fn order_sensitive_providers_require_one_crate_identity() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 32), None, 0),
        unit(1, WrittenUnitKind::Item, (16, 32), Some(0), 1),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );

    for provider_kind in [
        ExternalMetadataProviderKind::CompilerBuiltins,
        ExternalMetadataProviderKind::ProfilerRuntime,
        ExternalMetadataProviderKind::DefaultLibAllocator,
    ] {
        let first = external_dependency(10, ExternalDependencyKind::Conditional);
        let second = external_dependency(20, ExternalDependencyKind::Conditional);
        let mut constraints = complete_constraints(&inventory, &graph);
        constraints.external_crates.loaded_crates = vec![first, second];
        constraints.external_crates.activations = vec![
            ExternalCrateActivation {
                source: None,
                load: external_load(first, [first]),
            },
            ExternalCrateActivation {
                source: None,
                load: external_load(second, [second]),
            },
        ];
        constraints.external_crates.providers = vec![
            ExternalMetadataProvider {
                crate_identity: first.crate_identity,
                kind: provider_kind,
            },
            ExternalMetadataProvider {
                crate_identity: second.crate_identity,
                kind: provider_kind,
            },
        ];

        assert_eq!(
            compute_retention(&inventory, &graph, &constraints),
            Err(RetentionError::IncompleteExternalCrateConstraints)
        );
        assert_eq!(
            external_compiler_observation(&constraints),
            Err(RetentionError::IncompleteExternalCrateConstraints)
        );
    }
}

#[test]
fn external_compiler_outcome_detects_provider_and_kind_changes() {
    let provider = ExternalCompilerMetadataFact::Provider {
        crate_identity: 10,
        provider: ExternalMetadataProviderKind::GlobalAllocator,
        dependency_kind: ExternalDependencyKind::Unconditional,
    };
    let requirement =
        ExternalCompilerMetadataFact::Requirement(ExternalMetadataRequirementKind::PanicRuntime);
    let original = ExternalCompilerExpectation {
        metadata: BTreeSet::from([provider, requirement]),
        external_crates: BTreeSet::from([external_dependency(
            20,
            ExternalDependencyKind::Conditional,
        )]),
    };
    let matching = ExternalCompilerObservation {
        metadata: BTreeSet::from([provider, requirement]),
        loaded_crates: BTreeSet::from([external_dependency(
            20,
            ExternalDependencyKind::Conditional,
        )]),
    };
    assert_eq!(
        external_compiler_outcome_difference(&original, &matching),
        None
    );

    let mut missing_provider = matching.clone();
    missing_provider.metadata.remove(&provider);
    assert!(matches!(
        external_compiler_outcome_difference(&original, &missing_provider),
        Some(ExternalCompilerOutcomeDifference::Metadata { .. })
    ));

    let mut weaker_provider = matching.clone();
    weaker_provider.metadata.remove(&provider);
    weaker_provider
        .metadata
        .insert(ExternalCompilerMetadataFact::Provider {
            crate_identity: 10,
            provider: ExternalMetadataProviderKind::GlobalAllocator,
            dependency_kind: ExternalDependencyKind::Conditional,
        });
    assert!(matches!(
        external_compiler_outcome_difference(&original, &weaker_provider),
        Some(ExternalCompilerOutcomeDifference::Metadata { .. })
    ));

    let mut additional_provider = matching.clone();
    additional_provider
        .metadata
        .insert(ExternalCompilerMetadataFact::Provider {
            crate_identity: 30,
            provider: ExternalMetadataProviderKind::PanicRuntime,
            dependency_kind: ExternalDependencyKind::Conditional,
        });
    assert!(matches!(
        external_compiler_outcome_difference(&original, &additional_provider),
        Some(ExternalCompilerOutcomeDifference::Metadata { .. })
    ));

    let mut missing_requirement = matching.clone();
    missing_requirement.metadata.remove(&requirement);
    assert!(matches!(
        external_compiler_outcome_difference(&original, &missing_requirement),
        Some(ExternalCompilerOutcomeDifference::Metadata { .. })
    ));

    let mut weaker_external = matching;
    weaker_external.loaded_crates =
        BTreeSet::from([external_dependency(20, ExternalDependencyKind::MacrosOnly)]);
    assert_eq!(
        external_compiler_outcome_difference(&original, &weaker_external),
        Some(ExternalCompilerOutcomeDifference::ExternalCrate {
            crate_identity: 20,
            original: ExternalDependencyKind::Conditional,
            reduced: Some(ExternalDependencyKind::MacrosOnly),
        })
    );

    let stronger_external = ExternalCompilerObservation {
        metadata: BTreeSet::from([provider, requirement]),
        loaded_crates: BTreeSet::from([external_dependency(
            20,
            ExternalDependencyKind::Unconditional,
        )]),
    };
    assert_eq!(
        external_compiler_outcome_difference(&original, &stronger_external),
        Some(ExternalCompilerOutcomeDifference::ExternalCrate {
            crate_identity: 20,
            original: ExternalDependencyKind::Conditional,
            reduced: Some(ExternalDependencyKind::Unconditional),
        })
    );
}

#[test]
fn macro_source_contributor_index_is_keyed_and_fails_closed() {
    const COMPONENTS: u32 = 256;
    let mut units = vec![unit(0, WrittenUnitKind::CrateRoot, (0, 1), None, 0)];
    let mut templates = Vec::new();
    let mut repetitions = Vec::new();
    for component in 0..COMPONENTS {
        let rule = 1 + component * 4;
        let template = rule + 1;
        let invocation = rule + 2;
        let element = rule + 3;
        units.extend([
            unit(rule, WrittenUnitKind::MacroRule, (0, 1), Some(0), rule),
            unit(
                template,
                WrittenUnitKind::NestedItem,
                (0, 1),
                Some(rule),
                template,
            ),
            unit(
                invocation,
                WrittenUnitKind::MacroInvocation,
                (0, 1),
                Some(0),
                invocation,
            ),
            unit(
                element,
                WrittenUnitKind::NestedItem,
                (0, 1),
                Some(invocation),
                element,
            ),
        ]);
        templates.push(MacroTemplateSourceFacts {
            unit: SourceUnitId(template),
            rule: SourceUnitId(rule),
        });
        repetitions.push(MacroRepetitionSourceFacts {
            invocation: SourceUnitId(invocation),
            rule: SourceUnitId(rule),
            matcher_range: ByteRange { start: 0, end: 1 },
            parent: SourceUnitId(invocation),
            repetition_path: vec![0],
            input_range: ByteRange { start: 0, end: 1 },
            elements: vec![MacroRepetitionElementSourceFacts {
                unit: SourceUnitId(element),
                separator_after: None,
            }],
            minimum: 0,
            maximum: None,
        });
    }
    let empty_invocation = 1 + COMPONENTS * 4;
    units.push(unit(
        empty_invocation,
        WrittenUnitKind::MacroInvocation,
        (0, 1),
        Some(0),
        empty_invocation,
    ));
    repetitions.push(MacroRepetitionSourceFacts {
        invocation: SourceUnitId(empty_invocation),
        rule: SourceUnitId(1),
        matcher_range: ByteRange { start: 0, end: 1 },
        parent: SourceUnitId(empty_invocation),
        repetition_path: vec![0],
        input_range: ByteRange { start: 0, end: 0 },
        elements: Vec::new(),
        minimum: 0,
        maximum: Some(1),
    });
    let mut inventory = inventory("x", units);
    inventory.macro_templates = templates;
    inventory.macro_repetitions = repetitions;

    let index = MacroSourceContributorIndex::new(&inventory).unwrap();
    for component in 0..COMPONENTS {
        let rule = SourceUnitId(1 + component * 4);
        let template = SourceUnitId(rule.0 + 1);
        let invocation = SourceUnitId(rule.0 + 2);
        let element = SourceUnitId(rule.0 + 3);
        assert_eq!(index.templates(rule), [template]);
        assert_eq!(index.repetition_elements(invocation, rule), [element]);
    }
    assert!(
        index
            .repetition_elements(SourceUnitId(empty_invocation), SourceUnitId(1))
            .is_empty()
    );
    assert!(index.templates(SourceUnitId(u32::MAX)).is_empty());

    let mut duplicate = inventory.clone();
    duplicate
        .macro_templates
        .push(duplicate.macro_templates[0].clone());
    assert!(MacroSourceContributorIndex::new(&duplicate).is_err());

    let mut wrong_kind = inventory.clone();
    wrong_kind.units[2].kind = WrittenUnitKind::Item;
    assert!(MacroSourceContributorIndex::new(&wrong_kind).is_err());

    let mut wrong_parent = inventory.clone();
    wrong_parent.units[4].parent = Some(SourceUnitId(0));
    assert!(MacroSourceContributorIndex::new(&wrong_parent).is_err());

    let mut duplicate_element = inventory;
    let duplicate = duplicate_element.macro_repetitions[0].clone();
    duplicate_element.macro_repetitions.push(duplicate);
    assert!(MacroSourceContributorIndex::new(&duplicate_element).is_err());
}

#[test]
fn use_template_facts_accept_their_written_kind_without_private_component_kind() {
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 8), None, 0),
        unit(1, WrittenUnitKind::MacroRule, (0, 8), Some(0), 1),
        unit(2, WrittenUnitKind::UseItem, (1, 7), Some(1), 2),
        unit(3, WrittenUnitKind::UseLeaf, (2, 6), Some(2), 3),
    ];
    let mut inventory = inventory("use path", units);
    inventory.macro_templates = vec![
        MacroTemplateSourceFacts {
            unit: SourceUnitId(2),
            rule: SourceUnitId(1),
        },
        MacroTemplateSourceFacts {
            unit: SourceUnitId(3),
            rule: SourceUnitId(1),
        },
    ];

    assert_eq!(
        inventory.declarative_unit_kinds().unwrap(),
        vec![None, None, None, None]
    );
    let index = MacroSourceContributorIndex::new(&inventory).unwrap();
    assert_eq!(
        index.templates(SourceUnitId(1)),
        [SourceUnitId(2), SourceUnitId(3)]
    );
}

#[test]
fn macro_contributor_provenance_indexes_deep_and_shared_parent_chains() {
    const DEPTH: u32 = 1_025;
    const SHARED: SourceUnitId = SourceUnitId(42);
    let mut nodes = BTreeMap::new();
    nodes.insert(
        ExpansionId(0),
        MacroContributorProvenanceNode {
            local: BTreeSet::from([SourceUnitId(0), SHARED]),
            parent: None,
        },
    );
    for id in 1..DEPTH {
        nodes.insert(
            ExpansionId(id),
            MacroContributorProvenanceNode {
                local: BTreeSet::from([SourceUnitId(10_000 + id), SHARED]),
                parent: Some(ExpansionId(id - 1)),
            },
        );
    }
    for id in DEPTH..DEPTH + 2 {
        nodes.insert(
            ExpansionId(id),
            MacroContributorProvenanceNode {
                local: BTreeSet::from([SourceUnitId(10_000 + id), SHARED]),
                parent: Some(ExpansionId(512)),
            },
        );
    }

    let resolved = resolve_macro_contributor_provenance(&nodes).unwrap();
    let fact_count = nodes.values().map(|node| node.local.len()).sum::<usize>();
    assert_eq!(resolved.producer_range_count(), nodes.len());
    assert!(resolved.stored_range_count() <= fact_count);
    assert_eq!(resolved.stored_range_count(), nodes.len() + 1);

    let deepest = ExpansionId(DEPTH - 1);
    assert_eq!(resolved.allows(deepest, SourceUnitId(0)), Some(true));
    assert_eq!(resolved.allows(deepest, SourceUnitId(10_001)), Some(true));
    assert_eq!(resolved.allows(deepest, SHARED), Some(true));
    assert_eq!(
        resolved.allows(deepest, SourceUnitId(10_000 + DEPTH)),
        Some(false)
    );

    let left = ExpansionId(DEPTH);
    let right = ExpansionId(DEPTH + 1);
    assert_eq!(resolved.allows(left, SourceUnitId(10_512)), Some(true));
    assert_eq!(resolved.allows(right, SourceUnitId(10_512)), Some(true));
    assert_eq!(
        resolved.allows(left, SourceUnitId(10_000 + right.0)),
        Some(false)
    );
    assert_eq!(
        resolved.allows(right, SourceUnitId(10_000 + left.0)),
        Some(false)
    );
    assert_eq!(resolved.allows(ExpansionId(u32::MAX), SHARED), None);

    let cycle = BTreeMap::from([
        (
            ExpansionId(0),
            MacroContributorProvenanceNode {
                local: BTreeSet::new(),
                parent: Some(ExpansionId(1)),
            },
        ),
        (
            ExpansionId(1),
            MacroContributorProvenanceNode {
                local: BTreeSet::new(),
                parent: Some(ExpansionId(0)),
            },
        ),
    ]);
    assert_eq!(
        resolve_macro_contributor_provenance(&cycle).err(),
        Some(RetentionError::InvalidGraph)
    );

    let missing = BTreeMap::from([(
        ExpansionId(0),
        MacroContributorProvenanceNode {
            local: BTreeSet::new(),
            parent: Some(ExpansionId(1)),
        },
    )]);
    assert_eq!(
        resolve_macro_contributor_provenance(&missing).err(),
        Some(RetentionError::IncompleteMacroProductConstraints)
    );
}

#[test]
fn source_free_definitions_inherit_their_parent_unit() {
    let source = "xxxxxxxxxxxxxxxxxxxxxxxx";
    let units = vec![
        unit(0, WrittenUnitKind::CrateRoot, (0, 24), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 12), Some(0), 1),
    ];
    let inventory = inventory(source, units.clone());
    let graph = graph(
        vec![
            written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
            written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
            injected_definition(2, 1),
        ],
        vec![edge(
            GraphNode::Definition(DefinitionId(1)),
            GraphNode::Definition(DefinitionId(0)),
        )],
    );
    let retention = compute_retention(
        &inventory,
        &graph,
        &complete_constraints(&inventory, &graph),
    )
    .unwrap();

    assert!(
        retention
            .compile_required
            .contains(&GraphNode::Definition(DefinitionId(2)))
    );
}

#[test]
fn singleton_source_resolution_handles_a_deep_source_free_parent_chain_iteratively() {
    const DEPTH: u32 = 10_000;
    let units = [
        unit(0, WrittenUnitKind::CrateRoot, (0, 24), None, 0),
        unit(1, WrittenUnitKind::Item, (0, 12), Some(0), 1),
    ];
    let mut definitions = vec![
        written_definition(0, DefinitionKind::Crate, &units[0], None, "crate"),
        written_definition(1, DefinitionKind::Function, &units[1], Some(0), "main"),
    ];
    definitions.extend((2..DEPTH + 2).map(|id| compiler_generated_definition(id, id - 1)));
    let graph = graph(definitions, Vec::new());
    let mut definition_units = vec![units[0].id, units[1].id];
    definition_units.resize(DEPTH as usize + 2, units[1].id);
    let macro_producers = DefinitionMacroProducerIndex::new(macro_graph(&graph));

    let bindings = definition_singleton_source_units(
        &graph.definitions,
        &macro_producers,
        &definition_units,
        &BTreeSet::new(),
    )
    .unwrap();

    assert_eq!(bindings.len(), DEPTH as usize + 2);
    assert_eq!(bindings.last(), Some(&Some(units[1].id)));
}
