//! Owned compiler dependency graph.

use std::collections::{BTreeMap, BTreeSet};

use crate::compiler_terms::CanonicalCompilerTerm;
use crate::graph::{
    DefinitionGraph, DefinitionId, DefinitionKey, DefinitionTarget,
    DependencyKind as DefinitionDependencyKind, ExternalDefinitionId, ExternalDefinitionKey,
};
use crate::source::{ByteRange, SourceUnitId};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExpansionId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProofId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MonoId(pub u32);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DefinitionReferenceKey {
    Local(DefinitionKey),
    External(ExternalDefinitionKey),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GraphNode {
    Definition(DefinitionId),
    ExternalDefinition(ExternalDefinitionId),
    Expansion(ExpansionId),
    Proof(ProofId),
    Mono(MonoId),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExpansionKind {
    Macro { style: MacroStyle, name: String },
    AstPass(AstPassKind),
    Desugaring(DesugaringKind),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MacroStyle {
    Bang,
    Attribute,
    Derive,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AstPassKind {
    StandardImports,
    TestHarness,
    ProcMacroHarness,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DesugaringKind {
    QuestionMark,
    TryBlock,
    YeetExpression,
    OpaqueType,
    Async,
    Await,
    ForLoop,
    WhileLoop,
    BoundModifier,
    Contract,
    PatternTypeRange,
    WrittenFormatLiteral,
    ExpandedFormatLiteral,
    RangeExpression,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExpansionFragmentKind {
    OptionalExpression,
    MethodReceiverExpression,
    Expression,
    Pattern,
    Type,
    Statements,
    Items,
    TraitItems,
    ImplItems,
    TraitImplItems,
    ForeignItems,
    Arms,
    ExpressionFields,
    PatternFields,
    GenericParameters,
    Parameters,
    FieldDefinitions,
    Variants,
    WherePredicates,
    Crate,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MacroImplementationKind {
    Builtin,
    Declarative,
    Procedural,
    Legacy,
    InertAttribute,
    GlobDelegation,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExpansionKey(pub Vec<ExpansionKeyPart>);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExpansionKeyPart {
    pub kind: ExpansionKind,
    pub fragment: Option<ExpansionFragmentKind>,
    pub implementation: Option<MacroImplementationKind>,
    pub invocation_range: Option<ByteRange>,
    pub node_range: Option<ByteRange>,
    pub target_range: Option<ByteRange>,
    pub macro_definition: Option<DefinitionReferenceKey>,
    pub selected_macro_rule: Option<ByteRange>,
    pub same_role_ordinal: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpansionNode {
    pub id: ExpansionId,
    pub key: ExpansionKey,
    pub kind: ExpansionKind,
    pub fragment: Option<ExpansionFragmentKind>,
    pub implementation: Option<MacroImplementationKind>,
    pub discovered_in: Option<ExpansionId>,
    pub semantic_parent: Option<ExpansionId>,
    pub source_call_parent: Option<ExpansionId>,
    pub written_invocation: Option<SourceUnitId>,
    pub source_owner: Option<DefinitionId>,
    pub macro_definition: Option<DefinitionTarget>,
}

pub(crate) fn expansion_source_survival(
    expansions: &[ExpansionNode],
    mut written_unit_survives: impl FnMut(SourceUnitId) -> Option<bool>,
) -> Option<Vec<bool>> {
    let mut surviving = expansions
        .iter()
        .enumerate()
        .map(|(index, node)| {
            if node.id.0 as usize != index {
                return None;
            }
            node.written_invocation
                .map(&mut written_unit_survives)
                .unwrap_or(Some(true))
        })
        .collect::<Option<Vec<_>>>()?;

    loop {
        let mut changed = false;
        for node in expansions {
            let index = node.id.0 as usize;
            if !surviving[index] {
                continue;
            }
            for parent in [
                node.discovered_in,
                node.semantic_parent,
                node.source_call_parent,
            ]
            .into_iter()
            .flatten()
            {
                let parent_survives = expansions
                    .get(parent.0 as usize)
                    .filter(|parent_node| parent_node.id == parent && parent != node.id)
                    .and_then(|_| surviving.get(parent.0 as usize))
                    .copied()?;
                if !parent_survives {
                    surviving[index] = false;
                    changed = true;
                    break;
                }
            }
        }
        if !changed {
            return Some(surviving);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SelectionSourceKind {
    UserDefined,
    Parameter,
    Builtin,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SelectionSource {
    pub kind: SelectionSourceKind,
    pub term: CanonicalCompilerTerm,
    pub implementation: Option<DefinitionTarget>,
    pub builtin_trait: Option<BuiltinTraitTarget>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BuiltinTraitTargetKind {
    TraitDefinition,
    AutoTrait,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BuiltinTraitTarget {
    pub kind: BuiltinTraitTargetKind,
    pub target: DefinitionTarget,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProjectionOutcome {
    Progress { raw_term: CanonicalCompilerTerm },
    NoProgress { term: CanonicalCompilerTerm },
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProjectionSourceKind {
    ParameterEnvironment,
    TraitDefinition,
    Object,
    SelectedUserDefined,
    SelectedParameter,
    SelectedBuiltin,
    NoApplicableCandidate,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SolverTracePayload {
    pub root: ProofId,
    pub obligations: Vec<ProofId>,
    pub trait_selections: Vec<ProofId>,
    pub projections: Vec<ProofId>,
    pub fulfillments: Vec<ProofId>,
    pub cycles: Vec<ProofId>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MonoInstanceKey {
    pub definition: DefinitionReferenceKey,
    pub arguments: CanonicalCompilerTerm,
    pub kind: CanonicalCompilerTerm,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoInstanceRole {
    Callable,
    Const { promoted: Option<u32> },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProofKey {
    Obligation {
        environment: CanonicalCompilerTerm,
        predicate: CanonicalCompilerTerm,
    },
    Projection {
        environment: CanonicalCompilerTerm,
        alias: CanonicalCompilerTerm,
    },
    AssociatedItem {
        request: CanonicalCompilerTerm,
        raw_instance: MonoInstanceKey,
        codegen_instance: MonoInstanceKey,
    },
    Cycle {
        members: Vec<ProofKey>,
        coinductive: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofNodeKind {
    Obligation {
        environment: CanonicalCompilerTerm,
        predicate: CanonicalCompilerTerm,
        source: Option<SelectionSource>,
        selection_nested: Option<Vec<ProofId>>,
        fulfillment_nested: Option<Vec<ProofId>>,
        query_trace: Option<SolverTracePayload>,
    },
    Projection {
        environment: CanonicalCompilerTerm,
        alias: CanonicalCompilerTerm,
        source_kind: ProjectionSourceKind,
        source: CanonicalCompilerTerm,
        outcome: ProjectionOutcome,
        selected_trait: Option<ProofId>,
        selected_impl: Option<DefinitionTarget>,
        selected_item: Option<DefinitionTarget>,
        owners: Vec<ProofId>,
        nested: Vec<ProofId>,
        query_trace: Option<SolverTracePayload>,
        normalized_result: Option<CanonicalCompilerTerm>,
    },
    AssociatedItem {
        request: CanonicalCompilerTerm,
        raw_instance: MonoInstanceKey,
        codegen_instance: MonoInstanceKey,
        selection: ProofId,
        source_kind: SelectionSourceKind,
        leaf: Option<DefinitionTarget>,
        defining_node: Option<SpecializationNode>,
        finalizing_node: Option<SpecializationNode>,
        ancestor_path: Vec<SpecializationNode>,
    },
    Cycle {
        members: Vec<ProofId>,
        coinductive: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofNode {
    pub id: ProofId,
    pub key: ProofKey,
    pub kind: ProofNodeKind,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoCollection {
    Used,
    Mentioned,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoDependencyKind {
    DirectCall,
    FunctionPointer,
    ClosureFunctionPointer,
    InlineAsmSymbol,
    StaticReference,
    ThreadLocalReference,
    DropGlue,
    VTableConstruction,
    VTableMethod,
    VTableDrop,
    SupertraitVTable,
    ConstAllocation,
    AllocationReference,
    ThreadLocalShim,
    CompilerRequirement,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MonoKey {
    Instance {
        instance: MonoInstanceKey,
        role: MonoInstanceRole,
    },
    Static {
        definition: DefinitionKey,
    },
    VTable {
        concrete_type: CanonicalCompilerTerm,
        trait_reference: Option<CanonicalCompilerTerm>,
    },
    Allocation(AllocationKey),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AllocationKey {
    pub root: AllocationRootKey,
    pub path: Vec<AllocationPathPart>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AllocationRootKey {
    Instance {
        instance: MonoInstanceKey,
        role: MonoInstanceRole,
    },
    Static(DefinitionKey),
    VTable {
        concrete_type: CanonicalCompilerTerm,
        trait_reference: Option<CanonicalCompilerTerm>,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AllocationDescriptor {
    Memory,
    Function {
        instance: CanonicalCompilerTerm,
    },
    Static {
        definition: DefinitionReferenceKey,
    },
    VTable {
        concrete_type: CanonicalCompilerTerm,
        predicates: CanonicalCompilerTerm,
    },
    TypeId {
        value_type: CanonicalCompilerTerm,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AllocationPathPart {
    pub relation: MonoDependencyKind,
    pub collection: MonoCollection,
    pub site: AllocationPathSite,
    pub same_role_ordinal: u32,
}

/// The stable class of evidence that first reached an allocation.
///
/// Numeric allocation offsets are deliberately excluded: source-location
/// values may change the layout of constant memory without changing the
/// compiler dependency represented by the path. The exact offset remains on
/// the corresponding graph edge.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AllocationPathSite {
    Source(ByteRange),
    ExternalSource,
    AllocationReference,
    CompilerGenerated,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonoNode {
    pub id: MonoId,
    pub key: MonoKey,
    pub materialized_definition: Option<DefinitionTarget>,
    /// Session observation used to validate allocation facts. This is not part
    /// of allocation identity and must not be compared by the compiler-decision
    /// snapshot.
    pub(crate) allocation_observation: Option<AllocationDescriptor>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ObservationSite {
    Source(ByteRange),
    ExternalSource,
    AllocationOffset(u64),
    VTableSlot(u64),
    CompilerGenerated,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EvidenceOrigin {
    Compiler,
    PatchedObserver,
    Derived,
    Multiple,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DependencyKind {
    Definition(DefinitionDependencyKind),
    ExpansionDiscoveredIn,
    ExpansionSemanticParent,
    ExpansionSourceCallParent,
    MacroDefinition,
    ExpansionUse,
    GeneratedBy,
    SelectionProof {
        relation: MonoDependencyKind,
        collection: MonoCollection,
    },
    ProofRelation {
        relation: ProofRelationKind,
        ordinal: u32,
    },
    MaterializesDefinition,
    Mono {
        relation: MonoDependencyKind,
        collection: MonoCollection,
    },
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProofRelationKind {
    TraceObligation,
    TraceTraitSelection,
    TraceProjection,
    TraceFulfillment,
    TraceCycle,
    QueryTraceRoot,
    TraitSelectionNested,
    ProjectionOwner,
    ProjectionSelectedTrait,
    ProjectionNested,
    FulfillmentNested,
    CycleMember,
    AssociatedSelection,
    AssociatedLeaf,
    AssociatedDefining,
    AssociatedFinalizing,
    SpecializationAncestor,
    SelectedImpl,
    SelectedTraitItem,
    AutoTraitProof,
    TraitDefinition,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SpecializationNodeKind {
    Impl,
    Trait,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SpecializationNode {
    pub kind: SpecializationNodeKind,
    pub target: DefinitionTarget,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DependencyEdge {
    pub from: GraphNode,
    pub to: GraphNode,
    pub kind: DependencyKind,
    pub sites: Vec<ObservationSite>,
    pub evidence: EvidenceOrigin,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RootReason {
    Main,
    ExplicitEntry,
    DownstreamSelection,
    StartInstance,
    UsedAttribute,
    ExternalSymbol,
    NativeLink,
}

impl RootReason {
    pub(crate) fn is_semantic(self) -> bool {
        matches!(
            self,
            Self::Main | Self::ExplicitEntry | Self::DownstreamSelection
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RootRecord {
    pub node: GraphNode,
    pub reason: RootReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DependencyGraph {
    pub definitions: DefinitionGraph,
    pub expansions: Vec<ExpansionNode>,
    pub proofs: Vec<ProofNode>,
    pub mono_nodes: Vec<MonoNode>,
    pub edges: Vec<DependencyEdge>,
    pub roots: Vec<RootRecord>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum DependencyGraphError {
    InvalidExpansion,
    InvalidProof,
    InvalidMonoNode,
    InvalidEdge,
    InvalidRoot,
}

impl DependencyGraph {
    pub fn outgoing(&self, from: GraphNode) -> impl Iterator<Item = &DependencyEdge> {
        self.edges.iter().filter(move |edge| edge.from == from)
    }

    pub(crate) fn new(
        definitions: DefinitionGraph,
        mut expansions: Vec<ExpansionNode>,
        mut proofs: Vec<ProofNode>,
        mut mono_nodes: Vec<MonoNode>,
        edges: Vec<DependencyEdge>,
        mut roots: Vec<RootRecord>,
    ) -> Result<Self, DependencyGraphError> {
        expansions.sort_by_key(|node| node.id);
        proofs.sort_by_key(|node| node.id);
        mono_nodes.sort_by_key(|node| node.id);
        roots.sort();

        if !dense(&expansions, |node| node.id.0)
            || expansions
                .iter()
                .map(|node| &node.key)
                .collect::<BTreeSet<_>>()
                .len()
                != expansions.len()
            || expansions.iter().any(|node| {
                node.key.0.is_empty()
                    || invalid_expansion_ref(node.discovered_in, expansions.len())
                    || invalid_expansion_ref(node.semantic_parent, expansions.len())
                    || invalid_expansion_ref(node.source_call_parent, expansions.len())
                    || invalid_definition_target(node.macro_definition, &definitions)
                    || node
                        .source_owner
                        .is_some_and(|owner| owner.0 as usize >= definitions.definitions.len())
            })
        {
            return Err(DependencyGraphError::InvalidExpansion);
        }

        if !dense(&proofs, |node| node.id.0)
            || proofs
                .iter()
                .map(|node| &node.key)
                .collect::<BTreeSet<_>>()
                .len()
                != proofs.len()
            || proofs
                .iter()
                .any(|node| invalid_proof_node(node, &proofs, &definitions))
        {
            return Err(DependencyGraphError::InvalidProof);
        }

        if !dense(&mono_nodes, |node| node.id.0)
            || mono_nodes
                .iter()
                .map(|node| &node.key)
                .collect::<BTreeSet<_>>()
                .len()
                != mono_nodes.len()
            || mono_nodes
                .iter()
                .any(|node| invalid_mono_node(node, &definitions))
        {
            return Err(DependencyGraphError::InvalidMonoNode);
        }

        if !valid_roots(&roots, &definitions, &mono_nodes) {
            return Err(DependencyGraphError::InvalidRoot);
        }

        if !proof_relation_slots_are_unique(&edges) {
            return Err(DependencyGraphError::InvalidProof);
        }

        let mut grouped = BTreeMap::<
            (GraphNode, GraphNode, DependencyKind),
            (BTreeSet<ObservationSite>, BTreeSet<EvidenceOrigin>),
        >::new();
        for edge in definition_edges(&definitions).chain(edges) {
            if !valid_node(edge.from, &definitions, &expansions, &proofs, &mono_nodes)
                || !valid_node(edge.to, &definitions, &expansions, &proofs, &mono_nodes)
                || !valid_edge_shape(edge.from, edge.to, &edge.kind)
                || edge.sites.is_empty() && !structural_relation(&edge.kind)
            {
                return Err(DependencyGraphError::InvalidEdge);
            }
            let (sites, evidence) = grouped.entry((edge.from, edge.to, edge.kind)).or_default();
            sites.extend(edge.sites);
            evidence.insert(edge.evidence);
        }
        let edges = grouped
            .into_iter()
            .map(|((from, to, kind), (sites, evidence))| DependencyEdge {
                from,
                to,
                kind,
                sites: sites.into_iter().collect(),
                evidence: if evidence.len() == 1 {
                    *evidence.first().expect("one evidence source was observed")
                } else {
                    EvidenceOrigin::Multiple
                },
            })
            .collect::<Vec<_>>();

        if !valid_allocation_paths(&mono_nodes, &edges) {
            return Err(DependencyGraphError::InvalidMonoNode);
        }

        if !valid_proof_relations(&proofs, &edges) {
            return Err(DependencyGraphError::InvalidProof);
        }

        if !valid_associated_item_selection_joins(&proofs, &mono_nodes, &edges) {
            return Err(DependencyGraphError::InvalidProof);
        }

        let mono_roots = roots
            .iter()
            .filter_map(|root| match root.node {
                GraphNode::Mono(node) => Some(node),
                _ => None,
            })
            .collect::<Vec<_>>();
        let reachable_mono = reachable_mono_nodes(&mono_roots, &edges);
        if reachable_mono.len() != mono_nodes.len() {
            return Err(DependencyGraphError::InvalidMonoNode);
        }
        let reachable_proofs = reachable_proof_nodes(&reachable_mono, &edges);
        if reachable_proofs.len() != proofs.len() {
            return Err(DependencyGraphError::InvalidProof);
        }

        if expansions
            .iter()
            .any(|node| !valid_expansion_edges(node, &definitions, &expansions, &edges))
            || !expansion_relations_are_acyclic(&expansions)
            || definitions.definitions.iter().any(|definition| {
                if !matches!(
                    definition.origin,
                    crate::graph::DefinitionOrigin::Expanded { .. }
                ) {
                    return false;
                }
                edges
                    .iter()
                    .filter(|edge| {
                        edge.from == GraphNode::Definition(definition.id)
                            && matches!(edge.kind, DependencyKind::GeneratedBy)
                    })
                    .count()
                    != 1
            })
        {
            return Err(DependencyGraphError::InvalidExpansion);
        }

        for node in &mono_nodes {
            let materialization_edges = edges
                .iter()
                .filter(|edge| {
                    edge.from == GraphNode::Mono(node.id)
                        && edge.kind == DependencyKind::MaterializesDefinition
                })
                .collect::<Vec<_>>();
            match node.materialized_definition {
                Some(target)
                    if materialization_edges.len() == 1
                        && materialization_edges[0].to == definition_node(target) => {}
                None if materialization_edges.is_empty() => {}
                _ => return Err(DependencyGraphError::InvalidMonoNode),
            }
        }

        Ok(Self {
            definitions,
            expansions,
            proofs,
            mono_nodes,
            edges,
            roots,
        })
    }
}

pub(crate) fn valid_roots(
    roots: &[RootRecord],
    definitions: &DefinitionGraph,
    mono_nodes: &[MonoNode],
) -> bool {
    let records = roots.iter().copied().collect::<BTreeSet<_>>();
    if records.len() != roots.len() {
        return false;
    }

    let main_count = roots
        .iter()
        .filter(|root| root.reason == RootReason::Main)
        .count();
    let start_count = roots
        .iter()
        .filter(|root| root.reason == RootReason::StartInstance)
        .count();
    if main_count > 1 || start_count > 1 || main_count != start_count {
        return false;
    }

    roots.iter().all(|root| {
        let mono_node = |node| match node {
            GraphNode::Mono(node) => mono_nodes.get(node.0 as usize),
            _ => None,
        };
        match root.reason {
            RootReason::Main => matches!(
                mono_node(root.node).map(|node| &node.key),
                Some(MonoKey::Instance {
                    instance: MonoInstanceKey {
                        definition: DefinitionReferenceKey::Local(_),
                        ..
                    },
                    role: MonoInstanceRole::Callable,
                })
            ),
            RootReason::ExplicitEntry => match root.node {
                GraphNode::Definition(definition) => definitions
                    .definitions
                    .get(definition.0 as usize)
                    .is_some_and(|definition| {
                        matches!(
                            definition.kind,
                            crate::graph::DefinitionKind::Function
                                | crate::graph::DefinitionKind::Use
                        )
                    }),
                node => matches!(
                    mono_node(node).map(|node| &node.key),
                    Some(
                        MonoKey::Instance {
                            instance: MonoInstanceKey {
                                definition: DefinitionReferenceKey::Local(_),
                                ..
                            },
                            role: MonoInstanceRole::Callable,
                        } | MonoKey::Static { .. }
                    )
                ),
            },
            RootReason::DownstreamSelection => matches!(
                root.node,
                GraphNode::Definition(definition)
                    if is_downstream_selection_candidate(definitions, definition)
            ),
            RootReason::StartInstance => matches!(
                mono_node(root.node).map(|node| &node.key),
                Some(MonoKey::Instance {
                    role: MonoInstanceRole::Callable,
                    ..
                })
            ),
            RootReason::UsedAttribute => matches!(
                mono_node(root.node).map(|node| &node.key),
                Some(MonoKey::Static { .. })
            ),
            RootReason::ExternalSymbol => matches!(
                mono_node(root.node).map(|node| &node.key),
                Some(
                    MonoKey::Instance {
                        role: MonoInstanceRole::Callable,
                        ..
                    } | MonoKey::Static { .. }
                )
            ),
            RootReason::NativeLink => match root.node {
                GraphNode::Definition(definition) => definitions
                    .definitions
                    .get(definition.0 as usize)
                    .is_some_and(|definition| match definition.kind {
                        crate::graph::DefinitionKind::ForeignModule => true,
                        crate::graph::DefinitionKind::Function
                        | crate::graph::DefinitionKind::Static => {
                            definition.parent.is_some_and(|parent| {
                                definitions.definitions.get(parent.0 as usize).is_some_and(
                                    |parent| {
                                        parent.kind == crate::graph::DefinitionKind::ForeignModule
                                    },
                                )
                            })
                        }
                        _ => false,
                    }),
                _ => false,
            },
        }
    })
}

pub(crate) fn is_downstream_selection_candidate(
    definitions: &DefinitionGraph,
    id: DefinitionId,
) -> bool {
    let Some(definition) = definitions.definitions.get(id.0 as usize) else {
        return false;
    };
    matches!(
        definition.kind,
        crate::graph::DefinitionKind::Trait | crate::graph::DefinitionKind::Impl
    ) || matches!(
        definition.kind,
        crate::graph::DefinitionKind::AssociatedType
            | crate::graph::DefinitionKind::AssociatedFunction
            | crate::graph::DefinitionKind::AssociatedConst
    ) && definition.parent.is_some_and(|parent| {
        definitions
            .definitions
            .get(parent.0 as usize)
            .is_some_and(|parent| {
                matches!(
                    parent.kind,
                    crate::graph::DefinitionKind::Trait | crate::graph::DefinitionKind::Impl
                )
            })
    })
}

fn reachable_mono_nodes(roots: &[MonoId], edges: &[DependencyEdge]) -> BTreeSet<MonoId> {
    let mut reachable = roots.iter().copied().collect::<BTreeSet<_>>();
    let mut work = roots.to_vec();
    while let Some(from) = work.pop() {
        for edge in edges.iter().filter(|edge| {
            edge.from == GraphNode::Mono(from) && matches!(edge.kind, DependencyKind::Mono { .. })
        }) {
            let GraphNode::Mono(to) = edge.to else {
                continue;
            };
            if reachable.insert(to) {
                work.push(to);
            }
        }
    }
    reachable
}

fn reachable_proof_nodes(
    mono_nodes: &BTreeSet<MonoId>,
    edges: &[DependencyEdge],
) -> BTreeSet<ProofId> {
    let mut reachable = BTreeSet::new();
    let mut work = Vec::new();
    for edge in edges.iter().filter(|edge| {
        matches!(edge.from, GraphNode::Mono(id) if mono_nodes.contains(&id))
            && matches!(edge.kind, DependencyKind::SelectionProof { .. })
    }) {
        if let GraphNode::Proof(to) = edge.to
            && reachable.insert(to)
        {
            work.push(to);
        }
    }
    while let Some(from) = work.pop() {
        for edge in edges.iter().filter(|edge| {
            edge.from == GraphNode::Proof(from)
                && matches!(edge.kind, DependencyKind::ProofRelation { .. })
        }) {
            if let GraphNode::Proof(to) = edge.to
                && reachable.insert(to)
            {
                work.push(to);
            }
        }
    }
    reachable
}

fn valid_associated_item_selection_joins(
    proofs: &[ProofNode],
    mono_nodes: &[MonoNode],
    edges: &[DependencyEdge],
) -> bool {
    edges.iter().all(|proof_edge| {
        let DependencyKind::SelectionProof {
            relation,
            collection,
        } = proof_edge.kind
        else {
            return true;
        };
        let GraphNode::Proof(proof) = proof_edge.to else {
            return false;
        };
        let Some(ProofNode {
            kind:
                ProofNodeKind::AssociatedItem {
                    codegen_instance,
                    leaf,
                    source_kind,
                    ..
                },
            ..
        }) = proofs.get(proof.0 as usize)
        else {
            return true;
        };
        let GraphNode::Mono(from) = proof_edge.from else {
            return false;
        };
        if relation == MonoDependencyKind::ConstAllocation {
            return matches!(
                &mono_nodes[from.0 as usize].key,
                MonoKey::Instance {
                    instance,
                    role: MonoInstanceRole::Const { promoted: None },
                } if instance == codegen_instance
            );
        }
        if !matches!(
            relation,
            MonoDependencyKind::DirectCall
                | MonoDependencyKind::FunctionPointer
                | MonoDependencyKind::InlineAsmSymbol
                | MonoDependencyKind::VTableMethod
        ) {
            return false;
        }
        let mut matching = edges.iter().filter(|mono_edge| {
            mono_edge.from == proof_edge.from
                && mono_edge.kind
                    == DependencyKind::Mono {
                        relation,
                        collection,
                    }
                && selection_sites_match_mono(relation, &proof_edge.sites, &mono_edge.sites)
                && matches!(
                    mono_edge.to,
                    GraphNode::Mono(to)
                        if matches!(
                            &mono_nodes[to.0 as usize].key,
                            MonoKey::Instance {
                                instance,
                                role: MonoInstanceRole::Callable,
                            } if instance == codegen_instance
                        )
                )
        });
        let Some(mono_edge) = matching.next() else {
            let upstream_instance_is_not_materialized = matches!(
                codegen_instance.definition,
                DefinitionReferenceKey::External(_)
            ) && !mono_nodes.iter().any(|node| {
                matches!(
                    &node.key,
                    MonoKey::Instance {
                        instance,
                        role: MonoInstanceRole::Callable,
                    } if instance == codegen_instance
                )
            });
            if upstream_instance_is_not_materialized {
                return true;
            }
            // Parameter and builtin selections retain solver evidence but do
            // not necessarily materialize a concrete associated leaf.
            return leaf.is_none()
                && *source_kind != SelectionSourceKind::UserDefined
                && matches!(
                    relation,
                    MonoDependencyKind::DirectCall | MonoDependencyKind::VTableMethod
                );
        };
        if matching.next().is_some() {
            return false;
        }
        let GraphNode::Mono(to) = mono_edge.to else {
            return false;
        };
        matches!(
            &mono_nodes[to.0 as usize].key,
            MonoKey::Instance {
                instance,
                role: MonoInstanceRole::Callable,
            } if instance == codegen_instance
        )
    })
}

fn selection_sites_match_mono(
    relation: MonoDependencyKind,
    proof_sites: &[ObservationSite],
    mono_sites: &[ObservationSite],
) -> bool {
    if relation != MonoDependencyKind::DirectCall {
        return proof_sites == mono_sites;
    }
    proof_sites.iter().all(|proof| {
        mono_sites.iter().any(|mono| match (proof, mono) {
            (ObservationSite::Source(proof), ObservationSite::Source(mono)) => {
                mono.start <= proof.start && proof.end <= mono.end
            }
            _ => proof == mono,
        })
    })
}

fn proof_relation_slots_are_unique(edges: &[DependencyEdge]) -> bool {
    let mut slots = BTreeSet::new();
    edges.iter().all(|edge| match edge.kind {
        DependencyKind::ProofRelation { relation, ordinal } => {
            slots.insert((edge.from, relation, ordinal))
        }
        _ => true,
    })
}

fn dense<T>(values: &[T], id: impl Fn(&T) -> u32) -> bool {
    values
        .iter()
        .enumerate()
        .all(|(index, value)| id(value) as usize == index)
}

fn invalid_expansion_ref(value: Option<ExpansionId>, len: usize) -> bool {
    value.is_some_and(|id| id.0 as usize >= len)
}

fn invalid_definition_target(
    value: Option<DefinitionTarget>,
    definitions: &DefinitionGraph,
) -> bool {
    value.is_some_and(|target| match target {
        DefinitionTarget::Local(id) => id.0 as usize >= definitions.definitions.len(),
        DefinitionTarget::External(id) => id.0 as usize >= definitions.external_definitions.len(),
    })
}

fn invalid_mono_node(node: &MonoNode, definitions: &DefinitionGraph) -> bool {
    if invalid_definition_target(node.materialized_definition, definitions) {
        return true;
    }
    if matches!(node.key, MonoKey::Allocation(_)) != node.allocation_observation.is_some() {
        return true;
    }
    let expected = match &node.key {
        MonoKey::Instance { instance, .. } => Some(&instance.definition),
        MonoKey::Static { definition } => {
            return node.materialized_definition.is_none_or(|target| {
                definition_reference_key(definitions, target)
                    != DefinitionReferenceKey::Local(definition.clone())
            });
        }
        MonoKey::VTable { .. } => return node.materialized_definition.is_some(),
        MonoKey::Allocation(allocation) => {
            return node.materialized_definition.is_some()
                || allocation.path.is_empty()
                || allocation.path.iter().any(|part| {
                    !matches!(
                        (part.relation, part.site),
                        (
                            MonoDependencyKind::AllocationReference,
                            AllocationPathSite::AllocationReference
                                | AllocationPathSite::CompilerGenerated
                        ) | (
                            MonoDependencyKind::ConstAllocation,
                            AllocationPathSite::Source(_)
                                | AllocationPathSite::ExternalSource
                                | AllocationPathSite::CompilerGenerated
                        )
                    )
                });
        }
    };
    match (expected, node.materialized_definition) {
        (Some(reference), Some(target)) => {
            *reference != definition_reference_key(definitions, target)
        }
        _ => true,
    }
}

fn valid_allocation_paths(mono_nodes: &[MonoNode], edges: &[DependencyEdge]) -> bool {
    type AllocationRole = (
        MonoId,
        MonoDependencyKind,
        MonoCollection,
        AllocationPathSite,
    );
    let mut ordinals = BTreeMap::<AllocationRole, Vec<u32>>::new();

    for node in mono_nodes {
        let MonoKey::Allocation(allocation) = &node.key else {
            continue;
        };
        let Some((last, prefix)) = allocation.path.split_last() else {
            return false;
        };
        let mut parents = mono_nodes.iter().filter(|candidate| match &candidate.key {
            MonoKey::Allocation(parent) => {
                !prefix.is_empty() && parent.root == allocation.root && parent.path == prefix
            }
            key => prefix.is_empty() && key_matches_allocation_root(key, &allocation.root),
        });
        let Some(parent) = parents.next() else {
            return false;
        };
        if parents.next().is_some() {
            return false;
        }

        let matching_edges = edges
            .iter()
            .filter(|edge| {
                edge.from == GraphNode::Mono(parent.id)
                    && edge.to == GraphNode::Mono(node.id)
                    && edge.kind
                        == DependencyKind::Mono {
                            relation: last.relation,
                            collection: last.collection,
                        }
                    && edge
                        .sites
                        .iter()
                        .any(|site| allocation_site_matches(last.site, site))
            })
            .count();
        if matching_edges != 1 {
            return false;
        }
        ordinals
            .entry((parent.id, last.relation, last.collection, last.site))
            .or_default()
            .push(last.same_role_ordinal);
    }

    let mut targets = BTreeMap::<AllocationRole, BTreeSet<MonoId>>::new();
    if edges.iter().any(|edge| {
        let GraphNode::Mono(to) = edge.to else {
            return false;
        };
        if !matches!(mono_nodes[to.0 as usize].key, MonoKey::Allocation(_)) {
            return false;
        }
        let DependencyKind::Mono {
            relation,
            collection,
        } = edge.kind
        else {
            return true;
        };
        let GraphNode::Mono(from) = edge.from else {
            return true;
        };
        edge.sites.iter().any(|site| {
            let Some(site) = allocation_path_site(relation, site) else {
                return true;
            };
            targets
                .entry((from, relation, collection, site))
                .or_default()
                .insert(to);
            false
        })
    }) {
        return false;
    }

    ordinals.into_iter().all(|(role, mut values)| {
        values.sort_unstable();
        values.windows(2).all(|pair| pair[0] != pair[1])
            && targets.get(&role).is_some_and(|targets| {
                values.iter().all(|&ordinal| {
                    usize::try_from(ordinal).is_ok_and(|ordinal| ordinal < targets.len())
                })
            })
    })
}

fn key_matches_allocation_root(key: &MonoKey, root: &AllocationRootKey) -> bool {
    match (key, root) {
        (
            MonoKey::Instance { instance, role },
            AllocationRootKey::Instance {
                instance: root_instance,
                role: root_role,
            },
        ) => instance == root_instance && role == root_role,
        (MonoKey::Static { definition }, AllocationRootKey::Static(root_definition)) => {
            definition == root_definition
        }
        (
            MonoKey::VTable {
                concrete_type,
                trait_reference,
            },
            AllocationRootKey::VTable {
                concrete_type: root_type,
                trait_reference: root_trait,
            },
        ) => concrete_type == root_type && trait_reference == root_trait,
        _ => false,
    }
}

fn allocation_site_matches(expected: AllocationPathSite, actual: &ObservationSite) -> bool {
    match (expected, actual) {
        (AllocationPathSite::Source(expected), ObservationSite::Source(actual)) => {
            expected == *actual
        }
        (AllocationPathSite::ExternalSource, ObservationSite::ExternalSource)
        | (AllocationPathSite::AllocationReference, ObservationSite::AllocationOffset(_))
        | (AllocationPathSite::CompilerGenerated, ObservationSite::CompilerGenerated) => true,
        _ => false,
    }
}

fn allocation_path_site(
    relation: MonoDependencyKind,
    site: &ObservationSite,
) -> Option<AllocationPathSite> {
    match (relation, site) {
        (MonoDependencyKind::ConstAllocation, ObservationSite::Source(range)) => {
            Some(AllocationPathSite::Source(*range))
        }
        (MonoDependencyKind::ConstAllocation, ObservationSite::ExternalSource) => {
            Some(AllocationPathSite::ExternalSource)
        }
        (MonoDependencyKind::ConstAllocation, ObservationSite::CompilerGenerated)
        | (MonoDependencyKind::AllocationReference, ObservationSite::CompilerGenerated) => {
            Some(AllocationPathSite::CompilerGenerated)
        }
        (MonoDependencyKind::AllocationReference, ObservationSite::AllocationOffset(_)) => {
            Some(AllocationPathSite::AllocationReference)
        }
        _ => None,
    }
}

fn invalid_proof_node(
    node: &ProofNode,
    proofs: &[ProofNode],
    definitions: &DefinitionGraph,
) -> bool {
    match &node.kind {
        ProofNodeKind::Obligation {
            environment,
            predicate,
            source,
            selection_nested,
            fulfillment_nested,
            query_trace,
        } => {
            node.key
                != ProofKey::Obligation {
                    environment: environment.clone(),
                    predicate: predicate.clone(),
                }
                || source
                    .as_ref()
                    .is_some_and(|source| invalid_selection_source(source, definitions))
                || selection_nested.is_some() != source.is_some()
                || invalid_optional_proof_ids(selection_nested, proofs, obligation)
                || invalid_optional_proof_ids(fulfillment_nested, proofs, obligation)
                || query_trace
                    .as_ref()
                    .is_some_and(|trace| invalid_trace_payload(trace, proofs))
        }
        ProofNodeKind::Projection {
            environment,
            alias,
            source_kind,
            selected_trait,
            selected_impl,
            selected_item,
            owners,
            nested,
            query_trace,
            normalized_result,
            ..
        } => {
            node.key
                != ProofKey::Projection {
                    environment: environment.clone(),
                    alias: alias.clone(),
                }
                || selected_trait.is_some_and(|id| {
                    id.0 as usize >= proofs.len()
                        || !matches!(proofs[id.0 as usize].kind, ProofNodeKind::Obligation { .. })
                })
                || matches!(source_kind, ProjectionSourceKind::SelectedUserDefined)
                    != selected_impl.is_some()
                || matches!(
                    source_kind,
                    ProjectionSourceKind::SelectedUserDefined
                        | ProjectionSourceKind::SelectedParameter
                        | ProjectionSourceKind::SelectedBuiltin
                ) != selected_trait.is_some()
                || matches!(source_kind, ProjectionSourceKind::SelectedUserDefined)
                    != selected_item.is_some()
                || invalid_definition_target(*selected_impl, definitions)
                || invalid_definition_target(*selected_item, definitions)
                || owners.is_empty()
                || invalid_proof_ids(owners, proofs, obligation)
                || invalid_proof_ids(nested, proofs, obligation)
                || query_trace.is_some() != normalized_result.is_some()
                || query_trace
                    .as_ref()
                    .is_some_and(|trace| invalid_trace_payload(trace, proofs))
        }
        ProofNodeKind::AssociatedItem {
            request,
            raw_instance,
            codegen_instance,
            selection,
            source_kind,
            leaf,
            defining_node,
            finalizing_node,
            ancestor_path,
            ..
        } => {
            node.key
                != ProofKey::AssociatedItem {
                    request: request.clone(),
                    raw_instance: raw_instance.clone(),
                    codegen_instance: codegen_instance.clone(),
                }
                || selection.0 as usize >= proofs.len()
                || !associated_selection_matches(
                    proofs.get(selection.0 as usize),
                    *source_kind,
                    *leaf,
                    *defining_node,
                    *finalizing_node,
                    ancestor_path,
                )
                || invalid_definition_target(*leaf, definitions)
                || invalid_definition_target(defining_node.map(|node| node.target), definitions)
                || invalid_definition_target(finalizing_node.map(|node| node.target), definitions)
                || ancestor_path
                    .iter()
                    .any(|node| invalid_definition_target(Some(node.target), definitions))
        }
        ProofNodeKind::Cycle {
            members,
            coinductive,
        } => {
            members.is_empty()
                || members.iter().any(|id| {
                    id.0 as usize >= proofs.len()
                        || !matches!(proofs[id.0 as usize].kind, ProofNodeKind::Obligation { .. })
                })
                || node.key
                    != ProofKey::Cycle {
                        members: members
                            .iter()
                            .map(|id| proofs[id.0 as usize].key.clone())
                            .collect(),
                        coinductive: *coinductive,
                    }
        }
    }
}

fn invalid_selection_source(source: &SelectionSource, definitions: &DefinitionGraph) -> bool {
    let shape_is_invalid = match source.kind {
        SelectionSourceKind::UserDefined => {
            source.implementation.is_none() || source.builtin_trait.is_some()
        }
        SelectionSourceKind::Parameter => {
            source.implementation.is_some() || source.builtin_trait.is_some()
        }
        SelectionSourceKind::Builtin => {
            source.implementation.is_some() || source.builtin_trait.is_none()
        }
    };
    shape_is_invalid
        || invalid_definition_target(source.implementation, definitions)
        || source
            .builtin_trait
            .is_some_and(|builtin| invalid_definition_target(Some(builtin.target), definitions))
}

fn invalid_trace_payload(trace: &SolverTracePayload, proofs: &[ProofNode]) -> bool {
    !trace.obligations.contains(&trace.root)
        || invalid_proof_ids(std::slice::from_ref(&trace.root), proofs, obligation)
        || invalid_proof_ids(&trace.obligations, proofs, obligation)
        || invalid_proof_ids(&trace.trait_selections, proofs, obligation)
        || trace
            .trait_selections
            .iter()
            .any(|selection| !trace.obligations.contains(selection))
        || invalid_proof_ids(&trace.projections, proofs, projection)
        || invalid_proof_ids(&trace.fulfillments, proofs, obligation)
        || trace
            .fulfillments
            .iter()
            .any(|fulfillment| !trace.obligations.contains(fulfillment))
        || invalid_proof_ids(&trace.cycles, proofs, cycle)
}

fn invalid_optional_proof_ids(
    ids: &Option<Vec<ProofId>>,
    proofs: &[ProofNode],
    expected: fn(&ProofNodeKind) -> bool,
) -> bool {
    ids.as_ref()
        .is_some_and(|ids| invalid_proof_ids(ids, proofs, expected))
}

fn invalid_proof_ids(
    ids: &[ProofId],
    proofs: &[ProofNode],
    expected: fn(&ProofNodeKind) -> bool,
) -> bool {
    ids.iter().any(|id| {
        proofs
            .get(id.0 as usize)
            .is_none_or(|node| !expected(&node.kind))
    })
}

fn obligation(kind: &ProofNodeKind) -> bool {
    matches!(kind, ProofNodeKind::Obligation { .. })
}

fn projection(kind: &ProofNodeKind) -> bool {
    matches!(kind, ProofNodeKind::Projection { .. })
}

fn cycle(kind: &ProofNodeKind) -> bool {
    matches!(kind, ProofNodeKind::Cycle { .. })
}

fn associated_selection_matches(
    selection: Option<&ProofNode>,
    source_kind: SelectionSourceKind,
    leaf: Option<DefinitionTarget>,
    defining_node: Option<SpecializationNode>,
    finalizing_node: Option<SpecializationNode>,
    ancestor_path: &[SpecializationNode],
) -> bool {
    let Some(ProofNode {
        kind: ProofNodeKind::Obligation {
            source: Some(source),
            ..
        },
        ..
    }) = selection
    else {
        return false;
    };
    if source.kind != source_kind {
        return false;
    }
    match source_kind {
        SelectionSourceKind::UserDefined => {
            let (Some(implementation), Some(_), Some(defining_node), Some(first), Some(last)) = (
                source.implementation,
                leaf,
                defining_node,
                ancestor_path.first(),
                ancestor_path.last(),
            ) else {
                return false;
            };
            source.builtin_trait.is_none()
                && first.kind == SpecializationNodeKind::Impl
                && first.target == implementation
                && last.kind == SpecializationNodeKind::Trait
                && ancestor_path.contains(&defining_node)
                && finalizing_node.is_none_or(|node| ancestor_path.contains(&node))
        }
        SelectionSourceKind::Parameter => {
            source.implementation.is_none()
                && source.builtin_trait.is_none()
                && leaf.is_none()
                && defining_node.is_none()
                && finalizing_node.is_none()
                && ancestor_path.is_empty()
        }
        SelectionSourceKind::Builtin => {
            source.implementation.is_none()
                && source.builtin_trait.is_some()
                && leaf.is_none()
                && defining_node.is_none()
                && finalizing_node.is_none()
                && ancestor_path.is_empty()
        }
    }
}

fn valid_proof_relations(proofs: &[ProofNode], edges: &[DependencyEdge]) -> bool {
    let relations = edges
        .iter()
        .filter_map(|edge| match edge.kind {
            DependencyKind::ProofRelation { relation, ordinal } => {
                Some((edge.from, edge.to, relation, ordinal))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    let mut slots = BTreeSet::new();
    if relations
        .iter()
        .any(|&(from, _, relation, ordinal)| !slots.insert((from, relation, ordinal)))
    {
        return false;
    }
    let mut groups = BTreeMap::<(GraphNode, ProofRelationKind), Vec<u32>>::new();
    for &(from, _, relation, ordinal) in &relations {
        groups.entry((from, relation)).or_default().push(ordinal);
    }
    if groups.values_mut().any(|ordinals| {
        ordinals.sort_unstable();
        ordinals
            .iter()
            .enumerate()
            .any(|(expected, &actual)| usize::try_from(actual) != Ok(expected))
    }) {
        return false;
    }

    for proof in proofs {
        let from = GraphNode::Proof(proof.id);
        let exact = |relation, expected: &[GraphNode]| {
            ordered_relation_targets(&relations, from, relation) == expected
        };
        let mut expected = [
            ProofRelationKind::TraceObligation,
            ProofRelationKind::TraceTraitSelection,
            ProofRelationKind::TraceProjection,
            ProofRelationKind::TraceFulfillment,
            ProofRelationKind::TraceCycle,
            ProofRelationKind::QueryTraceRoot,
            ProofRelationKind::TraitSelectionNested,
            ProofRelationKind::ProjectionOwner,
            ProofRelationKind::ProjectionSelectedTrait,
            ProofRelationKind::ProjectionNested,
            ProofRelationKind::FulfillmentNested,
            ProofRelationKind::CycleMember,
            ProofRelationKind::AssociatedSelection,
            ProofRelationKind::AssociatedLeaf,
            ProofRelationKind::AssociatedDefining,
            ProofRelationKind::AssociatedFinalizing,
            ProofRelationKind::SpecializationAncestor,
            ProofRelationKind::SelectedImpl,
            ProofRelationKind::SelectedTraitItem,
            ProofRelationKind::AutoTraitProof,
            ProofRelationKind::TraitDefinition,
        ]
        .into_iter()
        .map(|relation| (relation, Vec::new()))
        .collect::<BTreeMap<_, _>>();
        match &proof.kind {
            ProofNodeKind::Obligation {
                source,
                selection_nested,
                fulfillment_nested,
                query_trace,
                ..
            } => {
                expected.insert(
                    ProofRelationKind::SelectedImpl,
                    source
                        .as_ref()
                        .and_then(|source| source.implementation)
                        .map(definition_node)
                        .into_iter()
                        .collect(),
                );
                expected.insert(
                    ProofRelationKind::TraitSelectionNested,
                    selection_nested
                        .iter()
                        .flatten()
                        .copied()
                        .map(GraphNode::Proof)
                        .collect(),
                );
                expected.insert(
                    ProofRelationKind::FulfillmentNested,
                    fulfillment_nested
                        .iter()
                        .flatten()
                        .copied()
                        .map(GraphNode::Proof)
                        .collect(),
                );
                if let Some(builtin) = source.as_ref().and_then(|source| source.builtin_trait) {
                    let relation = match builtin.kind {
                        BuiltinTraitTargetKind::TraitDefinition => {
                            ProofRelationKind::TraitDefinition
                        }
                        BuiltinTraitTargetKind::AutoTrait => ProofRelationKind::AutoTraitProof,
                    };
                    expected.insert(relation, vec![definition_node(builtin.target)]);
                }
                insert_trace_expectations(&mut expected, query_trace.as_ref());
            }
            ProofNodeKind::Projection {
                selected_trait,
                selected_impl,
                selected_item,
                owners,
                nested,
                query_trace,
                ..
            } => {
                expected.insert(
                    ProofRelationKind::ProjectionOwner,
                    owners.iter().copied().map(GraphNode::Proof).collect(),
                );
                expected.insert(
                    ProofRelationKind::ProjectionSelectedTrait,
                    selected_trait.map(GraphNode::Proof).into_iter().collect(),
                );
                expected.insert(
                    ProofRelationKind::ProjectionNested,
                    nested.iter().copied().map(GraphNode::Proof).collect(),
                );
                expected.insert(
                    ProofRelationKind::SelectedImpl,
                    selected_impl.map(definition_node).into_iter().collect(),
                );
                expected.insert(
                    ProofRelationKind::SelectedTraitItem,
                    selected_item.map(definition_node).into_iter().collect(),
                );
                insert_trace_expectations(&mut expected, query_trace.as_ref());
            }
            ProofNodeKind::AssociatedItem {
                selection,
                leaf,
                defining_node,
                finalizing_node,
                ancestor_path,
                ..
            } => {
                expected.insert(
                    ProofRelationKind::AssociatedSelection,
                    vec![GraphNode::Proof(*selection)],
                );
                expected.insert(
                    ProofRelationKind::AssociatedLeaf,
                    leaf.map(definition_node).into_iter().collect(),
                );
                expected.insert(
                    ProofRelationKind::AssociatedDefining,
                    defining_node
                        .map(|node| definition_node(node.target))
                        .into_iter()
                        .collect(),
                );
                expected.insert(
                    ProofRelationKind::AssociatedFinalizing,
                    finalizing_node
                        .map(|node| definition_node(node.target))
                        .into_iter()
                        .collect(),
                );
                expected.insert(
                    ProofRelationKind::SpecializationAncestor,
                    ancestor_path
                        .iter()
                        .map(|node| definition_node(node.target))
                        .collect(),
                );
            }
            ProofNodeKind::Cycle { members, .. } => {
                expected.insert(
                    ProofRelationKind::CycleMember,
                    members.iter().copied().map(GraphNode::Proof).collect(),
                );
            }
        }
        if expected
            .into_iter()
            .any(|(relation, targets)| !exact(relation, &targets))
        {
            return false;
        }
    }
    true
}

fn insert_trace_expectations(
    expected: &mut BTreeMap<ProofRelationKind, Vec<GraphNode>>,
    trace: Option<&SolverTracePayload>,
) {
    let Some(trace) = trace else {
        return;
    };
    expected.insert(
        ProofRelationKind::QueryTraceRoot,
        vec![GraphNode::Proof(trace.root)],
    );
    for (relation, ids) in [
        (ProofRelationKind::TraceObligation, &trace.obligations),
        (
            ProofRelationKind::TraceTraitSelection,
            &trace.trait_selections,
        ),
        (ProofRelationKind::TraceProjection, &trace.projections),
        (ProofRelationKind::TraceFulfillment, &trace.fulfillments),
        (ProofRelationKind::TraceCycle, &trace.cycles),
    ] {
        expected.insert(
            relation,
            ids.iter().copied().map(GraphNode::Proof).collect(),
        );
    }
}

fn ordered_relation_targets(
    relations: &[(GraphNode, GraphNode, ProofRelationKind, u32)],
    from: GraphNode,
    relation: ProofRelationKind,
) -> Vec<GraphNode> {
    let mut targets = relations
        .iter()
        .filter_map(|&(edge_from, to, edge_relation, ordinal)| {
            (edge_from == from && edge_relation == relation).then_some((ordinal, to))
        })
        .collect::<Vec<_>>();
    targets.sort_by_key(|&(ordinal, _)| ordinal);
    targets.into_iter().map(|(_, target)| target).collect()
}

fn definition_node(target: DefinitionTarget) -> GraphNode {
    match target {
        DefinitionTarget::Local(id) => GraphNode::Definition(id),
        DefinitionTarget::External(id) => GraphNode::ExternalDefinition(id),
    }
}

fn definition_edges(definitions: &DefinitionGraph) -> impl Iterator<Item = DependencyEdge> + '_ {
    definitions.edges.iter().map(|edge| DependencyEdge {
        from: GraphNode::Definition(edge.from),
        to: definition_node(edge.to),
        kind: DependencyKind::Definition(edge.kind),
        sites: edge
            .sites
            .iter()
            .copied()
            .map(ObservationSite::Source)
            .collect(),
        evidence: EvidenceOrigin::Compiler,
    })
}

fn valid_node(
    node: GraphNode,
    definitions: &DefinitionGraph,
    expansions: &[ExpansionNode],
    proofs: &[ProofNode],
    mono_nodes: &[MonoNode],
) -> bool {
    match node {
        GraphNode::Definition(id) => (id.0 as usize) < definitions.definitions.len(),
        GraphNode::ExternalDefinition(id) => {
            (id.0 as usize) < definitions.external_definitions.len()
        }
        GraphNode::Expansion(id) => (id.0 as usize) < expansions.len(),
        GraphNode::Proof(id) => (id.0 as usize) < proofs.len(),
        GraphNode::Mono(id) => (id.0 as usize) < mono_nodes.len(),
    }
}

fn structural_relation(kind: &DependencyKind) -> bool {
    matches!(
        kind,
        DependencyKind::Definition(DefinitionDependencyKind::Parent)
            | DependencyKind::ExpansionDiscoveredIn
            | DependencyKind::ExpansionSemanticParent
            | DependencyKind::ExpansionSourceCallParent
            | DependencyKind::MacroDefinition
            | DependencyKind::GeneratedBy
            | DependencyKind::ProofRelation { .. }
            | DependencyKind::MaterializesDefinition
    )
}

fn valid_edge_shape(from: GraphNode, to: GraphNode, kind: &DependencyKind) -> bool {
    let definition = |node| {
        matches!(
            node,
            GraphNode::Definition(_) | GraphNode::ExternalDefinition(_)
        )
    };
    match kind {
        DependencyKind::Definition(_) => matches!(from, GraphNode::Definition(_)) && definition(to),
        DependencyKind::ExpansionDiscoveredIn
        | DependencyKind::ExpansionSemanticParent
        | DependencyKind::ExpansionSourceCallParent => {
            matches!(from, GraphNode::Expansion(_)) && matches!(to, GraphNode::Expansion(_))
        }
        DependencyKind::MacroDefinition => {
            matches!(from, GraphNode::Expansion(_)) && definition(to)
        }
        DependencyKind::ExpansionUse | DependencyKind::GeneratedBy => {
            matches!(from, GraphNode::Definition(_)) && matches!(to, GraphNode::Expansion(_))
        }
        DependencyKind::SelectionProof { .. } => {
            matches!(from, GraphNode::Mono(_)) && matches!(to, GraphNode::Proof(_))
        }
        DependencyKind::ProofRelation { relation, .. } => match relation {
            ProofRelationKind::TraceObligation
            | ProofRelationKind::TraceTraitSelection
            | ProofRelationKind::TraceProjection
            | ProofRelationKind::TraceFulfillment
            | ProofRelationKind::TraceCycle
            | ProofRelationKind::QueryTraceRoot
            | ProofRelationKind::TraitSelectionNested
            | ProofRelationKind::ProjectionOwner
            | ProofRelationKind::ProjectionSelectedTrait
            | ProofRelationKind::ProjectionNested
            | ProofRelationKind::FulfillmentNested
            | ProofRelationKind::CycleMember
            | ProofRelationKind::AssociatedSelection => {
                matches!(from, GraphNode::Proof(_)) && matches!(to, GraphNode::Proof(_))
            }
            ProofRelationKind::AssociatedLeaf
            | ProofRelationKind::AssociatedDefining
            | ProofRelationKind::AssociatedFinalizing
            | ProofRelationKind::SpecializationAncestor
            | ProofRelationKind::SelectedImpl
            | ProofRelationKind::SelectedTraitItem
            | ProofRelationKind::AutoTraitProof
            | ProofRelationKind::TraitDefinition => {
                matches!(from, GraphNode::Proof(_)) && definition(to)
            }
        },
        DependencyKind::MaterializesDefinition => {
            matches!(from, GraphNode::Mono(_)) && definition(to)
        }
        DependencyKind::Mono { .. } => {
            matches!(from, GraphNode::Mono(_)) && matches!(to, GraphNode::Mono(_))
        }
    }
}

fn valid_expansion_edges(
    node: &ExpansionNode,
    definitions: &DefinitionGraph,
    expansions: &[ExpansionNode],
    edges: &[DependencyEdge],
) -> bool {
    match node.key.0.last() {
        Some(leaf)
            if leaf.kind == node.kind
                && leaf.fragment == node.fragment
                && leaf.implementation == node.implementation
                && leaf.macro_definition
                    == node
                        .macro_definition
                        .map(|target| definition_reference_key(definitions, target)) => {}
        _ => return false,
    }
    let identity_parent = node
        .discovered_in
        .or(node.source_call_parent)
        .or(node.semantic_parent);
    match identity_parent {
        Some(parent) => {
            let parent = match expansions.get(parent.0 as usize) {
                Some(parent) if parent.id != node.id => parent,
                _ => return false,
            };
            if node.key.0.len() != parent.key.0.len() + 1 || !node.key.0.starts_with(&parent.key.0)
            {
                return false;
            }
        }
        None if node.key.0.len() == 1 => {}
        None => return false,
    }
    let exact = |kind: DependencyKind, target: Option<GraphNode>| {
        let matching = edges
            .iter()
            .filter(|edge| edge.from == GraphNode::Expansion(node.id) && edge.kind == kind)
            .collect::<Vec<_>>();
        match target {
            Some(target) => matching.len() == 1 && matching[0].to == target,
            None => matching.is_empty(),
        }
    };
    exact(
        DependencyKind::ExpansionDiscoveredIn,
        node.discovered_in.map(GraphNode::Expansion),
    ) && exact(
        DependencyKind::ExpansionSemanticParent,
        node.semantic_parent.map(GraphNode::Expansion),
    ) && exact(
        DependencyKind::ExpansionSourceCallParent,
        node.source_call_parent.map(GraphNode::Expansion),
    ) && exact(
        DependencyKind::MacroDefinition,
        node.macro_definition.map(definition_node),
    ) && {
        let uses = edges
            .iter()
            .filter(|edge| {
                edge.to == GraphNode::Expansion(node.id)
                    && matches!(edge.kind, DependencyKind::ExpansionUse)
            })
            .collect::<Vec<_>>();
        match node.source_owner {
            Some(owner) => uses.len() == 1 && uses[0].from == GraphNode::Definition(owner),
            None => uses.is_empty(),
        }
    }
}

fn expansion_relations_are_acyclic(expansions: &[ExpansionNode]) -> bool {
    fn acyclic(
        expansions: &[ExpansionNode],
        relation: impl Fn(&ExpansionNode) -> Option<ExpansionId> + Copy,
    ) -> bool {
        expansions.iter().all(|start| {
            let mut seen = BTreeSet::new();
            let mut current = Some(start.id);
            while let Some(id) = current {
                if !seen.insert(id) {
                    return false;
                }
                current = expansions.get(id.0 as usize).and_then(relation);
            }
            true
        })
    }
    acyclic(expansions, |node| node.discovered_in)
        && acyclic(expansions, |node| node.semantic_parent)
        && acyclic(expansions, |node| node.source_call_parent)
}

fn definition_reference_key(
    definitions: &DefinitionGraph,
    target: DefinitionTarget,
) -> DefinitionReferenceKey {
    match target {
        DefinitionTarget::Local(id) => {
            DefinitionReferenceKey::Local(definitions.definitions[id.0 as usize].key.clone())
        }
        DefinitionTarget::External(id) => DefinitionReferenceKey::External(
            definitions.external_definitions[id.0 as usize].key.clone(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{
        Definition, DefinitionKeyPart, DefinitionKind, DefinitionOrigin, DefinitionOriginKey,
        ExternalDefinition,
    };
    use crate::source::WrittenUnitKind;

    fn term(tag: u8) -> CanonicalCompilerTerm {
        CanonicalCompilerTerm {
            schema_version: 1,
            bytes: vec![tag],
        }
    }

    fn obligation(id: u32, source: Option<SelectionSource>) -> ProofNode {
        let environment = term(id as u8);
        let predicate = term((id + 16) as u8);
        ProofNode {
            id: ProofId(id),
            key: ProofKey::Obligation {
                environment: environment.clone(),
                predicate: predicate.clone(),
            },
            kind: ProofNodeKind::Obligation {
                environment,
                predicate,
                source,
                selection_nested: None,
                fulfillment_nested: None,
                query_trace: None,
            },
        }
    }

    fn relation(
        from: u32,
        to: GraphNode,
        relation: ProofRelationKind,
        ordinal: u32,
    ) -> DependencyEdge {
        DependencyEdge {
            from: GraphNode::Proof(ProofId(from)),
            to,
            kind: DependencyKind::ProofRelation { relation, ordinal },
            sites: Vec::new(),
            evidence: EvidenceOrigin::PatchedObserver,
        }
    }

    fn allocation_graph_parts() -> (DefinitionGraph, Vec<MonoNode>, Vec<DependencyEdge>) {
        let main_range = ByteRange { start: 0, end: 4 };
        let main_key = DefinitionKey(vec![DefinitionKeyPart {
            kind: DefinitionKind::Function,
            origin: DefinitionOriginKey::Written {
                anchor: main_range,
                unit_kind: WrittenUnitKind::Item,
            },
            name: Some("main".to_owned()),
            same_role_ordinal: 0,
        }]);
        let start_key = ExternalDefinitionKey {
            crate_identity: 1,
            crate_name: "std".to_owned(),
            def_path_hash: [1; 16],
        };
        let definitions = DefinitionGraph {
            definitions: vec![Definition {
                id: DefinitionId(0),
                key: main_key.clone(),
                kind: DefinitionKind::Function,
                parent: None,
                origin: DefinitionOrigin::Written {
                    unit: SourceUnitId(0),
                    unit_range: main_range,
                    anchor: main_range,
                    unit_kind: WrittenUnitKind::Item,
                    unit_ordinal: 0,
                },
            }],
            external_definitions: vec![ExternalDefinition {
                id: ExternalDefinitionId(0),
                key: start_key.clone(),
                path: "std::rt::lang_start".to_owned(),
            }],
            edges: Vec::new(),
        };

        let main_arguments = term(1);
        let main_kind = term(2);
        let main_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(main_key.clone()),
            arguments: main_arguments.clone(),
            kind: main_kind.clone(),
        };
        let root = AllocationRootKey::Instance {
            instance: main_instance.clone(),
            role: MonoInstanceRole::Callable,
        };
        let root_part = AllocationPathPart {
            relation: MonoDependencyKind::ConstAllocation,
            collection: MonoCollection::Used,
            site: AllocationPathSite::Source(ByteRange { start: 8, end: 12 }),
            same_role_ordinal: 0,
        };
        let child_part = |ordinal| AllocationPathPart {
            relation: MonoDependencyKind::AllocationReference,
            collection: MonoCollection::Used,
            site: AllocationPathSite::CompilerGenerated,
            same_role_ordinal: ordinal,
        };
        let mono_nodes = vec![
            MonoNode {
                id: MonoId(0),
                key: MonoKey::Instance {
                    instance: main_instance,
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(DefinitionTarget::Local(DefinitionId(0))),
                allocation_observation: None,
            },
            MonoNode {
                id: MonoId(1),
                key: MonoKey::Instance {
                    instance: MonoInstanceKey {
                        definition: DefinitionReferenceKey::External(start_key),
                        arguments: term(3),
                        kind: term(4),
                    },
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(DefinitionTarget::External(ExternalDefinitionId(0))),
                allocation_observation: None,
            },
            MonoNode {
                id: MonoId(2),
                key: MonoKey::Allocation(AllocationKey {
                    root: root.clone(),
                    path: vec![root_part.clone()],
                }),
                materialized_definition: None,
                allocation_observation: Some(AllocationDescriptor::Memory),
            },
            MonoNode {
                id: MonoId(3),
                key: MonoKey::Allocation(AllocationKey {
                    root: root.clone(),
                    path: vec![root_part.clone(), child_part(0)],
                }),
                materialized_definition: None,
                allocation_observation: Some(AllocationDescriptor::Memory),
            },
            MonoNode {
                id: MonoId(4),
                key: MonoKey::Allocation(AllocationKey {
                    root,
                    path: vec![root_part, child_part(1)],
                }),
                materialized_definition: None,
                allocation_observation: Some(AllocationDescriptor::Memory),
            },
        ];
        let mono_edge = |from, to, relation, site| DependencyEdge {
            from: GraphNode::Mono(MonoId(from)),
            to: GraphNode::Mono(MonoId(to)),
            kind: DependencyKind::Mono {
                relation,
                collection: MonoCollection::Used,
            },
            sites: vec![site],
            evidence: EvidenceOrigin::PatchedObserver,
        };
        let materialization = |from, to| DependencyEdge {
            from: GraphNode::Mono(MonoId(from)),
            to,
            kind: DependencyKind::MaterializesDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Derived,
        };
        let edges = vec![
            mono_edge(
                0,
                2,
                MonoDependencyKind::ConstAllocation,
                ObservationSite::Source(ByteRange { start: 8, end: 12 }),
            ),
            mono_edge(
                2,
                3,
                MonoDependencyKind::AllocationReference,
                ObservationSite::CompilerGenerated,
            ),
            mono_edge(
                2,
                4,
                MonoDependencyKind::AllocationReference,
                ObservationSite::CompilerGenerated,
            ),
            materialization(0, GraphNode::Definition(DefinitionId(0))),
            materialization(1, GraphNode::ExternalDefinition(ExternalDefinitionId(0))),
        ];
        (definitions, mono_nodes, edges)
    }

    fn allocation_graph(
        mono_nodes: Vec<MonoNode>,
        edges: Vec<DependencyEdge>,
    ) -> Result<DependencyGraph, DependencyGraphError> {
        allocation_graph_with_roots(
            mono_nodes,
            edges,
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
            ],
        )
    }

    fn allocation_graph_with_roots(
        mono_nodes: Vec<MonoNode>,
        edges: Vec<DependencyEdge>,
        roots: Vec<RootRecord>,
    ) -> Result<DependencyGraph, DependencyGraphError> {
        let (definitions, _, _) = allocation_graph_parts();
        DependencyGraph::new(
            definitions,
            Vec::new(),
            Vec::new(),
            mono_nodes,
            edges,
            roots,
        )
    }

    fn allocation_key(nodes: &mut [MonoNode], id: u32) -> &mut AllocationKey {
        let MonoKey::Allocation(key) = &mut nodes[id as usize].key else {
            panic!("expected an allocation node")
        };
        key
    }

    fn associated_graph_parts() -> (
        DefinitionGraph,
        Vec<ProofNode>,
        Vec<MonoNode>,
        Vec<DependencyEdge>,
    ) {
        let written_definition = |id: u32, name: &str, kind, start| {
            let anchor = ByteRange {
                start,
                end: start + 4,
            };
            Definition {
                id: DefinitionId(id),
                key: DefinitionKey(vec![DefinitionKeyPart {
                    kind,
                    origin: DefinitionOriginKey::Written {
                        anchor,
                        unit_kind: WrittenUnitKind::Item,
                    },
                    name: Some(name.to_owned()),
                    same_role_ordinal: 0,
                }]),
                kind,
                parent: None,
                origin: DefinitionOrigin::Written {
                    unit: SourceUnitId(id),
                    unit_range: anchor,
                    anchor,
                    unit_kind: WrittenUnitKind::Item,
                    unit_ordinal: id,
                },
            }
        };
        let definitions = vec![
            written_definition(0, "main", DefinitionKind::Function, 0),
            written_definition(1, "selected", DefinitionKind::AssociatedFunction, 8),
            written_definition(2, "Dispatch", DefinitionKind::Trait, 16),
        ];
        let start_key = ExternalDefinitionKey {
            crate_identity: 1,
            crate_name: "std".to_owned(),
            def_path_hash: [1; 16],
        };
        let graph = DefinitionGraph {
            definitions: definitions.clone(),
            external_definitions: vec![ExternalDefinition {
                id: ExternalDefinitionId(0),
                key: start_key.clone(),
                path: "std::rt::lang_start".to_owned(),
            }],
            edges: Vec::new(),
        };

        let main_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(definitions[0].key.clone()),
            arguments: term(1),
            kind: term(2),
        };
        let target_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(definitions[1].key.clone()),
            arguments: term(3),
            kind: term(4),
        };
        let mono_nodes = vec![
            MonoNode {
                id: MonoId(0),
                key: MonoKey::Instance {
                    instance: main_instance,
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(DefinitionTarget::Local(DefinitionId(0))),
                allocation_observation: None,
            },
            MonoNode {
                id: MonoId(1),
                key: MonoKey::Instance {
                    instance: MonoInstanceKey {
                        definition: DefinitionReferenceKey::External(start_key),
                        arguments: term(5),
                        kind: term(6),
                    },
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(DefinitionTarget::External(ExternalDefinitionId(0))),
                allocation_observation: None,
            },
            MonoNode {
                id: MonoId(2),
                key: MonoKey::Instance {
                    instance: target_instance.clone(),
                    role: MonoInstanceRole::Callable,
                },
                materialized_definition: Some(DefinitionTarget::Local(DefinitionId(1))),
                allocation_observation: None,
            },
        ];

        let implementation = DefinitionTarget::Local(DefinitionId(0));
        let leaf = DefinitionTarget::Local(DefinitionId(1));
        let trait_definition = DefinitionTarget::Local(DefinitionId(2));
        let environment = term(10);
        let predicate = term(11);
        let selection = ProofNode {
            id: ProofId(0),
            key: ProofKey::Obligation {
                environment: environment.clone(),
                predicate: predicate.clone(),
            },
            kind: ProofNodeKind::Obligation {
                environment,
                predicate,
                source: Some(SelectionSource {
                    kind: SelectionSourceKind::UserDefined,
                    term: term(12),
                    implementation: Some(implementation),
                    builtin_trait: None,
                }),
                selection_nested: Some(Vec::new()),
                fulfillment_nested: None,
                query_trace: None,
            },
        };
        let request = term(13);
        let associated = ProofNode {
            id: ProofId(1),
            key: ProofKey::AssociatedItem {
                request: request.clone(),
                raw_instance: target_instance.clone(),
                codegen_instance: target_instance.clone(),
            },
            kind: ProofNodeKind::AssociatedItem {
                request,
                raw_instance: target_instance.clone(),
                codegen_instance: target_instance,
                selection: ProofId(0),
                source_kind: SelectionSourceKind::UserDefined,
                leaf: Some(leaf),
                defining_node: Some(SpecializationNode {
                    kind: SpecializationNodeKind::Impl,
                    target: implementation,
                }),
                finalizing_node: Some(SpecializationNode {
                    kind: SpecializationNodeKind::Trait,
                    target: trait_definition,
                }),
                ancestor_path: vec![
                    SpecializationNode {
                        kind: SpecializationNodeKind::Impl,
                        target: implementation,
                    },
                    SpecializationNode {
                        kind: SpecializationNodeKind::Trait,
                        target: trait_definition,
                    },
                ],
            },
        };
        let mut edges = vec![
            DependencyEdge {
                from: GraphNode::Mono(MonoId(0)),
                to: GraphNode::Mono(MonoId(2)),
                kind: DependencyKind::Mono {
                    relation: MonoDependencyKind::DirectCall,
                    collection: MonoCollection::Used,
                },
                sites: vec![ObservationSite::Source(ByteRange { start: 24, end: 28 })],
                evidence: EvidenceOrigin::PatchedObserver,
            },
            DependencyEdge {
                from: GraphNode::Mono(MonoId(0)),
                to: GraphNode::Proof(ProofId(1)),
                kind: DependencyKind::SelectionProof {
                    relation: MonoDependencyKind::DirectCall,
                    collection: MonoCollection::Used,
                },
                sites: vec![ObservationSite::Source(ByteRange { start: 25, end: 27 })],
                evidence: EvidenceOrigin::PatchedObserver,
            },
        ];
        for (from, to) in [
            (0, GraphNode::Definition(DefinitionId(0))),
            (1, GraphNode::ExternalDefinition(ExternalDefinitionId(0))),
            (2, GraphNode::Definition(DefinitionId(1))),
        ] {
            edges.push(DependencyEdge {
                from: GraphNode::Mono(MonoId(from)),
                to,
                kind: DependencyKind::MaterializesDefinition,
                sites: Vec::new(),
                evidence: EvidenceOrigin::Derived,
            });
        }
        edges.extend([
            relation(
                0,
                GraphNode::Definition(DefinitionId(0)),
                ProofRelationKind::SelectedImpl,
                0,
            ),
            relation(
                1,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::AssociatedSelection,
                0,
            ),
            relation(
                1,
                GraphNode::Definition(DefinitionId(1)),
                ProofRelationKind::AssociatedLeaf,
                0,
            ),
            relation(
                1,
                GraphNode::Definition(DefinitionId(0)),
                ProofRelationKind::AssociatedDefining,
                0,
            ),
            relation(
                1,
                GraphNode::Definition(DefinitionId(2)),
                ProofRelationKind::AssociatedFinalizing,
                0,
            ),
            relation(
                1,
                GraphNode::Definition(DefinitionId(0)),
                ProofRelationKind::SpecializationAncestor,
                0,
            ),
            relation(
                1,
                GraphNode::Definition(DefinitionId(2)),
                ProofRelationKind::SpecializationAncestor,
                1,
            ),
        ]);
        (graph, vec![selection, associated], mono_nodes, edges)
    }

    fn associated_graph(
        definitions: DefinitionGraph,
        proofs: Vec<ProofNode>,
        mono_nodes: Vec<MonoNode>,
        edges: Vec<DependencyEdge>,
    ) -> Result<DependencyGraph, DependencyGraphError> {
        DependencyGraph::new(
            definitions,
            Vec::new(),
            proofs,
            mono_nodes,
            edges,
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
            ],
        )
    }

    #[test]
    fn associated_item_codegen_instance_must_join_the_mono_target() {
        let (definitions, mut proofs, mono_nodes, edges) = associated_graph_parts();
        assert!(
            associated_graph(
                definitions.clone(),
                proofs.clone(),
                mono_nodes.clone(),
                edges.clone(),
            )
            .is_ok()
        );
        let changed = term(99);
        let ProofKey::AssociatedItem {
            codegen_instance, ..
        } = &mut proofs[1].key
        else {
            panic!("expected an associated proof key")
        };
        codegen_instance.arguments = changed.clone();
        let ProofNodeKind::AssociatedItem {
            codegen_instance, ..
        } = &mut proofs[1].kind
        else {
            panic!("expected an associated proof payload")
        };
        codegen_instance.arguments = changed;

        assert_eq!(
            associated_graph(definitions, proofs, mono_nodes, edges),
            Err(DependencyGraphError::InvalidProof)
        );
    }

    #[test]
    fn associated_item_codegen_target_must_be_callable() {
        let (definitions, proofs, mut mono_nodes, edges) = associated_graph_parts();
        let MonoKey::Instance { role, .. } = &mut mono_nodes[2].key else {
            panic!("expected an instance target")
        };
        *role = MonoInstanceRole::Const { promoted: None };

        assert_eq!(
            associated_graph(definitions, proofs, mono_nodes, edges),
            Err(DependencyGraphError::InvalidProof)
        );
    }

    #[test]
    fn associated_direct_call_proof_site_must_be_covered_by_the_mono_site() {
        let (definitions, proofs, mono_nodes, mut edges) = associated_graph_parts();
        let proof_edge = edges
            .iter_mut()
            .find(|edge| matches!(edge.kind, DependencyKind::SelectionProof { .. }))
            .expect("the graph must contain an associated selection edge");
        proof_edge.sites = vec![ObservationSite::Source(ByteRange { start: 32, end: 36 })];

        assert_eq!(
            associated_graph(definitions, proofs, mono_nodes, edges),
            Err(DependencyGraphError::InvalidProof)
        );
    }

    #[test]
    fn upstream_associated_proof_only_use_requires_an_absent_codegen_instance() {
        let (definitions, mut proofs, mono_nodes, mut edges) = associated_graph_parts();
        let upstream_key = definitions.external_definitions[0].key.clone();
        let upstream_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::External(upstream_key),
            arguments: term(90),
            kind: term(91),
        };
        let ProofNodeKind::AssociatedItem {
            codegen_instance, ..
        } = &mut proofs[1].kind
        else {
            panic!("expected an associated proof payload")
        };
        *codegen_instance = upstream_instance.clone();
        let ProofKey::AssociatedItem {
            codegen_instance, ..
        } = &mut proofs[1].key
        else {
            panic!("expected an associated proof key")
        };
        *codegen_instance = upstream_instance;
        edges.retain(|edge| {
            !(edge.from == GraphNode::Mono(MonoId(0))
                && matches!(edge.kind, DependencyKind::Mono { .. }))
        });

        assert!(valid_associated_item_selection_joins(
            &proofs,
            &mono_nodes,
            &edges
        ));

        let mut materialized = mono_nodes.clone();
        materialized[2].key = MonoKey::Instance {
            instance: match &proofs[1].kind {
                ProofNodeKind::AssociatedItem {
                    codegen_instance, ..
                } => codegen_instance.clone(),
                _ => unreachable!(),
            },
            role: MonoInstanceRole::Callable,
        };
        assert!(!valid_associated_item_selection_joins(
            &proofs,
            &materialized,
            &edges
        ));

        if let ProofNodeKind::AssociatedItem {
            codegen_instance, ..
        } = &mut proofs[1].kind
        {
            codegen_instance.definition =
                DefinitionReferenceKey::Local(definitions.definitions[1].key.clone());
        }
        assert!(!valid_associated_item_selection_joins(
            &proofs,
            &mono_nodes,
            &edges
        ));
    }

    #[test]
    fn accepts_allocation_paths_backed_by_mono_edges() {
        let (_, nodes, edges) = allocation_graph_parts();
        assert!(allocation_graph(nodes, edges).is_ok());
    }

    #[test]
    fn construction_is_independent_of_observation_order() {
        let (_, nodes, edges) = allocation_graph_parts();
        let expected = allocation_graph(nodes.clone(), edges.clone()).unwrap();
        let mut reversed_nodes = nodes;
        let mut reversed_edges = edges;
        reversed_nodes.reverse();
        reversed_edges.reverse();

        assert_eq!(
            allocation_graph(reversed_nodes, reversed_edges).unwrap(),
            expected
        );
    }

    #[test]
    fn roots_keep_distinct_reasons_for_the_same_node() {
        let (_, nodes, edges) = allocation_graph_parts();
        let graph = allocation_graph_with_roots(
            nodes,
            edges,
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::ExternalSymbol,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::ExplicitEntry,
                },
            ],
        )
        .unwrap();

        assert_eq!(
            graph.roots,
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::ExplicitEntry,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::ExternalSymbol,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
            ]
        );
    }

    #[test]
    fn explicit_definition_roots_accept_functions_and_uses() {
        for kind in [DefinitionKind::Function, DefinitionKind::Use] {
            let (mut definitions, _, _) = allocation_graph_parts();
            definitions.definitions[0].kind = kind;
            definitions.definitions[0].key.0[0].kind = kind;

            let graph = DependencyGraph::new(
                definitions,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                vec![RootRecord {
                    node: GraphNode::Definition(DefinitionId(0)),
                    reason: RootReason::ExplicitEntry,
                }],
            )
            .unwrap();

            assert_eq!(
                graph.roots,
                vec![RootRecord {
                    node: GraphNode::Definition(DefinitionId(0)),
                    reason: RootReason::ExplicitEntry,
                }]
            );
        }
    }

    #[test]
    fn explicit_definition_roots_reject_other_definition_kinds() {
        let (mut definitions, _, _) = allocation_graph_parts();
        definitions.definitions[0].kind = DefinitionKind::Static;
        definitions.definitions[0].key.0[0].kind = DefinitionKind::Static;

        assert_eq!(
            DependencyGraph::new(
                definitions,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                vec![RootRecord {
                    node: GraphNode::Definition(DefinitionId(0)),
                    reason: RootReason::ExplicitEntry,
                }],
            ),
            Err(DependencyGraphError::InvalidRoot)
        );
    }

    #[test]
    fn native_link_roots_accept_only_linked_definition_kinds() {
        let (mut definitions, mono_nodes, _) = allocation_graph_parts();
        definitions.definitions[0].kind = DefinitionKind::ForeignModule;
        let root = |definition| RootRecord {
            node: GraphNode::Definition(DefinitionId(definition)),
            reason: RootReason::NativeLink,
        };
        assert!(valid_roots(&[root(0)], &definitions, &mono_nodes));

        for kind in [DefinitionKind::Function, DefinitionKind::Static] {
            let mut with_child = definitions.clone();
            let mut child = with_child.definitions[0].clone();
            child.id = DefinitionId(1);
            child.kind = kind;
            child.parent = Some(DefinitionId(0));
            with_child.definitions.push(child);
            assert!(valid_roots(&[root(1)], &with_child, &mono_nodes));

            with_child.definitions[1].parent = None;
            assert!(!valid_roots(&[root(1)], &with_child, &mono_nodes));
        }

        definitions.definitions[0].kind = DefinitionKind::Struct;
        assert!(!valid_roots(&[root(0)], &definitions, &mono_nodes));
        assert!(!valid_roots(
            &[RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::NativeLink,
            }],
            &definitions,
            &mono_nodes,
        ));
    }

    #[test]
    fn downstream_selection_candidates_are_containers_and_their_direct_members() {
        let (mut definitions, _, _) = allocation_graph_parts();
        definitions.definitions[0].kind = DefinitionKind::Trait;
        assert!(is_downstream_selection_candidate(
            &definitions,
            DefinitionId(0)
        ));

        let mut member = definitions.definitions[0].clone();
        member.id = DefinitionId(1);
        member.kind = DefinitionKind::AssociatedFunction;
        member.parent = Some(DefinitionId(0));
        definitions.definitions.push(member);
        assert!(is_downstream_selection_candidate(
            &definitions,
            DefinitionId(1)
        ));

        definitions.definitions[0].kind = DefinitionKind::Function;
        assert!(!is_downstream_selection_candidate(
            &definitions,
            DefinitionId(0)
        ));
        assert!(!is_downstream_selection_candidate(
            &definitions,
            DefinitionId(1)
        ));
    }

    #[test]
    fn an_explicit_static_root_uses_the_local_mono_node() {
        let (mut definitions, _, _) = allocation_graph_parts();
        definitions.definitions[0].kind = DefinitionKind::Static;
        definitions.definitions[0].key.0[0].kind = DefinitionKind::Static;
        let definition_key = definitions.definitions[0].key.clone();
        let mono_nodes = vec![MonoNode {
            id: MonoId(0),
            key: MonoKey::Static {
                definition: definition_key,
            },
            materialized_definition: Some(DefinitionTarget::Local(DefinitionId(0))),
            allocation_observation: None,
        }];
        let edges = vec![DependencyEdge {
            from: GraphNode::Mono(MonoId(0)),
            to: GraphNode::Definition(DefinitionId(0)),
            kind: DependencyKind::MaterializesDefinition,
            sites: Vec::new(),
            evidence: EvidenceOrigin::Derived,
        }];

        assert!(
            DependencyGraph::new(
                definitions,
                Vec::new(),
                Vec::new(),
                mono_nodes,
                edges,
                vec![RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::ExplicitEntry,
                }],
            )
            .is_ok()
        );
    }

    #[test]
    fn roots_reject_duplicate_records_and_unpaired_binary_roots() {
        for roots in [
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
            ],
            vec![RootRecord {
                node: GraphNode::Mono(MonoId(0)),
                reason: RootReason::Main,
            }],
            vec![RootRecord {
                node: GraphNode::Mono(MonoId(1)),
                reason: RootReason::StartInstance,
            }],
        ] {
            let (_, nodes, edges) = allocation_graph_parts();
            assert_eq!(
                allocation_graph_with_roots(nodes, edges, roots),
                Err(DependencyGraphError::InvalidRoot)
            );
        }
    }

    #[test]
    fn roots_reject_an_invalid_reason_shape() {
        for roots in [
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::StartInstance,
                },
            ],
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(2)),
                    reason: RootReason::ExplicitEntry,
                },
            ],
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(2)),
                    reason: RootReason::StartInstance,
                },
            ],
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::UsedAttribute,
                },
            ],
            vec![
                RootRecord {
                    node: GraphNode::Mono(MonoId(0)),
                    reason: RootReason::Main,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(1)),
                    reason: RootReason::StartInstance,
                },
                RootRecord {
                    node: GraphNode::Mono(MonoId(2)),
                    reason: RootReason::ExternalSymbol,
                },
            ],
        ] {
            let (_, nodes, edges) = allocation_graph_parts();
            assert_eq!(
                allocation_graph_with_roots(nodes, edges, roots),
                Err(DependencyGraphError::InvalidRoot)
            );
        }
    }

    #[test]
    fn accepts_an_allocation_ordinal_gap_from_another_incoming_edge() {
        let (_, mut nodes, mut edges) = allocation_graph_parts();
        allocation_key(&mut nodes, 3).path = vec![AllocationPathPart {
            relation: MonoDependencyKind::ConstAllocation,
            collection: MonoCollection::Used,
            site: AllocationPathSite::Source(ByteRange { start: 20, end: 24 }),
            same_role_ordinal: 0,
        }];
        edges.push(DependencyEdge {
            from: GraphNode::Mono(MonoId(0)),
            to: GraphNode::Mono(MonoId(3)),
            kind: DependencyKind::Mono {
                relation: MonoDependencyKind::ConstAllocation,
                collection: MonoCollection::Used,
            },
            sites: vec![ObservationSite::Source(ByteRange { start: 20, end: 24 })],
            evidence: EvidenceOrigin::PatchedObserver,
        });

        assert!(allocation_graph(nodes, edges).is_ok());
    }

    #[test]
    fn rejects_an_allocation_path_with_a_different_root() {
        let (_, mut nodes, edges) = allocation_graph_parts();
        allocation_key(&mut nodes, 2).root = AllocationRootKey::Static(DefinitionKey(Vec::new()));
        assert_eq!(
            allocation_graph(nodes, edges),
            Err(DependencyGraphError::InvalidMonoNode)
        );
    }

    #[test]
    fn rejects_an_allocation_path_with_a_missing_prefix() {
        let (_, mut nodes, edges) = allocation_graph_parts();
        allocation_key(&mut nodes, 3).path.remove(0);
        assert_eq!(
            allocation_graph(nodes, edges),
            Err(DependencyGraphError::InvalidMonoNode)
        );
    }

    #[test]
    fn rejects_an_allocation_path_with_a_different_relation_or_collection() {
        for mutate in [
            |part: &mut AllocationPathPart| part.relation = MonoDependencyKind::ConstAllocation,
            |part: &mut AllocationPathPart| part.collection = MonoCollection::Mentioned,
        ] {
            let (_, mut nodes, edges) = allocation_graph_parts();
            let part = allocation_key(&mut nodes, 3).path.last_mut().unwrap();
            mutate(part);
            assert_eq!(
                allocation_graph(nodes, edges),
                Err(DependencyGraphError::InvalidMonoNode)
            );
        }
    }

    #[test]
    fn rejects_an_allocation_path_with_a_different_site() {
        let (_, mut nodes, edges) = allocation_graph_parts();
        allocation_key(&mut nodes, 2).path[0].site =
            AllocationPathSite::Source(ByteRange { start: 9, end: 12 });
        assert_eq!(
            allocation_graph(nodes, edges),
            Err(DependencyGraphError::InvalidMonoNode)
        );
    }

    #[test]
    fn rejects_duplicate_or_out_of_range_allocation_ordinals() {
        for ordinal in [0, 2] {
            let (_, mut nodes, edges) = allocation_graph_parts();
            allocation_key(&mut nodes, 4)
                .path
                .last_mut()
                .unwrap()
                .same_role_ordinal = ordinal;
            assert_eq!(
                allocation_graph(nodes, edges),
                Err(DependencyGraphError::InvalidMonoNode)
            );
        }
    }

    fn exact_proofs() -> (Vec<ProofNode>, Vec<DependencyEdge>) {
        let implementation = DefinitionTarget::Local(DefinitionId(0));
        let leaf = DefinitionTarget::Local(DefinitionId(1));
        let trait_definition = DefinitionTarget::Local(DefinitionId(2));
        let source = SelectionSource {
            kind: SelectionSourceKind::UserDefined,
            term: term(40),
            implementation: Some(implementation),
            builtin_trait: None,
        };
        let mut first = obligation(0, Some(source));
        let mut second = obligation(1, None);

        let projection_environment = term(50);
        let projection_alias = term(51);
        let projection = ProofNode {
            id: ProofId(2),
            key: ProofKey::Projection {
                environment: projection_environment.clone(),
                alias: projection_alias.clone(),
            },
            kind: ProofNodeKind::Projection {
                environment: projection_environment,
                alias: projection_alias,
                source_kind: ProjectionSourceKind::SelectedUserDefined,
                source: term(52),
                outcome: ProjectionOutcome::Progress { raw_term: term(53) },
                selected_trait: Some(ProofId(0)),
                selected_impl: Some(implementation),
                selected_item: Some(leaf),
                owners: vec![ProofId(0)],
                nested: vec![ProofId(1)],
                query_trace: None,
                normalized_result: None,
            },
        };

        let request = term(60);
        let raw_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(DefinitionKey(Vec::new())),
            arguments: term(61),
            kind: term(62),
        };
        let codegen_instance = MonoInstanceKey {
            definition: DefinitionReferenceKey::Local(DefinitionKey(Vec::new())),
            arguments: term(63),
            kind: term(64),
        };
        let associated = ProofNode {
            id: ProofId(3),
            key: ProofKey::AssociatedItem {
                request: request.clone(),
                raw_instance: raw_instance.clone(),
                codegen_instance: codegen_instance.clone(),
            },
            kind: ProofNodeKind::AssociatedItem {
                request,
                raw_instance,
                codegen_instance,
                selection: ProofId(0),
                source_kind: SelectionSourceKind::UserDefined,
                leaf: Some(leaf),
                defining_node: Some(SpecializationNode {
                    kind: SpecializationNodeKind::Impl,
                    target: implementation,
                }),
                finalizing_node: Some(SpecializationNode {
                    kind: SpecializationNodeKind::Trait,
                    target: trait_definition,
                }),
                ancestor_path: vec![
                    SpecializationNode {
                        kind: SpecializationNodeKind::Impl,
                        target: implementation,
                    },
                    SpecializationNode {
                        kind: SpecializationNodeKind::Trait,
                        target: trait_definition,
                    },
                ],
            },
        };

        let cycle = ProofNode {
            id: ProofId(4),
            key: ProofKey::Cycle {
                members: vec![first.key.clone(), second.key.clone()],
                coinductive: true,
            },
            kind: ProofNodeKind::Cycle {
                members: vec![ProofId(0), ProofId(1)],
                coinductive: true,
            },
        };
        if let ProofNodeKind::Obligation {
            selection_nested,
            query_trace,
            ..
        } = &mut first.kind
        {
            *selection_nested = Some(vec![ProofId(1)]);
            *query_trace = Some(SolverTracePayload {
                root: ProofId(0),
                obligations: vec![ProofId(0), ProofId(1)],
                trait_selections: vec![ProofId(0)],
                projections: vec![ProofId(2)],
                fulfillments: vec![ProofId(1)],
                cycles: vec![ProofId(4)],
            });
        }
        if let ProofNodeKind::Obligation {
            fulfillment_nested, ..
        } = &mut second.kind
        {
            *fulfillment_nested = Some(vec![ProofId(0)]);
        }
        let edges = vec![
            relation(
                0,
                definition_node(implementation),
                ProofRelationKind::SelectedImpl,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::QueryTraceRoot,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::TraceObligation,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(1)),
                ProofRelationKind::TraceObligation,
                1,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::TraceTraitSelection,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(2)),
                ProofRelationKind::TraceProjection,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(1)),
                ProofRelationKind::TraceFulfillment,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(4)),
                ProofRelationKind::TraceCycle,
                0,
            ),
            relation(
                0,
                GraphNode::Proof(ProofId(1)),
                ProofRelationKind::TraitSelectionNested,
                0,
            ),
            relation(
                1,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::FulfillmentNested,
                0,
            ),
            relation(
                2,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::ProjectionOwner,
                0,
            ),
            relation(
                2,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::ProjectionSelectedTrait,
                0,
            ),
            relation(
                2,
                definition_node(implementation),
                ProofRelationKind::SelectedImpl,
                0,
            ),
            relation(
                2,
                definition_node(leaf),
                ProofRelationKind::SelectedTraitItem,
                0,
            ),
            relation(
                2,
                GraphNode::Proof(ProofId(1)),
                ProofRelationKind::ProjectionNested,
                0,
            ),
            relation(
                3,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::AssociatedSelection,
                0,
            ),
            relation(
                3,
                definition_node(leaf),
                ProofRelationKind::AssociatedLeaf,
                0,
            ),
            relation(
                3,
                definition_node(implementation),
                ProofRelationKind::AssociatedDefining,
                0,
            ),
            relation(
                3,
                definition_node(trait_definition),
                ProofRelationKind::AssociatedFinalizing,
                0,
            ),
            relation(
                3,
                definition_node(implementation),
                ProofRelationKind::SpecializationAncestor,
                0,
            ),
            relation(
                3,
                definition_node(trait_definition),
                ProofRelationKind::SpecializationAncestor,
                1,
            ),
            relation(
                4,
                GraphNode::Proof(ProofId(0)),
                ProofRelationKind::CycleMember,
                0,
            ),
            relation(
                4,
                GraphNode::Proof(ProofId(1)),
                ProofRelationKind::CycleMember,
                1,
            ),
        ];
        (vec![first, second, projection, associated, cycle], edges)
    }

    #[test]
    fn accepts_relations_that_exactly_match_proof_payloads() {
        let (proofs, edges) = exact_proofs();
        assert!(valid_proof_relations(&proofs, &edges));
    }

    #[test]
    fn rejects_a_payload_relation_with_the_wrong_target() {
        let (proofs, mut edges) = exact_proofs();
        let edge = edges
            .iter_mut()
            .find(|edge| {
                matches!(
                    edge.kind,
                    DependencyKind::ProofRelation {
                        relation: ProofRelationKind::AssociatedLeaf,
                        ..
                    }
                )
            })
            .unwrap();
        edge.to = GraphNode::Definition(DefinitionId(0));
        assert!(!valid_proof_relations(&proofs, &edges));
    }

    #[test]
    fn rejects_reordered_cycle_members() {
        let (proofs, mut edges) = exact_proofs();
        for edge in &mut edges {
            if let DependencyKind::ProofRelation {
                relation: ProofRelationKind::CycleMember,
                ordinal,
            } = &mut edge.kind
            {
                *ordinal = 1 - *ordinal;
            }
        }
        assert!(!valid_proof_relations(&proofs, &edges));
    }

    #[test]
    fn rejects_gapped_and_duplicate_relation_slots() {
        let (proofs, mut edges) = exact_proofs();
        let ancestor = edges
            .iter_mut()
            .find(|edge| {
                matches!(
                    edge.kind,
                    DependencyKind::ProofRelation {
                        relation: ProofRelationKind::SpecializationAncestor,
                        ordinal: 1,
                    }
                )
            })
            .unwrap();
        ancestor.kind = DependencyKind::ProofRelation {
            relation: ProofRelationKind::SpecializationAncestor,
            ordinal: 2,
        };
        assert!(!valid_proof_relations(&proofs, &edges));

        let (proofs, mut edges) = exact_proofs();
        edges.push(relation(
            4,
            GraphNode::Proof(ProofId(0)),
            ProofRelationKind::CycleMember,
            1,
        ));
        assert!(!valid_proof_relations(&proofs, &edges));
    }

    #[test]
    fn accepts_an_associated_request_without_a_user_defined_leaf() {
        let (mut proofs, mut edges) = exact_proofs();
        let trait_definition = DefinitionTarget::Local(DefinitionId(2));
        if let ProofNodeKind::Obligation { source, .. } = &mut proofs[0].kind {
            *source = Some(SelectionSource {
                kind: SelectionSourceKind::Builtin,
                term: term(70),
                implementation: None,
                builtin_trait: Some(BuiltinTraitTarget {
                    kind: BuiltinTraitTargetKind::TraitDefinition,
                    target: trait_definition,
                }),
            });
        }
        if let ProofNodeKind::AssociatedItem {
            source_kind,
            leaf,
            defining_node,
            finalizing_node,
            ancestor_path,
            ..
        } = &mut proofs[3].kind
        {
            *source_kind = SelectionSourceKind::Builtin;
            *leaf = None;
            *defining_node = None;
            *finalizing_node = None;
            ancestor_path.clear();
        }
        edges.retain(|edge| {
            !(edge.from == GraphNode::Proof(ProofId(0))
                && matches!(
                    edge.kind,
                    DependencyKind::ProofRelation {
                        relation: ProofRelationKind::SelectedImpl,
                        ..
                    }
                ))
                && !(edge.from == GraphNode::Proof(ProofId(3))
                    && matches!(
                        edge.kind,
                        DependencyKind::ProofRelation {
                            relation: ProofRelationKind::AssociatedLeaf
                                | ProofRelationKind::AssociatedDefining
                                | ProofRelationKind::AssociatedFinalizing
                                | ProofRelationKind::SpecializationAncestor,
                            ..
                        }
                    ))
        });
        edges.push(relation(
            0,
            definition_node(trait_definition),
            ProofRelationKind::TraitDefinition,
            0,
        ));
        assert!(valid_proof_relations(&proofs, &edges));
        let empty_definitions = DefinitionGraph {
            definitions: Vec::new(),
            external_definitions: Vec::new(),
            edges: Vec::new(),
        };
        assert!(!invalid_proof_node(&proofs[3], &proofs, &empty_definitions));
    }
}
