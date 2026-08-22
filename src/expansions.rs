//! Ownership-preserving conversion of compiler expansion provenance.

#[cfg(rust_item_dependencies_patched)]
use std::collections::{BTreeMap, BTreeSet};

use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::ty::{
    MacroImplementationKind as RustcImplementationKind, MacroInvocationFragmentKind,
    MacroInvocationOrigin,
};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::hygiene::{AstPass, DesugaringKind as RustcDesugaringKind};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::{ExpnId, ExpnKind, MacroKind, Span};

use crate::definitions::{CollectedDefinitions, DefinitionError};
#[cfg(rust_item_dependencies_patched)]
use crate::dependency_graph::{
    AstPassKind, DependencyKind, DesugaringKind, EvidenceOrigin, ExpansionFragmentKind,
    ExpansionId, ExpansionKey, ExpansionKeyPart, ExpansionKind, GraphNode, MacroImplementationKind,
    MacroStyle, ObservationSite,
};
use crate::dependency_graph::{DependencyEdge, ExpansionNode};
#[cfg(rust_item_dependencies_patched)]
use crate::graph::{DefinitionId, DefinitionOrigin, DefinitionTarget};
use crate::source::SourceInventory;
#[cfg(rust_item_dependencies_patched)]
use crate::source::{ByteRange, original_span_range, resolve_attribute_source};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpansionError {
    IncompleteOrigin,
    InvalidSpan,
    Definition(DefinitionError),
}

impl From<DefinitionError> for ExpansionError {
    fn from(error: DefinitionError) -> Self {
        Self::Definition(error)
    }
}

pub(crate) struct CollectedExpansions {
    pub nodes: Vec<ExpansionNode>,
    pub edges: Vec<DependencyEdge>,
}

#[cfg(not(rust_item_dependencies_patched))]
pub(crate) fn collect_expansions(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _definitions: &mut CollectedDefinitions,
) -> Result<CollectedExpansions, ExpansionError> {
    Err(ExpansionError::IncompleteOrigin)
}

#[cfg(rust_item_dependencies_patched)]
pub(crate) fn collect_expansions(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definitions: &mut CollectedDefinitions,
) -> Result<CollectedExpansions, ExpansionError> {
    let origins = &tcx.resolutions(()).macro_invocation_origins;
    let mut expansion_ids = Vec::<ExpnId>::new();
    let sorted_origins = origins
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    for (_, expansion, origin) in sorted_origins {
        add_expansion_closure(origins, expansion, &mut expansion_ids)?;
        add_expansion_closure(origins, origin.discovered_in_expansion, &mut expansion_ids)?;
    }
    for definition in tcx.iter_local_def_id() {
        add_expansion_closure(
            origins,
            tcx.expn_that_defined(definition.to_def_id()),
            &mut expansion_ids,
        )?;
    }
    expansion_ids.retain(|expansion| *expansion != ExpnId::root());

    let mut raw = Vec::with_capacity(expansion_ids.len());
    for expansion in expansion_ids {
        let origin = origins.get(&expansion);
        let data = expansion.expn_data();
        let kind = expansion_kind(&data.kind)?;
        let macro_definition = data
            .macro_def_id
            .map(|definition| definitions.target(tcx, definition))
            .transpose()?;
        let macro_definition_key = data
            .macro_def_id
            .map(|definition| definitions.target_key(tcx, definition))
            .transpose()?;
        let invocation_range = source_range(compiler, source, data.call_site)?;
        let node_range = origin
            .map(|origin| source_range(compiler, source, origin.invocation_node_span))
            .transpose()?
            .flatten();
        let target_range = origin
            .and_then(|origin| origin.target_span)
            .map(|span| source_range(compiler, source, span))
            .transpose()?
            .flatten();
        let discovered_in = origin
            .map(|origin| origin.discovered_in_expansion)
            .filter(|parent| *parent != ExpnId::root());
        let semantic_parent = (data.parent != ExpnId::root()).then_some(data.parent);
        let source_call = data.call_site.ctxt().outer_expn();
        let source_call_parent =
            (source_call != ExpnId::root() && source_call != expansion).then_some(source_call);
        let identity_parent = discovered_in.or(source_call_parent).or(semantic_parent);
        let fragment = origin.map(|origin| fragment_kind(origin.fragment_kind));
        let implementation = origin.map(|origin| implementation_kind(origin.implementation_kind));
        let selected_macro_rule = origin
            .map(|origin| selected_macro_rule_range(compiler, tcx, source, origin))
            .transpose()?
            .flatten();
        let attribute = matches!(&data.kind, ExpnKind::Macro(MacroKind::Attr, _));
        let written_invocation = if let Some(origin) =
            origin.filter(|origin| origin.discovered_in_expansion == ExpnId::root())
        {
            Some(
                written_invocation(
                    source,
                    invocation_range,
                    node_range,
                    target_range,
                    origin,
                    attribute,
                )
                .ok_or(ExpansionError::IncompleteOrigin)?,
            )
        } else {
            None
        };
        let source_owner = origin
            .map(|origin| {
                expansion_source_owner(
                    compiler,
                    source,
                    definitions,
                    origin,
                    written_invocation,
                    attribute,
                )
            })
            .transpose()?
            .flatten();
        raw.push(RawExpansion {
            compiler_id: expansion,
            identity_parent,
            kind: kind.clone(),
            part: ExpansionKeyPart {
                kind,
                fragment,
                implementation,
                invocation_range,
                node_range,
                target_range,
                macro_definition: macro_definition_key,
                selected_macro_rule,
                same_role_ordinal: 0,
            },
            fragment,
            implementation,
            discovered_in,
            semantic_parent,
            source_call_parent,
            written_invocation,
            source_owner,
            macro_definition,
            key: ExpansionKey(Vec::new()),
        });
    }

    assign_expansion_keys(&mut raw)?;
    raw.sort_by(|left, right| left.key.cmp(&right.key));
    let compiler_ids = raw
        .iter()
        .enumerate()
        .map(|(index, expansion)| (expansion.compiler_id, ExpansionId(index as u32)))
        .collect::<Vec<_>>();
    let expansion_id = |compiler_id: ExpnId| {
        compiler_ids
            .iter()
            .find_map(|(candidate, id)| (*candidate == compiler_id).then_some(*id))
    };

    let mut nodes = Vec::with_capacity(raw.len());
    let mut edges = Vec::new();
    for (index, expansion) in raw.iter().enumerate() {
        let id = ExpansionId(index as u32);
        let site = expansion_site(expansion);
        let discovered_in = map_relation(expansion.discovered_in, &expansion_id)?;
        let semantic_parent = map_relation(expansion.semantic_parent, &expansion_id)?;
        let source_call_parent = map_relation(expansion.source_call_parent, &expansion_id)?;
        nodes.push(ExpansionNode {
            id,
            key: expansion.key.clone(),
            kind: expansion.kind.clone(),
            fragment: expansion.fragment,
            implementation: expansion.implementation,
            discovered_in,
            semantic_parent,
            source_call_parent,
            written_invocation: expansion.written_invocation,
            source_owner: expansion.source_owner,
            macro_definition: expansion.macro_definition,
        });
        for (parent, kind) in [
            (discovered_in, DependencyKind::ExpansionDiscoveredIn),
            (semantic_parent, DependencyKind::ExpansionSemanticParent),
            (
                source_call_parent,
                DependencyKind::ExpansionSourceCallParent,
            ),
        ] {
            if let Some(parent) = parent {
                edges.push(structural_edge(
                    GraphNode::Expansion(id),
                    GraphNode::Expansion(parent),
                    kind,
                ));
            }
        }
        if let Some(target) = expansion.macro_definition {
            edges.push(structural_edge(
                GraphNode::Expansion(id),
                definition_node(target),
                DependencyKind::MacroDefinition,
            ));
        }
        if let Some(owner) = expansion.source_owner {
            edges.push(edge(
                GraphNode::Definition(owner),
                GraphNode::Expansion(id),
                DependencyKind::ExpansionUse,
                site,
            ));
        }
    }

    for definition in tcx.iter_local_def_id() {
        let Some(id) = definitions.definition_id(definition) else {
            return Err(ExpansionError::IncompleteOrigin);
        };
        let compiler_expansion = match definitions.graph.definitions[id.0 as usize].origin {
            DefinitionOrigin::Expanded { .. } => definition_expansion(tcx, definition)?,
            DefinitionOrigin::CompilerGenerated { .. } => {
                let expansion = tcx.expn_that_defined(definition.to_def_id());
                if expansion == ExpnId::root() {
                    continue;
                }
                expansion
            }
            DefinitionOrigin::Written { .. } | DefinitionOrigin::Injected { .. } => continue,
        };
        let expansion = nearest_observed_expansion(origins, compiler_expansion, &expansion_id)?;
        edges.push(structural_edge(
            GraphNode::Definition(id),
            GraphNode::Expansion(expansion),
            DependencyKind::GeneratedBy,
        ));
    }

    Ok(CollectedExpansions { nodes, edges })
}

#[cfg(rust_item_dependencies_patched)]
struct RawExpansion {
    compiler_id: ExpnId,
    identity_parent: Option<ExpnId>,
    kind: ExpansionKind,
    part: ExpansionKeyPart,
    key: ExpansionKey,
    fragment: Option<ExpansionFragmentKind>,
    implementation: Option<MacroImplementationKind>,
    discovered_in: Option<ExpnId>,
    semantic_parent: Option<ExpnId>,
    source_call_parent: Option<ExpnId>,
    written_invocation: Option<crate::source::SourceUnitId>,
    source_owner: Option<DefinitionId>,
    macro_definition: Option<DefinitionTarget>,
}

#[cfg(rust_item_dependencies_patched)]
fn add_expansion_closure(
    origins: &rustc_data_structures::unord::UnordMap<ExpnId, MacroInvocationOrigin>,
    expansion: ExpnId,
    output: &mut Vec<ExpnId>,
) -> Result<(), ExpansionError> {
    if expansion == ExpnId::root() || output.contains(&expansion) {
        return Ok(());
    }
    output.push(expansion);
    let data = expansion.expn_data();
    if let Some(origin) = origins.get(&expansion) {
        add_expansion_closure(origins, origin.discovered_in_expansion, output)?;
    }
    add_expansion_closure(origins, data.parent, output)?;
    let source_call_parent = data.call_site.ctxt().outer_expn();
    if source_call_parent != expansion {
        add_expansion_closure(origins, source_call_parent, output)?;
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_kind(kind: &ExpnKind) -> Result<ExpansionKind, ExpansionError> {
    Ok(match kind {
        ExpnKind::Root => return Err(ExpansionError::IncompleteOrigin),
        ExpnKind::Macro(style, name) => ExpansionKind::Macro {
            style: match style {
                MacroKind::Bang => MacroStyle::Bang,
                MacroKind::Attr => MacroStyle::Attribute,
                MacroKind::Derive => MacroStyle::Derive,
            },
            name: name.to_string(),
        },
        ExpnKind::AstPass(pass) => ExpansionKind::AstPass(match pass {
            AstPass::StdImports => AstPassKind::StandardImports,
            AstPass::TestHarness => AstPassKind::TestHarness,
            AstPass::ProcMacroHarness => AstPassKind::ProcMacroHarness,
        }),
        ExpnKind::Desugaring(kind) => ExpansionKind::Desugaring(match kind {
            RustcDesugaringKind::QuestionMark => DesugaringKind::QuestionMark,
            RustcDesugaringKind::TryBlock => DesugaringKind::TryBlock,
            RustcDesugaringKind::YeetExpr => DesugaringKind::YeetExpression,
            RustcDesugaringKind::OpaqueTy => DesugaringKind::OpaqueType,
            RustcDesugaringKind::Async => DesugaringKind::Async,
            RustcDesugaringKind::Await => DesugaringKind::Await,
            RustcDesugaringKind::ForLoop => DesugaringKind::ForLoop,
            RustcDesugaringKind::WhileLoop => DesugaringKind::WhileLoop,
            RustcDesugaringKind::BoundModifier => DesugaringKind::BoundModifier,
            RustcDesugaringKind::Contract => DesugaringKind::Contract,
            RustcDesugaringKind::PatTyRange => DesugaringKind::PatternTypeRange,
            RustcDesugaringKind::FormatLiteral { source: true } => {
                DesugaringKind::WrittenFormatLiteral
            }
            RustcDesugaringKind::FormatLiteral { source: false } => {
                DesugaringKind::ExpandedFormatLiteral
            }
            RustcDesugaringKind::RangeExpr => DesugaringKind::RangeExpression,
        }),
    })
}

#[cfg(rust_item_dependencies_patched)]
fn fragment_kind(kind: MacroInvocationFragmentKind) -> ExpansionFragmentKind {
    match kind {
        MacroInvocationFragmentKind::OptExpr => ExpansionFragmentKind::OptionalExpression,
        MacroInvocationFragmentKind::MethodReceiverExpr => {
            ExpansionFragmentKind::MethodReceiverExpression
        }
        MacroInvocationFragmentKind::Expr => ExpansionFragmentKind::Expression,
        MacroInvocationFragmentKind::Pat => ExpansionFragmentKind::Pattern,
        MacroInvocationFragmentKind::Ty => ExpansionFragmentKind::Type,
        MacroInvocationFragmentKind::Stmts => ExpansionFragmentKind::Statements,
        MacroInvocationFragmentKind::Items => ExpansionFragmentKind::Items,
        MacroInvocationFragmentKind::TraitItems => ExpansionFragmentKind::TraitItems,
        MacroInvocationFragmentKind::ImplItems => ExpansionFragmentKind::ImplItems,
        MacroInvocationFragmentKind::TraitImplItems => ExpansionFragmentKind::TraitImplItems,
        MacroInvocationFragmentKind::ForeignItems => ExpansionFragmentKind::ForeignItems,
        MacroInvocationFragmentKind::Arms => ExpansionFragmentKind::Arms,
        MacroInvocationFragmentKind::ExprFields => ExpansionFragmentKind::ExpressionFields,
        MacroInvocationFragmentKind::PatFields => ExpansionFragmentKind::PatternFields,
        MacroInvocationFragmentKind::GenericParams => ExpansionFragmentKind::GenericParameters,
        MacroInvocationFragmentKind::Params => ExpansionFragmentKind::Parameters,
        MacroInvocationFragmentKind::FieldDefs => ExpansionFragmentKind::FieldDefinitions,
        MacroInvocationFragmentKind::Variants => ExpansionFragmentKind::Variants,
        MacroInvocationFragmentKind::WherePredicates => ExpansionFragmentKind::WherePredicates,
        MacroInvocationFragmentKind::Crate => ExpansionFragmentKind::Crate,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn implementation_kind(kind: RustcImplementationKind) -> MacroImplementationKind {
    match kind {
        RustcImplementationKind::Builtin => MacroImplementationKind::Builtin,
        RustcImplementationKind::Declarative => MacroImplementationKind::Declarative,
        RustcImplementationKind::Procedural => MacroImplementationKind::Procedural,
        RustcImplementationKind::Legacy => MacroImplementationKind::Legacy,
        RustcImplementationKind::InertAttribute => MacroImplementationKind::InertAttribute,
        RustcImplementationKind::GlobDelegation => MacroImplementationKind::GlobDelegation,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn source_range(
    compiler: &Compiler,
    source: &SourceInventory,
    span: Span,
) -> Result<Option<ByteRange>, ExpansionError> {
    if span.is_dummy() {
        return Ok(None);
    }
    let source_map = compiler.sess.source_map();
    let start = source_map.lookup_byte_offset(span.lo());
    let end = source_map.lookup_byte_offset(span.hi());
    if start.sf.start_pos != end.sf.start_pos {
        return Err(ExpansionError::InvalidSpan);
    }
    if start.sf.name.short().to_string() != "main.rs" {
        return Ok(None);
    }
    original_span_range(compiler, &source.offsets, span)
        .map(Some)
        .map_err(|_| ExpansionError::InvalidSpan)
}

#[cfg(rust_item_dependencies_patched)]
fn selected_macro_rule_range(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    origin: &MacroInvocationOrigin,
) -> Result<Option<ByteRange>, ExpansionError> {
    let Some(selection) = origin.selected_macro_rule else {
        return Ok(None);
    };
    let resolutions = tcx.resolutions(());
    let rules = resolutions
        .macro_rules_definitions
        .get(&selection.definition)
        .ok_or(ExpansionError::IncompleteOrigin)?;
    let rule = rules
        .get(selection.rule_index)
        .ok_or(ExpansionError::IncompleteOrigin)?;
    if resolutions
        .expn_that_defined
        .contains_key(&selection.definition)
    {
        return Ok(None);
    }
    let start =
        source_range(compiler, source, rule.start_span)?.ok_or(ExpansionError::IncompleteOrigin)?;
    let end =
        source_range(compiler, source, rule.end_span)?.ok_or(ExpansionError::IncompleteOrigin)?;
    let range = ByteRange {
        start: start.start,
        end: end.end,
    };
    if range.start >= range.end
        || !source.units.iter().any(|unit| {
            unit.kind == crate::source::WrittenUnitKind::MacroRule && unit.full_range == range
        })
    {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok(Some(range))
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_source_owner(
    compiler: &Compiler,
    source: &SourceInventory,
    definitions: &CollectedDefinitions,
    origin: &MacroInvocationOrigin,
    written_invocation: Option<crate::source::SourceUnitId>,
    attribute: bool,
) -> Result<Option<DefinitionId>, ExpansionError> {
    if let Some(target_span) = origin.target_span {
        if let Some(target_range) = source_range(compiler, source, target_span)? {
            let mut candidates = definitions
                .graph
                .definitions
                .iter()
                .filter_map(|definition| match definition.origin {
                    DefinitionOrigin::Written { anchor, .. }
                        if target_range.contains(anchor)
                            && !matches!(definition.kind, crate::graph::DefinitionKind::Crate) =>
                    {
                        Some((definition.key.0.len(), definition.id))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            candidates.sort();
            if let Some(&(depth, owner)) = candidates.first()
                && candidates
                    .get(1)
                    .is_none_or(|candidate| candidate.0 != depth)
            {
                return Ok(Some(owner));
            }
            if candidates.is_empty()
                && attribute
                && (origin.discovered_in_expansion != ExpnId::root()
                    || written_invocation.is_some_and(|invocation| {
                        source
                            .ownerless_attribute_target(invocation)
                            .and_then(|target| source.units.get(target.0 as usize))
                            .is_some_and(|target| target.full_range.contains(target_range))
                            || definitions.graph.definitions.iter().any(|definition| {
                                matches!(
                                    definition.origin,
                                    DefinitionOrigin::Expanded {
                                        invocation: definition_invocation,
                                        ..
                                    } if definition_invocation == invocation
                                )
                            })
                    }))
            {
                return Ok(None);
            }
            return Err(ExpansionError::IncompleteOrigin);
        }
    }
    definitions
        .definition_id(origin.parent_definition)
        .map(Some)
        .ok_or(ExpansionError::IncompleteOrigin)
}

#[cfg(rust_item_dependencies_patched)]
fn written_invocation(
    source: &SourceInventory,
    invocation_range: Option<ByteRange>,
    node_range: Option<ByteRange>,
    target_range: Option<ByteRange>,
    origin: &MacroInvocationOrigin,
    attribute: bool,
) -> Option<crate::source::SourceUnitId> {
    if origin.discovered_in_expansion != ExpnId::root() {
        return None;
    }
    if attribute {
        return resolve_attribute_source(source, invocation_range?, node_range?, target_range?)
            .ok()?
            .invocation;
    }
    let mut matches = source
        .units
        .iter()
        .filter(|unit| {
            unit.kind == crate::source::WrittenUnitKind::MacroInvocation
                && unit.cfg_state == crate::source::CfgState::Active
                && (Some(unit.full_range) == invocation_range
                    || Some(unit.full_range) == node_range)
        })
        .map(|unit| unit.id);
    let invocation = matches.next()?;
    matches.next().is_none().then_some(invocation)
}

#[cfg(rust_item_dependencies_patched)]
fn assign_expansion_keys(raw: &mut [RawExpansion]) -> Result<(), ExpansionError> {
    let mut remaining = (0..raw.len()).collect::<BTreeSet<_>>();
    let mut keys = BTreeMap::<usize, ExpansionKey>::new();
    while !remaining.is_empty() {
        let ready = remaining
            .iter()
            .copied()
            .filter(|&index| {
                raw[index].identity_parent.is_none_or(|parent| {
                    raw.iter()
                        .position(|candidate| candidate.compiler_id == parent)
                        .is_some_and(|parent_index| keys.contains_key(&parent_index))
                })
            })
            .collect::<Vec<_>>();
        if ready.is_empty() {
            return Err(ExpansionError::IncompleteOrigin);
        }
        let mut groups = BTreeMap::<(Option<ExpansionKey>, ExpansionKeyPart), Vec<usize>>::new();
        for index in ready {
            let parent = raw[index].identity_parent.and_then(|parent| {
                raw.iter()
                    .position(|candidate| candidate.compiler_id == parent)
                    .and_then(|parent_index| keys.get(&parent_index).cloned())
            });
            groups
                .entry((parent, raw[index].part.clone()))
                .or_default()
                .push(index);
        }
        for ((parent, _), mut members) in groups {
            members.sort_by_key(|&index| raw[index].compiler_id.expn_hash().local_hash().as_u64());
            let hashes = members
                .iter()
                .map(|&index| raw[index].compiler_id.expn_hash().local_hash().as_u64())
                .collect::<BTreeSet<_>>();
            if hashes.len() != members.len() {
                return Err(ExpansionError::IncompleteOrigin);
            }
            for (ordinal, index) in members.into_iter().enumerate() {
                raw[index].part.same_role_ordinal = ordinal as u32;
                let mut parts = parent.as_ref().map_or_else(Vec::new, |key| key.0.clone());
                parts.push(raw[index].part.clone());
                let key = ExpansionKey(parts);
                keys.insert(index, key.clone());
                raw[index].key = key;
                remaining.remove(&index);
            }
        }
    }
    if keys.values().collect::<BTreeSet<_>>().len() != raw.len() {
        return Err(ExpansionError::IncompleteOrigin);
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn nearest_observed_expansion(
    origins: &rustc_data_structures::unord::UnordMap<ExpnId, MacroInvocationOrigin>,
    mut expansion: ExpnId,
    lookup: &impl Fn(ExpnId) -> Option<ExpansionId>,
) -> Result<ExpansionId, ExpansionError> {
    let mut visited = Vec::new();
    while expansion != ExpnId::root() && !visited.contains(&expansion) {
        visited.push(expansion);
        if let Some(id) = lookup(expansion) {
            return Ok(id);
        }
        expansion = origins.get(&expansion).map_or_else(
            || expansion.expn_data().call_site.ctxt().outer_expn(),
            |origin| origin.discovered_in_expansion,
        );
    }
    Err(ExpansionError::IncompleteOrigin)
}

#[cfg(rust_item_dependencies_patched)]
fn definition_expansion(
    tcx: TyCtxt<'_>,
    mut definition: rustc_hir::def_id::LocalDefId,
) -> Result<ExpnId, ExpansionError> {
    let mut visited = Vec::new();
    loop {
        if visited.contains(&definition) {
            return Err(ExpansionError::IncompleteOrigin);
        }
        visited.push(definition);
        let expansion = tcx.expn_that_defined(definition.to_def_id());
        if expansion != ExpnId::root() {
            return Ok(expansion);
        }
        definition = tcx
            .opt_local_parent(definition)
            .ok_or(ExpansionError::IncompleteOrigin)?;
    }
}

#[cfg(rust_item_dependencies_patched)]
fn expansion_site(expansion: &RawExpansion) -> Vec<ObservationSite> {
    expansion
        .part
        .invocation_range
        .or(expansion.part.node_range)
        .map_or_else(
            || vec![ObservationSite::CompilerGenerated],
            |range| vec![ObservationSite::Source(range)],
        )
}

#[cfg(rust_item_dependencies_patched)]
fn structural_edge(from: GraphNode, to: GraphNode, kind: DependencyKind) -> DependencyEdge {
    DependencyEdge {
        from,
        to,
        kind,
        sites: Vec::new(),
        evidence: EvidenceOrigin::PatchedObserver,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn edge(
    from: GraphNode,
    to: GraphNode,
    kind: DependencyKind,
    sites: Vec<ObservationSite>,
) -> DependencyEdge {
    DependencyEdge {
        from,
        to,
        kind,
        sites,
        evidence: EvidenceOrigin::PatchedObserver,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn definition_node(target: DefinitionTarget) -> GraphNode {
    match target {
        DefinitionTarget::Local(id) => GraphNode::Definition(id),
        DefinitionTarget::External(id) => GraphNode::ExternalDefinition(id),
    }
}

#[cfg(rust_item_dependencies_patched)]
fn map_relation(
    relation: Option<ExpnId>,
    lookup: &impl Fn(ExpnId) -> Option<ExpansionId>,
) -> Result<Option<ExpansionId>, ExpansionError> {
    relation
        .map(|relation| lookup(relation).ok_or(ExpansionError::IncompleteOrigin))
        .transpose()
}

#[cfg(all(test, rust_item_dependencies_patched))]
#[path = "expansions/tests.rs"]
mod tests;
