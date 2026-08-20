//! Collection of local definitions and definition-level dependencies.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir as hir;
use rustc_hir::def::{DefKind, Namespace, Res};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId, LocalDefId};
use rustc_hir::definitions::DefPathData;
use rustc_hir::intravisit::{self, FnKind, Visitor, VisitorExt};
use rustc_interface::interface::Compiler;
use rustc_middle::hir::nested_filter;
#[cfg(rust_item_dependencies_patched)]
use rustc_middle::metadata::Reexport;
use rustc_middle::ty::{self, GenericArgKind, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::{ExpnId, Span};
#[cfg(rust_item_dependencies_patched)]
use rustc_span::{ExpnKind, MacroKind, sym};

use crate::graph::{
    Definition, DefinitionEdge, DefinitionGraph, DefinitionId, DefinitionKey, DefinitionKeyPart,
    DefinitionKind, DefinitionOrigin, DefinitionOriginKey, DefinitionTarget, DependencyKind,
    ExternalDefinition, ExternalDefinitionId, ExternalDefinitionKey, GeneratedRole, GraphError,
    InjectedRole,
};
use crate::rewrite::{SourceRewrite, SourceRewriteError};
use crate::source::{
    ByteRange, CfgState, SourceError, SourceInventory, WrittenUnitKind, original_span_range,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DefinitionError {
    IncompleteDefinition,
    IncompleteDependency,
    IncompleteHirDependency,
    IncompleteTypeckDependency,
    IncompleteImportDependency,
    InvalidSource,
    InvalidGraph,
}

impl DefinitionError {
    fn at_hir(self) -> Self {
        if self == Self::IncompleteDependency {
            Self::IncompleteHirDependency
        } else {
            self
        }
    }

    fn at_typeck(self) -> Self {
        if self == Self::IncompleteDependency {
            Self::IncompleteTypeckDependency
        } else {
            self
        }
    }

    fn at_import(self) -> Self {
        if self == Self::IncompleteDependency {
            Self::IncompleteImportDependency
        } else {
            self
        }
    }
}

impl From<SourceError> for DefinitionError {
    fn from(_: SourceError) -> Self {
        Self::InvalidSource
    }
}

impl From<GraphError> for DefinitionError {
    fn from(_: GraphError) -> Self {
        Self::InvalidGraph
    }
}

struct RawDefinition {
    compiler_id: LocalDefId,
    parent: Option<LocalDefId>,
    kind: DefinitionKind,
    origin: DefinitionOrigin,
    name: Option<String>,
    structural_ordinal: u32,
}

struct RawEdge {
    from: LocalDefId,
    to: DefId,
    kind: DependencyKind,
    site: Option<ByteRange>,
}

pub(crate) struct CollectedDefinitions {
    pub graph: DefinitionGraph,
    compiler_ids: BTreeMap<u32, DefinitionId>,
    identity_keys: Vec<DefinitionKey>,
    hir_definitions: BTreeSet<u32>,
}

impl CollectedDefinitions {
    pub(crate) fn definition_id(&self, definition: LocalDefId) -> Option<DefinitionId> {
        self.compiler_ids.get(&raw_local_id(definition)).copied()
    }

    pub(crate) fn definition_key(&self, definition: LocalDefId) -> Option<&DefinitionKey> {
        let id = self.definition_id(definition)?;
        self.identity_key(id)
    }

    pub(crate) fn identity_key(&self, definition: DefinitionId) -> Option<&DefinitionKey> {
        self.identity_keys.get(definition.0 as usize)
    }

    pub(crate) fn has_hir_definition(&self, definition: LocalDefId) -> bool {
        self.hir_definitions.contains(&raw_local_id(definition))
    }

    /// Switches compiler-term identity to the coordinates of the original
    /// source without changing the definition graph used by source-retention
    /// collection. The graph itself is normalized only after all collectors
    /// have finished using its reduced-source origins.
    pub(crate) fn normalize_identity_keys(
        &mut self,
        coordinates: &SourceRewrite,
    ) -> Result<(), SourceRewriteError> {
        for key in &mut self.identity_keys {
            normalize_definition_key(key, coordinates)?;
        }
        Ok(())
    }

    pub(crate) fn target(
        &mut self,
        tcx: TyCtxt<'_>,
        definition: DefId,
    ) -> Result<DefinitionTarget, DefinitionError> {
        if let Some(local) = definition.as_local() {
            return self
                .definition_id(local)
                .map(DefinitionTarget::Local)
                .ok_or(DefinitionError::IncompleteDefinition);
        }

        let key = external_key(tcx, definition);
        if let Some(existing) = self
            .graph
            .external_definitions
            .iter()
            .find(|external| external.key == key)
        {
            return Ok(DefinitionTarget::External(existing.id));
        }
        let id = ExternalDefinitionId(
            self.graph
                .external_definitions
                .len()
                .try_into()
                .map_err(|_| DefinitionError::IncompleteDependency)?,
        );
        let path = external_path(tcx, &key)?;
        self.graph
            .external_definitions
            .push(ExternalDefinition { id, key, path });
        Ok(DefinitionTarget::External(id))
    }

    pub(crate) fn target_key(
        &mut self,
        tcx: TyCtxt<'_>,
        definition: DefId,
    ) -> Result<crate::dependency_graph::DefinitionReferenceKey, DefinitionError> {
        Ok(match self.target(tcx, definition)? {
            DefinitionTarget::Local(id) => crate::dependency_graph::DefinitionReferenceKey::Local(
                self.identity_keys[id.0 as usize].clone(),
            ),
            DefinitionTarget::External(id) => {
                crate::dependency_graph::DefinitionReferenceKey::External(
                    self.graph.external_definitions[id.0 as usize].key.clone(),
                )
            }
        })
    }
}

pub(crate) fn collect_definition_graph(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
) -> Result<DefinitionGraph, DefinitionError> {
    collect_definitions(compiler, tcx, source).map(|definitions| definitions.graph)
}

pub(crate) fn collect_definitions(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
) -> Result<CollectedDefinitions, DefinitionError> {
    let hir_definitions = collect_hir_definitions(tcx);
    let mut raw_definitions = tcx
        .iter_local_def_id()
        .map(|definition| {
            let kind = definition_kind(tcx, definition, &hir_definitions)?;
            let parent = tcx.opt_local_parent(definition);
            let origin = definition_origin(
                compiler,
                tcx,
                source,
                definition,
                kind,
                parent,
                &hir_definitions,
            )?;
            let def_key = tcx.def_key(definition);
            let name = match def_key.disambiguated_data.data {
                DefPathData::AnonAssocTy(method) => Some(method.to_string()),
                _ => def_key.get_opt_name().map(|name| name.to_string()),
            };
            Ok(RawDefinition {
                compiler_id: definition,
                parent,
                kind,
                origin,
                name,
                structural_ordinal: def_key.disambiguated_data.disambiguator,
            })
        })
        .collect::<Result<Vec<_>, DefinitionError>>()?;

    assign_structural_ordinals(&mut raw_definitions)?;
    let source_owners = source_definition_owners(source, &raw_definitions);
    let (definitions, local_ids) = canonicalize_definitions(raw_definitions)?;

    let mut raw_edges = collect_hir_edges(compiler, tcx, source, &hir_definitions)
        .map_err(DefinitionError::at_hir)?;
    collect_typeck_edges(compiler, tcx, source, &mut raw_edges)
        .map_err(DefinitionError::at_typeck)?;
    collect_import_edges(compiler, tcx, source, &source_owners, &mut raw_edges)
        .map_err(DefinitionError::at_import)?;
    for compiler_id in tcx.iter_local_def_id() {
        let definition_id = *local_ids
            .get(&raw_local_id(compiler_id))
            .ok_or(DefinitionError::IncompleteDefinition)?;
        if let Some(parent) = tcx.opt_local_parent(compiler_id) {
            raw_edges.push(RawEdge {
                from: compiler_id,
                to: parent.to_def_id(),
                kind: DependencyKind::Parent,
                site: definition_site(&definitions[definition_id.0 as usize]),
            });
        }
    }

    let external_keys = raw_edges
        .iter()
        .filter(|edge| !edge.to.is_local())
        .map(|edge| external_key(tcx, edge.to))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let external_ids = external_keys
        .iter()
        .enumerate()
        .map(|(index, key)| (key.clone(), ExternalDefinitionId(index as u32)))
        .collect::<BTreeMap<_, _>>();
    let external_definitions = external_keys
        .into_iter()
        .enumerate()
        .map(|(index, key)| {
            Ok(ExternalDefinition {
                id: ExternalDefinitionId(index as u32),
                path: external_path(tcx, &key)?,
                key,
            })
        })
        .collect::<Result<Vec<_>, DefinitionError>>()?;

    let edges = raw_edges
        .into_iter()
        .map(|edge| {
            let from = *local_ids
                .get(&raw_local_id(edge.from))
                .ok_or(DefinitionError::IncompleteDependency)?;
            let to = if let Some(local) = edge.to.as_local() {
                DefinitionTarget::Local(
                    *local_ids
                        .get(&raw_local_id(local))
                        .ok_or(DefinitionError::IncompleteDependency)?,
                )
            } else {
                let key = external_key(tcx, edge.to);
                DefinitionTarget::External(
                    *external_ids
                        .get(&key)
                        .ok_or(DefinitionError::IncompleteDependency)?,
                )
            };
            Ok(DefinitionEdge {
                from,
                to,
                kind: edge.kind,
                sites: edge.site.into_iter().collect(),
            })
        })
        .collect::<Result<Vec<_>, DefinitionError>>()?;

    let graph = DefinitionGraph::new(definitions, external_definitions, edges)?;
    let identity_keys = graph
        .definitions
        .iter()
        .map(|definition| definition.key.clone())
        .collect();
    Ok(CollectedDefinitions {
        graph,
        compiler_ids: local_ids,
        identity_keys,
        hir_definitions,
    })
}

pub(crate) fn normalize_definition_key(
    key: &mut DefinitionKey,
    coordinates: &SourceRewrite,
) -> Result<(), SourceRewriteError> {
    for part in &mut key.0 {
        match &mut part.origin {
            DefinitionOriginKey::Written { anchor, .. } => {
                *anchor = if part.kind == DefinitionKind::Crate {
                    coordinates.original_crate_range(*anchor)?
                } else {
                    coordinates.original_range(*anchor)?
                };
            }
            DefinitionOriginKey::Expanded {
                invocation_range, ..
            } => {
                *invocation_range = coordinates.original_range(*invocation_range)?;
            }
            DefinitionOriginKey::CompilerGenerated { .. }
            | DefinitionOriginKey::Injected { .. } => {}
        }
    }
    Ok(())
}

fn source_definition_owners(
    source: &SourceInventory,
    definitions: &[RawDefinition],
) -> BTreeMap<crate::source::SourceUnitId, LocalDefId> {
    let mut candidates = BTreeMap::<crate::source::SourceUnitId, Vec<&RawDefinition>>::new();
    for definition in definitions {
        if let DefinitionOrigin::Written { unit, .. } = &definition.origin {
            candidates.entry(*unit).or_default().push(definition);
        }
    }
    let mut owners = BTreeMap::new();
    for unit in &source.units {
        let Some(unit_candidates) = candidates.get(&unit.id) else {
            continue;
        };
        let compiler_ids = unit_candidates
            .iter()
            .map(|definition| raw_local_id(definition.compiler_id))
            .collect::<BTreeSet<_>>();
        let roots = unit_candidates
            .iter()
            .filter(|definition| {
                definition
                    .parent
                    .is_none_or(|parent| !compiler_ids.contains(&raw_local_id(parent)))
            })
            .copied()
            .collect::<Vec<_>>();
        if roots.len() == 1 {
            owners.insert(unit.id, roots[0].compiler_id);
        }
    }
    owners
}

fn raw_local_id(definition: LocalDefId) -> u32 {
    definition.local_def_index.as_u32()
}

fn collect_hir_definitions(tcx: TyCtxt<'_>) -> BTreeSet<u32> {
    let mut collector = HirDefinitionCollector {
        tcx,
        definitions: BTreeSet::from([raw_local_id(CRATE_DEF_ID)]),
    };
    tcx.hir_walk_toplevel_module(&mut collector);
    collector.definitions
}

struct HirDefinitionCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    definitions: BTreeSet<u32>,
}

impl<'tcx> Visitor<'tcx> for HirDefinitionCollector<'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        self.definitions.insert(raw_local_id(item.owner_id.def_id));
        match item.kind {
            hir::ItemKind::Struct(_, _, data) | hir::ItemKind::Union(_, _, data) => {
                if let Some((_, _, constructor)) = data.ctor() {
                    self.definitions.insert(raw_local_id(constructor));
                }
            }
            _ => {}
        }
        intravisit::walk_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'tcx hir::TraitItem<'tcx>) {
        self.definitions.insert(raw_local_id(item.owner_id.def_id));
        intravisit::walk_trait_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        self.definitions.insert(raw_local_id(item.owner_id.def_id));
        intravisit::walk_impl_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) {
        self.definitions.insert(raw_local_id(item.owner_id.def_id));
        intravisit::walk_foreign_item(self, item);
    }

    fn visit_variant(&mut self, variant: &'tcx hir::Variant<'tcx>) {
        self.definitions.insert(raw_local_id(variant.def_id));
        if let Some((_, _, constructor)) = variant.data.ctor() {
            self.definitions.insert(raw_local_id(constructor));
        }
        intravisit::walk_variant(self, variant);
    }

    fn visit_field_def(&mut self, field: &'tcx hir::FieldDef<'tcx>) {
        self.definitions.insert(raw_local_id(field.def_id));
        intravisit::walk_field_def(self, field);
    }

    fn visit_generic_param(&mut self, parameter: &'tcx hir::GenericParam<'tcx>) {
        self.definitions.insert(raw_local_id(parameter.def_id));
        intravisit::walk_generic_param(self, parameter);
    }

    fn visit_anon_const(&mut self, constant: &'tcx hir::AnonConst) {
        self.definitions.insert(raw_local_id(constant.def_id));
        intravisit::walk_anon_const(self, constant);
    }

    fn visit_inline_const(&mut self, constant: &'tcx hir::ConstBlock) {
        self.definitions.insert(raw_local_id(constant.def_id));
        intravisit::walk_inline_const(self, constant);
    }

    fn visit_opaque_ty(&mut self, opaque: &'tcx hir::OpaqueTy<'tcx>) {
        self.definitions.insert(raw_local_id(opaque.def_id));
        intravisit::walk_opaque_ty(self, opaque);
    }

    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(closure) = expression.kind {
            self.definitions.insert(raw_local_id(closure.def_id));
        }
        intravisit::walk_expr(self, expression);
    }
}

fn definition_kind(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    hir_definitions: &BTreeSet<u32>,
) -> Result<DefinitionKind, DefinitionError> {
    Ok(match tcx.def_kind(definition) {
        DefKind::Mod if definition == CRATE_DEF_ID => DefinitionKind::Crate,
        DefKind::Mod => DefinitionKind::Module,
        DefKind::Struct => DefinitionKind::Struct,
        DefKind::Union => DefinitionKind::Union,
        DefKind::Enum => DefinitionKind::Enum,
        DefKind::Variant => DefinitionKind::Variant,
        DefKind::Trait => DefinitionKind::Trait,
        DefKind::TyAlias => DefinitionKind::TypeAlias,
        DefKind::ForeignTy => DefinitionKind::ForeignType,
        DefKind::TraitAlias => DefinitionKind::TraitAlias,
        DefKind::AssocTy => DefinitionKind::AssociatedType,
        DefKind::TyParam => DefinitionKind::TypeParameter,
        DefKind::Fn => DefinitionKind::Function,
        DefKind::Const { .. } => DefinitionKind::Const,
        DefKind::ConstParam => DefinitionKind::ConstParameter,
        DefKind::Static { .. } => DefinitionKind::Static,
        DefKind::Ctor(..) => DefinitionKind::Constructor,
        DefKind::AssocFn => DefinitionKind::AssociatedFunction,
        DefKind::AssocConst { .. } => DefinitionKind::AssociatedConst,
        DefKind::Macro(..) => DefinitionKind::Macro,
        DefKind::ExternCrate => DefinitionKind::ExternCrate,
        DefKind::Use => DefinitionKind::Use,
        DefKind::ForeignMod => DefinitionKind::ForeignModule,
        DefKind::AnonConst if !hir_definitions.contains(&raw_local_id(definition)) => {
            DefinitionKind::AnonymousConst
        }
        DefKind::AnonConst => match tcx.hir_node_by_def_id(definition) {
            hir::Node::ConstBlock(_) => DefinitionKind::InlineConst,
            hir::Node::AnonConst(_) | hir::Node::ConstArg(_) => DefinitionKind::AnonymousConst,
            _ => return Err(DefinitionError::IncompleteDefinition),
        },
        DefKind::OpaqueTy => DefinitionKind::OpaqueType,
        DefKind::Field => DefinitionKind::Field,
        DefKind::LifetimeParam => DefinitionKind::LifetimeParameter,
        DefKind::GlobalAsm => DefinitionKind::GlobalAsm,
        DefKind::Impl { .. } => DefinitionKind::Impl,
        DefKind::Closure => {
            if !hir_definitions.contains(&raw_local_id(definition)) {
                return Err(DefinitionError::IncompleteDefinition);
            }
            match tcx.hir_node_by_def_id(definition) {
                hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Closure(closure),
                    ..
                }) => match closure.kind {
                    hir::ClosureKind::Closure => DefinitionKind::Closure,
                    hir::ClosureKind::Coroutine(_) => DefinitionKind::Coroutine,
                    hir::ClosureKind::CoroutineClosure(_) => DefinitionKind::CoroutineClosure,
                },
                _ => return Err(DefinitionError::IncompleteDefinition),
            }
        }
        DefKind::SyntheticCoroutineBody => DefinitionKind::SyntheticCoroutineBody,
    })
}

fn definition_origin(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definition: LocalDefId,
    kind: DefinitionKind,
    parent: Option<LocalDefId>,
    hir_definitions: &BTreeSet<u32>,
) -> Result<DefinitionOrigin, DefinitionError> {
    if definition == CRATE_DEF_ID {
        let root = source
            .units
            .iter()
            .find(|unit| unit.kind == WrittenUnitKind::CrateRoot)
            .ok_or(DefinitionError::InvalidSource)?;
        return Ok(written_origin(root, root.full_range));
    }
    if parent == Some(definition) {
        return Err(DefinitionError::IncompleteDefinition);
    }

    let expansion = tcx.expn_that_defined(definition.to_def_id());
    if expansion != ExpnId::root() {
        #[cfg(rust_item_dependencies_patched)]
        if let Some(origin) = written_derive_target_origin(
            compiler,
            tcx,
            source,
            definition,
            kind,
            expansion,
            hir_definitions,
        )? {
            return Ok(origin);
        }
        return definition_origin_from_expansion(
            compiler,
            tcx,
            source,
            definition,
            kind,
            expansion,
            hir_definitions,
        );
    }

    if is_injected(tcx, definition, kind, hir_definitions) {
        return Ok(DefinitionOrigin::Injected {
            role: match kind {
                DefinitionKind::ExternCrate => InjectedRole::ExternCrate,
                DefinitionKind::Use => InjectedRole::PreludeImport,
                _ => return Err(DefinitionError::IncompleteDefinition),
            },
            ordinal: 0,
        });
    }

    if is_compiler_generated(tcx, definition, kind, hir_definitions)? {
        let role = generated_role(tcx, definition, kind, hir_definitions)?;
        if let Some(parent) = parent {
            let parent_kind = definition_kind(tcx, parent, hir_definitions)?;
            let parent_origin = definition_origin(
                compiler,
                tcx,
                source,
                parent,
                parent_kind,
                tcx.opt_local_parent(parent),
                hir_definitions,
            )?;
            if let DefinitionOrigin::Expanded {
                invocation,
                invocation_range,
                ..
            } = parent_origin
            {
                return Ok(DefinitionOrigin::Expanded {
                    invocation,
                    invocation_range,
                    generated_role: Some(role),
                    ordinal: 0,
                });
            }
        }
        return Ok(DefinitionOrigin::CompilerGenerated { role, ordinal: 0 });
    }

    if !hir_definitions.contains(&raw_local_id(definition)) {
        return Err(DefinitionError::IncompleteDefinition);
    }
    let span = tcx.hir_span(tcx.local_def_id_to_hir_id(definition));
    let range = original_span_range(compiler, &source.offsets, span.source_callsite())?;
    let unit = source_unit_for_definition(source, range, kind)
        .ok_or(DefinitionError::IncompleteDefinition)?;
    Ok(written_origin(unit, range))
}

#[cfg(rust_item_dependencies_patched)]
fn written_derive_target_origin(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definition: LocalDefId,
    kind: DefinitionKind,
    expansion: ExpnId,
    hir_definitions: &BTreeSet<u32>,
) -> Result<Option<DefinitionOrigin>, DefinitionError> {
    let Some(origin) = tcx.resolutions(()).macro_invocation_origins.get(&expansion) else {
        return Ok(None);
    };
    if origin.discovered_in_expansion != ExpnId::root()
        || !matches!(
            expansion.expn_data().kind,
            ExpnKind::Macro(MacroKind::Attr, name) if name == sym::derive
        )
        || !hir_definitions.contains(&raw_local_id(definition))
    {
        return Ok(None);
    }
    let Some(target_span) = origin.target_span else {
        return Err(DefinitionError::IncompleteDefinition);
    };
    let target_range = original_span_range(compiler, &source.offsets, target_span)?;
    let span = tcx.hir_span(tcx.local_def_id_to_hir_id(definition));
    let range = original_span_range(compiler, &source.offsets, span.source_callsite())?;
    if !target_range.contains(range) {
        return Ok(None);
    }
    let unit = source_unit_for_definition(source, range, kind)
        .filter(|unit| unit.kind != WrittenUnitKind::CrateRoot)
        .ok_or(DefinitionError::IncompleteDefinition)?;
    Ok(Some(written_origin(unit, range)))
}

#[cfg(not(rust_item_dependencies_patched))]
fn definition_origin_from_expansion(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _definition: LocalDefId,
    _kind: DefinitionKind,
    _expansion: ExpnId,
    _hir_definitions: &BTreeSet<u32>,
) -> Result<DefinitionOrigin, DefinitionError> {
    Err(DefinitionError::IncompleteDefinition)
}

#[cfg(rust_item_dependencies_patched)]
fn definition_origin_from_expansion(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    definition: LocalDefId,
    kind: DefinitionKind,
    expansion: ExpnId,
    hir_definitions: &BTreeSet<u32>,
) -> Result<DefinitionOrigin, DefinitionError> {
    if recorded_macro_expansion(tcx, expansion).is_some() {
        let role = generated_role_for_expanded_definition(
            tcx,
            definition,
            kind,
            expansion,
            hir_definitions,
        )?;
        return expanded_origin(compiler, tcx, source, expansion, role);
    }
    Ok(DefinitionOrigin::CompilerGenerated {
        role: generated_role(tcx, definition, kind, hir_definitions)?,
        ordinal: 0,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn generated_role_for_expanded_definition(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    kind: DefinitionKind,
    expansion: ExpnId,
    hir_definitions: &BTreeSet<u32>,
) -> Result<Option<GeneratedRole>, DefinitionError> {
    let direct_macro_product = tcx
        .resolutions(())
        .macro_invocation_origins
        .contains_key(&expansion);
    let role = match kind {
        DefinitionKind::AssociatedType
            if matches!(
                tcx.def_key(definition).disambiguated_data.data,
                DefPathData::AnonAssocTy(_)
            ) =>
        {
            Some(GeneratedRole::AnonymousAssociatedType)
        }
        DefinitionKind::AnonymousConst if !hir_definitions.contains(&raw_local_id(definition)) => {
            Some(GeneratedRole::AnonymousConst)
        }
        DefinitionKind::Coroutine => {
            let hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Closure(closure),
                ..
            }) = tcx.hir_node_by_def_id(definition)
            else {
                return Err(DefinitionError::IncompleteDefinition);
            };
            match closure.kind {
                hir::ClosureKind::Coroutine(hir::CoroutineKind::Desugared(
                    _,
                    hir::CoroutineSource::Fn,
                )) => Some(GeneratedRole::Coroutine),
                hir::ClosureKind::Coroutine(_) => None,
                _ => return Err(DefinitionError::IncompleteDefinition),
            }
        }
        DefinitionKind::CoroutineClosure => None,
        DefinitionKind::SyntheticCoroutineBody => Some(GeneratedRole::CoroutineBody),
        DefinitionKind::LifetimeParameter
            if matches!(
                tcx.def_key(definition).disambiguated_data.data,
                DefPathData::OpaqueLifetime(_)
            ) =>
        {
            Some(GeneratedRole::OpaqueLifetime)
        }
        DefinitionKind::LifetimeParameter
            if hir_definitions.contains(&raw_local_id(definition))
                && matches!(
                    tcx.hir_node_by_def_id(definition),
                    hir::Node::GenericParam(parameter) if parameter.is_elided_lifetime()
                ) =>
        {
            Some(GeneratedRole::ElidedLifetime)
        }
        DefinitionKind::Static
            if matches!(
                tcx.def_key(definition).disambiguated_data.data,
                DefPathData::NestedStatic
            ) =>
        {
            Some(GeneratedRole::NestedStatic)
        }
        DefinitionKind::OpaqueType => match tcx.local_opaque_ty_origin(definition) {
            hir::OpaqueTyOrigin::AsyncFn { .. } => Some(GeneratedRole::OpaqueType),
            hir::OpaqueTyOrigin::FnReturn { .. } | hir::OpaqueTyOrigin::TyAlias { .. } => None,
        },
        _ if direct_macro_product => None,
        _ => Some(generated_role(tcx, definition, kind, hir_definitions)?),
    };
    Ok(role)
}

fn written_origin(unit: &crate::source::WrittenUnit, anchor: ByteRange) -> DefinitionOrigin {
    DefinitionOrigin::Written {
        unit: unit.id,
        unit_range: unit.full_range,
        anchor,
        unit_kind: unit.kind,
        unit_ordinal: unit.same_role_ordinal,
    }
}

#[cfg(rust_item_dependencies_patched)]
fn expanded_origin(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    expansion: ExpnId,
    generated_role: Option<GeneratedRole>,
) -> Result<DefinitionOrigin, DefinitionError> {
    let origins = &tcx.resolutions(()).macro_invocation_origins;
    let mut current =
        recorded_macro_expansion(tcx, expansion).ok_or(DefinitionError::IncompleteDefinition)?;
    loop {
        let origin = origins
            .get(&current)
            .ok_or(DefinitionError::IncompleteDefinition)?;
        if origin.discovered_in_expansion == ExpnId::root() {
            break;
        }
        current = recorded_macro_expansion(tcx, origin.discovered_in_expansion)
            .ok_or(DefinitionError::IncompleteDefinition)?;
    }
    let origin = origins
        .get(&current)
        .ok_or(DefinitionError::IncompleteDefinition)?;
    let invocation = written_macro_invocation(compiler, source, current, origin)
        .map_err(|_| DefinitionError::IncompleteDefinition)?;
    Ok(DefinitionOrigin::Expanded {
        invocation: invocation.id,
        invocation_range: invocation.full_range,
        generated_role,
        ordinal: 0,
    })
}

#[cfg(rust_item_dependencies_patched)]
fn written_macro_invocation<'a>(
    compiler: &Compiler,
    source: &'a SourceInventory,
    expansion: ExpnId,
    origin: &rustc_middle::ty::MacroInvocationOrigin,
) -> Result<&'a crate::source::WrittenUnit, DefinitionError> {
    let node_range = original_span_range(compiler, &source.offsets, origin.invocation_node_span)?;
    let call_range =
        original_span_range(compiler, &source.offsets, expansion.expn_data().call_site)?;
    let mut matches = source.units.iter().filter(|unit| {
        unit.kind == WrittenUnitKind::MacroInvocation
            && unit.cfg_state == CfgState::Active
            && (unit.full_range == node_range || unit.full_range == call_range)
    });
    let invocation = matches
        .next()
        .ok_or(DefinitionError::IncompleteDependency)?;
    if matches.next().is_some() {
        return Err(DefinitionError::IncompleteDependency);
    }
    Ok(invocation)
}

#[cfg(rust_item_dependencies_patched)]
fn recorded_macro_expansion(tcx: TyCtxt<'_>, mut expansion: ExpnId) -> Option<ExpnId> {
    let origins = &tcx.resolutions(()).macro_invocation_origins;
    let mut visited = Vec::new();
    while expansion != ExpnId::root() && !visited.contains(&expansion) {
        visited.push(expansion);
        if origins.contains_key(&expansion) {
            return Some(expansion);
        }
        let parent = expansion.expn_data().call_site.ctxt().outer_expn();
        if parent == expansion {
            return None;
        }
        expansion = parent;
    }
    None
}

fn is_injected(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    kind: DefinitionKind,
    hir_definitions: &BTreeSet<u32>,
) -> bool {
    matches!(kind, DefinitionKind::ExternCrate | DefinitionKind::Use)
        && (!hir_definitions.contains(&raw_local_id(definition))
            || tcx
                .hir_span_if_local(definition.to_def_id())
                .is_none_or(|span| span.is_dummy()))
}

fn is_compiler_generated(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    kind: DefinitionKind,
    hir_definitions: &BTreeSet<u32>,
) -> Result<bool, DefinitionError> {
    let path_data = tcx.def_key(definition).disambiguated_data.data;
    Ok(match kind {
        DefinitionKind::AssociatedType => matches!(path_data, DefPathData::AnonAssocTy(_)),
        DefinitionKind::OpaqueType => {
            matches!(
                tcx.local_opaque_ty_origin(definition),
                hir::OpaqueTyOrigin::AsyncFn { .. }
            )
        }
        DefinitionKind::Coroutine => {
            let hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::Closure(closure),
                ..
            }) = tcx.hir_node_by_def_id(definition)
            else {
                return Err(DefinitionError::IncompleteDefinition);
            };
            match closure.kind {
                hir::ClosureKind::Coroutine(hir::CoroutineKind::Desugared(
                    _,
                    hir::CoroutineSource::Fn,
                )) => true,
                hir::ClosureKind::Coroutine(_) => false,
                _ => return Err(DefinitionError::IncompleteDefinition),
            }
        }
        DefinitionKind::SyntheticCoroutineBody => true,
        DefinitionKind::Static => matches!(path_data, DefPathData::NestedStatic),
        DefinitionKind::AnonymousConst => !hir_definitions.contains(&raw_local_id(definition)),
        DefinitionKind::LifetimeParameter => {
            matches!(path_data, DefPathData::OpaqueLifetime(_))
                || hir_definitions.contains(&raw_local_id(definition))
                    && matches!(
                        tcx.hir_node_by_def_id(definition),
                        hir::Node::GenericParam(parameter) if parameter.is_elided_lifetime()
                    )
        }
        _ => false,
    })
}

fn generated_role(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    kind: DefinitionKind,
    hir_definitions: &BTreeSet<u32>,
) -> Result<GeneratedRole, DefinitionError> {
    let path_data = tcx.def_key(definition).disambiguated_data.data;
    Ok(match kind {
        DefinitionKind::AssociatedType if matches!(path_data, DefPathData::AnonAssocTy(_)) => {
            GeneratedRole::AnonymousAssociatedType
        }
        DefinitionKind::AnonymousConst => GeneratedRole::AnonymousConst,
        DefinitionKind::Coroutine => GeneratedRole::Coroutine,
        DefinitionKind::SyntheticCoroutineBody => GeneratedRole::CoroutineBody,
        DefinitionKind::CoroutineClosure => GeneratedRole::CoroutineClosure,
        DefinitionKind::LifetimeParameter => {
            if matches!(path_data, DefPathData::OpaqueLifetime(_)) {
                GeneratedRole::OpaqueLifetime
            } else if hir_definitions.contains(&raw_local_id(definition))
                && matches!(
                    tcx.hir_node_by_def_id(definition),
                    hir::Node::GenericParam(parameter) if parameter.is_elided_lifetime()
                )
            {
                GeneratedRole::ElidedLifetime
            } else {
                return Err(DefinitionError::IncompleteDefinition);
            }
        }
        DefinitionKind::Static if matches!(path_data, DefPathData::NestedStatic) => {
            GeneratedRole::NestedStatic
        }
        DefinitionKind::OpaqueType => GeneratedRole::OpaqueType,
        _ => return Err(DefinitionError::IncompleteDefinition),
    })
}

fn source_unit_for_definition(
    source: &SourceInventory,
    range: ByteRange,
    kind: DefinitionKind,
) -> Option<&crate::source::WrittenUnit> {
    source
        .units
        .iter()
        .filter(|unit| {
            unit.cfg_state == CfgState::Active
                && unit.full_range.contains(range)
                && match kind {
                    DefinitionKind::Crate => unit.kind == WrittenUnitKind::CrateRoot,
                    DefinitionKind::Use => {
                        matches!(
                            unit.kind,
                            WrittenUnitKind::UseLeaf | WrittenUnitKind::UseItem
                        )
                    }
                    DefinitionKind::Macro => unit.kind == WrittenUnitKind::MacroDefinition,
                    _ => !matches!(
                        unit.kind,
                        WrittenUnitKind::CrateRoot
                            | WrittenUnitKind::MacroInvocation
                            | WrittenUnitKind::UseLeaf
                    ),
                }
        })
        .min_by_key(|unit| (unit.full_range.len(), unit.kind.rank(), unit.id))
}

fn assign_structural_ordinals(definitions: &mut [RawDefinition]) -> Result<(), DefinitionError> {
    type Group = (
        Option<u32>,
        DefinitionOriginKey,
        DefinitionKind,
        Option<String>,
    );

    let mut groups = BTreeMap::<Group, Vec<(u32, usize)>>::new();
    for (index, definition) in definitions.iter().enumerate() {
        groups
            .entry((
                definition.parent.map(raw_local_id),
                definition.origin.key(),
                definition.kind,
                definition.name.clone(),
            ))
            .or_default()
            .push((definition.structural_ordinal, index));
    }
    for members in groups.values_mut() {
        members.sort_unstable();
        if members.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return Err(DefinitionError::IncompleteDefinition);
        }
        for (rank, &(_, index)) in members.iter().enumerate() {
            let rank = u32::try_from(rank).map_err(|_| DefinitionError::IncompleteDefinition)?;
            let definition = &mut definitions[index];
            definition.structural_ordinal = rank;
            match &mut definition.origin {
                DefinitionOrigin::Expanded { ordinal, .. }
                | DefinitionOrigin::CompilerGenerated { ordinal, .. }
                | DefinitionOrigin::Injected { ordinal, .. } => *ordinal = rank,
                DefinitionOrigin::Written { .. } => {}
            }
        }
    }
    Ok(())
}

fn canonicalize_definitions(
    definitions: Vec<RawDefinition>,
) -> Result<(Vec<Definition>, BTreeMap<u32, DefinitionId>), DefinitionError> {
    let by_compiler_id = definitions
        .iter()
        .enumerate()
        .map(|(index, definition)| (raw_local_id(definition.compiler_id), index))
        .collect::<BTreeMap<_, _>>();
    let root = definitions
        .iter()
        .position(|definition| definition.compiler_id == CRATE_DEF_ID)
        .ok_or(DefinitionError::IncompleteDefinition)?;
    if definitions.iter().enumerate().any(|(index, definition)| {
        index != root
            && definition
                .parent
                .is_none_or(|parent| !by_compiler_id.contains_key(&raw_local_id(parent)))
    }) {
        return Err(DefinitionError::IncompleteDefinition);
    }

    let mut children = BTreeMap::<u32, Vec<usize>>::new();
    for (index, definition) in definitions.iter().enumerate() {
        if let Some(parent) = definition.parent {
            children
                .entry(raw_local_id(parent))
                .or_default()
                .push(index);
        }
    }
    for indices in children.values_mut() {
        indices.sort_by(|&left, &right| {
            definitions[left]
                .origin
                .cmp(&definitions[right].origin)
                .then(definitions[left].kind.cmp(&definitions[right].kind))
                .then(definitions[left].name.cmp(&definitions[right].name))
                .then(
                    definitions[left]
                        .structural_ordinal
                        .cmp(&definitions[right].structural_ordinal),
                )
        });
    }

    fn append(
        index: usize,
        definitions: &[RawDefinition],
        children: &BTreeMap<u32, Vec<usize>>,
        local_ids: &mut BTreeMap<u32, DefinitionId>,
        output: &mut Vec<Definition>,
    ) {
        let raw = &definitions[index];
        let id = DefinitionId(output.len() as u32);
        let parent = raw
            .parent
            .and_then(|parent| local_ids.get(&raw_local_id(parent)).copied());
        let mut parts = parent
            .map(|parent| output[parent.0 as usize].key.0.clone())
            .unwrap_or_default();
        parts.push(DefinitionKeyPart {
            kind: raw.kind,
            origin: raw.origin.key(),
            name: raw.name.clone(),
            same_role_ordinal: raw.structural_ordinal,
        });
        local_ids.insert(raw_local_id(raw.compiler_id), id);
        output.push(Definition {
            id,
            key: DefinitionKey(parts),
            kind: raw.kind,
            parent,
            origin: raw.origin.clone(),
        });
        if let Some(indices) = children.get(&raw_local_id(raw.compiler_id)) {
            for &child in indices {
                append(child, definitions, children, local_ids, output);
            }
        }
    }

    let mut local_ids = BTreeMap::new();
    let mut output = Vec::with_capacity(definitions.len());
    append(root, &definitions, &children, &mut local_ids, &mut output);
    if output.len() != definitions.len() {
        return Err(DefinitionError::IncompleteDefinition);
    }
    Ok((output, local_ids))
}

fn definition_site(definition: &Definition) -> Option<ByteRange> {
    match &definition.origin {
        DefinitionOrigin::Written { anchor, .. } => Some(*anchor),
        DefinitionOrigin::Expanded {
            invocation_range, ..
        } => Some(*invocation_range),
        DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => None,
    }
}

pub(crate) fn external_key(tcx: TyCtxt<'_>, definition: DefId) -> ExternalDefinitionKey {
    ExternalDefinitionKey {
        crate_identity: tcx.stable_crate_id(definition.krate).as_u64(),
        crate_name: tcx.crate_name(definition.krate).to_string(),
        def_path_hash: tcx.def_path_hash(definition).0.to_le_bytes(),
    }
}

pub(crate) fn external_path(
    tcx: TyCtxt<'_>,
    key: &ExternalDefinitionKey,
) -> Result<String, DefinitionError> {
    let hash = rustc_span::def_id::DefPathHash(
        rustc_data_structures::fingerprint::Fingerprint::from_le_bytes(key.def_path_hash),
    );
    let definition = tcx
        .def_path_hash_to_def_id(hash)
        .ok_or(DefinitionError::IncompleteDependency)?;
    if external_key(tcx, definition) != *key {
        return Err(DefinitionError::IncompleteDependency);
    }
    Ok(tcx.def_path_str(definition))
}

fn collect_hir_edges(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    hir_definitions: &BTreeSet<u32>,
) -> Result<Vec<RawEdge>, DefinitionError> {
    let mut collector = HirEdgeCollector {
        compiler,
        tcx,
        source,
        hir_definitions,
        current: Some(CRATE_DEF_ID),
        context: DependencyKind::TypePath,
        edges: Vec::new(),
        error: None,
    };
    tcx.hir_walk_toplevel_module(&mut collector);
    collector.error.map_or(Ok(collector.edges), Err)
}

fn supertrait_definitions(
    tcx: TyCtxt<'_>,
    trait_definition: DefId,
) -> Result<Vec<DefId>, DefinitionError> {
    let mut active = Vec::new();
    let mut complete = Vec::new();
    let mut definitions = Vec::new();

    fn visit(
        tcx: TyCtxt<'_>,
        definition: DefId,
        active: &mut Vec<DefId>,
        complete: &mut Vec<DefId>,
        definitions: &mut Vec<DefId>,
    ) -> Result<(), DefinitionError> {
        if complete.contains(&definition) {
            return Ok(());
        }
        if active.contains(&definition) {
            return Err(DefinitionError::IncompleteDependency);
        }
        active.push(definition);
        definitions.push(definition);
        for clause in tcx
            .explicit_super_clauses_of(definition)
            .iter_identity_copied()
        {
            let (clause, _) = clause.skip_normalization();
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            visit(
                tcx,
                trait_clause.skip_binder().trait_ref.def_id,
                active,
                complete,
                definitions,
            )?;
        }
        active.pop();
        complete.push(definition);
        Ok(())
    }

    visit(
        tcx,
        trait_definition,
        &mut active,
        &mut complete,
        &mut definitions,
    )?;
    Ok(definitions)
}

struct HirEdgeCollector<'a, 'tcx> {
    compiler: &'a Compiler,
    tcx: TyCtxt<'tcx>,
    source: &'a SourceInventory,
    hir_definitions: &'a BTreeSet<u32>,
    current: Option<LocalDefId>,
    context: DependencyKind,
    edges: Vec<RawEdge>,
    error: Option<DefinitionError>,
}

impl HirEdgeCollector<'_, '_> {
    fn with_definition(&mut self, definition: LocalDefId, f: impl FnOnce(&mut Self)) {
        let previous = self.current.replace(definition);
        f(self);
        self.current = previous;
    }

    fn with_context(&mut self, context: DependencyKind, f: impl FnOnce(&mut Self)) {
        let previous = std::mem::replace(&mut self.context, context);
        f(self);
        self.context = previous;
    }

    fn record(&mut self, target: DefId, kind: DependencyKind, span: Span) {
        if self.error.is_some() {
            return;
        }
        let Some(from) = self.current else {
            self.error = Some(DefinitionError::IncompleteDependency);
            return;
        };
        match original_span_range(self.compiler, &self.source.offsets, span.source_callsite()) {
            Ok(site) => self.edges.push(RawEdge {
                from,
                to: target,
                kind,
                site: Some(site),
            }),
            Err(_) => self.error = Some(DefinitionError::InvalidSource),
        }
    }

    fn record_res(&mut self, resolution: Res, span: Span) {
        let namespace = resolution.ns();
        let (target, target_kind) = match resolution {
            Res::Def(kind, target) => (target, Some(kind)),
            Res::SelfTyParam { trait_ } => (trait_, None),
            Res::SelfTyAlias { alias_to, .. } | Res::SelfCtor(alias_to) => (alias_to, None),
            Res::PrimTy(_)
            | Res::Local(_)
            | Res::ToolMod
            | Res::OpenMod(_)
            | Res::NonMacroAttr(_) => {
                return;
            }
            Res::Err => {
                if self
                    .current
                    .is_some_and(|definition| matches!(self.tcx.def_kind(definition), DefKind::Use))
                    && span.is_dummy()
                {
                    return;
                }
                self.error = Some(DefinitionError::IncompleteDependency);
                return;
            }
        };
        let kind = match (target_kind, namespace) {
            (_, Some(namespace))
                if self
                    .current
                    .is_some_and(|definition| self.tcx.def_kind(definition) == DefKind::Use) =>
            {
                match namespace {
                    Namespace::TypeNS => DependencyKind::TypePath,
                    Namespace::ValueNS => DependencyKind::ValuePath,
                    Namespace::MacroNS => DependencyKind::MacroPath,
                }
            }
            (Some(DefKind::Macro(..)), _) => DependencyKind::MacroPath,
            (Some(kind), _) if kind.is_assoc() => DependencyKind::AssociatedItemTarget,
            _ => self.context,
        };
        self.record(target, kind, span);
    }

    fn record_visibility(&mut self, definition: LocalDefId, span: Span) {
        if span.is_empty() {
            return;
        }
        if let ty::Visibility::Restricted(module) = self.tcx.visibility(definition) {
            self.record(module.to_def_id(), DependencyKind::VisibilityPath, span);
        }
    }

    fn body_context(&self) -> DependencyKind {
        match self.current.map(|definition| self.tcx.def_kind(definition)) {
            Some(
                DefKind::Const { .. }
                | DefKind::AssocConst { .. }
                | DefKind::AnonConst
                | DefKind::Static { .. },
            ) => DependencyKind::ConstExpression,
            _ => DependencyKind::ValuePath,
        }
    }

    fn signature_context(&self) -> bool {
        matches!(
            self.context,
            DependencyKind::SignatureType
                | DependencyKind::ReturnType
                | DependencyKind::AssociatedTypeBound
                | DependencyKind::Predicate
        )
    }
}

impl<'tcx> Visitor<'tcx> for HirEdgeCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let context = match item.kind {
            hir::ItemKind::Impl(_) => DependencyKind::ImplSelfType,
            hir::ItemKind::Trait { .. } | hir::ItemKind::TraitAlias(..) => {
                DependencyKind::SuperTrait
            }
            _ => DependencyKind::TypePath,
        };
        self.with_definition(item.owner_id.def_id, |this| {
            this.record_visibility(item.owner_id.def_id, item.vis_span);
            this.with_context(context, |this| intravisit::walk_item(this, item));
        });
    }

    fn visit_trait_item(&mut self, item: &'tcx hir::TraitItem<'tcx>) {
        self.with_definition(item.owner_id.def_id, |this| {
            let context = match item.kind {
                hir::TraitItemKind::Type(..) => DependencyKind::AssociatedTypeBound,
                _ => DependencyKind::SignatureType,
            };
            this.with_context(context, |this| intravisit::walk_trait_item(this, item));
        });
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        self.with_definition(item.owner_id.def_id, |this| {
            if let Some(span) = item.vis_span() {
                this.record_visibility(item.owner_id.def_id, span);
            }
            this.with_context(DependencyKind::SignatureType, |this| {
                intravisit::walk_impl_item(this, item)
            });
        });
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) {
        self.with_definition(item.owner_id.def_id, |this| {
            this.record_visibility(item.owner_id.def_id, item.vis_span);
            this.with_context(DependencyKind::SignatureType, |this| {
                intravisit::walk_foreign_item(this, item)
            });
        });
    }

    fn visit_variant(&mut self, variant: &'tcx hir::Variant<'tcx>) {
        self.with_definition(variant.def_id, |this| {
            if let Some(discriminant) = variant.disr_expr {
                this.record(
                    discriminant.def_id.to_def_id(),
                    DependencyKind::Discriminant,
                    discriminant.span,
                );
            }
            intravisit::walk_variant(this, variant)
        });
    }

    fn visit_field_def(&mut self, field: &'tcx hir::FieldDef<'tcx>) {
        self.with_definition(field.def_id, |this| {
            this.record_visibility(field.def_id, field.vis_span);
            this.with_context(DependencyKind::FieldType, |this| {
                intravisit::walk_field_def(this, field)
            });
        });
    }

    fn visit_generic_param(&mut self, parameter: &'tcx hir::GenericParam<'tcx>) {
        self.with_definition(parameter.def_id, |this| match parameter.kind {
            hir::GenericParamKind::Lifetime { .. } => {}
            hir::GenericParamKind::Type { default, .. } => {
                if let Some(default) = default {
                    this.with_context(DependencyKind::GenericDefault, |this| {
                        this.visit_ty_unambig(default)
                    });
                }
            }
            hir::GenericParamKind::Const { ty, default } => {
                this.with_context(DependencyKind::SignatureType, |this| {
                    this.visit_ty_unambig(ty)
                });
                if let Some(default) = default {
                    if let hir::ConstArgKind::Anon(constant) = default.kind {
                        this.record(
                            constant.def_id.to_def_id(),
                            DependencyKind::GenericDefault,
                            default.span,
                        );
                    }
                    this.with_context(DependencyKind::GenericDefault, |this| {
                        this.visit_const_arg_unambig(default)
                    });
                }
            }
        });
    }

    fn visit_anon_const(&mut self, constant: &'tcx hir::AnonConst) {
        self.with_definition(constant.def_id, |this| {
            this.with_context(DependencyKind::ConstExpression, |this| {
                intravisit::walk_anon_const(this, constant)
            });
        });
    }

    fn visit_inline_const(&mut self, constant: &'tcx hir::ConstBlock) {
        self.with_definition(constant.def_id, |this| {
            this.with_context(DependencyKind::ConstExpression, |this| {
                intravisit::walk_inline_const(this, constant)
            });
        });
    }

    fn visit_opaque_ty(&mut self, opaque: &'tcx hir::OpaqueTy<'tcx>) {
        self.with_definition(opaque.def_id, |this| {
            this.with_context(DependencyKind::AssociatedTypeBound, |this| {
                intravisit::walk_opaque_ty(this, opaque)
            });
        });
    }

    fn visit_fn(
        &mut self,
        kind: FnKind<'tcx>,
        declaration: &'tcx hir::FnDecl<'tcx>,
        body: hir::BodyId,
        span: Span,
        definition: LocalDefId,
    ) {
        self.with_definition(definition, |this| {
            let _ = span;
            intravisit::walk_fn(this, kind, declaration, body, definition)
        });
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        let context = self.body_context();
        self.with_context(context, |this| intravisit::walk_body(this, body));
    }

    fn visit_fn_decl(&mut self, declaration: &'tcx hir::FnDecl<'tcx>) {
        self.with_context(DependencyKind::SignatureType, |this| {
            for input in declaration.inputs {
                this.visit_ty_unambig(input);
            }
        });
        if let hir::FnRetTy::Return(output) = declaration.output {
            self.with_context(DependencyKind::ReturnType, |this| {
                this.visit_ty_unambig(output)
            });
        }
    }

    fn visit_where_predicate(&mut self, predicate: &'tcx hir::WherePredicate<'tcx>) {
        self.with_context(DependencyKind::Predicate, |this| {
            intravisit::walk_where_predicate(this, predicate)
        });
    }

    fn visit_trait_ref(&mut self, trait_ref: &'tcx hir::TraitRef<'tcx>) {
        let context = if self.context == DependencyKind::Predicate {
            DependencyKind::Predicate
        } else {
            match self.current.map(|definition| self.tcx.def_kind(definition)) {
                Some(DefKind::Impl { .. }) => DependencyKind::ImplementedTrait,
                Some(DefKind::Trait | DefKind::TraitAlias) => DependencyKind::SuperTrait,
                _ => self.context,
            }
        };
        self.with_context(context, |this| intravisit::walk_trait_ref(this, trait_ref));
    }

    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx, hir::AmbigArg>) {
        let context = if matches!(
            self.context,
            DependencyKind::ValuePath | DependencyKind::ConstExpression
        ) {
            DependencyKind::TypePath
        } else {
            self.context
        };
        self.with_context(context, |this| intravisit::walk_ty(this, ty));
    }

    fn visit_lifetime(&mut self, lifetime: &'tcx hir::Lifetime) {
        match lifetime.kind {
            hir::LifetimeKind::Param(target) => {
                self.record(target.to_def_id(), self.context, lifetime.ident.span);
            }
            hir::LifetimeKind::Error(_) => {
                self.error = Some(DefinitionError::IncompleteDependency);
            }
            hir::LifetimeKind::ImplicitObjectLifetimeDefault
            | hir::LifetimeKind::Infer
            | hir::LifetimeKind::Static => {}
        }
        intravisit::walk_lifetime(self, lifetime);
    }

    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        self.with_context(DependencyKind::PatternConstructor, |this| {
            intravisit::walk_pat(this, pattern)
        });
    }

    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(closure) = expression.kind {
            self.with_definition(closure.def_id, |this| {
                intravisit::walk_expr(this, expression)
            });
        } else {
            intravisit::walk_expr(self, expression);
        }
    }

    fn visit_qpath(&mut self, path: &'tcx hir::QPath<'tcx>, id: hir::HirId, span: Span) {
        if let hir::QPath::TypeRelative(qualifier, segment) = path
            && segment.res == Res::Err
            && let Some(current) = self.current
            && id.owner.def_id == current
            && self.tcx.def_kind(current).is_assoc()
            && self.signature_context()
            && let hir::TyKind::Path(hir::QPath::Resolved(None, qualifier_path)) = qualifier.kind
        {
            let Some(container) = self.tcx.opt_local_parent(current) else {
                self.error = Some(DefinitionError::IncompleteDependency);
                return;
            };
            if !matches!(
                self.tcx.def_kind(container),
                DefKind::Trait | DefKind::Impl { .. }
            ) {
                self.error = Some(DefinitionError::IncompleteDependency);
                return;
            }
            let qualifier_container = match qualifier_path.res {
                Res::SelfTyParam { trait_ } => trait_,
                Res::SelfTyAlias { alias_to, .. } => alias_to,
                _ => {
                    intravisit::walk_qpath(self, path, id);
                    return;
                }
            };
            if qualifier_container != container.to_def_id() {
                self.error = Some(DefinitionError::IncompleteDependency);
                return;
            }
            let direct = self
                .tcx
                .associated_items(container.to_def_id())
                .in_definition_order()
                .filter(|item| item.opt_name() == Some(segment.ident.name))
                .collect::<Vec<_>>();
            let target = match direct.as_slice() {
                [item] => Some(item.def_id),
                [] => {
                    let trait_definition = match self.tcx.def_kind(container) {
                        DefKind::Impl { of_trait: true } => Some(
                            self.tcx
                                .impl_trait_ref(container.to_def_id())
                                .instantiate_identity()
                                .skip_norm_wip()
                                .def_id,
                        ),
                        DefKind::Impl { of_trait: false } => None,
                        DefKind::Trait => Some(container.to_def_id()),
                        _ => unreachable!(),
                    };
                    let Some(trait_definition) = trait_definition else {
                        intravisit::walk_qpath(self, path, id);
                        return;
                    };
                    let scopes = match supertrait_definitions(self.tcx, trait_definition) {
                        Ok(scopes) => scopes,
                        Err(error) => {
                            self.error = Some(error);
                            return;
                        }
                    };
                    let matches = scopes
                        .into_iter()
                        .flat_map(|scope| {
                            self.tcx
                                .associated_items(scope)
                                .in_definition_order()
                                .filter(|item| item.opt_name() == Some(segment.ident.name))
                        })
                        .collect::<Vec<_>>();
                    match matches.as_slice() {
                        [item] => Some(item.def_id),
                        _ => None,
                    }
                }
                _ => None,
            };
            match target {
                Some(target) => self.record(target, self.context, segment.ident.span),
                None => self.error = Some(DefinitionError::IncompleteDependency),
            }
        }
        let _ = span;
        intravisit::walk_qpath(self, path, id);
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, id: hir::HirId) {
        self.record_res(path.res, path.span);
        intravisit::walk_path(self, path);
        self.visit_id(id);
    }
}

fn collect_typeck_edges(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    let mut roots = tcx
        .hir_body_owners()
        .map(|owner| tcx.typeck_root_def_id_local(owner))
        .collect::<Vec<_>>();
    roots.sort_by_key(|root| tcx.def_path_hash(root.to_def_id()));
    roots.dedup();

    for root in roots {
        let results = tcx.typeck(root);
        for (local_id, result) in results.type_dependent_defs().items_in_stable_order() {
            let (_, target) = result
                .as_ref()
                .map_err(|_| DefinitionError::IncompleteDependency)?;
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            let node = tcx.hir_node(site);
            let (kind, span) = type_dependent_kind_and_span(node)?;
            edges.push(RawEdge {
                from: tcx.hir_enclosing_body_owner(site),
                to: *target,
                kind,
                site: Some(source_range(compiler, source, span)?),
            });
        }

        for (local_id, adjustments) in results.adjustments().items_in_stable_order() {
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            let from = tcx.hir_enclosing_body_owner(site);
            let site_span = tcx.hir_span(site);
            for adjustment in adjustments {
                collect_type_references(
                    tcx,
                    from,
                    adjustment.target,
                    DependencyKind::AdjustmentType,
                    Some(source_range(compiler, source, site_span)?),
                    edges,
                )?;
                if let ty::adjustment::Adjust::Deref(ty::adjustment::DerefAdjustKind::Overloaded(
                    overloaded,
                )) = adjustment.kind
                {
                    edges.push(RawEdge {
                        from,
                        to: overloaded.method_call(tcx),
                        kind: DependencyKind::DerefTarget,
                        site: Some(source_range(compiler, source, overloaded.span)?),
                    });
                }
            }
        }

        for (local_id, _) in tcx
            .hir_owner_nodes(results.hir_owner)
            .nodes
            .iter_enumerated()
        {
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            if let Some(arguments) = results.node_args_opt(site) {
                let from = tcx.hir_enclosing_body_owner(site);
                let range = source_range(compiler, source, tcx.hir_span(site))?;
                for argument in arguments {
                    collect_generic_references(
                        tcx,
                        from,
                        argument,
                        DependencyKind::ResolvedGenericArgument,
                        Some(range),
                        edges,
                    )?;
                }
            }
        }

        for (&opaque, hidden) in &results.hidden_types {
            collect_type_references(
                tcx,
                opaque,
                hidden.ty.instantiate_identity().skip_norm_wip(),
                DependencyKind::OpaqueHiddenType,
                Some(source_range(compiler, source, hidden.span)?),
                edges,
            )?;
        }

        for (local_id, fields) in results.offset_of_data().items_in_stable_order() {
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            let hir::Node::Expr(hir::Expr {
                kind: hir::ExprKind::OffsetOf(_, identifiers),
                ..
            }) = tcx.hir_node(site)
            else {
                return Err(DefinitionError::IncompleteDependency);
            };
            if fields.len() != identifiers.len() {
                return Err(DefinitionError::IncompleteDependency);
            }
            let from = tcx.hir_enclosing_body_owner(site);
            for (&(container, variant, field), identifier) in fields.iter().zip(identifiers.iter())
            {
                let container = container.peel_refs();
                let Some(adt) = container.ty_adt_def() else {
                    if let ty::Tuple(types) = *container.kind()
                        && variant.index() == 0
                        && types.get(field.index()).is_some()
                    {
                        continue;
                    }
                    return Err(DefinitionError::IncompleteDependency);
                };
                let Some(field) = adt
                    .variants()
                    .get(variant)
                    .and_then(|variant| variant.fields.get(field))
                else {
                    return Err(DefinitionError::IncompleteDependency);
                };
                edges.push(RawEdge {
                    from,
                    to: field.did,
                    kind: DependencyKind::FieldTarget,
                    site: Some(source_range(compiler, source, identifier.span)?),
                });
            }
        }
    }

    for definition in tcx.iter_local_def_id() {
        if tcx.def_kind(definition) != DefKind::Closure {
            continue;
        }
        for capture in tcx.closure_captures(definition) {
            collect_type_references(
                tcx,
                definition,
                capture.place.ty(),
                DependencyKind::ClosureCaptureType,
                Some(source_range(compiler, source, capture.get_path_span(tcx))?),
                edges,
            )?;
        }
    }
    collect_field_edges(compiler, tcx, source, edges)
}

fn type_dependent_kind_and_span(
    node: hir::Node<'_>,
) -> Result<(DependencyKind, Span), DefinitionError> {
    Ok(match node {
        hir::Node::Expr(expression) => match expression.kind {
            hir::ExprKind::MethodCall(segment, ..) => {
                (DependencyKind::MethodTarget, segment.ident.span)
            }
            hir::ExprKind::Binary(operator, ..) => {
                (DependencyKind::OverloadedOperator, operator.span)
            }
            hir::ExprKind::AssignOp(operator, ..) => {
                (DependencyKind::OverloadedOperator, operator.span)
            }
            hir::ExprKind::Unary(rustc_ast::ast::UnOp::Deref, _) => {
                (DependencyKind::DerefTarget, expression.span)
            }
            hir::ExprKind::Unary(..) => (DependencyKind::OverloadedOperator, expression.span),
            hir::ExprKind::Index(_, _, span) => (DependencyKind::IndexTarget, span),
            hir::ExprKind::Call(..) => (DependencyKind::CallableTrait, expression.span),
            hir::ExprKind::Path(..) | hir::ExprKind::Struct(..) => {
                (DependencyKind::AssociatedItemTarget, expression.span)
            }
            _ => return Err(DefinitionError::IncompleteDependency),
        },
        hir::Node::Ty(ty) => (DependencyKind::AssociatedItemTarget, ty.span),
        hir::Node::Pat(pattern) => (DependencyKind::AssociatedItemTarget, pattern.span),
        hir::Node::PatExpr(pattern) => (DependencyKind::AssociatedItemTarget, pattern.span),
        _ => return Err(DefinitionError::IncompleteDependency),
    })
}

fn collect_type_references<'tcx>(
    tcx: TyCtxt<'tcx>,
    from: LocalDefId,
    ty: Ty<'tcx>,
    kind: DependencyKind,
    site: Option<ByteRange>,
    edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    collect_generic_references(tcx, from, ty.into(), kind, site, edges)
}

fn collect_generic_references<'tcx>(
    tcx: TyCtxt<'tcx>,
    from: LocalDefId,
    root: ty::GenericArg<'tcx>,
    kind: DependencyKind,
    site: Option<ByteRange>,
    edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    for argument in root.walk() {
        match argument.kind() {
            GenericArgKind::Type(ty) => match *ty.kind() {
                ty::Adt(definition, _) => edges.push(RawEdge {
                    from,
                    to: definition.did(),
                    kind,
                    site,
                }),
                ty::Foreign(definition)
                | ty::FnDef(definition, _)
                | ty::Closure(definition, _)
                | ty::CoroutineClosure(definition, _)
                | ty::Coroutine(definition, _) => edges.push(RawEdge {
                    from,
                    to: definition,
                    kind,
                    site,
                }),
                ty::Alias(_, alias) => {
                    let definition = match alias.kind {
                        ty::AliasTyKind::Projection { def_id } => def_id,
                        ty::AliasTyKind::Inherent { def_id } => def_id,
                        ty::AliasTyKind::Opaque { def_id } => def_id,
                        ty::AliasTyKind::Free { def_id } => def_id,
                    };
                    edges.push(RawEdge {
                        from,
                        to: definition,
                        kind,
                        site,
                    });
                }
                ty::Dynamic(predicates, ..) => {
                    for predicate in predicates {
                        let definition = match predicate.skip_binder() {
                            ty::ExistentialPredicate::Trait(trait_ref) => trait_ref.def_id,
                            ty::ExistentialPredicate::Projection(projection) => projection.def_id,
                            ty::ExistentialPredicate::AutoTrait(definition) => definition,
                        };
                        edges.push(RawEdge {
                            from,
                            to: definition,
                            kind,
                            site,
                        });
                    }
                }
                ty::Param(parameter) => edges.push(RawEdge {
                    from,
                    to: generic_parameter_definition(
                        tcx,
                        from,
                        parameter.index,
                        parameter.name,
                        DefinitionKind::TypeParameter,
                    )?,
                    kind,
                    site,
                }),
                ty::Bool
                | ty::Char
                | ty::Int(_)
                | ty::Uint(_)
                | ty::Float(_)
                | ty::Str
                | ty::Never
                | ty::Array(_, _)
                | ty::Slice(_)
                | ty::Tuple(_)
                | ty::RawPtr(_, _)
                | ty::Ref(_, _, _)
                | ty::Pat(_, _)
                | ty::FnPtr(_, _)
                | ty::UnsafeBinder(_)
                | ty::Bound(_, _)
                | ty::Placeholder(_)
                | ty::Infer(_)
                | ty::Error(_) => {}
                ty::CoroutineWitness(definition, _) => edges.push(RawEdge {
                    from,
                    to: definition,
                    kind,
                    site,
                }),
            },
            GenericArgKind::Const(constant) => match constant.kind() {
                ty::ConstKind::Alias(_, alias) => {
                    let definition = match alias.kind {
                        ty::AliasConstKind::Projection { def_id }
                        | ty::AliasConstKind::Inherent { def_id }
                        | ty::AliasConstKind::Free { def_id }
                        | ty::AliasConstKind::Anon { def_id } => def_id,
                    };
                    edges.push(RawEdge {
                        from,
                        to: definition,
                        kind,
                        site,
                    });
                }
                ty::ConstKind::Param(parameter) => edges.push(RawEdge {
                    from,
                    to: generic_parameter_definition(
                        tcx,
                        from,
                        parameter.index,
                        parameter.name,
                        DefinitionKind::ConstParameter,
                    )?,
                    kind,
                    site,
                }),
                ty::ConstKind::Infer(_)
                | ty::ConstKind::Bound(_, _)
                | ty::ConstKind::Placeholder(_)
                | ty::ConstKind::Value(_)
                | ty::ConstKind::Error(_)
                | ty::ConstKind::Expr(_) => {}
            },
            GenericArgKind::Lifetime(_) => {}
        }
    }
    if root.has_infer() {
        return Err(DefinitionError::IncompleteDependency);
    }
    Ok(())
}

fn generic_parameter_definition(
    tcx: TyCtxt<'_>,
    from: LocalDefId,
    index: u32,
    name: rustc_span::Symbol,
    expected_kind: DefinitionKind,
) -> Result<DefId, DefinitionError> {
    let mut owner = Some(from.to_def_id());
    while let Some(definition) = owner {
        let generics = tcx.generics_of(definition);
        if let Some(parameter) = generics
            .own_params
            .iter()
            .find(|parameter| parameter.index == index)
        {
            let kind_matches = matches!(
                (&parameter.kind, expected_kind),
                (
                    ty::GenericParamDefKind::Type { .. },
                    DefinitionKind::TypeParameter
                ) | (
                    ty::GenericParamDefKind::Const { .. },
                    DefinitionKind::ConstParameter
                )
            );
            if !kind_matches || parameter.name != name {
                return Err(DefinitionError::IncompleteDependency);
            }
            return Ok(parameter.def_id);
        }
        owner = generics.parent;
    }
    Err(DefinitionError::IncompleteDependency)
}

fn collect_field_edges(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    let mut roots = tcx
        .hir_body_owners()
        .map(|owner| tcx.typeck_root_def_id_local(owner))
        .collect::<Vec<_>>();
    roots.sort_by_key(|root| tcx.def_path_hash(root.to_def_id()));
    roots.dedup();
    for root in roots {
        let results = tcx.typeck(root);
        for (local_id, field_index) in results.field_indices().items_in_stable_order() {
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            let (base_ty, struct_path, span) = match tcx.hir_node(site) {
                hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Field(base, identifier),
                    ..
                }) => (results.expr_ty_adjusted(base), None, identifier.span),
                hir::Node::ExprField(field) => {
                    let Some((parent_id, hir::Node::Expr(parent))) = tcx
                        .hir_parent_iter(site)
                        .find(|(_, node)| matches!(node, hir::Node::Expr(_)))
                    else {
                        return Err(DefinitionError::IncompleteDependency);
                    };
                    let hir::ExprKind::Struct(path, ..) = parent.kind else {
                        return Err(DefinitionError::IncompleteDependency);
                    };
                    (
                        results.expr_ty(parent),
                        Some((path, parent_id)),
                        field.ident.span,
                    )
                }
                hir::Node::PatField(field) => {
                    let Some((parent_id, hir::Node::Pat(parent))) = tcx
                        .hir_parent_iter(site)
                        .find(|(_, node)| matches!(node, hir::Node::Pat(_)))
                    else {
                        return Err(DefinitionError::IncompleteDependency);
                    };
                    let hir::PatKind::Struct(path, ..) = &parent.kind else {
                        return Err(DefinitionError::IncompleteDependency);
                    };
                    (
                        results.node_type(parent_id),
                        Some((path, parent_id)),
                        field.ident.span,
                    )
                }
                _ => return Err(DefinitionError::IncompleteDependency),
            };
            let base_ty = base_ty.peel_refs();
            let Some(adt) = base_ty.ty_adt_def() else {
                if let ty::Tuple(fields) = *base_ty.kind()
                    && fields.get(field_index.index()).is_some()
                {
                    continue;
                }
                return Err(DefinitionError::IncompleteDependency);
            };
            let variant = if let Some((path, parent_id)) = struct_path {
                let resolution = results.qpath_res(path, parent_id);
                let valid = match resolution {
                    Res::Def(DefKind::Variant, definition) => adt
                        .variants()
                        .iter()
                        .any(|variant| variant.def_id == definition),
                    Res::Def(DefKind::Ctor(..), definition) => adt
                        .variants()
                        .iter()
                        .any(|variant| variant.ctor_def_id() == Some(definition)),
                    Res::Def(
                        DefKind::Struct | DefKind::Union | DefKind::TyAlias | DefKind::AssocTy,
                        _,
                    )
                    | Res::SelfTyParam { .. }
                    | Res::SelfTyAlias { .. }
                    | Res::SelfCtor(..) => !adt.is_enum(),
                    _ => false,
                };
                if !valid {
                    return Err(DefinitionError::IncompleteDependency);
                }
                adt.variant_of_res(resolution)
            } else {
                if adt.is_enum() {
                    return Err(DefinitionError::IncompleteDependency);
                }
                adt.non_enum_variant()
            };
            let Some(field) = variant.fields.get(*field_index) else {
                return Err(DefinitionError::IncompleteDependency);
            };
            edges.push(RawEdge {
                from: tcx.hir_enclosing_body_owner(site),
                to: field.did,
                kind: DependencyKind::FieldTarget,
                site: Some(source_range(compiler, source, span)?),
            });
        }
    }
    Ok(())
}

#[cfg(not(rust_item_dependencies_patched))]
fn collect_import_edges(
    _compiler: &Compiler,
    _tcx: TyCtxt<'_>,
    _source: &SourceInventory,
    _source_owners: &BTreeMap<crate::source::SourceUnitId, LocalDefId>,
    _edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    Err(DefinitionError::IncompleteDependency)
}

#[cfg(rust_item_dependencies_patched)]
fn collect_import_edges(
    compiler: &Compiler,
    tcx: TyCtxt<'_>,
    source: &SourceInventory,
    source_owners: &BTreeMap<crate::source::SourceUnitId, LocalDefId>,
    edges: &mut Vec<RawEdge>,
) -> Result<(), DefinitionError> {
    for record in &tcx.resolutions(()).resolved_import_uses {
        let site = source_range(compiler, source, record.segment_span)?;
        for step in &record.import_chain {
            let definition = match *step {
                Reexport::Single(definition)
                | Reexport::Glob(definition)
                | Reexport::ExternCrate(definition) => definition,
                Reexport::MacroUse | Reexport::MacroExport => continue,
            };
            edges.push(RawEdge {
                from: record.owner,
                to: definition,
                kind: DependencyKind::ImportLeaf,
                site: Some(site),
            });
        }
    }

    let mut roots = tcx
        .hir_body_owners()
        .map(|owner| tcx.typeck_root_def_id_local(owner))
        .collect::<Vec<_>>();
    roots.sort_by_key(|root| tcx.def_path_hash(root.to_def_id()));
    roots.dedup();
    for root in roots {
        let results = tcx.typeck(root);
        for (local_id, imports) in results.selected_trait_imports().items_in_stable_order() {
            let site = hir::HirId {
                owner: results.hir_owner,
                local_id,
            };
            if results.type_dependent_def_id(site).is_none() {
                return Err(DefinitionError::IncompleteDependency);
            }
            let range = source_range(compiler, source, tcx.hir_span(site))?;
            let from = tcx.hir_enclosing_body_owner(site);
            for &import in imports {
                edges.push(RawEdge {
                    from,
                    to: import.to_def_id(),
                    kind: DependencyKind::ImportLeaf,
                    site: Some(range),
                });
            }
        }
    }

    let macro_origins = tcx
        .resolutions(())
        .macro_invocation_origins
        .items()
        .map(|(&expansion, origin)| {
            (
                expansion.expn_hash().local_hash().as_u64(),
                expansion,
                origin,
            )
        })
        .into_sorted_stable_ord_by_key(|record| &record.0);
    for (_, expansion, origin) in macro_origins {
        let macro_definition = expansion.expn_data().macro_def_id;
        if macro_definition.is_none() && origin.resolved_import_uses.is_empty() {
            continue;
        }
        let outer_expansion = outer_macro_expansion(tcx, expansion)?;
        let outer = tcx
            .resolutions(())
            .macro_invocation_origins
            .get(&outer_expansion)
            .ok_or(DefinitionError::IncompleteDependency)?;
        let invocation = written_macro_invocation(compiler, source, outer_expansion, outer)?;
        let from = if outer.target_span.is_some() {
            source_owner(source, source_owners, invocation.id)?
        } else {
            outer.parent_definition
        };
        if let Some(target) = macro_definition {
            let site = original_span_range(
                compiler,
                &source.offsets,
                outer_expansion.expn_data().call_site,
            )?;
            edges.push(RawEdge {
                from,
                to: target,
                kind: DependencyKind::MacroPath,
                site: Some(site),
            });
        }
        for record in &origin.resolved_import_uses {
            let site = source_range(compiler, source, record.segment_span)?;
            let target = record
                .target
                .opt_def_id()
                .ok_or(DefinitionError::IncompleteDependency)?;
            if record.namespace == Namespace::MacroNS && Some(target) != macro_definition {
                return Err(DefinitionError::IncompleteDependency);
            }
            for step in &record.import_chain {
                edges.push(RawEdge {
                    from,
                    to: step.definition.to_def_id(),
                    kind: DependencyKind::ImportLeaf,
                    site: Some(site),
                });
            }
        }
    }
    Ok(())
}

#[cfg(rust_item_dependencies_patched)]
fn outer_macro_expansion(tcx: TyCtxt<'_>, expansion: ExpnId) -> Result<ExpnId, DefinitionError> {
    let origins = &tcx.resolutions(()).macro_invocation_origins;
    let mut current = expansion;
    let mut visited = Vec::new();
    loop {
        if current == ExpnId::root() || visited.contains(&current) {
            return Err(DefinitionError::IncompleteDependency);
        }
        visited.push(current);
        let origin = origins
            .get(&current)
            .ok_or(DefinitionError::IncompleteDependency)?;
        if origin.discovered_in_expansion == ExpnId::root() {
            return Ok(current);
        }
        current = recorded_macro_expansion(tcx, origin.discovered_in_expansion)
            .ok_or(DefinitionError::IncompleteDependency)?;
    }
}

#[cfg(rust_item_dependencies_patched)]
fn source_owner(
    source: &SourceInventory,
    source_owners: &BTreeMap<crate::source::SourceUnitId, LocalDefId>,
    mut unit: crate::source::SourceUnitId,
) -> Result<LocalDefId, DefinitionError> {
    loop {
        if let Some(&owner) = source_owners.get(&unit) {
            return Ok(owner);
        }
        unit = source
            .units
            .get(unit.0 as usize)
            .and_then(|unit| unit.parent)
            .ok_or(DefinitionError::IncompleteDependency)?;
    }
}

fn source_range(
    compiler: &Compiler,
    source: &SourceInventory,
    span: Span,
) -> Result<ByteRange, DefinitionError> {
    original_span_range(compiler, &source.offsets, span.source_callsite()).map_err(Into::into)
}

#[cfg(all(test, rust_item_dependencies_patched))]
mod exact_tests {
    use std::collections::BTreeSet;
    use std::path::PathBuf;
    use std::process::Command;

    use super::*;
    use crate::graph::{DefinitionTarget, ExternalDefinitionId};
    use crate::input::{Edition, SourceInput, inspect_source_with_definitions};

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum OriginRef {
        Written {
            unit_range: ByteRange,
            anchor: ByteRange,
            unit_kind: WrittenUnitKind,
            unit_ordinal: u32,
        },
        Expanded {
            invocation_range: ByteRange,
            generated_role: Option<GeneratedRole>,
            ordinal: u32,
        },
        CompilerGenerated {
            role: GeneratedRole,
            ordinal: u32,
        },
        Injected {
            role: InjectedRole,
            ordinal: u32,
        },
    }

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct LocalRef {
        kind: DefinitionKind,
        origin: OriginRef,
        name: Option<String>,
        structural_ordinal: u32,
        parent: Option<Box<LocalRef>>,
    }

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct ExternalRef {
        crate_name: String,
        path: String,
    }

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum TargetRef {
        Local(LocalRef),
        External(ExternalRef),
    }

    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct EdgeRef {
        from: LocalRef,
        to: TargetRef,
        kind: DependencyKind,
        sites: Vec<ByteRange>,
    }

    #[derive(Debug, Eq, PartialEq)]
    struct GraphRef {
        definitions: BTreeSet<LocalRef>,
        external_definitions: BTreeSet<ExternalRef>,
        edges: BTreeSet<EdgeRef>,
    }

    #[test]
    fn reports_exact_path_constructor_and_callable_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/path_resolution.rs");
        let graph = inspect(source);

        let root = named(
            written(
                DefinitionKind::Crate,
                ByteRange {
                    start: 0,
                    end: source.len() as u32,
                },
                WrittenUnitKind::CrateRoot,
                0,
                None,
            ),
            None,
            0,
        );
        let pair_item = marker_range(source, "struct Pair(u8);");
        let pair = named(
            written_with_anchor(
                DefinitionKind::Struct,
                pair_item,
                marker_in(source, "struct Pair(u8);", "struct Pair"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Pair"),
            0,
        );
        let field = named(
            written_with_anchor(
                DefinitionKind::Field,
                pair_item,
                marker_in(source, "struct Pair(u8);", "u8"),
                WrittenUnitKind::Item,
                0,
                Some(&pair),
            ),
            Some("0"),
            0,
        );
        let constructor = named(
            written_with_anchor(
                DefinitionKind::Constructor,
                pair_item,
                marker_in(source, "struct Pair(u8);", "struct Pair"),
                WrittenUnitKind::Item,
                0,
                Some(&pair),
            ),
            None,
            0,
        );
        let chosen_item = marker_range(source, "fn chosen() -> u8 {\n    1\n}");
        let chosen = named(
            written_with_anchor(
                DefinitionKind::Function,
                chosen_item,
                marker_range(source, "fn chosen() -> u8"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("chosen"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let closure = named(
            written_with_anchor(
                DefinitionKind::Closure,
                main_item,
                marker_range(source, "||"),
                WrittenUnitKind::Item,
                2,
                Some(&main),
            ),
            None,
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = named(
            injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root),
            None,
            0,
        );

        let callable = external("core", "std::ops::Fn::call");
        let option = external("core", "std::option::Option");
        let some = external("core", "std::prelude::v1::Some");
        let closure_call = marker_in(source, "let _ = chosen();", "chosen()");
        let closure_callee = marker_in(source, "let _ = chosen();", "chosen");
        let constructor_statement = "let Pair(value) = Pair(3);";

        let expected = GraphRef {
            definitions: BTreeSet::from([
                root.clone(),
                pair.clone(),
                field.clone(),
                constructor.clone(),
                chosen.clone(),
                main.clone(),
                closure.clone(),
                injected_std.clone(),
                injected_prelude.clone(),
            ]),
            external_definitions: BTreeSet::from([callable.clone(), option.clone(), some.clone()]),
            edges: BTreeSet::from([
                edge(
                    &pair,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [marker_in(source, "struct Pair(u8);", "struct Pair")],
                ),
                edge(
                    &field,
                    TargetRef::Local(pair.clone()),
                    DependencyKind::Parent,
                    [marker_in(source, "struct Pair(u8);", "u8")],
                ),
                edge(
                    &constructor,
                    TargetRef::Local(pair.clone()),
                    DependencyKind::Parent,
                    [marker_in(source, "struct Pair(u8);", "struct Pair")],
                ),
                edge(
                    &chosen,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [marker_range(source, "fn chosen() -> u8")],
                ),
                edge(
                    &main,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [marker_range(source, "fn main()")],
                ),
                edge(
                    &closure,
                    TargetRef::Local(main.clone()),
                    DependencyKind::Parent,
                    [marker_range(source, "||")],
                ),
                edge(
                    &injected_std,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [],
                ),
                edge(
                    &injected_prelude,
                    TargetRef::Local(root),
                    DependencyKind::Parent,
                    [],
                ),
                edge(
                    &main,
                    TargetRef::Local(chosen),
                    DependencyKind::ValuePath,
                    [marker_in(
                        source,
                        "let _ = crate::chosen();",
                        "crate::chosen",
                    )],
                ),
                edge(
                    &main,
                    TargetRef::Local(constructor.clone()),
                    DependencyKind::PatternConstructor,
                    [nth_marker_in(source, constructor_statement, "Pair", 0)],
                ),
                edge(
                    &main,
                    TargetRef::Local(constructor),
                    DependencyKind::ValuePath,
                    [nth_marker_in(source, constructor_statement, "Pair", 1)],
                ),
                edge(
                    &main,
                    TargetRef::Local(pair),
                    DependencyKind::TypePath,
                    [marker_in(source, "let _: Pair;", "Pair")],
                ),
                edge(
                    &main,
                    TargetRef::Local(closure.clone()),
                    DependencyKind::ResolvedGenericArgument,
                    [closure_call],
                ),
                edge(
                    &main,
                    TargetRef::Local(closure),
                    DependencyKind::AdjustmentType,
                    [closure_callee],
                ),
                edge(
                    &main,
                    TargetRef::External(callable),
                    DependencyKind::CallableTrait,
                    [closure_call],
                ),
                edge(
                    &main,
                    TargetRef::External(option),
                    DependencyKind::TypePath,
                    [marker_in(
                        source,
                        "let _: Option<u8> = Some(value);",
                        "Option<u8>",
                    )],
                ),
                edge(
                    &main,
                    TargetRef::External(some),
                    DependencyKind::ValuePath,
                    [marker_in(
                        source,
                        "let _: Option<u8> = Some(value);",
                        "Some",
                    )],
                ),
            ]),
        };

        assert_eq!(project_graph(&graph), expected);
    }

    #[test]
    fn reports_exact_method_ufcs_and_autoderef_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/dispatch_resolution.rs");
        let graph = inspect(source);
        let expected = expected_dispatch_graph(source);
        assert_eq!(project_graph(&graph), expected);
    }

    #[test]
    fn reports_exact_nested_glob_renamed_and_trait_import_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/import_resolution.rs");
        let graph = inspect(source);
        let expected = expected_import_graph(source);
        assert_eq!(project_graph(&graph), expected);
    }

    #[test]
    fn reports_exact_operator_index_and_callable_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/operator_resolution.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_operator_definitions(source);
        let expected_edges = expected_operator_target_edges(source, &expected_definitions);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(
            actual.external_definitions,
            BTreeSet::from([
                external("core", "std::ops::Add"),
                external("core", "std::ops::Add::add"),
                external("core", "std::ops::Fn"),
                external("core", "std::ops::Fn::call"),
                external("core", "std::ops::Index"),
                external("core", "std::ops::Index::index"),
            ])
        );
        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[
                    DependencyKind::OverloadedOperator,
                    DependencyKind::IndexTarget,
                    DependencyKind::CallableTrait,
                ],
            ),
            expected_edges
        );
    }

    #[test]
    fn reports_exact_declaration_and_named_field_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/declaration_resolution.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_declaration_definitions(source);
        let expected_edges = expected_declaration_target_edges(source, &expected_definitions);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(actual.external_definitions, BTreeSet::new());
        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[
                    DependencyKind::GenericDefault,
                    DependencyKind::Predicate,
                    DependencyKind::Discriminant,
                    DependencyKind::VisibilityPath,
                    DependencyKind::FieldTarget,
                ],
            ),
            expected_edges
        );
    }

    #[test]
    fn reports_exact_async_definition_origins() {
        let source = include_str!("../tests/fixtures/definitions/async_origins.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_async_definitions(source);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::Parent, DependencyKind::MacroPath],
            ),
            expected_async_structure_edges(source, &actual.definitions)
        );
    }

    #[test]
    fn reports_exact_derive_definition_origins_and_macro_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/derive_resolution.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_derive_definitions(source);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(
            actual.external_definitions,
            BTreeSet::from([
                external("core", "std::clone::Clone"),
                external("core", "std::derive"),
            ])
        );
        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::Parent, DependencyKind::MacroPath],
            ),
            expected_derive_structure_edges(source, &actual.definitions)
        );
    }

    #[test]
    fn reports_exact_macro_import_paths_and_chains() {
        let source = include_str!("../tests/fixtures/compiler/macro_import_provenance.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);

        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::MacroPath, DependencyKind::ImportLeaf],
            ),
            expected_macro_import_edges(source, &actual.definitions)
        );
    }

    #[test]
    fn reports_exact_macro_export_path_and_chain() {
        let source = include_str!("../tests/fixtures/compiler/macro_export_provenance.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let exported = find_local(&actual.definitions, DefinitionKind::Macro, Some("exported"));
        let alias_anchor = marker_in(source, "use crate::exported as alias;", "crate::exported");
        let alias = find_local_with_anchor(&actual.definitions, DefinitionKind::Use, alias_anchor);
        let run = find_local(&actual.definitions, DefinitionKind::Function, Some("run"));
        let invocation = marker_range(source, "alias!()");
        let invocation_path = marker_in(source, "alias!()", "alias");

        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::MacroPath, DependencyKind::ImportLeaf],
            ),
            BTreeSet::from([
                edge(
                    &alias,
                    TargetRef::Local(exported.clone()),
                    DependencyKind::MacroPath,
                    [alias_anchor],
                ),
                edge(
                    &run,
                    TargetRef::Local(exported.clone()),
                    DependencyKind::MacroPath,
                    [invocation],
                ),
                edge(
                    &run,
                    TargetRef::Local(alias),
                    DependencyKind::ImportLeaf,
                    [invocation_path],
                ),
                edge(
                    &run,
                    TargetRef::Local(exported),
                    DependencyKind::ImportLeaf,
                    [invocation_path],
                ),
            ])
        );
    }

    #[test]
    fn reports_exact_return_position_impl_trait_definitions() {
        let source = include_str!("../tests/fixtures/definitions/return_position_impl_trait.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_return_position_impl_trait_definitions(source);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(
            edges_of_kinds(&actual.edges, &[DependencyKind::Parent]),
            expected_return_position_impl_trait_parent_edges(source, &actual.definitions)
        );
    }

    #[test]
    fn reports_exact_offset_of_field_dependency() {
        let source = include_str!("../tests/fixtures/definitions/offset_of.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let structure = find_local(&actual.definitions, DefinitionKind::Struct, Some("S"));
        let field = child_of(
            &actual.definitions,
            DefinitionKind::Field,
            &structure,
            Some("a"),
        );
        let main = find_local(&actual.definitions, DefinitionKind::Function, Some("main"));
        let inline_constant = child_of(
            &actual.definitions,
            DefinitionKind::InlineConst,
            &main,
            None,
        );

        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::TypePath, DependencyKind::FieldTarget],
            ),
            BTreeSet::from([
                edge(
                    &inline_constant,
                    TargetRef::Local(structure),
                    DependencyKind::TypePath,
                    [marker_in(source, "offset_of!(S, a)", "S")],
                ),
                edge(
                    &inline_constant,
                    TargetRef::Local(field),
                    DependencyKind::FieldTarget,
                    [marker_in(source, "offset_of!(S, a)", "a")],
                ),
            ])
        );
    }

    #[test]
    fn reports_exact_inferred_generic_parameter_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/generic_arguments.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);

        assert_eq!(
            edges_of_kinds(&actual.edges, &[DependencyKind::ResolvedGenericArgument],),
            expected_generic_parameter_edges(source)
        );
    }

    #[test]
    fn reports_exact_explicit_lifetime_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/lifetime_dependencies.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);

        assert_eq!(
            edges_targeting_kind(&actual.edges, DefinitionKind::LifetimeParameter,),
            expected_explicit_lifetime_edges(source)
        );
    }

    #[test]
    fn reports_expanded_elided_lifetime_origin() {
        let source = include_str!("../tests/fixtures/definitions/macro_elided_lifetime.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let root = crate_root(source);
        let invocation = marker_range(source, "define_borrow!();");
        let function = named(
            expanded(DefinitionKind::Function, invocation, None, 0, Some(&root)),
            Some("generated"),
            0,
        );
        let lifetime = named(
            expanded(
                DefinitionKind::LifetimeParameter,
                invocation,
                Some(GeneratedRole::ElidedLifetime),
                0,
                Some(&function),
            ),
            Some("'_"),
            0,
        );

        assert_eq!(
            actual
                .definitions
                .iter()
                .filter(|definition| {
                    matches!(
                        definition.kind,
                        DefinitionKind::Function | DefinitionKind::LifetimeParameter
                    ) && matches!(definition.origin, OriginRef::Expanded { .. })
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([function.clone(), lifetime.clone()])
        );
        assert_eq!(
            edges_of_kinds(&actual.edges, &[DependencyKind::Parent])
                .into_iter()
                .filter(|edge| edge.from == lifetime)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([edge(
                &lifetime,
                TargetRef::Local(function),
                DependencyKind::Parent,
                [invocation],
            )])
        );
    }

    #[test]
    fn reports_direct_macro_product_origins() {
        let source = include_str!("../tests/fixtures/definitions/macro_direct_origins.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let root = crate_root(source);
        let macro_item = marker_range(
            source,
            concat!(
                "macro_rules! make_products {\n",
                "    () => {\n",
                "        fn generated() -> impl Copy {\n",
                "            let _ = async {};\n",
                "            1_u8\n",
                "        }\n",
                "    };\n",
                "}",
            ),
        );
        let macro_definition = named(
            written_with_anchor(
                DefinitionKind::Macro,
                macro_item,
                marker_range(source, "macro_rules! make_products"),
                WrittenUnitKind::MacroDefinition,
                0,
                Some(&root),
            ),
            Some("make_products"),
            0,
        );
        let invocation = marker_range(source, "make_products!();");
        let function = named(
            expanded(DefinitionKind::Function, invocation, None, 0, Some(&root)),
            Some("generated"),
            0,
        );
        let opaque = expanded(
            DefinitionKind::OpaqueType,
            invocation,
            None,
            0,
            Some(&function),
        );
        let coroutine = expanded(
            DefinitionKind::Coroutine,
            invocation,
            None,
            0,
            Some(&function),
        );

        assert_eq!(
            actual
                .definitions
                .iter()
                .filter(|definition| matches!(definition.origin, OriginRef::Expanded { .. }))
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([function.clone(), opaque.clone(), coroutine.clone()])
        );
        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[DependencyKind::Parent, DependencyKind::MacroPath],
            )
            .into_iter()
            .filter(|edge| {
                matches!(edge.from.origin, OriginRef::Expanded { .. })
                    || edge.kind == DependencyKind::MacroPath
            })
            .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                edge(
                    &function,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [invocation],
                ),
                edge(
                    &opaque,
                    TargetRef::Local(function.clone()),
                    DependencyKind::Parent,
                    [invocation],
                ),
                edge(
                    &coroutine,
                    TargetRef::Local(function),
                    DependencyKind::Parent,
                    [invocation],
                ),
                edge(
                    &root,
                    TargetRef::Local(macro_definition),
                    DependencyKind::MacroPath,
                    [marker_range(source, "make_products!()")],
                ),
            ])
        );
    }

    #[test]
    fn reports_macro_dependencies_from_innermost_semantic_owners() {
        let source = include_str!("../tests/fixtures/definitions/macro_owner_resolution.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let field_type = find_local(
            &actual.definitions,
            DefinitionKind::Macro,
            Some("field_type"),
        );
        let value = find_local(&actual.definitions, DefinitionKind::Macro, Some("value"));
        let holder = find_local(&actual.definitions, DefinitionKind::Struct, Some("Holder"));
        let field = child_of(
            &actual.definitions,
            DefinitionKind::Field,
            &holder,
            Some("field"),
        );
        let generic = find_local(&actual.definitions, DefinitionKind::Struct, Some("Generic"));
        let type_parameter = child_of(
            &actual.definitions,
            DefinitionKind::TypeParameter,
            &generic,
            Some("T"),
        );
        let capture = find_local(
            &actual.definitions,
            DefinitionKind::Function,
            Some("capture"),
        );
        let closure = child_of(&actual.definitions, DefinitionKind::Closure, &capture, None);
        let constant = find_local(&actual.definitions, DefinitionKind::Const, Some("INLINE"));
        let inline_constant = child_of(
            &actual.definitions,
            DefinitionKind::InlineConst,
            &constant,
            None,
        );

        assert_eq!(
            edges_of_kinds(&actual.edges, &[DependencyKind::MacroPath]),
            BTreeSet::from([
                edge(
                    &field,
                    TargetRef::Local(field_type.clone()),
                    DependencyKind::MacroPath,
                    [nth_marker_range(source, "field_type!()", 0)],
                ),
                edge(
                    &type_parameter,
                    TargetRef::Local(field_type),
                    DependencyKind::MacroPath,
                    [nth_marker_range(source, "field_type!()", 1)],
                ),
                edge(
                    &closure,
                    TargetRef::Local(value.clone()),
                    DependencyKind::MacroPath,
                    [nth_marker_range(source, "value!()", 0)],
                ),
                edge(
                    &inline_constant,
                    TargetRef::Local(value),
                    DependencyKind::MacroPath,
                    [nth_marker_range(source, "value!()", 1)],
                ),
            ])
        );
    }

    #[test]
    fn sibling_impl_does_not_change_definition_key() {
        const OMITTED: &str = "                             ";
        const INCLUDED: &str = "impl A { fn a(&self) {} }    ";
        const SUFFIX: &str = concat!(
            "struct A;\n",
            "struct B;\n",
            "impl B { fn b(&self) {} }\n",
            "fn main() { B.b(); }\n",
        );
        let with_sibling = format!("{INCLUDED}{SUFFIX}");
        let without_sibling = format!("{OMITTED}{SUFFIX}");
        assert_eq!(with_sibling.len(), without_sibling.len());

        let with_graph = inspect(&with_sibling);
        let without_graph = inspect(&without_sibling);

        assert_eq!(impl_key(&with_graph, "B"), impl_key(&without_graph, "B"));
        assert_eq!(
            associated_function_key(&with_graph, "b"),
            associated_function_key(&without_graph, "b")
        );
    }

    #[test]
    fn reports_exact_generic_associated_type_definitions_and_dependencies() {
        let source = include_str!("../tests/fixtures/definitions/generic_associated_type.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);
        let expected_definitions = expected_generic_associated_type_definitions(source);

        assert_eq!(actual.definitions, expected_definitions);
        assert_eq!(actual.external_definitions, BTreeSet::new());
        let actual_edges = edges_of_kinds(
            &actual.edges,
            &[
                DependencyKind::Parent,
                DependencyKind::AssociatedTypeBound,
                DependencyKind::SignatureType,
                DependencyKind::ReturnType,
                DependencyKind::ClosureCaptureType,
            ],
        );
        let expected_edges = expected_generic_associated_type_edges(source, &actual.definitions);
        assert_eq!(actual_edges, expected_edges,);
    }

    #[test]
    fn generic_type_relative_path_does_not_resolve_to_same_named_self_member() {
        let source = concat!(
            "trait Other { type Output; }\n",
            "trait Service {\n",
            "    type Output;\n",
            "    fn f<T: Other>() -> T::Output;\n",
            "}\n",
            "fn main() {}\n",
        );
        let actual = project_graph(&inspect(source));
        let service = find_local(&actual.definitions, DefinitionKind::Trait, Some("Service"));
        let function = child_of(
            &actual.definitions,
            DefinitionKind::AssociatedFunction,
            &service,
            Some("f"),
        );
        let parameter = child_of(
            &actual.definitions,
            DefinitionKind::TypeParameter,
            &function,
            Some("T"),
        );

        assert_eq!(
            actual
                .edges
                .iter()
                .filter(|edge| { edge.from == function && edge.kind == DependencyKind::ReturnType })
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([edge(
                &function,
                TargetRef::Local(parameter),
                DependencyKind::ReturnType,
                [marker_in(source, "-> T::Output", "T")],
            )]),
        );
    }

    #[test]
    fn inherited_associated_type_projection_skips_non_trait_super_clause() {
        let source = concat!(
            "trait Root { type Assoc; }\n",
            "trait Middle: Root {}\n",
            "trait Service: Middle + 'static {\n",
            "    fn project() -> Self::Assoc;\n",
            "}\n",
            "fn main() {}\n",
        );
        let actual = project_graph(&inspect(source));
        let root = find_local(&actual.definitions, DefinitionKind::Trait, Some("Root"));
        let associated = child_of(
            &actual.definitions,
            DefinitionKind::AssociatedType,
            &root,
            Some("Assoc"),
        );
        let service = find_local(&actual.definitions, DefinitionKind::Trait, Some("Service"));
        let project = child_of(
            &actual.definitions,
            DefinitionKind::AssociatedFunction,
            &service,
            Some("project"),
        );

        assert_eq!(
            actual
                .edges
                .iter()
                .filter(|edge| {
                    edge.from == project
                        && edge.kind == DependencyKind::ReturnType
                        && matches!(
                            &edge.to,
                            TargetRef::Local(target)
                                if target.kind == DefinitionKind::AssociatedType
                        )
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([edge(
                &project,
                TargetRef::Local(associated),
                DependencyKind::ReturnType,
                [marker_in(source, "-> Self::Assoc", "Assoc")],
            )]),
        );
    }

    #[test]
    fn impl_body_self_const_resolves_to_unoverridden_trait_default() {
        let source = concat!(
            "trait Defaults {\n",
            "    const N: usize = 7;\n",
            "    fn value(&self) -> usize;\n",
            "}\n",
            "struct Value;\n",
            "impl Defaults for Value {\n",
            "    fn value(&self) -> usize { Self::N }\n",
            "}\n",
            "fn main() {}\n",
        );
        let actual = project_graph(&inspect(source));
        let defaults = find_local(&actual.definitions, DefinitionKind::Trait, Some("Defaults"));
        let constant = child_of(
            &actual.definitions,
            DefinitionKind::AssociatedConst,
            &defaults,
            Some("N"),
        );
        let implementation = find_local_with_anchor(
            &actual.definitions,
            DefinitionKind::Impl,
            marker_range(source, "impl Defaults for Value"),
        );
        let value = child_of(
            &actual.definitions,
            DefinitionKind::AssociatedFunction,
            &implementation,
            Some("value"),
        );

        assert_eq!(
            actual
                .edges
                .iter()
                .filter(|edge| {
                    edge.from == value && edge.to == TargetRef::Local(constant.clone())
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([edge(
                &value,
                TargetRef::Local(constant),
                DependencyKind::AssociatedItemTarget,
                [marker_range(source, "Self::N")],
            )]),
        );
    }

    #[test]
    fn reports_exact_dynamic_trait_signature_dependency() {
        let source = include_str!("../tests/fixtures/definitions/dynamic_trait.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);

        assert_eq!(
            edges_targeting_kind(&actual.edges, DefinitionKind::Trait),
            expected_dynamic_trait_edges(source)
        );
    }

    #[test]
    fn reports_exact_dynamic_trait_closure_capture_dependency() {
        let source = include_str!("../tests/fixtures/definitions/closure_capture.rs");
        let graph = inspect(source);
        let actual = project_graph(&graph);

        assert_eq!(
            edges_of_kinds(
                &actual.edges,
                &[
                    DependencyKind::SignatureType,
                    DependencyKind::ClosureCaptureType,
                ],
            ),
            expected_dynamic_trait_capture_edges(source)
        );
    }

    fn expected_generic_associated_type_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let bound_item = marker_range(source, "trait Bound {}");
        let bound = named(
            written_with_anchor(
                DefinitionKind::Trait,
                bound_item,
                marker_range(source, "trait Bound"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Bound"),
            0,
        );
        let concrete_item = marker_range(source, "struct Concrete;");
        let concrete = named(
            written_with_anchor(
                DefinitionKind::Struct,
                concrete_item,
                marker_range(source, "struct Concrete"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("Concrete"),
            0,
        );
        let constructor = written_with_anchor(
            DefinitionKind::Constructor,
            concrete_item,
            marker_range(source, "struct Concrete"),
            WrittenUnitKind::Item,
            1,
            Some(&concrete),
        );
        let family_item = marker_range(
            source,
            concat!(
                "trait Family {\n",
                "    type Item<'a>: Bound\n",
                "    where\n",
                "        Self: 'a;\n\n",
                "    fn get<'a>(&'a self) -> Self::Item<'a>;\n",
                "}",
            ),
        );
        let family = named(
            written_with_anchor(
                DefinitionKind::Trait,
                family_item,
                marker_range(source, "trait Family"),
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("Family"),
            0,
        );
        let trait_type_item =
            marker_range(source, "type Item<'a>: Bound\n    where\n        Self: 'a;");
        let trait_type = named(
            written_with_anchor(
                DefinitionKind::AssociatedType,
                trait_type_item,
                marker_range(source, "type Item<'a>: Bound"),
                WrittenUnitKind::TraitMember,
                0,
                Some(&family),
            ),
            Some("Item"),
            0,
        );
        let trait_type_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                trait_type_item,
                marker_in(source, "type Item<'a>: Bound", "'a"),
                WrittenUnitKind::TraitMember,
                0,
                Some(&trait_type),
            ),
            Some("'a"),
            0,
        );
        let trait_get_item = marker_range(source, "fn get<'a>(&'a self) -> Self::Item<'a>;");
        let trait_get = named(
            written(
                DefinitionKind::AssociatedFunction,
                trait_get_item,
                WrittenUnitKind::TraitMember,
                1,
                Some(&family),
            ),
            Some("get"),
            0,
        );
        let trait_get_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                trait_get_item,
                marker_in(source, "fn get<'a>(&'a self) -> Self::Item<'a>;", "'a"),
                WrittenUnitKind::TraitMember,
                1,
                Some(&trait_get),
            ),
            Some("'a"),
            0,
        );
        let bound_impl_item = marker_range(source, "impl Bound for Concrete {}");
        let bound_impl = written_with_anchor(
            DefinitionKind::Impl,
            bound_impl_item,
            marker_range(source, "impl Bound for Concrete"),
            WrittenUnitKind::Item,
            3,
            Some(&root),
        );
        let family_impl_item = marker_range(
            source,
            concat!(
                "impl Family for Concrete {\n",
                "    type Item<'a> = Concrete;\n\n",
                "    fn get<'a>(&'a self) -> Self::Item<'a> {\n",
                "        Concrete\n",
                "    }\n",
                "}",
            ),
        );
        let family_impl = written_with_anchor(
            DefinitionKind::Impl,
            family_impl_item,
            marker_range(source, "impl Family for Concrete"),
            WrittenUnitKind::Item,
            4,
            Some(&root),
        );
        let impl_type_item = marker_range(source, "type Item<'a> = Concrete;");
        let impl_type = named(
            written_with_anchor(
                DefinitionKind::AssociatedType,
                impl_type_item,
                marker_in(source, "type Item<'a> = Concrete;", "type Item<'a>"),
                WrittenUnitKind::ImplMember,
                0,
                Some(&family_impl),
            ),
            Some("Item"),
            0,
        );
        let impl_type_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                impl_type_item,
                marker_in(source, "type Item<'a> = Concrete;", "'a"),
                WrittenUnitKind::ImplMember,
                0,
                Some(&impl_type),
            ),
            Some("'a"),
            0,
        );
        let impl_get_text = "fn get<'a>(&'a self) -> Self::Item<'a> {\n        Concrete\n    }";
        let impl_get_item = marker_range(source, impl_get_text);
        let impl_get = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                impl_get_item,
                marker_in(
                    source,
                    impl_get_text,
                    "fn get<'a>(&'a self) -> Self::Item<'a>",
                ),
                WrittenUnitKind::ImplMember,
                1,
                Some(&family_impl),
            ),
            Some("get"),
            0,
        );
        let impl_get_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                impl_get_item,
                marker_in(source, impl_get_text, "'a"),
                WrittenUnitKind::ImplMember,
                1,
                Some(&impl_get),
            ),
            Some("'a"),
            0,
        );
        let capture_text = concat!(
            "fn capture<'a, T: Family>(value: T::Item<'a>) {\n",
            "    let _ = || &value;\n",
            "}",
        );
        let capture_item = marker_range(source, capture_text);
        let capture_header = "fn capture<'a, T: Family>(value: T::Item<'a>)";
        let capture = named(
            written_with_anchor(
                DefinitionKind::Function,
                capture_item,
                marker_range(source, capture_header),
                WrittenUnitKind::Item,
                5,
                Some(&root),
            ),
            Some("capture"),
            0,
        );
        let capture_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                capture_item,
                marker_in(source, "fn capture<'a, T: Family>", "'a"),
                WrittenUnitKind::Item,
                5,
                Some(&capture),
            ),
            Some("'a"),
            0,
        );
        let capture_type = named(
            written_with_anchor(
                DefinitionKind::TypeParameter,
                capture_item,
                marker_in(source, "fn capture<'a, T: Family>", "T"),
                WrittenUnitKind::Item,
                5,
                Some(&capture),
            ),
            Some("T"),
            0,
        );
        let closure = written_with_anchor(
            DefinitionKind::Closure,
            capture_item,
            marker_in(source, "let _ = || &value;", "||"),
            WrittenUnitKind::Item,
            5,
            Some(&capture),
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                6,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            bound,
            concrete,
            constructor,
            family,
            trait_type,
            trait_type_lifetime,
            trait_get,
            trait_get_lifetime,
            bound_impl,
            family_impl,
            impl_type,
            impl_type_lifetime,
            impl_get,
            impl_get_lifetime,
            capture,
            capture_lifetime,
            capture_type,
            closure,
            main,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_generic_associated_type_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let root = find_local(definitions, DefinitionKind::Crate, None);
        let bound = find_local(definitions, DefinitionKind::Trait, Some("Bound"));
        let concrete = find_local(definitions, DefinitionKind::Struct, Some("Concrete"));
        let constructor = child_of(definitions, DefinitionKind::Constructor, &concrete, None);
        let family = find_local(definitions, DefinitionKind::Trait, Some("Family"));
        let trait_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &family,
            Some("Item"),
        );
        let trait_type_lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &trait_type,
            Some("'a"),
        );
        let trait_get = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &family,
            Some("get"),
        );
        let trait_get_lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &trait_get,
            Some("'a"),
        );
        let bound_impl = find_local_with_anchor(
            definitions,
            DefinitionKind::Impl,
            marker_range(source, "impl Bound for Concrete"),
        );
        let family_impl = find_local_with_anchor(
            definitions,
            DefinitionKind::Impl,
            marker_range(source, "impl Family for Concrete"),
        );
        let impl_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &family_impl,
            Some("Item"),
        );
        let impl_type_lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &impl_type,
            Some("'a"),
        );
        let impl_get = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &family_impl,
            Some("get"),
        );
        let impl_get_lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &impl_get,
            Some("'a"),
        );
        let capture = find_local(definitions, DefinitionKind::Function, Some("capture"));
        let capture_lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &capture,
            Some("'a"),
        );
        let capture_type = child_of(
            definitions,
            DefinitionKind::TypeParameter,
            &capture,
            Some("T"),
        );
        let closure = child_of(definitions, DefinitionKind::Closure, &capture, None);
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let injected_std = find_local(definitions, DefinitionKind::ExternCrate, Some("std"));
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);
        let trait_get_header = "fn get<'a>(&'a self) -> Self::Item<'a>;";
        let impl_get_header = "fn get<'a>(&'a self) -> Self::Item<'a>";
        let impl_get_text = "fn get<'a>(&'a self) -> Self::Item<'a> {\n        Concrete\n    }";
        let capture_header = "fn capture<'a, T: Family>(value: T::Item<'a>)";

        BTreeSet::from([
            edge(
                &bound,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "trait Bound")],
            ),
            edge(
                &concrete,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "struct Concrete")],
            ),
            edge(
                &constructor,
                TargetRef::Local(concrete.clone()),
                DependencyKind::Parent,
                [marker_range(source, "struct Concrete")],
            ),
            edge(
                &family,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "trait Family")],
            ),
            edge(
                &trait_type,
                TargetRef::Local(family.clone()),
                DependencyKind::Parent,
                [marker_range(source, "type Item<'a>: Bound")],
            ),
            edge(
                &trait_type_lifetime,
                TargetRef::Local(trait_type.clone()),
                DependencyKind::Parent,
                [marker_in(source, "type Item<'a>: Bound", "'a")],
            ),
            edge(
                &trait_get,
                TargetRef::Local(family.clone()),
                DependencyKind::Parent,
                [marker_range(source, trait_get_header)],
            ),
            edge(
                &trait_get_lifetime,
                TargetRef::Local(trait_get.clone()),
                DependencyKind::Parent,
                [marker_in(source, trait_get_header, "'a")],
            ),
            edge(
                &bound_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "impl Bound for Concrete")],
            ),
            edge(
                &family_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "impl Family for Concrete")],
            ),
            edge(
                &impl_type,
                TargetRef::Local(family_impl.clone()),
                DependencyKind::Parent,
                [marker_in(
                    source,
                    "type Item<'a> = Concrete;",
                    "type Item<'a>",
                )],
            ),
            edge(
                &impl_type_lifetime,
                TargetRef::Local(impl_type.clone()),
                DependencyKind::Parent,
                [marker_in(source, "type Item<'a> = Concrete;", "'a")],
            ),
            edge(
                &impl_get,
                TargetRef::Local(family_impl.clone()),
                DependencyKind::Parent,
                [marker_in(source, impl_get_text, impl_get_header)],
            ),
            edge(
                &impl_get_lifetime,
                TargetRef::Local(impl_get.clone()),
                DependencyKind::Parent,
                [marker_in(source, impl_get_text, "'a")],
            ),
            edge(
                &capture,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, capture_header)],
            ),
            edge(
                &capture_lifetime,
                TargetRef::Local(capture.clone()),
                DependencyKind::Parent,
                [marker_in(source, "fn capture<'a, T: Family>", "'a")],
            ),
            edge(
                &capture_type,
                TargetRef::Local(capture.clone()),
                DependencyKind::Parent,
                [marker_in(source, "fn capture<'a, T: Family>", "T")],
            ),
            edge(
                &closure,
                TargetRef::Local(capture.clone()),
                DependencyKind::Parent,
                [marker_in(source, "let _ = || &value;", "||")],
            ),
            edge(
                &main,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn main()")],
            ),
            edge(
                &injected_std,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &injected_prelude,
                TargetRef::Local(root),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &trait_type,
                TargetRef::Local(bound),
                DependencyKind::AssociatedTypeBound,
                [marker_in(source, "type Item<'a>: Bound", "Bound")],
            ),
            edge(
                &trait_get,
                TargetRef::Local(family.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, trait_get_header, "self")],
            ),
            edge(
                &trait_get,
                TargetRef::Local(trait_get_lifetime.clone()),
                DependencyKind::SignatureType,
                [nth_marker_in(source, trait_get_header, "'a", 1)],
            ),
            edge(
                &trait_get,
                TargetRef::Local(family),
                DependencyKind::ReturnType,
                [nth_marker_in(source, trait_get_header, "Self", 0)],
            ),
            edge(
                &trait_get,
                TargetRef::Local(trait_type.clone()),
                DependencyKind::ReturnType,
                [marker_in(source, trait_get_header, "Item")],
            ),
            edge(
                &trait_get,
                TargetRef::Local(trait_get_lifetime),
                DependencyKind::ReturnType,
                [nth_marker_in(source, trait_get_header, "'a", 2)],
            ),
            edge(
                &impl_type,
                TargetRef::Local(concrete),
                DependencyKind::SignatureType,
                [marker_in(source, "type Item<'a> = Concrete;", "Concrete")],
            ),
            edge(
                &impl_get,
                TargetRef::Local(family_impl.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, impl_get_text, "self")],
            ),
            edge(
                &impl_get,
                TargetRef::Local(impl_get_lifetime.clone()),
                DependencyKind::SignatureType,
                [nth_marker_in(source, impl_get_text, "'a", 1)],
            ),
            edge(
                &impl_get,
                TargetRef::Local(family_impl),
                DependencyKind::ReturnType,
                [marker_in(source, impl_get_text, "Self")],
            ),
            edge(
                &impl_get,
                TargetRef::Local(impl_type),
                DependencyKind::ReturnType,
                [marker_in(source, impl_get_text, "Item")],
            ),
            edge(
                &impl_get,
                TargetRef::Local(impl_get_lifetime),
                DependencyKind::ReturnType,
                [nth_marker_in(source, impl_get_text, "'a", 2)],
            ),
            edge(
                &capture,
                TargetRef::Local(capture_lifetime),
                DependencyKind::SignatureType,
                [nth_marker_in(source, capture_header, "'a", 1)],
            ),
            edge(
                &capture,
                TargetRef::Local(capture_type.clone()),
                DependencyKind::SignatureType,
                [nth_marker_in(source, capture_header, "T", 1)],
            ),
            edge(
                &closure,
                TargetRef::Local(trait_type),
                DependencyKind::ClosureCaptureType,
                [marker_in(source, "let _ = || &value;", "value")],
            ),
            edge(
                &closure,
                TargetRef::Local(capture_type),
                DependencyKind::ClosureCaptureType,
                [marker_in(source, "let _ = || &value;", "value")],
            ),
        ])
    }

    fn expected_dynamic_trait_edges(source: &str) -> BTreeSet<EdgeRef> {
        let root = crate_root(source);
        let show_item = marker_range(source, "trait Show {}");
        let show = named(
            written_with_anchor(
                DefinitionKind::Trait,
                show_item,
                marker_range(source, "trait Show"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Show"),
            0,
        );
        let take_item = marker_range(source, "fn take(_: &dyn Show) {}");
        let take = named(
            written_with_anchor(
                DefinitionKind::Function,
                take_item,
                marker_range(source, "fn take(_: &dyn Show)"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("take"),
            0,
        );

        BTreeSet::from([edge(
            &take,
            TargetRef::Local(show),
            DependencyKind::SignatureType,
            [marker_in(source, "fn take(_: &dyn Show)", "Show")],
        )])
    }

    fn expected_dynamic_trait_capture_edges(source: &str) -> BTreeSet<EdgeRef> {
        let root = crate_root(source);
        let show_item = marker_range(source, "trait Show {}");
        let show = named(
            written_with_anchor(
                DefinitionKind::Trait,
                show_item,
                marker_range(source, "trait Show"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Show"),
            0,
        );
        let capture_text = concat!(
            "fn capture(value: &dyn Show) {\n",
            "    let _ = || value;\n",
            "}",
        );
        let capture_item = marker_range(source, capture_text);
        let capture_header = "fn capture(value: &dyn Show)";
        let capture = named(
            written_with_anchor(
                DefinitionKind::Function,
                capture_item,
                marker_range(source, capture_header),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("capture"),
            0,
        );
        let lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &capture,
            ),
            Some("'_"),
            0,
        );
        let closure = written_with_anchor(
            DefinitionKind::Closure,
            capture_item,
            marker_in(source, "let _ = || value;", "||"),
            WrittenUnitKind::Item,
            1,
            Some(&capture),
        );

        BTreeSet::from([
            edge(
                &capture,
                TargetRef::Local(show.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, capture_header, "Show")],
            ),
            edge(
                &capture,
                TargetRef::Local(lifetime),
                DependencyKind::SignatureType,
                [zero_width_before(source, capture_header, "dyn Show")],
            ),
            edge(
                &closure,
                TargetRef::Local(show),
                DependencyKind::ClosureCaptureType,
                [marker_in(source, "let _ = || value;", "value")],
            ),
        ])
    }

    fn expected_generic_parameter_edges(source: &str) -> BTreeSet<EdgeRef> {
        let root = crate_root(source);
        let type_caller_item = marker_range(
            source,
            "fn type_caller<U>(value: U) {\n    type_target(value);\n}",
        );
        let type_caller_header = "fn type_caller<U>(value: U)";
        let type_caller = named(
            written_with_anchor(
                DefinitionKind::Function,
                type_caller_item,
                marker_range(source, type_caller_header),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("type_caller"),
            0,
        );
        let type_parameter = named(
            written_with_anchor(
                DefinitionKind::TypeParameter,
                type_caller_item,
                marker_in(source, type_caller_header, "U"),
                WrittenUnitKind::Item,
                1,
                Some(&type_caller),
            ),
            Some("U"),
            0,
        );
        let const_caller_item = marker_range(
            source,
            concat!(
                "fn const_caller<const M: usize>(value: [u8; M]) {\n",
                "    const_target(value);\n",
                "}",
            ),
        );
        let const_caller_header = "fn const_caller<const M: usize>(value: [u8; M])";
        let const_caller = named(
            written_with_anchor(
                DefinitionKind::Function,
                const_caller_item,
                marker_range(source, const_caller_header),
                WrittenUnitKind::Item,
                3,
                Some(&root),
            ),
            Some("const_caller"),
            0,
        );
        let const_parameter = named(
            written_with_anchor(
                DefinitionKind::ConstParameter,
                const_caller_item,
                marker_in(source, const_caller_header, "const M: usize"),
                WrittenUnitKind::Item,
                3,
                Some(&const_caller),
            ),
            Some("M"),
            0,
        );

        BTreeSet::from([
            edge(
                &type_caller,
                TargetRef::Local(type_parameter),
                DependencyKind::ResolvedGenericArgument,
                [marker_in(source, "type_target(value)", "type_target")],
            ),
            edge(
                &const_caller,
                TargetRef::Local(const_parameter),
                DependencyKind::ResolvedGenericArgument,
                [marker_in(source, "const_target(value)", "const_target")],
            ),
        ])
    }

    fn expected_explicit_lifetime_edges(source: &str) -> BTreeSet<EdgeRef> {
        let root = crate_root(source);
        let hold_item = marker_range(source, "struct Hold<'a>(&'a u8);");
        let hold = named(
            written_with_anchor(
                DefinitionKind::Struct,
                hold_item,
                marker_range(source, "struct Hold<'a>"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Hold"),
            0,
        );
        let hold_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                hold_item,
                marker_in(source, "struct Hold<'a>", "'a"),
                WrittenUnitKind::Item,
                0,
                Some(&hold),
            ),
            Some("'a"),
            0,
        );
        let field = named(
            written_with_anchor(
                DefinitionKind::Field,
                hold_item,
                marker_in(source, "struct Hold<'a>(&'a u8);", "&'a u8"),
                WrittenUnitKind::Item,
                0,
                Some(&hold),
            ),
            Some("0"),
            0,
        );
        let borrow_item = marker_range(
            source,
            "fn borrow<'a>(value: &'a u8) -> &'a u8 {\n    value\n}",
        );
        let borrow_header = "fn borrow<'a>(value: &'a u8) -> &'a u8";
        let borrow = named(
            written_with_anchor(
                DefinitionKind::Function,
                borrow_item,
                marker_range(source, borrow_header),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("borrow"),
            0,
        );
        let borrow_lifetime = named(
            written_with_anchor(
                DefinitionKind::LifetimeParameter,
                borrow_item,
                marker_in(source, "fn borrow<'a>", "'a"),
                WrittenUnitKind::Item,
                1,
                Some(&borrow),
            ),
            Some("'a"),
            0,
        );

        BTreeSet::from([
            edge(
                &field,
                TargetRef::Local(hold_lifetime),
                DependencyKind::FieldType,
                [nth_marker_in(source, "struct Hold<'a>(&'a u8);", "'a", 1)],
            ),
            edge(
                &borrow,
                TargetRef::Local(borrow_lifetime.clone()),
                DependencyKind::SignatureType,
                [nth_marker_in(source, borrow_header, "'a", 1)],
            ),
            edge(
                &borrow,
                TargetRef::Local(borrow_lifetime),
                DependencyKind::ReturnType,
                [nth_marker_in(source, borrow_header, "'a", 2)],
            ),
        ])
    }

    fn edges_targeting_kind(edges: &BTreeSet<EdgeRef>, kind: DefinitionKind) -> BTreeSet<EdgeRef> {
        edges
            .iter()
            .filter(|edge| matches!(&edge.to, TargetRef::Local(target) if target.kind == kind))
            .cloned()
            .collect()
    }

    fn impl_key(graph: &DefinitionGraph, self_type: &str) -> DefinitionKey {
        graph
            .edges
            .iter()
            .filter(|edge| edge.kind == DependencyKind::ImplSelfType)
            .find_map(|edge| {
                let DefinitionTarget::Local(target) = edge.to else {
                    return None;
                };
                let target = &graph.definitions[target.0 as usize];
                let target_name = target.key.0.last().and_then(|part| part.name.as_deref());
                (target_name == Some(self_type))
                    .then(|| graph.definitions[edge.from.0 as usize].key.clone())
            })
            .expect("fixture must contain the requested inherent impl")
    }

    fn associated_function_key(graph: &DefinitionGraph, name: &str) -> DefinitionKey {
        let mut matches = graph.definitions.iter().filter(|definition| {
            definition.kind == DefinitionKind::AssociatedFunction
                && definition
                    .key
                    .0
                    .last()
                    .and_then(|part| part.name.as_deref())
                    == Some(name)
        });
        let definition = matches
            .next()
            .expect("fixture must contain the requested associated function");
        assert!(
            matches.next().is_none(),
            "associated function must be unique"
        );
        definition.key.clone()
    }

    fn expected_operator_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let use_item = named(
            written_with_anchor(
                DefinitionKind::Use,
                marker_range(source, "use core::ops::{Add, Index};"),
                marker_in(source, "use core::ops::{Add, Index};", "core::ops"),
                WrittenUnitKind::UseItem,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let add_use = named(
            written(
                DefinitionKind::Use,
                marker_in(source, "use core::ops::{Add, Index};", "Add"),
                WrittenUnitKind::UseLeaf,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let index_use = named(
            written(
                DefinitionKind::Use,
                marker_in(source, "use core::ops::{Add, Index};", "Index"),
                WrittenUnitKind::UseLeaf,
                1,
                Some(&root),
            ),
            None,
            0,
        );
        let number_item = marker_range(source, "struct Number(u8);");
        let number_anchor = marker_in(source, "struct Number(u8);", "struct Number");
        let number = named(
            written_with_anchor(
                DefinitionKind::Struct,
                number_item,
                number_anchor,
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Number"),
            0,
        );
        let number_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            number_item,
            number_anchor,
            WrittenUnitKind::Item,
            0,
            Some(&number),
        );
        let number_field = named(
            written_with_anchor(
                DefinitionKind::Field,
                number_item,
                marker_in(source, "struct Number(u8);", "u8"),
                WrittenUnitKind::Item,
                0,
                Some(&number),
            ),
            Some("0"),
            0,
        );
        let add_impl_item = marker_range(
            source,
            concat!(
                "impl Add for Number {\n",
                "    type Output = Number;\n\n",
                "    fn add(self, rhs: Number) -> Number {\n",
                "        Number(self.0 + rhs.0)\n",
                "    }\n",
                "}",
            ),
        );
        let add_impl = written_with_anchor(
            DefinitionKind::Impl,
            add_impl_item,
            marker_range(source, "impl Add for Number"),
            WrittenUnitKind::Item,
            1,
            Some(&root),
        );
        let add_output_item = nth_marker_range(source, "type Output = Number;", 0);
        let add_output = named(
            written_with_anchor(
                DefinitionKind::AssociatedType,
                add_output_item,
                nth_marker_range(source, "type Output", 0),
                WrittenUnitKind::ImplMember,
                0,
                Some(&add_impl),
            ),
            Some("Output"),
            0,
        );
        let add_member_item = marker_range(
            source,
            "fn add(self, rhs: Number) -> Number {\n        Number(self.0 + rhs.0)\n    }",
        );
        let add_member = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                add_member_item,
                marker_range(source, "fn add(self, rhs: Number) -> Number"),
                WrittenUnitKind::ImplMember,
                1,
                Some(&add_impl),
            ),
            Some("add"),
            0,
        );
        let values_item = marker_range(source, "struct Values([u8; 1]);");
        let values_anchor = marker_in(source, "struct Values([u8; 1]);", "struct Values");
        let values = named(
            written_with_anchor(
                DefinitionKind::Struct,
                values_item,
                values_anchor,
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("Values"),
            0,
        );
        let values_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            values_item,
            values_anchor,
            WrittenUnitKind::Item,
            2,
            Some(&values),
        );
        let values_field = named(
            written_with_anchor(
                DefinitionKind::Field,
                values_item,
                marker_in(source, "struct Values([u8; 1]);", "[u8; 1]"),
                WrittenUnitKind::Item,
                2,
                Some(&values),
            ),
            Some("0"),
            0,
        );
        let array_length = written_with_anchor(
            DefinitionKind::AnonymousConst,
            values_item,
            marker_in(source, "struct Values([u8; 1]);", "1"),
            WrittenUnitKind::Item,
            2,
            Some(&values_field),
        );
        let index_impl_item = marker_range(
            source,
            concat!(
                "impl Index<usize> for Values {\n",
                "    type Output = u8;\n\n",
                "    fn index(&self, index: usize) -> &u8 {\n",
                "        &self.0[index]\n",
                "    }\n",
                "}",
            ),
        );
        let index_impl = named(
            written_with_anchor(
                DefinitionKind::Impl,
                index_impl_item,
                marker_range(source, "impl Index<usize> for Values"),
                WrittenUnitKind::Item,
                3,
                Some(&root),
            ),
            None,
            0,
        );
        let index_output_item = nth_marker_range(source, "type Output = u8;", 0);
        let index_output = named(
            written_with_anchor(
                DefinitionKind::AssociatedType,
                index_output_item,
                nth_marker_range(source, "type Output", 1),
                WrittenUnitKind::ImplMember,
                2,
                Some(&index_impl),
            ),
            Some("Output"),
            0,
        );
        let index_member_item = marker_range(
            source,
            "fn index(&self, index: usize) -> &u8 {\n        &self.0[index]\n    }",
        );
        let index_member = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                index_member_item,
                marker_range(source, "fn index(&self, index: usize) -> &u8"),
                WrittenUnitKind::ImplMember,
                3,
                Some(&index_impl),
            ),
            Some("index"),
            0,
        );
        let index_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &index_member,
            ),
            Some("'_"),
            0,
        );
        let call_item = marker_range(
            source,
            "fn call<F: Fn(u8) -> u8>(function: F) -> u8 {\n    function(1)\n}",
        );
        let call = named(
            written_with_anchor(
                DefinitionKind::Function,
                call_item,
                marker_range(source, "fn call<F: Fn(u8) -> u8>(function: F) -> u8"),
                WrittenUnitKind::Item,
                4,
                Some(&root),
            ),
            Some("call"),
            0,
        );
        let function_parameter = named(
            written_with_anchor(
                DefinitionKind::TypeParameter,
                call_item,
                marker_in(source, "fn call<F: Fn(u8) -> u8>(function: F) -> u8", "F"),
                WrittenUnitKind::Item,
                4,
                Some(&call),
            ),
            Some("F"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                5,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let closure = written_with_anchor(
            DefinitionKind::Closure,
            main_item,
            marker_range(source, "|value|"),
            WrittenUnitKind::Item,
            5,
            Some(&main),
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            use_item,
            add_use,
            index_use,
            number,
            number_constructor,
            number_field,
            add_impl,
            add_output,
            add_member,
            values,
            values_constructor,
            values_field,
            array_length,
            index_impl,
            index_output,
            index_member,
            index_lifetime,
            call,
            function_parameter,
            main,
            closure,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_operator_target_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let call = find_local(definitions, DefinitionKind::Function, Some("call"));

        BTreeSet::from([
            edge(
                &main,
                TargetRef::External(external("core", "std::ops::Add::add")),
                DependencyKind::OverloadedOperator,
                [marker_in(source, "Number(1) + Number(2)", "+")],
            ),
            edge(
                &main,
                TargetRef::External(external("core", "std::ops::Index::index")),
                DependencyKind::IndexTarget,
                [marker_in(source, "Values([3])[0]", "[0]")],
            ),
            edge(
                &call,
                TargetRef::External(external("core", "std::ops::Fn::call")),
                DependencyKind::CallableTrait,
                [marker_range(source, "function(1)")],
            ),
        ])
    }
    fn expected_declaration_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let limit_item = marker_range(source, "const LIMIT: usize = 3;");
        let limit = named(
            written_with_anchor(
                DefinitionKind::Const,
                limit_item,
                marker_range(source, "const LIMIT: usize"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("LIMIT"),
            0,
        );
        let tag_value_item = marker_range(source, "const TAG: isize = 1;");
        let tag_value = named(
            written_with_anchor(
                DefinitionKind::Const,
                tag_value_item,
                marker_range(source, "const TAG: isize"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("TAG"),
            0,
        );
        let marker_item = marker_range(source, "trait Marker {}");
        let marker = named(
            written_with_anchor(
                DefinitionKind::Trait,
                marker_item,
                marker_range(source, "trait Marker"),
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("Marker"),
            0,
        );
        let default_item = marker_range(source, "struct DefaultType;");
        let default_anchor = marker_range(source, "struct DefaultType");
        let default_type = named(
            written_with_anchor(
                DefinitionKind::Struct,
                default_item,
                default_anchor,
                WrittenUnitKind::Item,
                3,
                Some(&root),
            ),
            Some("DefaultType"),
            0,
        );
        let default_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            default_item,
            default_anchor,
            WrittenUnitKind::Item,
            3,
            Some(&default_type),
        );
        let marker_impl_item = marker_range(source, "impl Marker for DefaultType {}");
        let marker_impl = written_with_anchor(
            DefinitionKind::Impl,
            marker_impl_item,
            marker_range(source, "impl Marker for DefaultType"),
            WrittenUnitKind::Item,
            4,
            Some(&root),
        );
        let container_item = marker_range(
            source,
            concat!(
                "struct Container<T: Marker = DefaultType, const N: usize = LIMIT> {\n",
                "    pub(crate) value: T,\n",
                "}",
            ),
        );
        let container_header = "struct Container<T: Marker = DefaultType, const N: usize = LIMIT>";
        let container = named(
            written_with_anchor(
                DefinitionKind::Struct,
                container_item,
                marker_range(source, container_header),
                WrittenUnitKind::Item,
                5,
                Some(&root),
            ),
            Some("Container"),
            0,
        );
        let type_parameter = named(
            written_with_anchor(
                DefinitionKind::TypeParameter,
                container_item,
                marker_in(source, container_header, "T: Marker = DefaultType"),
                WrittenUnitKind::Item,
                5,
                Some(&container),
            ),
            Some("T"),
            0,
        );
        let const_parameter = named(
            written_with_anchor(
                DefinitionKind::ConstParameter,
                container_item,
                marker_in(source, container_header, "const N: usize = LIMIT"),
                WrittenUnitKind::Item,
                5,
                Some(&container),
            ),
            Some("N"),
            0,
        );
        let default_constant = written_with_anchor(
            DefinitionKind::AnonymousConst,
            container_item,
            marker_in(source, container_header, "LIMIT"),
            WrittenUnitKind::Item,
            5,
            Some(&container),
        );
        let value_field = named(
            written_with_anchor(
                DefinitionKind::Field,
                container_item,
                marker_range(source, "pub(crate) value: T"),
                WrittenUnitKind::Item,
                5,
                Some(&container),
            ),
            Some("value"),
            0,
        );
        let tag_item = marker_range(source, "enum Tag {\n    First = TAG,\n}");
        let tag = named(
            written_with_anchor(
                DefinitionKind::Enum,
                tag_item,
                marker_range(source, "enum Tag"),
                WrittenUnitKind::Item,
                6,
                Some(&root),
            ),
            Some("Tag"),
            0,
        );
        let first = named(
            written_with_anchor(
                DefinitionKind::Variant,
                tag_item,
                marker_in(source, "First = TAG", "First"),
                WrittenUnitKind::Item,
                6,
                Some(&tag),
            ),
            Some("First"),
            0,
        );
        let first_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            tag_item,
            marker_in(source, "First = TAG", "First"),
            WrittenUnitKind::Item,
            6,
            Some(&first),
        );
        let discriminant = written_with_anchor(
            DefinitionKind::AnonymousConst,
            tag_item,
            marker_in(source, "First = TAG", "TAG"),
            WrittenUnitKind::Item,
            6,
            Some(&first),
        );
        let choice_item = marker_range(source, "enum Choice {\n    Second { value: u8 },\n}");
        let choice = named(
            written_with_anchor(
                DefinitionKind::Enum,
                choice_item,
                marker_range(source, "enum Choice"),
                WrittenUnitKind::Item,
                7,
                Some(&root),
            ),
            Some("Choice"),
            0,
        );
        let second = named(
            written_with_anchor(
                DefinitionKind::Variant,
                choice_item,
                marker_in(source, "Second { value: u8 }", "Second"),
                WrittenUnitKind::Item,
                7,
                Some(&choice),
            ),
            Some("Second"),
            0,
        );
        let second_field = named(
            written_with_anchor(
                DefinitionKind::Field,
                choice_item,
                marker_in(source, "Second { value: u8 }", "value: u8"),
                WrittenUnitKind::Item,
                7,
                Some(&second),
            ),
            Some("value"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                8,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            limit,
            tag_value,
            marker,
            default_type,
            default_constructor,
            marker_impl,
            container,
            type_parameter,
            const_parameter,
            default_constant,
            value_field,
            tag,
            first,
            first_constructor,
            discriminant,
            choice,
            second,
            second_field,
            main,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_declaration_target_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let root = find_local(definitions, DefinitionKind::Crate, None);
        let marker = find_local(definitions, DefinitionKind::Trait, Some("Marker"));
        let default_type = find_local(definitions, DefinitionKind::Struct, Some("DefaultType"));
        let container = find_local(definitions, DefinitionKind::Struct, Some("Container"));
        let type_parameter = child_of(
            definitions,
            DefinitionKind::TypeParameter,
            &container,
            Some("T"),
        );
        let const_parameter = child_of(
            definitions,
            DefinitionKind::ConstParameter,
            &container,
            Some("N"),
        );
        let default_constant = child_of(
            definitions,
            DefinitionKind::AnonymousConst,
            &container,
            None,
        );
        let value_field = child_of(
            definitions,
            DefinitionKind::Field,
            &container,
            Some("value"),
        );
        let tag = find_local(definitions, DefinitionKind::Enum, Some("Tag"));
        let first = child_of(definitions, DefinitionKind::Variant, &tag, Some("First"));
        let discriminant = child_of(definitions, DefinitionKind::AnonymousConst, &first, None);
        let choice = find_local(definitions, DefinitionKind::Enum, Some("Choice"));
        let second = child_of(
            definitions,
            DefinitionKind::Variant,
            &choice,
            Some("Second"),
        );
        let second_field = child_of(definitions, DefinitionKind::Field, &second, Some("value"));
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let container_header = "struct Container<T: Marker = DefaultType, const N: usize = LIMIT>";

        BTreeSet::from([
            edge(
                &container,
                TargetRef::Local(marker),
                DependencyKind::Predicate,
                [marker_in(source, container_header, "Marker")],
            ),
            edge(
                &container,
                TargetRef::Local(type_parameter.clone()),
                DependencyKind::Predicate,
                [marker_in(source, container_header, "T")],
            ),
            edge(
                &type_parameter,
                TargetRef::Local(default_type),
                DependencyKind::GenericDefault,
                [marker_in(source, container_header, "DefaultType")],
            ),
            edge(
                &const_parameter,
                TargetRef::Local(default_constant),
                DependencyKind::GenericDefault,
                [marker_in(source, container_header, "LIMIT")],
            ),
            edge(
                &value_field,
                TargetRef::Local(root),
                DependencyKind::VisibilityPath,
                [marker_in(source, "pub(crate) value: T", "pub(crate)")],
            ),
            edge(
                &first,
                TargetRef::Local(discriminant),
                DependencyKind::Discriminant,
                [marker_in(source, "First = TAG", "TAG")],
            ),
            edge(
                &main,
                TargetRef::Local(second_field),
                DependencyKind::FieldTarget,
                [
                    marker_in(source, "Choice::Second { value }", "value"),
                    marker_in(source, "Choice::Second { value: 1 }", "value"),
                ],
            ),
        ])
    }
    fn expected_async_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let direct_item = marker_range(source, "async fn direct() {}");
        let direct = named(
            written_with_anchor(
                DefinitionKind::Function,
                direct_item,
                marker_range(source, "async fn direct()"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("direct"),
            0,
        );
        let direct_opaque = generated(
            DefinitionKind::OpaqueType,
            GeneratedRole::OpaqueType,
            0,
            &direct,
        );
        let direct_coroutine = generated(
            DefinitionKind::Coroutine,
            GeneratedRole::Coroutine,
            0,
            &direct,
        );
        let macro_item = marker_range(
            source,
            concat!(
                "macro_rules! make_async {\n",
                "    () => {\n",
                "        async fn generated() {}\n",
                "    };\n",
                "}",
            ),
        );
        let macro_definition = named(
            written_with_anchor(
                DefinitionKind::Macro,
                macro_item,
                marker_range(source, "macro_rules! make_async"),
                WrittenUnitKind::MacroDefinition,
                0,
                Some(&root),
            ),
            Some("make_async"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let async_block = written_with_anchor(
            DefinitionKind::Coroutine,
            main_item,
            marker_in(source, "let _ = async {};", "async"),
            WrittenUnitKind::Item,
            1,
            Some(&main),
        );
        let invocation = marker_range(source, "make_async!();");
        let generated_function = named(
            expanded(DefinitionKind::Function, invocation, None, 0, Some(&root)),
            Some("generated"),
            0,
        );
        let generated_opaque = expanded(
            DefinitionKind::OpaqueType,
            invocation,
            Some(GeneratedRole::OpaqueType),
            0,
            Some(&generated_function),
        );
        let generated_coroutine = expanded(
            DefinitionKind::Coroutine,
            invocation,
            Some(GeneratedRole::Coroutine),
            0,
            Some(&generated_function),
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            direct,
            direct_opaque,
            direct_coroutine,
            macro_definition,
            main,
            async_block,
            generated_function,
            generated_opaque,
            generated_coroutine,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_async_structure_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let root = find_local(definitions, DefinitionKind::Crate, None);
        let direct = find_local(definitions, DefinitionKind::Function, Some("direct"));
        let direct_opaque = child_of(definitions, DefinitionKind::OpaqueType, &direct, None);
        let direct_coroutine = child_of(definitions, DefinitionKind::Coroutine, &direct, None);
        let macro_definition = find_local(definitions, DefinitionKind::Macro, Some("make_async"));
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let async_block = child_of(definitions, DefinitionKind::Coroutine, &main, None);
        let generated_function =
            find_local(definitions, DefinitionKind::Function, Some("generated"));
        let generated_opaque = child_of(
            definitions,
            DefinitionKind::OpaqueType,
            &generated_function,
            None,
        );
        let generated_coroutine = child_of(
            definitions,
            DefinitionKind::Coroutine,
            &generated_function,
            None,
        );
        let injected_std = find_local(definitions, DefinitionKind::ExternCrate, Some("std"));
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);
        let invocation = marker_range(source, "make_async!();");

        BTreeSet::from([
            edge(
                &direct,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "async fn direct()")],
            ),
            edge(
                &direct_opaque,
                TargetRef::Local(direct.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &direct_coroutine,
                TargetRef::Local(direct),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &macro_definition,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "macro_rules! make_async")],
            ),
            edge(
                &main,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn main()")],
            ),
            edge(
                &async_block,
                TargetRef::Local(main),
                DependencyKind::Parent,
                [marker_in(source, "let _ = async {};", "async")],
            ),
            edge(
                &generated_function,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &generated_opaque,
                TargetRef::Local(generated_function.clone()),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &generated_coroutine,
                TargetRef::Local(generated_function),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &root,
                TargetRef::Local(macro_definition),
                DependencyKind::MacroPath,
                [marker_range(source, "make_async!()")],
            ),
            edge(
                &injected_std,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &injected_prelude,
                TargetRef::Local(root),
                DependencyKind::Parent,
                [],
            ),
        ])
    }

    fn expected_derive_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let item = marker_range(source, "#[derive(Clone)]\nstruct Derived;");
        let item_anchor = marker_range(source, "struct Derived");
        let derived = named(
            written_with_anchor(
                DefinitionKind::Struct,
                item,
                item_anchor,
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Derived"),
            0,
        );
        let constructor = written_with_anchor(
            DefinitionKind::Constructor,
            item,
            item_anchor,
            WrittenUnitKind::Item,
            0,
            Some(&derived),
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                1,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let invocation = marker_range(source, "#[derive(Clone)]");
        let clone_impl = expanded(DefinitionKind::Impl, invocation, None, 0, Some(&root));
        let clone = named(
            expanded(
                DefinitionKind::AssociatedFunction,
                invocation,
                None,
                0,
                Some(&clone_impl),
            ),
            Some("clone"),
            0,
        );
        let lifetime = named(
            expanded(
                DefinitionKind::LifetimeParameter,
                invocation,
                Some(GeneratedRole::ElidedLifetime),
                0,
                Some(&clone),
            ),
            Some("'_"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            derived,
            constructor,
            main,
            clone_impl,
            clone,
            lifetime,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_derive_structure_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let root = find_local(definitions, DefinitionKind::Crate, None);
        let derived = find_local(definitions, DefinitionKind::Struct, Some("Derived"));
        let constructor = child_of(definitions, DefinitionKind::Constructor, &derived, None);
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let clone_impl = find_local(definitions, DefinitionKind::Impl, None);
        let clone = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &clone_impl,
            Some("clone"),
        );
        let lifetime = child_of(
            definitions,
            DefinitionKind::LifetimeParameter,
            &clone,
            Some("'_"),
        );
        let injected_std = find_local(definitions, DefinitionKind::ExternCrate, Some("std"));
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);
        let invocation = marker_range(source, "#[derive(Clone)]");
        let item_anchor = marker_range(source, "struct Derived");

        BTreeSet::from([
            edge(
                &derived,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [item_anchor],
            ),
            edge(
                &constructor,
                TargetRef::Local(derived.clone()),
                DependencyKind::Parent,
                [item_anchor],
            ),
            edge(
                &main,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn main()")],
            ),
            edge(
                &clone_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &clone,
                TargetRef::Local(clone_impl),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &lifetime,
                TargetRef::Local(clone),
                DependencyKind::Parent,
                [invocation],
            ),
            edge(
                &derived,
                TargetRef::External(external("core", "std::clone::Clone")),
                DependencyKind::MacroPath,
                [invocation],
            ),
            edge(
                &derived,
                TargetRef::External(external("core", "std::derive")),
                DependencyKind::MacroPath,
                [invocation],
            ),
            edge(
                &injected_std,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &injected_prelude,
                TargetRef::Local(root),
                DependencyKind::Parent,
                [],
            ),
        ])
    }

    fn expected_macro_import_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let value = find_local(definitions, DefinitionKind::Macro, Some("value"));
        let unused = find_local(definitions, DefinitionKind::Macro, Some("unused"));
        let origin_unused_site =
            marker_in(source, "pub(crate) use unused as unused_first;", "unused");
        let origin_value_site = marker_in(source, "pub(crate) use value as first;", "value");
        let origin_unused =
            find_local_with_anchor(definitions, DefinitionKind::Use, origin_unused_site);
        let origin_value =
            find_local_with_anchor(definitions, DefinitionKind::Use, origin_value_site);

        let facade_statement = concat!(
            "pub(crate) use crate::origin::{first as second, ",
            "unused_first as unused_second};",
        );
        let facade_value_site = marker_in(source, facade_statement, "first");
        let facade_unused_site = marker_in(source, facade_statement, "unused_first");
        let facade_value =
            find_local_with_anchor(definitions, DefinitionKind::Use, facade_value_site);
        let facade_unused =
            find_local_with_anchor(definitions, DefinitionKind::Use, facade_unused_site);

        let local_statement =
            "use crate::facade::{second as local_alias, unused_second as unused_alias};";
        let local_value_site = marker_in(source, local_statement, "second");
        let local_unused_site = marker_in(source, local_statement, "unused_second");
        let local_value =
            find_local_with_anchor(definitions, DefinitionKind::Use, local_value_site);
        let local_unused =
            find_local_with_anchor(definitions, DefinitionKind::Use, local_unused_site);

        let std_statement = "use std::{println as print_alias, vec as unused_std_alias};";
        let print_site = marker_in(source, std_statement, "println");
        let vec_site = marker_in(source, std_statement, "vec");
        let print_use = find_local_with_anchor(definitions, DefinitionKind::Use, print_site);
        let vec_use = find_local_with_anchor(definitions, DefinitionKind::Use, vec_site);

        let prefix_site = marker_in(
            source,
            "use crate::facade as facade_alias;",
            "crate::facade",
        );
        let prefix_use = find_local_with_anchor(definitions, DefinitionKind::Use, prefix_site);
        let run = find_local(definitions, DefinitionKind::Function, Some("run"));
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let prefix_call = "facade_alias::second!()";
        let prefix_macro_site = marker_in(source, prefix_call, "second");
        let prefix_module_site = marker_in(source, prefix_call, "facade_alias");
        let local_call = "local_alias!()";
        let local_call_site = marker_in(source, local_call, "local_alias");
        let print_call = marker_range(source, "print_alias!(\"alias\")");
        let prelude_call = marker_range(source, "println!(\"prelude\")");

        BTreeSet::from([
            edge(
                &origin_unused,
                TargetRef::Local(unused.clone()),
                DependencyKind::MacroPath,
                [origin_unused_site],
            ),
            edge(
                &origin_value,
                TargetRef::Local(value.clone()),
                DependencyKind::MacroPath,
                [origin_value_site],
            ),
            edge(
                &facade_value,
                TargetRef::Local(value.clone()),
                DependencyKind::MacroPath,
                [facade_value_site],
            ),
            edge(
                &facade_value,
                TargetRef::Local(origin_value.clone()),
                DependencyKind::ImportLeaf,
                [facade_value_site],
            ),
            edge(
                &facade_unused,
                TargetRef::Local(unused.clone()),
                DependencyKind::MacroPath,
                [facade_unused_site],
            ),
            edge(
                &facade_unused,
                TargetRef::Local(origin_unused.clone()),
                DependencyKind::ImportLeaf,
                [facade_unused_site],
            ),
            edge(
                &local_value,
                TargetRef::Local(value.clone()),
                DependencyKind::MacroPath,
                [local_value_site],
            ),
            edge(
                &local_value,
                TargetRef::Local(origin_value.clone()),
                DependencyKind::ImportLeaf,
                [local_value_site],
            ),
            edge(
                &local_value,
                TargetRef::Local(facade_value.clone()),
                DependencyKind::ImportLeaf,
                [local_value_site],
            ),
            edge(
                &local_unused,
                TargetRef::Local(unused),
                DependencyKind::MacroPath,
                [local_unused_site],
            ),
            edge(
                &local_unused,
                TargetRef::Local(origin_unused.clone()),
                DependencyKind::ImportLeaf,
                [local_unused_site],
            ),
            edge(
                &local_unused,
                TargetRef::Local(facade_unused),
                DependencyKind::ImportLeaf,
                [local_unused_site],
            ),
            edge(
                &print_use,
                TargetRef::External(external("std", "std::println")),
                DependencyKind::MacroPath,
                [print_site],
            ),
            edge(
                &vec_use,
                TargetRef::External(external("alloc", "std::vec")),
                DependencyKind::MacroPath,
                [vec_site],
            ),
            edge(
                &run,
                TargetRef::Local(value.clone()),
                DependencyKind::MacroPath,
                [marker_range(source, prefix_call)],
            ),
            edge(
                &run,
                TargetRef::Local(origin_value.clone()),
                DependencyKind::ImportLeaf,
                [prefix_macro_site],
            ),
            edge(
                &run,
                TargetRef::Local(facade_value.clone()),
                DependencyKind::ImportLeaf,
                [prefix_macro_site],
            ),
            edge(
                &run,
                TargetRef::Local(prefix_use),
                DependencyKind::ImportLeaf,
                [prefix_module_site],
            ),
            edge(
                &main,
                TargetRef::Local(value),
                DependencyKind::MacroPath,
                [marker_range(source, local_call)],
            ),
            edge(
                &main,
                TargetRef::Local(origin_value),
                DependencyKind::ImportLeaf,
                [local_call_site],
            ),
            edge(
                &main,
                TargetRef::Local(facade_value),
                DependencyKind::ImportLeaf,
                [local_call_site],
            ),
            edge(
                &main,
                TargetRef::Local(local_value),
                DependencyKind::ImportLeaf,
                [local_call_site],
            ),
            edge(
                &main,
                TargetRef::Local(print_use),
                DependencyKind::ImportLeaf,
                [marker_in(source, "print_alias!(\"alias\")", "print_alias")],
            ),
            edge(
                &main,
                TargetRef::External(external("core", "std::format_args_nl")),
                DependencyKind::MacroPath,
                [print_call, prelude_call],
            ),
            edge(
                &main,
                TargetRef::External(external("std", "std::println")),
                DependencyKind::MacroPath,
                [print_call, prelude_call],
            ),
        ])
    }

    fn expected_return_position_impl_trait_definitions(source: &str) -> BTreeSet<LocalRef> {
        let root = crate_root(source);
        let trait_item = marker_range(
            source,
            "trait T {\n    fn a() -> impl Copy;\n    fn b() -> impl Copy;\n}",
        );
        let trait_definition = named(
            written_with_anchor(
                DefinitionKind::Trait,
                trait_item,
                marker_range(source, "trait T"),
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("T"),
            0,
        );
        let trait_a_range = marker_range(source, "fn a() -> impl Copy;");
        let trait_a = named(
            written(
                DefinitionKind::AssociatedFunction,
                trait_a_range,
                WrittenUnitKind::TraitMember,
                0,
                Some(&trait_definition),
            ),
            Some("a"),
            0,
        );
        let trait_a_opaque = written_with_anchor(
            DefinitionKind::OpaqueType,
            trait_a_range,
            marker_in(source, "fn a() -> impl Copy;", "impl Copy"),
            WrittenUnitKind::TraitMember,
            0,
            Some(&trait_a),
        );
        let trait_a_associated_type = named(
            generated(
                DefinitionKind::AssociatedType,
                GeneratedRole::AnonymousAssociatedType,
                0,
                &trait_definition,
            ),
            Some("a"),
            0,
        );
        let trait_b_range = marker_range(source, "fn b() -> impl Copy;");
        let trait_b = named(
            written(
                DefinitionKind::AssociatedFunction,
                trait_b_range,
                WrittenUnitKind::TraitMember,
                1,
                Some(&trait_definition),
            ),
            Some("b"),
            0,
        );
        let trait_b_opaque = written_with_anchor(
            DefinitionKind::OpaqueType,
            trait_b_range,
            marker_in(source, "fn b() -> impl Copy;", "impl Copy"),
            WrittenUnitKind::TraitMember,
            1,
            Some(&trait_b),
        );
        let trait_b_associated_type = named(
            generated(
                DefinitionKind::AssociatedType,
                GeneratedRole::AnonymousAssociatedType,
                0,
                &trait_definition,
            ),
            Some("b"),
            0,
        );
        let impl_item = marker_range(
            source,
            concat!(
                "impl T for () {\n",
                "    fn a() -> impl Copy {\n",
                "        1_u8\n",
                "    }\n\n",
                "    fn b() -> impl Copy {\n",
                "        2_u8\n",
                "    }\n",
                "}",
            ),
        );
        let impl_definition = written_with_anchor(
            DefinitionKind::Impl,
            impl_item,
            marker_range(source, "impl T for ()"),
            WrittenUnitKind::Item,
            1,
            Some(&root),
        );
        let impl_a_text = "fn a() -> impl Copy {\n        1_u8\n    }";
        let impl_a_range = marker_range(source, impl_a_text);
        let impl_a = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                impl_a_range,
                marker_in(source, impl_a_text, "fn a() -> impl Copy"),
                WrittenUnitKind::ImplMember,
                0,
                Some(&impl_definition),
            ),
            Some("a"),
            0,
        );
        let impl_a_opaque = written_with_anchor(
            DefinitionKind::OpaqueType,
            impl_a_range,
            marker_in(source, impl_a_text, "impl Copy"),
            WrittenUnitKind::ImplMember,
            0,
            Some(&impl_a),
        );
        let impl_a_associated_type = named(
            generated(
                DefinitionKind::AssociatedType,
                GeneratedRole::AnonymousAssociatedType,
                0,
                &impl_definition,
            ),
            Some("a"),
            0,
        );
        let impl_b_text = "fn b() -> impl Copy {\n        2_u8\n    }";
        let impl_b_range = marker_range(source, impl_b_text);
        let impl_b = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                impl_b_range,
                marker_in(source, impl_b_text, "fn b() -> impl Copy"),
                WrittenUnitKind::ImplMember,
                1,
                Some(&impl_definition),
            ),
            Some("b"),
            0,
        );
        let impl_b_opaque = written_with_anchor(
            DefinitionKind::OpaqueType,
            impl_b_range,
            marker_in(source, impl_b_text, "impl Copy"),
            WrittenUnitKind::ImplMember,
            1,
            Some(&impl_b),
        );
        let impl_b_associated_type = named(
            generated(
                DefinitionKind::AssociatedType,
                GeneratedRole::AnonymousAssociatedType,
                0,
                &impl_definition,
            ),
            Some("b"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                marker_range(source, "fn main()"),
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            root,
            trait_definition,
            trait_a,
            trait_a_opaque,
            trait_a_associated_type,
            trait_b,
            trait_b_opaque,
            trait_b_associated_type,
            impl_definition,
            impl_a,
            impl_a_opaque,
            impl_a_associated_type,
            impl_b,
            impl_b_opaque,
            impl_b_associated_type,
            main,
            injected_std,
            injected_prelude,
        ])
    }

    fn expected_return_position_impl_trait_parent_edges(
        source: &str,
        definitions: &BTreeSet<LocalRef>,
    ) -> BTreeSet<EdgeRef> {
        let root = find_local(definitions, DefinitionKind::Crate, None);
        let trait_definition = find_local(definitions, DefinitionKind::Trait, Some("T"));
        let trait_a = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &trait_definition,
            Some("a"),
        );
        let trait_a_opaque = child_of(definitions, DefinitionKind::OpaqueType, &trait_a, None);
        let trait_a_associated_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &trait_definition,
            Some("a"),
        );
        let trait_b = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &trait_definition,
            Some("b"),
        );
        let trait_b_opaque = child_of(definitions, DefinitionKind::OpaqueType, &trait_b, None);
        let trait_b_associated_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &trait_definition,
            Some("b"),
        );
        let impl_definition = find_local(definitions, DefinitionKind::Impl, None);
        let impl_a = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &impl_definition,
            Some("a"),
        );
        let impl_a_opaque = child_of(definitions, DefinitionKind::OpaqueType, &impl_a, None);
        let impl_a_associated_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &impl_definition,
            Some("a"),
        );
        let impl_b = child_of(
            definitions,
            DefinitionKind::AssociatedFunction,
            &impl_definition,
            Some("b"),
        );
        let impl_b_opaque = child_of(definitions, DefinitionKind::OpaqueType, &impl_b, None);
        let impl_b_associated_type = child_of(
            definitions,
            DefinitionKind::AssociatedType,
            &impl_definition,
            Some("b"),
        );
        let main = find_local(definitions, DefinitionKind::Function, Some("main"));
        let injected_std = find_local(definitions, DefinitionKind::ExternCrate, Some("std"));
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        BTreeSet::from([
            edge(
                &trait_definition,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "trait T")],
            ),
            edge(
                &trait_a,
                TargetRef::Local(trait_definition.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn a() -> impl Copy;")],
            ),
            edge(
                &trait_a_opaque,
                TargetRef::Local(trait_a),
                DependencyKind::Parent,
                [marker_in(source, "fn a() -> impl Copy;", "impl Copy")],
            ),
            edge(
                &trait_a_associated_type,
                TargetRef::Local(trait_definition.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &trait_b,
                TargetRef::Local(trait_definition.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn b() -> impl Copy;")],
            ),
            edge(
                &trait_b_opaque,
                TargetRef::Local(trait_b),
                DependencyKind::Parent,
                [marker_in(source, "fn b() -> impl Copy;", "impl Copy")],
            ),
            edge(
                &trait_b_associated_type,
                TargetRef::Local(trait_definition),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &impl_definition,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "impl T for ()")],
            ),
            edge(
                &impl_a,
                TargetRef::Local(impl_definition.clone()),
                DependencyKind::Parent,
                [marker_in(
                    source,
                    "fn a() -> impl Copy {\n        1_u8\n    }",
                    "fn a() -> impl Copy",
                )],
            ),
            edge(
                &impl_a_opaque,
                TargetRef::Local(impl_a),
                DependencyKind::Parent,
                [marker_in(
                    source,
                    "fn a() -> impl Copy {\n        1_u8\n    }",
                    "impl Copy",
                )],
            ),
            edge(
                &impl_a_associated_type,
                TargetRef::Local(impl_definition.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &impl_b,
                TargetRef::Local(impl_definition.clone()),
                DependencyKind::Parent,
                [marker_in(
                    source,
                    "fn b() -> impl Copy {\n        2_u8\n    }",
                    "fn b() -> impl Copy",
                )],
            ),
            edge(
                &impl_b_opaque,
                TargetRef::Local(impl_b),
                DependencyKind::Parent,
                [marker_in(
                    source,
                    "fn b() -> impl Copy {\n        2_u8\n    }",
                    "impl Copy",
                )],
            ),
            edge(
                &impl_b_associated_type,
                TargetRef::Local(impl_definition),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &main,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [marker_range(source, "fn main()")],
            ),
            edge(
                &injected_std,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &injected_prelude,
                TargetRef::Local(root),
                DependencyKind::Parent,
                [],
            ),
        ])
    }

    fn expected_import_graph(source: &str) -> GraphRef {
        let root = written(
            DefinitionKind::Crate,
            ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            WrittenUnitKind::CrateRoot,
            0,
            None,
        );
        let definitions_item = marker_range(
            source,
            concat!(
                "mod definitions {\n",
                "    pub fn direct() {}\n\n",
                "    pub mod nested {\n",
                "        pub fn renamed() {}\n",
                "        pub fn globbed() {}\n",
                "    }\n\n",
                "    pub trait Speak {\n",
                "        fn speak(&self);\n",
                "    }\n\n",
                "    impl Speak for u8 {\n",
                "        fn speak(&self) {}\n",
                "    }\n",
                "}",
            ),
        );
        let definitions_anchor = marker_range(source, "mod definitions");
        let definitions = named(
            written_with_anchor(
                DefinitionKind::Module,
                definitions_item,
                definitions_anchor,
                WrittenUnitKind::InlineModule,
                0,
                Some(&root),
            ),
            Some("definitions"),
            0,
        );
        let direct_item = marker_range(source, "pub fn direct() {}");
        let direct_anchor = marker_in(source, "pub fn direct() {}", "pub fn direct()");
        let direct = named(
            written_with_anchor(
                DefinitionKind::Function,
                direct_item,
                direct_anchor,
                WrittenUnitKind::Item,
                0,
                Some(&definitions),
            ),
            Some("direct"),
            0,
        );
        let nested_item = marker_range(
            source,
            concat!(
                "pub mod nested {\n",
                "        pub fn renamed() {}\n",
                "        pub fn globbed() {}\n",
                "    }",
            ),
        );
        let nested_anchor = marker_range(source, "pub mod nested");
        let nested = named(
            written_with_anchor(
                DefinitionKind::Module,
                nested_item,
                nested_anchor,
                WrittenUnitKind::InlineModule,
                1,
                Some(&definitions),
            ),
            Some("nested"),
            0,
        );
        let renamed_item = marker_range(source, "pub fn renamed() {}");
        let renamed_anchor = marker_in(source, "pub fn renamed() {}", "pub fn renamed()");
        let renamed = named(
            written_with_anchor(
                DefinitionKind::Function,
                renamed_item,
                renamed_anchor,
                WrittenUnitKind::Item,
                1,
                Some(&nested),
            ),
            Some("renamed"),
            0,
        );
        let globbed_item = marker_range(source, "pub fn globbed() {}");
        let globbed_anchor = marker_in(source, "pub fn globbed() {}", "pub fn globbed()");
        let globbed = named(
            written_with_anchor(
                DefinitionKind::Function,
                globbed_item,
                globbed_anchor,
                WrittenUnitKind::Item,
                2,
                Some(&nested),
            ),
            Some("globbed"),
            0,
        );
        let speak_trait_item =
            marker_range(source, "pub trait Speak {\n        fn speak(&self);\n    }");
        let speak_trait_anchor = marker_range(source, "pub trait Speak");
        let speak_trait = named(
            written_with_anchor(
                DefinitionKind::Trait,
                speak_trait_item,
                speak_trait_anchor,
                WrittenUnitKind::Item,
                3,
                Some(&definitions),
            ),
            Some("Speak"),
            0,
        );
        let trait_speak_item = marker_range(source, "fn speak(&self);");
        let trait_speak = named(
            written(
                DefinitionKind::AssociatedFunction,
                trait_speak_item,
                WrittenUnitKind::TraitMember,
                0,
                Some(&speak_trait),
            ),
            Some("speak"),
            0,
        );
        let trait_speak_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &trait_speak,
            ),
            Some("'_"),
            0,
        );
        let speak_impl_item = marker_range(
            source,
            "impl Speak for u8 {\n        fn speak(&self) {}\n    }",
        );
        let speak_impl_anchor = marker_range(source, "impl Speak for u8");
        let speak_impl = written_with_anchor(
            DefinitionKind::Impl,
            speak_impl_item,
            speak_impl_anchor,
            WrittenUnitKind::Item,
            4,
            Some(&definitions),
        );
        let impl_speak_item = marker_range(source, "fn speak(&self) {}");
        let impl_speak_anchor = marker_in(source, "fn speak(&self) {}", "fn speak(&self)");
        let impl_speak = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                impl_speak_item,
                impl_speak_anchor,
                WrittenUnitKind::ImplMember,
                0,
                Some(&speak_impl),
            ),
            Some("speak"),
            0,
        );
        let impl_speak_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &impl_speak,
            ),
            Some("'_"),
            0,
        );

        let use_item_text = concat!(
            "use crate::definitions::{\n",
            "    direct as alias,\n",
            "    nested::{renamed as nested_alias, *},\n",
            "    Speak as _,\n",
            "};",
        );
        let use_item_range = marker_range(source, use_item_text);
        let outer_use_anchor = marker_in(source, use_item_text, "crate::definitions");
        let outer_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                use_item_range,
                outer_use_anchor,
                WrittenUnitKind::UseItem,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let nested_name = marker_in(source, use_item_text, "nested");
        let nested_use_anchor = ByteRange {
            start: outer_use_anchor.start,
            end: nested_name.end,
        };
        let nested_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                use_item_range,
                nested_use_anchor,
                WrittenUnitKind::UseItem,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let direct_use_range = marker_in(source, use_item_text, "direct as alias");
        let direct_use_anchor = marker_in(source, use_item_text, "direct");
        let direct_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                direct_use_range,
                direct_use_anchor,
                WrittenUnitKind::UseLeaf,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let renamed_use_range = marker_in(source, use_item_text, "renamed as nested_alias");
        let renamed_use_anchor = marker_in(source, use_item_text, "renamed");
        let renamed_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                renamed_use_range,
                renamed_use_anchor,
                WrittenUnitKind::UseLeaf,
                1,
                Some(&root),
            ),
            None,
            0,
        );
        let glob_use_range = marker_in(source, use_item_text, "*");
        let glob_use_anchor = ByteRange {
            start: glob_use_range.start,
            end: glob_use_range.start,
        };
        let glob_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                glob_use_range,
                glob_use_anchor,
                WrittenUnitKind::UseLeaf,
                2,
                Some(&root),
            ),
            None,
            0,
        );
        let trait_use_range = marker_in(source, use_item_text, "Speak as _");
        let trait_use_anchor = marker_in(source, use_item_text, "Speak");
        let trait_use = named(
            written_with_anchor(
                DefinitionKind::Use,
                trait_use_range,
                trait_use_anchor,
                WrittenUnitKind::UseLeaf,
                3,
                Some(&root),
            ),
            None,
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main_anchor = marker_range(source, "fn main()");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                main_anchor,
                WrittenUnitKind::Item,
                5,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);

        GraphRef {
            definitions: BTreeSet::from([
                root.clone(),
                definitions.clone(),
                direct.clone(),
                nested.clone(),
                renamed.clone(),
                globbed.clone(),
                speak_trait.clone(),
                trait_speak.clone(),
                trait_speak_lifetime.clone(),
                speak_impl.clone(),
                impl_speak.clone(),
                impl_speak_lifetime.clone(),
                outer_use.clone(),
                nested_use.clone(),
                direct_use.clone(),
                renamed_use.clone(),
                glob_use.clone(),
                trait_use.clone(),
                main.clone(),
                injected_std.clone(),
                injected_prelude.clone(),
            ]),
            external_definitions: BTreeSet::new(),
            edges: BTreeSet::from([
                edge(
                    &definitions,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [definitions_anchor],
                ),
                edge(
                    &direct,
                    TargetRef::Local(definitions.clone()),
                    DependencyKind::Parent,
                    [direct_anchor],
                ),
                edge(
                    &nested,
                    TargetRef::Local(definitions.clone()),
                    DependencyKind::Parent,
                    [nested_anchor],
                ),
                edge(
                    &renamed,
                    TargetRef::Local(nested.clone()),
                    DependencyKind::Parent,
                    [renamed_anchor],
                ),
                edge(
                    &globbed,
                    TargetRef::Local(nested.clone()),
                    DependencyKind::Parent,
                    [globbed_anchor],
                ),
                edge(
                    &speak_trait,
                    TargetRef::Local(definitions.clone()),
                    DependencyKind::Parent,
                    [speak_trait_anchor],
                ),
                edge(
                    &trait_speak,
                    TargetRef::Local(speak_trait.clone()),
                    DependencyKind::Parent,
                    [trait_speak_item],
                ),
                edge(
                    &trait_speak,
                    TargetRef::Local(speak_trait.clone()),
                    DependencyKind::SignatureType,
                    [marker_in(source, "fn speak(&self);", "self")],
                ),
                edge(
                    &trait_speak,
                    TargetRef::Local(trait_speak_lifetime.clone()),
                    DependencyKind::SignatureType,
                    [zero_width_before(source, "fn speak(&self);", "self")],
                ),
                edge(
                    &trait_speak_lifetime,
                    TargetRef::Local(trait_speak.clone()),
                    DependencyKind::Parent,
                    [],
                ),
                edge(
                    &speak_impl,
                    TargetRef::Local(definitions.clone()),
                    DependencyKind::Parent,
                    [speak_impl_anchor],
                ),
                edge(
                    &speak_impl,
                    TargetRef::Local(speak_trait.clone()),
                    DependencyKind::ImplementedTrait,
                    [marker_in(source, "impl Speak for u8", "Speak")],
                ),
                edge(
                    &impl_speak,
                    TargetRef::Local(speak_impl.clone()),
                    DependencyKind::Parent,
                    [impl_speak_anchor],
                ),
                edge(
                    &impl_speak,
                    TargetRef::Local(speak_impl.clone()),
                    DependencyKind::SignatureType,
                    [marker_in(source, "fn speak(&self) {}", "self")],
                ),
                edge(
                    &impl_speak,
                    TargetRef::Local(impl_speak_lifetime.clone()),
                    DependencyKind::SignatureType,
                    [zero_width_before(source, "fn speak(&self) {}", "self")],
                ),
                edge(
                    &impl_speak_lifetime,
                    TargetRef::Local(impl_speak.clone()),
                    DependencyKind::Parent,
                    [],
                ),
                edge(
                    &outer_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [outer_use_anchor],
                ),
                edge(
                    &nested_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [nested_use_anchor],
                ),
                edge(
                    &direct_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [direct_use_anchor],
                ),
                edge(
                    &direct_use,
                    TargetRef::Local(direct.clone()),
                    DependencyKind::ValuePath,
                    [direct_use_anchor],
                ),
                edge(
                    &renamed_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [renamed_use_anchor],
                ),
                edge(
                    &renamed_use,
                    TargetRef::Local(renamed.clone()),
                    DependencyKind::ValuePath,
                    [renamed_use_anchor],
                ),
                edge(
                    &glob_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [glob_use_anchor],
                ),
                edge(
                    &glob_use,
                    TargetRef::Local(nested),
                    DependencyKind::TypePath,
                    [glob_use_anchor],
                ),
                edge(
                    &trait_use,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [trait_use_anchor],
                ),
                edge(
                    &trait_use,
                    TargetRef::Local(speak_trait),
                    DependencyKind::TypePath,
                    [trait_use_anchor],
                ),
                edge(
                    &main,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [main_anchor],
                ),
                edge(
                    &main,
                    TargetRef::Local(direct),
                    DependencyKind::ValuePath,
                    [marker_in(source, "\n    alias();", "alias")],
                ),
                edge(
                    &main,
                    TargetRef::Local(renamed),
                    DependencyKind::ValuePath,
                    [marker_in(source, "nested_alias();", "nested_alias")],
                ),
                edge(
                    &main,
                    TargetRef::Local(globbed),
                    DependencyKind::ValuePath,
                    [marker_in(source, "globbed();", "globbed")],
                ),
                edge(
                    &main,
                    TargetRef::Local(trait_speak),
                    DependencyKind::MethodTarget,
                    [marker_in(source, "1_u8.speak();", "speak")],
                ),
                edge(
                    &main,
                    TargetRef::Local(direct_use),
                    DependencyKind::ImportLeaf,
                    [marker_in(source, "\n    alias();", "alias")],
                ),
                edge(
                    &main,
                    TargetRef::Local(renamed_use),
                    DependencyKind::ImportLeaf,
                    [marker_in(source, "nested_alias();", "nested_alias")],
                ),
                edge(
                    &main,
                    TargetRef::Local(glob_use),
                    DependencyKind::ImportLeaf,
                    [marker_in(source, "globbed();", "globbed")],
                ),
                edge(
                    &main,
                    TargetRef::Local(trait_use),
                    DependencyKind::ImportLeaf,
                    [marker_range(source, "1_u8.speak()")],
                ),
                edge(
                    &injected_std,
                    TargetRef::Local(root.clone()),
                    DependencyKind::Parent,
                    [],
                ),
                edge(
                    &injected_prelude,
                    TargetRef::Local(root),
                    DependencyKind::Parent,
                    [],
                ),
            ]),
        }
    }

    fn expected_dispatch_graph(source: &str) -> GraphRef {
        let root = written(
            DefinitionKind::Crate,
            ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            WrittenUnitKind::CrateRoot,
            0,
            None,
        );
        let use_leaf_range = marker_in(source, "use core::ops::Deref;", "core::ops::Deref");
        let use_leaf = named(
            written(
                DefinitionKind::Use,
                use_leaf_range,
                WrittenUnitKind::UseLeaf,
                0,
                Some(&root),
            ),
            None,
            0,
        );
        let value_item = marker_range(source, "struct Value;");
        let value_anchor = marker_in(source, "struct Value;", "struct Value");
        let value = named(
            written_with_anchor(
                DefinitionKind::Struct,
                value_item,
                value_anchor,
                WrittenUnitKind::Item,
                0,
                Some(&root),
            ),
            Some("Value"),
            0,
        );
        let value_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            value_item,
            value_anchor,
            WrittenUnitKind::Item,
            0,
            Some(&value),
        );
        let inherent_impl_item = marker_range(source, "impl Value {\n    fn inherent(&self) {}\n}");
        let inherent_impl_anchor = marker_range(source, "impl Value");
        let inherent_impl = written_with_anchor(
            DefinitionKind::Impl,
            inherent_impl_item,
            inherent_impl_anchor,
            WrittenUnitKind::Item,
            1,
            Some(&root),
        );
        let inherent_member = marker_range(source, "fn inherent(&self) {}");
        let inherent_anchor = marker_in(source, "fn inherent(&self) {}", "fn inherent(&self)");
        let inherent = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                inherent_member,
                inherent_anchor,
                WrittenUnitKind::ImplMember,
                0,
                Some(&inherent_impl),
            ),
            Some("inherent"),
            0,
        );
        let inherent_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &inherent,
            ),
            Some("'_"),
            0,
        );
        let scale_trait_item = marker_range(source, "trait Scale {\n    fn scale(&self);\n}");
        let scale_anchor = marker_range(source, "trait Scale");
        let scale = named(
            written_with_anchor(
                DefinitionKind::Trait,
                scale_trait_item,
                scale_anchor,
                WrittenUnitKind::Item,
                2,
                Some(&root),
            ),
            Some("Scale"),
            0,
        );
        let trait_scale_member = marker_range(source, "fn scale(&self);");
        let trait_scale = named(
            written(
                DefinitionKind::AssociatedFunction,
                trait_scale_member,
                WrittenUnitKind::TraitMember,
                0,
                Some(&scale),
            ),
            Some("scale"),
            0,
        );
        let trait_scale_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &trait_scale,
            ),
            Some("'_"),
            0,
        );
        let scale_impl_item =
            marker_range(source, "impl Scale for Value {\n    fn scale(&self) {}\n}");
        let scale_impl_anchor = marker_range(source, "impl Scale for Value");
        let scale_impl = named(
            written_with_anchor(
                DefinitionKind::Impl,
                scale_impl_item,
                scale_impl_anchor,
                WrittenUnitKind::Item,
                3,
                Some(&root),
            ),
            None,
            0,
        );
        let impl_scale_member = marker_range(source, "fn scale(&self) {}");
        let impl_scale_anchor = marker_in(source, "fn scale(&self) {}", "fn scale(&self)");
        let impl_scale = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                impl_scale_member,
                impl_scale_anchor,
                WrittenUnitKind::ImplMember,
                1,
                Some(&scale_impl),
            ),
            Some("scale"),
            0,
        );
        let impl_scale_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &impl_scale,
            ),
            Some("'_"),
            0,
        );
        let wrapper_item = marker_range(source, "struct Wrapper(Value);");
        let wrapper_anchor = marker_in(source, "struct Wrapper(Value);", "struct Wrapper");
        let wrapper = named(
            written_with_anchor(
                DefinitionKind::Struct,
                wrapper_item,
                wrapper_anchor,
                WrittenUnitKind::Item,
                4,
                Some(&root),
            ),
            Some("Wrapper"),
            0,
        );
        let wrapper_field = named(
            written_with_anchor(
                DefinitionKind::Field,
                wrapper_item,
                marker_in(source, "struct Wrapper(Value);", "Value"),
                WrittenUnitKind::Item,
                4,
                Some(&wrapper),
            ),
            Some("0"),
            0,
        );
        let wrapper_constructor = written_with_anchor(
            DefinitionKind::Constructor,
            wrapper_item,
            wrapper_anchor,
            WrittenUnitKind::Item,
            4,
            Some(&wrapper),
        );
        let deref_impl_item = marker_range(
            source,
            concat!(
                "impl Deref for Wrapper {\n",
                "    type Target = Value;\n\n",
                "    fn deref(&self) -> &Value {\n",
                "        loop {}\n",
                "    }\n",
                "}",
            ),
        );
        let deref_impl_anchor = marker_range(source, "impl Deref for Wrapper");
        let deref_impl = named(
            written_with_anchor(
                DefinitionKind::Impl,
                deref_impl_item,
                deref_impl_anchor,
                WrittenUnitKind::Item,
                5,
                Some(&root),
            ),
            None,
            0,
        );
        let target_member = marker_range(source, "type Target = Value;");
        let target = named(
            written_with_anchor(
                DefinitionKind::AssociatedType,
                target_member,
                marker_in(source, "type Target = Value;", "type Target"),
                WrittenUnitKind::ImplMember,
                2,
                Some(&deref_impl),
            ),
            Some("Target"),
            0,
        );
        let deref_member = marker_range(
            source,
            "fn deref(&self) -> &Value {\n        loop {}\n    }",
        );
        let deref_anchor = marker_in(
            source,
            "fn deref(&self) -> &Value {",
            "fn deref(&self) -> &Value",
        );
        let deref = named(
            written_with_anchor(
                DefinitionKind::AssociatedFunction,
                deref_member,
                deref_anchor,
                WrittenUnitKind::ImplMember,
                3,
                Some(&deref_impl),
            ),
            Some("deref"),
            0,
        );
        let deref_lifetime = named(
            generated(
                DefinitionKind::LifetimeParameter,
                GeneratedRole::ElidedLifetime,
                0,
                &deref,
            ),
            Some("'_"),
            0,
        );
        let main_item = final_item_range(source, "fn main() {");
        let main_anchor = marker_range(source, "fn main()");
        let main = named(
            written_with_anchor(
                DefinitionKind::Function,
                main_item,
                main_anchor,
                WrittenUnitKind::Item,
                6,
                Some(&root),
            ),
            Some("main"),
            0,
        );
        let injected_std = named(
            injected(
                DefinitionKind::ExternCrate,
                InjectedRole::ExternCrate,
                0,
                &root,
            ),
            Some("std"),
            0,
        );
        let injected_prelude = injected(DefinitionKind::Use, InjectedRole::PreludeImport, 0, &root);
        let external_deref = external("core", "std::ops::Deref");
        let external_deref_method = external("core", "std::ops::Deref::deref");

        let definitions = BTreeSet::from([
            root.clone(),
            use_leaf.clone(),
            value.clone(),
            value_constructor.clone(),
            inherent_impl.clone(),
            inherent.clone(),
            inherent_lifetime.clone(),
            scale.clone(),
            trait_scale.clone(),
            trait_scale_lifetime.clone(),
            scale_impl.clone(),
            impl_scale.clone(),
            impl_scale_lifetime.clone(),
            wrapper.clone(),
            wrapper_field.clone(),
            wrapper_constructor.clone(),
            deref_impl.clone(),
            target.clone(),
            deref.clone(),
            deref_lifetime.clone(),
            main.clone(),
            injected_std.clone(),
            injected_prelude.clone(),
        ]);
        let mut edges = BTreeSet::from([
            edge(
                &use_leaf,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [use_leaf_range],
            ),
            edge(
                &use_leaf,
                TargetRef::External(external_deref.clone()),
                DependencyKind::TypePath,
                [use_leaf_range],
            ),
            edge(
                &value,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [value_anchor],
            ),
            edge(
                &value_constructor,
                TargetRef::Local(value.clone()),
                DependencyKind::Parent,
                [value_anchor],
            ),
            edge(
                &inherent_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [inherent_impl_anchor],
            ),
            edge(
                &inherent_impl,
                TargetRef::Local(value.clone()),
                DependencyKind::ImplSelfType,
                [marker_in(source, "impl Value {", "Value")],
            ),
            edge(
                &inherent,
                TargetRef::Local(inherent_impl.clone()),
                DependencyKind::Parent,
                [inherent_anchor],
            ),
            edge(
                &inherent,
                TargetRef::Local(inherent_impl.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, "fn inherent(&self) {}", "self")],
            ),
            edge(
                &inherent,
                TargetRef::Local(inherent_lifetime.clone()),
                DependencyKind::SignatureType,
                [zero_width_before(source, "fn inherent(&self) {}", "self")],
            ),
            edge(
                &inherent_lifetime,
                TargetRef::Local(inherent.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &scale,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [scale_anchor],
            ),
            edge(
                &trait_scale,
                TargetRef::Local(scale.clone()),
                DependencyKind::Parent,
                [trait_scale_member],
            ),
            edge(
                &trait_scale,
                TargetRef::Local(scale.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, "fn scale(&self);", "self")],
            ),
            edge(
                &trait_scale,
                TargetRef::Local(trait_scale_lifetime.clone()),
                DependencyKind::SignatureType,
                [zero_width_before(source, "fn scale(&self);", "self")],
            ),
            edge(
                &trait_scale_lifetime,
                TargetRef::Local(trait_scale.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &scale_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [scale_impl_anchor],
            ),
            edge(
                &scale_impl,
                TargetRef::Local(value.clone()),
                DependencyKind::ImplSelfType,
                [marker_in(source, "impl Scale for Value {", "Value")],
            ),
            edge(
                &scale_impl,
                TargetRef::Local(scale.clone()),
                DependencyKind::ImplementedTrait,
                [marker_in(source, "impl Scale for Value {", "Scale")],
            ),
            edge(
                &impl_scale,
                TargetRef::Local(scale_impl.clone()),
                DependencyKind::Parent,
                [impl_scale_anchor],
            ),
            edge(
                &impl_scale,
                TargetRef::Local(scale_impl.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, "fn scale(&self) {}", "self")],
            ),
            edge(
                &impl_scale,
                TargetRef::Local(impl_scale_lifetime.clone()),
                DependencyKind::SignatureType,
                [zero_width_before(source, "fn scale(&self) {}", "self")],
            ),
            edge(
                &impl_scale_lifetime,
                TargetRef::Local(impl_scale.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &wrapper,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [wrapper_anchor],
            ),
            edge(
                &wrapper_field,
                TargetRef::Local(value.clone()),
                DependencyKind::FieldType,
                [marker_in(source, "struct Wrapper(Value);", "Value")],
            ),
            edge(
                &wrapper_field,
                TargetRef::Local(wrapper.clone()),
                DependencyKind::Parent,
                [marker_in(source, "struct Wrapper(Value);", "Value")],
            ),
            edge(
                &wrapper_constructor,
                TargetRef::Local(wrapper.clone()),
                DependencyKind::Parent,
                [wrapper_anchor],
            ),
            edge(
                &deref_impl,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [deref_impl_anchor],
            ),
            edge(
                &deref_impl,
                TargetRef::Local(wrapper.clone()),
                DependencyKind::ImplSelfType,
                [marker_in(source, "impl Deref for Wrapper {", "Wrapper")],
            ),
            edge(
                &deref_impl,
                TargetRef::External(external_deref.clone()),
                DependencyKind::ImplementedTrait,
                [marker_in(source, "impl Deref for Wrapper {", "Deref")],
            ),
            edge(
                &target,
                TargetRef::Local(value.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, "type Target = Value;", "Value")],
            ),
            edge(
                &target,
                TargetRef::Local(deref_impl.clone()),
                DependencyKind::Parent,
                [marker_in(source, "type Target = Value;", "type Target")],
            ),
            edge(
                &deref,
                TargetRef::Local(value.clone()),
                DependencyKind::ReturnType,
                [marker_in(source, "fn deref(&self) -> &Value {", "Value")],
            ),
            edge(
                &deref,
                TargetRef::Local(value.clone()),
                DependencyKind::AdjustmentType,
                [marker_range(source, "loop {}")],
            ),
            edge(
                &deref,
                TargetRef::Local(deref_impl.clone()),
                DependencyKind::Parent,
                [deref_anchor],
            ),
            edge(
                &deref,
                TargetRef::Local(deref_impl.clone()),
                DependencyKind::SignatureType,
                [marker_in(source, "fn deref(&self) -> &Value {", "self")],
            ),
            edge(
                &deref,
                TargetRef::Local(deref_lifetime.clone()),
                DependencyKind::SignatureType,
                [zero_width_before(
                    source,
                    "fn deref(&self) -> &Value {",
                    "self",
                )],
            ),
            edge(
                &deref,
                TargetRef::Local(deref_lifetime.clone()),
                DependencyKind::ReturnType,
                [zero_width_before(
                    source,
                    "fn deref(&self) -> &Value {",
                    "Value",
                )],
            ),
            edge(
                &deref_lifetime,
                TargetRef::Local(deref.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &main,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [main_anchor],
            ),
            edge(
                &main,
                TargetRef::Local(value.clone()),
                DependencyKind::TypePath,
                [
                    marker_in(source, "Value::inherent(&value);", "Value"),
                    marker_in(source, "<Value as Scale>::scale(&value);", "Value"),
                ],
            ),
            edge(
                &main,
                TargetRef::Local(value.clone()),
                DependencyKind::ResolvedGenericArgument,
                [
                    marker_in(source, "value.scale();", "value.scale()"),
                    marker_in(
                        source,
                        "<Value as Scale>::scale(&value);",
                        "<Value as Scale>::scale",
                    ),
                ],
            ),
            edge(
                &main,
                TargetRef::Local(value.clone()),
                DependencyKind::AdjustmentType,
                [
                    marker_in(source, "value.inherent();", "value"),
                    marker_in(source, "value.scale();", "value"),
                    marker_in(source, "Value::inherent(&value);", "&value"),
                    marker_in(source, "<Value as Scale>::scale(&value);", "&value"),
                    marker_in(source, "Wrapper(value).inherent();", "Wrapper(value)"),
                ],
            ),
            edge(
                &main,
                TargetRef::Local(value_constructor),
                DependencyKind::ValuePath,
                [marker_in(source, "let value = Value;", "Value")],
            ),
            edge(
                &main,
                TargetRef::Local(inherent.clone()),
                DependencyKind::MethodTarget,
                [
                    marker_in(source, "value.inherent();", "inherent"),
                    marker_in(source, "Wrapper(value).inherent();", "inherent"),
                ],
            ),
            edge(
                &main,
                TargetRef::Local(inherent),
                DependencyKind::AssociatedItemTarget,
                [marker_in(
                    source,
                    "Value::inherent(&value);",
                    "Value::inherent",
                )],
            ),
            edge(
                &main,
                TargetRef::Local(trait_scale.clone()),
                DependencyKind::MethodTarget,
                [marker_in(source, "value.scale();", "scale")],
            ),
            edge(
                &main,
                TargetRef::Local(trait_scale),
                DependencyKind::AssociatedItemTarget,
                [marker_in(
                    source,
                    "<Value as Scale>::scale(&value);",
                    "<Value as Scale>::scale",
                )],
            ),
            edge(
                &main,
                TargetRef::Local(wrapper_constructor),
                DependencyKind::ValuePath,
                [marker_in(source, "Wrapper(value).inherent();", "Wrapper")],
            ),
            edge(
                &main,
                TargetRef::External(external_deref_method.clone()),
                DependencyKind::DerefTarget,
                [marker_in(
                    source,
                    "Wrapper(value).inherent();",
                    "Wrapper(value).inherent()",
                )],
            ),
            edge(
                &injected_std,
                TargetRef::Local(root.clone()),
                DependencyKind::Parent,
                [],
            ),
            edge(
                &injected_prelude,
                TargetRef::Local(root),
                DependencyKind::Parent,
                [],
            ),
        ]);

        edges.insert(edge(
            &deref_impl,
            TargetRef::Local(use_leaf),
            DependencyKind::ImportLeaf,
            [marker_in(source, "impl Deref for Wrapper {", "Deref")],
        ));

        GraphRef {
            definitions,
            external_definitions: BTreeSet::from([external_deref, external_deref_method]),
            edges,
        }
    }

    fn inspect(source: &str) -> DefinitionGraph {
        let (sysroot, target) = compiler_context();
        inspect_source_with_definitions(
            &SourceInput {
                source: source.to_owned(),
                edition: Edition::Rust2024,
                target,
            },
            &sysroot,
        )
        .expect("the fixture must compile and produce a complete definition graph")
        .definitions
    }

    fn project_graph(graph: &DefinitionGraph) -> GraphRef {
        GraphRef {
            definitions: graph
                .definitions
                .iter()
                .map(|definition| local_ref(graph, definition.id))
                .collect(),
            external_definitions: graph
                .external_definitions
                .iter()
                .map(external_ref)
                .collect(),
            edges: graph
                .edges
                .iter()
                .map(|edge| EdgeRef {
                    from: local_ref(graph, edge.from),
                    to: target_ref(graph, edge.to),
                    kind: edge.kind,
                    sites: edge.sites.clone(),
                })
                .collect(),
        }
    }

    fn edges_of_kinds(edges: &BTreeSet<EdgeRef>, kinds: &[DependencyKind]) -> BTreeSet<EdgeRef> {
        edges
            .iter()
            .filter(|edge| kinds.contains(&edge.kind))
            .cloned()
            .collect()
    }

    fn local_ref(graph: &DefinitionGraph, id: DefinitionId) -> LocalRef {
        let definition = &graph.definitions[id.0 as usize];
        LocalRef {
            kind: definition.kind,
            origin: match &definition.origin {
                DefinitionOrigin::Written {
                    unit_range,
                    anchor,
                    unit_kind,
                    unit_ordinal,
                    ..
                } => OriginRef::Written {
                    unit_range: *unit_range,
                    anchor: *anchor,
                    unit_kind: *unit_kind,
                    unit_ordinal: *unit_ordinal,
                },
                DefinitionOrigin::Expanded {
                    invocation_range,
                    generated_role,
                    ordinal,
                    ..
                } => OriginRef::Expanded {
                    invocation_range: *invocation_range,
                    generated_role: *generated_role,
                    ordinal: *ordinal,
                },
                DefinitionOrigin::CompilerGenerated { role, ordinal } => {
                    OriginRef::CompilerGenerated {
                        role: *role,
                        ordinal: *ordinal,
                    }
                }
                DefinitionOrigin::Injected { role, ordinal } => OriginRef::Injected {
                    role: *role,
                    ordinal: *ordinal,
                },
            },
            name: definition.key.0.last().and_then(|part| part.name.clone()),
            structural_ordinal: definition
                .key
                .0
                .last()
                .map_or(0, |part| part.same_role_ordinal),
            parent: definition
                .parent
                .map(|parent| Box::new(local_ref(graph, parent))),
        }
    }

    fn target_ref(graph: &DefinitionGraph, target: DefinitionTarget) -> TargetRef {
        match target {
            DefinitionTarget::Local(id) => TargetRef::Local(local_ref(graph, id)),
            DefinitionTarget::External(id) => TargetRef::External(external_ref_by_id(graph, id)),
        }
    }

    fn external_ref_by_id(graph: &DefinitionGraph, id: ExternalDefinitionId) -> ExternalRef {
        external_ref(&graph.external_definitions[id.0 as usize])
    }

    fn external_ref(definition: &ExternalDefinition) -> ExternalRef {
        ExternalRef {
            crate_name: definition.key.crate_name.clone(),
            path: definition.path.clone(),
        }
    }

    fn written(
        kind: DefinitionKind,
        range: ByteRange,
        unit_kind: WrittenUnitKind,
        unit_ordinal: u32,
        parent: Option<&LocalRef>,
    ) -> LocalRef {
        LocalRef {
            kind,
            origin: OriginRef::Written {
                unit_range: range,
                anchor: range,
                unit_kind,
                unit_ordinal,
            },
            name: None,
            structural_ordinal: 0,
            parent: parent.cloned().map(Box::new),
        }
    }

    fn named(mut definition: LocalRef, name: Option<&str>, structural_ordinal: u32) -> LocalRef {
        definition.name = name.map(str::to_owned);
        definition.structural_ordinal = structural_ordinal;
        definition
    }

    fn written_with_anchor(
        kind: DefinitionKind,
        unit_range: ByteRange,
        anchor: ByteRange,
        unit_kind: WrittenUnitKind,
        unit_ordinal: u32,
        parent: Option<&LocalRef>,
    ) -> LocalRef {
        LocalRef {
            kind,
            origin: OriginRef::Written {
                unit_range,
                anchor,
                unit_kind,
                unit_ordinal,
            },
            name: None,
            structural_ordinal: 0,
            parent: parent.cloned().map(Box::new),
        }
    }

    fn generated(
        kind: DefinitionKind,
        role: GeneratedRole,
        ordinal: u32,
        parent: &LocalRef,
    ) -> LocalRef {
        LocalRef {
            kind,
            origin: OriginRef::CompilerGenerated { role, ordinal },
            name: None,
            structural_ordinal: 0,
            parent: Some(Box::new(parent.clone())),
        }
    }

    fn expanded(
        kind: DefinitionKind,
        invocation_range: ByteRange,
        generated_role: Option<GeneratedRole>,
        ordinal: u32,
        parent: Option<&LocalRef>,
    ) -> LocalRef {
        LocalRef {
            kind,
            origin: OriginRef::Expanded {
                invocation_range,
                generated_role,
                ordinal,
            },
            name: None,
            structural_ordinal: 0,
            parent: parent.cloned().map(Box::new),
        }
    }

    fn injected(
        kind: DefinitionKind,
        role: InjectedRole,
        ordinal: u32,
        parent: &LocalRef,
    ) -> LocalRef {
        LocalRef {
            kind,
            origin: OriginRef::Injected { role, ordinal },
            name: None,
            structural_ordinal: 0,
            parent: Some(Box::new(parent.clone())),
        }
    }

    fn external(crate_name: &str, path: &str) -> ExternalRef {
        ExternalRef {
            crate_name: crate_name.to_owned(),
            path: path.to_owned(),
        }
    }

    fn edge<const N: usize>(
        from: &LocalRef,
        to: TargetRef,
        kind: DependencyKind,
        sites: [ByteRange; N],
    ) -> EdgeRef {
        EdgeRef {
            from: from.clone(),
            to,
            kind,
            sites: sites.into(),
        }
    }

    fn marker_range(source: &str, marker: &str) -> ByteRange {
        let mut matches = source.match_indices(marker);
        let (start, matched) = matches
            .next()
            .unwrap_or_else(|| panic!("missing fixture marker: {marker:?}"));
        assert!(
            matches.next().is_none(),
            "fixture marker must be unique: {marker:?}"
        );
        ByteRange {
            start: start as u32,
            end: (start + matched.len()) as u32,
        }
    }

    fn nth_marker_range(source: &str, marker: &str, occurrence: usize) -> ByteRange {
        let (start, matched) = source
            .match_indices(marker)
            .nth(occurrence)
            .unwrap_or_else(|| panic!("missing occurrence {occurrence} of {marker:?}"));
        ByteRange {
            start: start as u32,
            end: (start + matched.len()) as u32,
        }
    }

    fn find_local(
        definitions: &BTreeSet<LocalRef>,
        kind: DefinitionKind,
        name: Option<&str>,
    ) -> LocalRef {
        let mut matches = definitions
            .iter()
            .filter(|definition| definition.kind == kind && definition.name.as_deref() == name)
            .cloned();
        let definition = matches
            .next()
            .unwrap_or_else(|| panic!("missing {kind:?} definition named {name:?}"));
        assert!(
            matches.next().is_none(),
            "ambiguous {kind:?} definition named {name:?}"
        );
        definition
    }

    fn find_local_with_anchor(
        definitions: &BTreeSet<LocalRef>,
        kind: DefinitionKind,
        anchor: ByteRange,
    ) -> LocalRef {
        let mut matches = definitions
            .iter()
            .filter(|definition| {
                definition.kind == kind
                    && matches!(
                        definition.origin,
                        OriginRef::Written {
                            anchor: actual,
                            ..
                        } if actual == anchor
                    )
            })
            .cloned();
        let definition = matches
            .next()
            .unwrap_or_else(|| panic!("missing {kind:?} definition at {anchor:?}"));
        assert!(
            matches.next().is_none(),
            "ambiguous {kind:?} definition at {anchor:?}"
        );
        definition
    }

    fn child_of(
        definitions: &BTreeSet<LocalRef>,
        kind: DefinitionKind,
        parent: &LocalRef,
        name: Option<&str>,
    ) -> LocalRef {
        let mut matches = definitions
            .iter()
            .filter(|definition| {
                definition.kind == kind
                    && definition.name.as_deref() == name
                    && definition.parent.as_deref() == Some(parent)
            })
            .cloned();
        let definition = matches
            .next()
            .unwrap_or_else(|| panic!("missing {kind:?} child named {name:?} of {parent:?}"));
        assert!(
            matches.next().is_none(),
            "ambiguous {kind:?} child named {name:?} of {parent:?}"
        );
        definition
    }

    fn crate_root(source: &str) -> LocalRef {
        written(
            DefinitionKind::Crate,
            ByteRange {
                start: 0,
                end: source.len() as u32,
            },
            WrittenUnitKind::CrateRoot,
            0,
            None,
        )
    }

    fn marker_in(source: &str, container: &str, marker: &str) -> ByteRange {
        nth_marker_in(source, container, marker, 0)
    }

    fn zero_width_before(source: &str, container: &str, marker: &str) -> ByteRange {
        let start = marker_in(source, container, marker).start;
        ByteRange { start, end: start }
    }

    fn nth_marker_in(source: &str, container: &str, marker: &str, occurrence: usize) -> ByteRange {
        let container_range = marker_range(source, container);
        let contents = &source[container_range.start as usize..container_range.end as usize];
        let (relative_start, matched) = contents
            .match_indices(marker)
            .nth(occurrence)
            .unwrap_or_else(|| {
                panic!("missing occurrence {occurrence} of {marker:?} in {container:?}")
            });
        let start = container_range.start as usize + relative_start;
        ByteRange {
            start: start as u32,
            end: (start + matched.len()) as u32,
        }
    }

    fn final_item_range(source: &str, marker: &str) -> ByteRange {
        let start = marker_range(source, marker).start;
        ByteRange {
            start,
            end: source.trim_end().len() as u32,
        }
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
}

#[cfg(all(test, not(rust_item_dependencies_patched)))]
mod unpatched_tests {
    use std::path::PathBuf;
    use std::process::Command;

    use super::DefinitionError;
    use crate::input::{Edition, InputError, SourceInput, inspect_source_with_definitions};

    #[test]
    fn reports_missing_import_provenance() {
        let source = include_str!("../tests/fixtures/definitions/path_resolution.rs");
        let rustc = env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC");
        let sysroot = PathBuf::from(rustc_output(rustc, &["--print", "sysroot"]).trim());
        let version = rustc_output(rustc, &["-Vv"]);
        let target = version
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .expect("rustc -Vv must report a host")
            .to_owned();

        let error = inspect_source_with_definitions(
            &SourceInput {
                source: source.to_owned(),
                edition: Edition::Rust2024,
                target,
            },
            &sysroot,
        )
        .expect_err("an unpatched compiler cannot provide import provenance");

        assert_eq!(
            error,
            InputError::Definition(DefinitionError::IncompleteImportDependency)
        );
    }

    fn rustc_output(rustc: &str, arguments: &[&str]) -> String {
        let output = Command::new(rustc)
            .args(arguments)
            .output()
            .expect("rustc query must start");
        assert!(output.status.success(), "rustc query failed");
        String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
    }
}
