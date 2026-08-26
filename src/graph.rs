//! Owned definition-level dependency graph.

use std::collections::{BTreeMap, BTreeSet};

use crate::source::{ByteRange, SourceUnitId, WrittenUnitKind};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DefinitionId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExternalDefinitionId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DefinitionKind {
    Crate,
    Module,
    Function,
    Static,
    Const,
    TypeAlias,
    OpaqueType,
    Struct,
    Enum,
    Union,
    Variant,
    Field,
    Constructor,
    Trait,
    TraitAlias,
    AssociatedType,
    AssociatedFunction,
    AssociatedConst,
    Impl,
    TypeParameter,
    ConstParameter,
    LifetimeParameter,
    ExternCrate,
    Use,
    ForeignModule,
    ForeignType,
    GlobalAsm,
    Closure,
    Coroutine,
    CoroutineClosure,
    SyntheticCoroutineBody,
    AnonymousConst,
    InlineConst,
    Macro,
}

impl DefinitionKind {
    pub(crate) fn rank(self) -> u8 {
        self as u8
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GeneratedRole {
    AnonymousAssociatedType,
    AnonymousConst,
    Coroutine,
    CoroutineBody,
    CoroutineClosure,
    ElidedLifetime,
    NestedStatic,
    OpaqueLifetime,
    OpaqueType,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum InjectedRole {
    ExternCrate,
    PreludeImport,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DefinitionOrigin {
    Written {
        unit: SourceUnitId,
        unit_range: ByteRange,
        anchor: ByteRange,
        unit_kind: WrittenUnitKind,
        unit_ordinal: u32,
    },
    Expanded {
        invocation: SourceUnitId,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub id: DefinitionId,
    pub key: DefinitionKey,
    pub kind: DefinitionKind,
    pub parent: Option<DefinitionId>,
    pub origin: DefinitionOrigin,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DefinitionKey(pub Vec<DefinitionKeyPart>);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DefinitionKeyPart {
    pub kind: DefinitionKind,
    pub origin: DefinitionOriginKey,
    pub name: Option<String>,
    pub same_role_ordinal: u32,
}

/// Source-derived identity for one definition, independent of compiler IDs and
/// dense inventory numbering.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DefinitionOriginKey {
    Written {
        anchor: ByteRange,
        unit_kind: WrittenUnitKind,
    },
    Expanded {
        invocation_range: ByteRange,
        generated_role: Option<GeneratedRole>,
    },
    CompilerGenerated {
        role: GeneratedRole,
    },
    Injected {
        role: InjectedRole,
    },
}

impl DefinitionOrigin {
    pub(crate) fn key(&self) -> DefinitionOriginKey {
        match self {
            Self::Written {
                anchor, unit_kind, ..
            } => DefinitionOriginKey::Written {
                anchor: *anchor,
                unit_kind: *unit_kind,
            },
            Self::Expanded {
                invocation_range,
                generated_role,
                ..
            } => DefinitionOriginKey::Expanded {
                invocation_range: *invocation_range,
                generated_role: *generated_role,
            },
            Self::CompilerGenerated { role, .. } => {
                DefinitionOriginKey::CompilerGenerated { role: *role }
            }
            Self::Injected { role, .. } => DefinitionOriginKey::Injected { role: *role },
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExternalDefinitionKey {
    pub crate_identity: u64,
    pub crate_name: String,
    pub def_path_hash: [u8; 16],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExternalDefinition {
    pub id: ExternalDefinitionId,
    pub key: ExternalDefinitionKey,
    /// Human-readable diagnostic label. Identity is carried only by `key`.
    pub path: String,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DefinitionTarget {
    Local(DefinitionId),
    External(ExternalDefinitionId),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DependencyKind {
    Parent,
    SignatureType,
    ReturnType,
    GenericDefault,
    Predicate,
    FieldType,
    Discriminant,
    VisibilityPath,
    SuperTrait,
    ImplSelfType,
    ImplementedTrait,
    AssociatedTypeBound,
    OpaqueHiddenType,
    ConstExpression,
    ValuePath,
    TypePath,
    MacroPath,
    PatternConstructor,
    ImportLeaf,
    MethodTarget,
    AssociatedItemTarget,
    OverloadedOperator,
    DerefTarget,
    IndexTarget,
    CallableTrait,
    ResolvedGenericArgument,
    AdjustmentType,
    ClosureCaptureType,
    FieldTarget,
    OpaqueSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionEdge {
    pub from: DefinitionId,
    pub to: DefinitionTarget,
    pub kind: DependencyKind,
    pub sites: Vec<ByteRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionGraph {
    pub definitions: Vec<Definition>,
    pub external_definitions: Vec<ExternalDefinition>,
    pub edges: Vec<DefinitionEdge>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum GraphError {
    InvalidDefinition,
    InvalidExternalDefinition,
    InvalidEdge,
}

impl DefinitionGraph {
    pub(crate) fn new(
        mut definitions: Vec<Definition>,
        mut external_definitions: Vec<ExternalDefinition>,
        edges: Vec<DefinitionEdge>,
    ) -> Result<Self, GraphError> {
        definitions.sort_by_key(|definition| definition.id);
        external_definitions.sort_by_key(|definition| definition.id);
        if definitions
            .iter()
            .enumerate()
            .any(|(index, definition)| definition.id.0 as usize != index)
        {
            return Err(GraphError::InvalidDefinition);
        }
        if external_definitions
            .iter()
            .enumerate()
            .any(|(index, definition)| definition.id.0 as usize != index)
        {
            return Err(GraphError::InvalidExternalDefinition);
        }

        let roots = definitions
            .iter()
            .filter(|definition| definition.parent.is_none())
            .collect::<Vec<_>>();
        if roots.len() != 1
            || roots[0].kind != DefinitionKind::Crate
            || roots[0].key.0.len() != 1
            || !matches!(
                roots[0].origin,
                DefinitionOrigin::Written {
                    unit_kind: WrittenUnitKind::CrateRoot,
                    ..
                }
            )
        {
            return Err(GraphError::InvalidDefinition);
        }

        for definition in &definitions {
            let leaf = definition.key.0.last();
            if definition.parent.is_some_and(|parent| {
                parent.0 >= definition.id.0 || parent.0 as usize >= definitions.len()
            }) || leaf.is_none_or(|part| {
                part.kind != definition.kind || part.origin != definition.origin.key()
            }) || definition.parent.is_some_and(|parent| {
                let parent_key = &definitions[parent.0 as usize].key.0;
                definition.key.0.len() != parent_key.len() + 1
                    || !definition.key.0.starts_with(parent_key)
            }) || (match (&definition.origin, leaf) {
                (
                    DefinitionOrigin::Expanded { ordinal, .. }
                    | DefinitionOrigin::CompilerGenerated { ordinal, .. }
                    | DefinitionOrigin::Injected { ordinal, .. },
                    Some(part),
                ) => *ordinal != part.same_role_ordinal,
                _ => false,
            }) {
                return Err(GraphError::InvalidDefinition);
            }
        }
        if definitions
            .iter()
            .map(|definition| &definition.key)
            .collect::<BTreeSet<_>>()
            .len()
            != definitions.len()
        {
            return Err(GraphError::InvalidDefinition);
        }
        if external_definitions
            .iter()
            .map(|definition| &definition.key)
            .collect::<BTreeSet<_>>()
            .len()
            != external_definitions.len()
        {
            return Err(GraphError::InvalidExternalDefinition);
        }

        let mut grouped =
            BTreeMap::<(DefinitionId, DefinitionTarget, DependencyKind), BTreeSet<ByteRange>>::new(
            );
        for edge in edges {
            if edge.from.0 as usize >= definitions.len()
                || match edge.to {
                    DefinitionTarget::Local(target) => target.0 as usize >= definitions.len(),
                    DefinitionTarget::External(target) => {
                        target.0 as usize >= external_definitions.len()
                    }
                }
                || edge.sites.iter().any(|site| site.start > site.end)
                || (edge.kind != DependencyKind::Parent && edge.sites.is_empty())
            {
                return Err(GraphError::InvalidEdge);
            }
            grouped
                .entry((edge.from, edge.to, edge.kind))
                .or_default()
                .extend(edge.sites);
        }
        let edges = grouped
            .into_iter()
            .map(|((from, to, kind), sites)| DefinitionEdge {
                from,
                to,
                kind,
                sites: sites.into_iter().collect(),
            })
            .collect::<Vec<_>>();
        for definition in definitions
            .iter()
            .filter(|definition| definition.parent.is_some())
        {
            let parent = definition
                .parent
                .expect("filtered definitions have a parent");
            let parent_edges = edges
                .iter()
                .filter(|edge| {
                    edge.from == definition.id
                        && edge.kind == DependencyKind::Parent
                        && edge.to == DefinitionTarget::Local(parent)
                })
                .count();
            let expected_sites = match definition.origin {
                DefinitionOrigin::Written { anchor, .. } => vec![anchor],
                DefinitionOrigin::Expanded {
                    invocation_range, ..
                } => vec![invocation_range],
                DefinitionOrigin::CompilerGenerated { .. } | DefinitionOrigin::Injected { .. } => {
                    Vec::new()
                }
            };
            if parent_edges != 1
                || edges.iter().any(|edge| {
                    edge.from == definition.id
                        && edge.kind == DependencyKind::Parent
                        && edge.to != DefinitionTarget::Local(parent)
                })
                || edges.iter().any(|edge| {
                    edge.from == definition.id
                        && edge.kind == DependencyKind::Parent
                        && edge.to == DefinitionTarget::Local(parent)
                        && edge.sites != expected_sites
                })
            {
                return Err(GraphError::InvalidEdge);
            }
        }
        if edges
            .iter()
            .any(|edge| edge.from == roots[0].id && edge.kind == DependencyKind::Parent)
        {
            return Err(GraphError::InvalidEdge);
        }
        Ok(Self {
            definitions,
            external_definitions,
            edges,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_definitions() -> Vec<Definition> {
        let root_origin = DefinitionOrigin::Written {
            unit: SourceUnitId(0),
            unit_range: ByteRange { start: 0, end: 10 },
            anchor: ByteRange { start: 0, end: 10 },
            unit_kind: WrittenUnitKind::CrateRoot,
            unit_ordinal: 0,
        };
        let child_origin = DefinitionOrigin::CompilerGenerated {
            role: GeneratedRole::OpaqueType,
            ordinal: 0,
        };
        let root_part = DefinitionKeyPart {
            kind: DefinitionKind::Crate,
            origin: root_origin.key(),
            name: None,
            same_role_ordinal: 0,
        };
        let child_part = DefinitionKeyPart {
            kind: DefinitionKind::Function,
            origin: child_origin.key(),
            name: None,
            same_role_ordinal: 0,
        };
        vec![
            Definition {
                id: DefinitionId(0),
                key: DefinitionKey(vec![root_part.clone()]),
                kind: DefinitionKind::Crate,
                parent: None,
                origin: root_origin,
            },
            Definition {
                id: DefinitionId(1),
                key: DefinitionKey(vec![root_part, child_part]),
                kind: DefinitionKind::Function,
                parent: Some(DefinitionId(0)),
                origin: child_origin,
            },
        ]
    }

    fn parent_edge() -> DefinitionEdge {
        DefinitionEdge {
            from: DefinitionId(1),
            to: DefinitionTarget::Local(DefinitionId(0)),
            kind: DependencyKind::Parent,
            sites: Vec::new(),
        }
    }

    #[test]
    fn edges_are_grouped_without_losing_kind_or_site() {
        let definitions = valid_definitions();
        let edges = vec![
            parent_edge(),
            DefinitionEdge {
                from: DefinitionId(1),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DependencyKind::ValuePath,
                sites: vec![ByteRange { start: 8, end: 9 }],
            },
            DefinitionEdge {
                from: DefinitionId(1),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DependencyKind::ValuePath,
                sites: vec![
                    ByteRange { start: 3, end: 4 },
                    ByteRange { start: 8, end: 9 },
                ],
            },
            DefinitionEdge {
                from: DefinitionId(1),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DependencyKind::TypePath,
                sites: vec![ByteRange { start: 3, end: 4 }],
            },
        ];
        let graph = DefinitionGraph::new(definitions, Vec::new(), edges).unwrap();
        assert_eq!(graph.edges.len(), 3);
        let value_path = graph
            .edges
            .iter()
            .find(|edge| edge.kind == DependencyKind::ValuePath)
            .unwrap();
        assert_eq!(
            value_path.sites,
            vec![
                ByteRange { start: 3, end: 4 },
                ByteRange { start: 8, end: 9 }
            ]
        );
        assert!(
            graph
                .edges
                .iter()
                .any(|edge| edge.kind == DependencyKind::TypePath)
        );
    }

    #[test]
    fn rejects_a_root_key_with_a_synthetic_prefix() {
        let mut definitions = valid_definitions();
        let prefix = definitions[0].key.0[0].clone();
        definitions[0].key.0.insert(0, prefix.clone());
        definitions[1].key.0.insert(0, prefix);

        assert_eq!(
            DefinitionGraph::new(definitions, Vec::new(), vec![parent_edge()]),
            Err(GraphError::InvalidDefinition)
        );
    }

    #[test]
    fn rejects_a_child_key_that_does_not_extend_its_parent() {
        let mut definitions = valid_definitions();
        definitions[1].key.0[0].name = Some("different-root".into());

        assert_eq!(
            DefinitionGraph::new(definitions, Vec::new(), vec![parent_edge()]),
            Err(GraphError::InvalidDefinition)
        );
    }

    #[test]
    fn rejects_duplicate_external_keys() {
        let definitions = valid_definitions();
        let key = ExternalDefinitionKey {
            crate_identity: 1,
            crate_name: "dependency".into(),
            def_path_hash: [2; 16],
        };
        let external_definitions = vec![
            ExternalDefinition {
                id: ExternalDefinitionId(0),
                key: key.clone(),
                path: "dependency::first".into(),
            },
            ExternalDefinition {
                id: ExternalDefinitionId(1),
                key,
                path: "dependency::second".into(),
            },
        ];

        assert_eq!(
            DefinitionGraph::new(definitions, external_definitions, vec![parent_edge()]),
            Err(GraphError::InvalidExternalDefinition)
        );
    }

    #[test]
    fn rejects_a_parent_edge_that_disagrees_with_the_definition() {
        let definitions = valid_definitions();
        let mut edge = parent_edge();
        edge.to = DefinitionTarget::Local(DefinitionId(1));

        assert_eq!(
            DefinitionGraph::new(definitions, Vec::new(), vec![edge]),
            Err(GraphError::InvalidEdge)
        );
    }

    #[test]
    fn rejects_a_parent_edge_with_the_wrong_site() {
        let definitions = valid_definitions();
        let mut edge = parent_edge();
        edge.sites = vec![ByteRange { start: 1, end: 2 }];

        assert_eq!(
            DefinitionGraph::new(definitions, Vec::new(), vec![edge]),
            Err(GraphError::InvalidEdge)
        );
    }

    #[test]
    fn rejects_a_semantic_edge_without_a_site() {
        let definitions = valid_definitions();
        let edges = vec![
            parent_edge(),
            DefinitionEdge {
                from: DefinitionId(1),
                to: DefinitionTarget::Local(DefinitionId(0)),
                kind: DependencyKind::ValuePath,
                sites: Vec::new(),
            },
        ];

        assert_eq!(
            DefinitionGraph::new(definitions, Vec::new(), edges),
            Err(GraphError::InvalidEdge)
        );
    }
}
