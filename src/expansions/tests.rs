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
use crate::graph::{DefinitionKind, DefinitionOrigin, DefinitionTarget};
use crate::source::{
    SourceInventory, collect_source, refine_attribute_macros_from_compiler,
    refine_derive_targets_from_compiler, refine_macro_rules_from_compiler,
};

const FIXTURE: &str = include_str!("../../tests/fixtures/dependencies/expansion_graph.rs");

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

fn inspect(source: &str) -> GraphRef {
    let (sysroot, target) = compiler_context();
    let result = Arc::new(Mutex::new(None));
    let mut callbacks = ExpansionCallbacks {
        source: Arc::from(source),
        result: Arc::clone(&result),
        inventory: None,
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
    let collected = result
        .lock()
        .expect("expansion result mutex is poisoned")
        .take()
        .expect("the compiler must reach analysis")
        .expect("the expansion graph must be complete");
    project_graph(&collected)
}

struct ExpansionCallbacks {
    source: Arc<str>,
    result: Arc<Mutex<Option<Result<TestCollection, ExpansionError>>>>,
    inventory: Option<SourceInventory>,
}

struct TestCollection {
    definitions: crate::graph::DefinitionGraph,
    expansions: CollectedExpansions,
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
        let value = collect_definitions(compiler, tcx, inventory)
            .map_err(ExpansionError::from)
            .and_then(|mut definitions| {
                let expansions = collect_expansions(compiler, tcx, inventory, &mut definitions)?;
                Ok(TestCollection {
                    definitions: definitions.graph,
                    expansions,
                })
            });
        *self
            .result
            .lock()
            .expect("expansion result mutex is poisoned") = Some(value);
        Compilation::Stop
    }

    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
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
            false,
        )
        .expect("macro rule inventory must be complete");
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
    let forwarded = generated_bang(source, "forwarded!()", "forwarded", "crate");
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
            sites: vec![ObservationSite::Source(
                expansion
                    .invocation_range
                    .expect("fixture expansion must have an invocation range"),
            )],
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
