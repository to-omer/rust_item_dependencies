#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::qualification::DeniedResourceProbe;
#[cfg(rust_item_dependencies_patched)]
use rust_item_dependencies::qualification::{
    ImportKindProbe, MacroInvocationProbe, MacroResolvedImportUseProbe, MonoProofKindProbe,
    MonoProofOriginProbe, MonoSiteProbe, MonoUseCauseProbe, QualificationReport,
    ResolvedImportUseProbe, probe_incremental_import_cache,
};
use rust_item_dependencies::qualification::{
    ProbeCollection, ProbeConfig, ProbeError, probe_source,
};

#[test]
fn pinned_driver_exposes_entry_definitions_expansion_and_main_children() {
    let config = local_probe_config();
    let report = probe_source(include_str!("fixtures/compiler/driver_smoke.rs"), &config)
        .expect("the pinned compiler must reach after_analysis");

    assert_eq!(
        report.entry_definition,
        "rust_item_dependencies_compiler_qualification::main"
    );

    let definition_paths = report
        .definitions
        .iter()
        .map(|definition| definition.path.as_str())
        .collect::<Vec<_>>();
    assert!(
        definition_paths
            .iter()
            .any(|path| path.ends_with("::unused")),
        "the inventory must include definitions outside main's closure"
    );

    let generated = report
        .definitions
        .iter()
        .find(|definition| definition.path.ends_with("::generated"))
        .expect("macro-generated function must be inventoried");
    let expansion = generated
        .expansion
        .as_ref()
        .expect("macro-generated function must retain expansion provenance");
    assert_eq!(expansion.kind, "make_generated!");
    assert_eq!(
        expansion.macro_definition.as_deref(),
        Some("rust_item_dependencies_compiler_qualification::make_generated")
    );

    let calls = report
        .main_children
        .iter()
        .filter(|child| {
            child.collection == ProbeCollection::Used && child.definition.ends_with("::call")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        calls.len(),
        2,
        "main's stock mono children must keep both concrete call instances: {calls:?}"
    );
    assert!(
        calls.iter().any(|call| {
            call.instance
                .as_deref()
                .is_some_and(|instance| instance.contains("Kept"))
        }),
        "the mono observation must retain call::<Kept>'s concrete instance: {calls:?}"
    );
    assert!(
        calls.iter().any(|call| {
            call.instance
                .as_deref()
                .is_some_and(|instance| instance.contains("AlsoKept"))
        }),
        "the mono observation must retain call::<AlsoKept>'s concrete instance: {calls:?}"
    );
    assert!(
        report
            .main_children
            .iter()
            .all(|child| !child.definition.ends_with("::unused")),
        "unused must not appear in main's mono children"
    );

    let error = probe_source(
        include_str!("fixtures/compiler/external_module.rs"),
        &config,
    )
    .expect_err("the in-memory source loader must deny an out-of-line module");
    let ProbeError::ExternalSourceAccess(paths) = error else {
        panic!("expected a denied source access, got {error:?}");
    };
    assert!(
        paths.iter().any(|path| path.ends_with("external.rs")),
        "rustc must have attempted the ordinary module path: {paths:?}"
    );

    let error = probe_source(
        include_str!("fixtures/compiler/include_resource.rs"),
        &config,
    )
    .expect_err("the in-memory source loader must deny include_str!");
    let ProbeError::ExternalSourceAccess(paths) = error else {
        panic!("expected a denied include resource, got {error:?}");
    };
    assert!(
        paths.iter().any(|path| path.ends_with("secret.txt")),
        "a macro-generated include must be denied before the file is read: {paths:?}"
    );

    let error = probe_source(
        include_str!("fixtures/compiler/unstable_feature.rs"),
        &config,
    )
    .expect_err("the nightly analyzer must reject unstable user syntax");
    assert_eq!(error, ProbeError::CompilationDidNotReachAnalysis);

    #[cfg(rust_item_dependencies_patched)]
    {
        let error = probe_source(
            include_str!("fixtures/compiler/environment_macro.rs"),
            &config,
        )
        .expect_err("the patched compiler must reject environment macros");
        assert_eq!(
            error,
            ProbeError::ExternalResourceAccess(vec![
                DeniedResourceProbe::Environment,
                DeniedResourceProbe::OptionalEnvironment,
            ])
        );
    }
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_preserves_import_leaf_and_trait_import_provenance() {
    let source = include_str!("fixtures/compiler/import_provenance.rs");
    let report = probe_source(source, &local_probe_config())
        .expect("the patched compiler must expose import provenance after analysis");
    assert_import_provenance_oracle(source, &report);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_joins_mono_proofs_and_selected_supertrait_impls() {
    let source = include_str!("fixtures/compiler/mono_proofs.rs");
    let report = probe_source(source, &local_probe_config())
        .expect("the patched compiler must expose complete monomorphization proofs");

    let dispatch = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::CompilerObservation
                && proof.cause == MonoUseCauseProbe::DirectCall
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::AssociatedItem { item, .. }
                        if item.ends_with("::Dispatch::invoke")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(dispatch.len(), 1, "{dispatch:#?}");
    let MonoProofKindProbe::AssociatedItem {
        arguments,
        raw_instance,
        codegen_instance,
        ..
    } = &dispatch[0].kind
    else {
        unreachable!()
    };
    assert_eq!(arguments, &["Routed", "u16", "3_usize"]);
    assert_eq!(raw_instance, codegen_instance);
    assert_eq!(
        dispatch[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(source, "impl Dispatch<u16, 3> for Routed")]
    );

    let dispatch_marker = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::SupertraitConstraint
                && proof.cause == MonoUseCauseProbe::DirectCall
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::TraitSelection {
                        trait_definition,
                        arguments,
                    } if trait_definition.ends_with("::Marker") && arguments == &["Routed"]
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(dispatch_marker.len(), 1, "{dispatch_marker:#?}");
    assert_eq!(dispatch_marker[0].from, dispatch[0].from);
    assert_eq!(dispatch_marker[0].site, dispatch[0].site);
    assert_eq!(
        dispatch_marker[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(source, "impl Marker for Routed")]
    );
    assert!(dispatch_marker[0].local_leaves.is_empty());

    let hrtb_call = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::CompilerObservation
                && proof.cause == MonoUseCauseProbe::DirectCall
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::AssociatedItem { item, .. }
                        if item.ends_with("::HrtbDispatch::invoke_hrtb")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(hrtb_call.len(), 1, "{hrtb_call:#?}");
    let hrtb_marker = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::SupertraitConstraint
                && proof.cause == MonoUseCauseProbe::DirectCall
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::TraitSelection {
                        trait_definition,
                        ..
                    } if trait_definition.ends_with("::LifetimeMarker")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(hrtb_marker.len(), 1, "{hrtb_marker:#?}");
    let MonoProofKindProbe::TraitSelection { arguments, .. } = &hrtb_marker[0].kind else {
        unreachable!()
    };
    assert_eq!(arguments, &["LifetimeRouted", "'{erased}", "u16"]);
    assert_eq!(hrtb_marker[0].from, hrtb_call[0].from);
    assert_eq!(hrtb_marker[0].site, hrtb_call[0].site);
    assert_eq!(
        hrtb_marker[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(
            source,
            "impl<'a> LifetimeMarker<'a, u16> for LifetimeRouted",
        )]
    );
    assert!(hrtb_marker[0].local_leaves.is_empty());

    let marker = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::SupertraitConstraint
                && proof.cause == MonoUseCauseProbe::VTableConstruction
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::TraitSelection {
                        trait_definition,
                        ..
                    } if trait_definition.ends_with("::Marker")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(marker.len(), 1, "{marker:#?}");
    assert_eq!(
        marker[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(source, "impl Marker for Concrete")]
    );
    assert!(marker[0].local_leaves.is_empty());
    assert!(matches!(marker[0].site, MonoSiteProbe::Source(_)));

    let projections = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            matches!(
                &proof.kind,
                MonoProofKindProbe::Projection { item, .. }
                    if item.ends_with("::Object::Value")
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(projections.len(), 1, "{projections:#?}");
    let MonoProofKindProbe::Projection {
        arguments,
        expected,
        ..
    } = &projections[0].kind
    else {
        unreachable!()
    };
    assert_eq!(arguments, &["Concrete"]);
    assert_eq!(expected, "Term::Ty(u8)");
    assert_eq!(
        projections[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(source, "impl Object for Concrete")]
    );
    assert_eq!(
        projections[0]
            .local_leaves
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range_in_statement(
            source,
            "type Value = u8",
            "type Value",
        )]
    );

    let decoy_proofs = report
        .mono_proofs
        .iter()
        .filter(|proof| {
            let arguments = match &proof.kind {
                MonoProofKindProbe::TraitSelection { arguments, .. }
                | MonoProofKindProbe::AssociatedItem { arguments, .. }
                | MonoProofKindProbe::Projection { arguments, .. } => arguments,
            };
            arguments.iter().any(|argument| argument == "UnusedRoute")
                || proof
                    .local_impls
                    .iter()
                    .chain(&proof.local_leaves)
                    .any(|definition| definition.path.contains("UnusedRoute"))
        })
        .count();
    assert_eq!(decoy_proofs, 0);

    let projection_source = include_str!("fixtures/compiler/non_trait_super_clause.rs");
    let projection_report = probe_source(projection_source, &local_probe_config())
        .expect("a projection clause in a supertrait declaration must not invalidate mono proofs");
    let base_selection = projection_report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::SupertraitConstraint
                && proof.cause == MonoUseCauseProbe::DirectCall
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::TraitSelection {
                        trait_definition,
                        arguments,
                    } if trait_definition.ends_with("::Base") && arguments == &["Concrete"]
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(base_selection.len(), 1, "{base_selection:#?}");
    assert_eq!(
        base_selection[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(projection_source, "impl Base for Concrete")]
    );

    let item_projection = projection_report
        .mono_proofs
        .iter()
        .filter(|proof| {
            proof.origin == MonoProofOriginProbe::CompilerObservation
                && proof.cause == MonoUseCauseProbe::VTableConstruction
                && matches!(
                    &proof.kind,
                    MonoProofKindProbe::Projection {
                        item,
                        arguments,
                        expected,
                    } if item.ends_with("::Base::Item")
                        && arguments == &["Concrete"]
                        && expected == "Term::Ty(u8)"
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(item_projection.len(), 1, "{item_projection:#?}");
    assert_eq!(
        item_projection[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(projection_source, "impl Base for Concrete")]
    );
    assert_eq!(
        item_projection[0]
            .local_leaves
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range_in_statement(
            projection_source,
            "type Item = u8",
            "type Item",
        )]
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_follows_required_consts_before_function_allocation() {
    let source = include_str!("fixtures/compiler/const_trait_function.rs");
    let report = probe_source(source, &local_probe_config())
        .expect("the patched compiler must preserve trait function requests in const bodies");

    let mut function_uses = report
        .const_trait_function_uses
        .iter()
        .filter(|use_| {
            use_.item.ends_with("::Table::make")
                && use_.body.promoted.is_none()
                && matches!(
                    use_.arguments.first().map(String::as_str),
                    Some("Defaulted" | "Overridden")
                )
        })
        .collect::<Vec<_>>();
    function_uses.sort_by(|left, right| left.arguments.cmp(&right.arguments));
    assert_eq!(function_uses.len(), 2, "{function_uses:#?}");
    assert_eq!(
        function_uses
            .iter()
            .map(|use_| use_.arguments.as_slice())
            .collect::<Vec<_>>(),
        [
            ["Defaulted", "u16", "3_usize",],
            ["Overridden", "u32", "5_usize",],
        ]
    );
    assert!(
        function_uses
            .iter()
            .all(|use_| use_.raw_instance == use_.codegen_instance)
    );
    assert_eq!(
        function_uses
            .iter()
            .map(|use_| {
                use_.local_impls
                    .iter()
                    .map(|definition| (definition.path.as_str(), definition.source_range))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
        [
            vec![(
                "rust_item_dependencies_compiler_qualification::<Defaulted as Table<u16, 3>>",
                marker_range(source, "impl Table<u16, 3> for Defaulted"),
            )],
            vec![(
                "rust_item_dependencies_compiler_qualification::<Overridden as Table<u32, 5>>",
                marker_range(source, "impl Table<u32, 5> for Overridden"),
            )],
        ]
    );
    assert_eq!(
        function_uses
            .iter()
            .map(|use_| {
                use_.local_leaves
                    .iter()
                    .map(|definition| (definition.path.as_str(), definition.source_range))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
        [
            vec![(
                "rust_item_dependencies_compiler_qualification::<Defaulted as Table<u16, 3>>::make",
                marker_range_after(source, "impl Table<u16, 3> for Defaulted", "fn make()",),
            )],
            vec![(
                "rust_item_dependencies_compiler_qualification::<Overridden as Table<u32, 5>>::make",
                marker_range_after(source, "impl Table<u32, 5> for Overridden", "fn make()",),
            )],
        ]
    );
    assert_eq!(
        function_uses
            .iter()
            .map(|use_| use_.collection)
            .collect::<Vec<_>>(),
        [ProbeCollection::Used, ProbeCollection::Used]
    );
    assert_eq!(
        function_uses
            .iter()
            .map(|use_| use_.site.clone())
            .collect::<Vec<_>>(),
        [
            MonoSiteProbe::Source(marker_range(source, "Self::make")),
            MonoSiteProbe::Source(marker_range(source, "<Self as Table<u32, 5>>::make")),
        ]
    );

    let promoted_uses = report
        .const_trait_function_uses
        .iter()
        .filter(|use_| use_.item.ends_with("::Table::make") && use_.body.promoted.is_some())
        .collect::<Vec<_>>();
    assert_eq!(promoted_uses.len(), 1, "{promoted_uses:#?}");
    assert!(
        promoted_uses[0]
            .body
            .definition
            .ends_with("::from_promoted")
    );
    assert_eq!(promoted_uses[0].arguments, ["Defaulted", "u16", "3_usize"]);
    assert_eq!(
        promoted_uses[0].raw_instance,
        promoted_uses[0].codegen_instance
    );
    assert_eq!(promoted_uses[0].collection, ProbeCollection::Used);
    assert_eq!(promoted_uses[0].local_impls, function_uses[0].local_impls);
    assert_eq!(promoted_uses[0].local_leaves, function_uses[0].local_leaves);
    assert_eq!(
        promoted_uses[0].site,
        MonoSiteProbe::Source(marker_range(source, "<T as Table<A, K>>::make"))
    );

    let tracked_uses = report
        .const_trait_function_uses
        .iter()
        .filter(|use_| use_.item.ends_with("::Tracked::call"))
        .collect::<Vec<_>>();
    assert_eq!(tracked_uses.len(), 1, "{tracked_uses:#?}");
    assert_eq!(tracked_uses[0].arguments, ["TrackedImpl"]);
    assert_ne!(
        tracked_uses[0].raw_instance,
        tracked_uses[0].codegen_instance
    );
    assert_eq!(tracked_uses[0].collection, ProbeCollection::Used);
    assert_eq!(
        tracked_uses[0].site,
        MonoSiteProbe::Source(marker_range_after(source, "trait Tracked", "Self::call"))
    );
    assert_eq!(
        tracked_uses[0]
            .local_impls
            .iter()
            .map(|definition| (definition.path.as_str(), definition.source_range))
            .collect::<Vec<_>>(),
        [(
            "rust_item_dependencies_compiler_qualification::<TrackedImpl as Tracked>",
            marker_range(source, "impl Tracked for TrackedImpl"),
        )]
    );
    assert_eq!(
        tracked_uses[0]
            .local_leaves
            .iter()
            .map(|definition| (definition.path.as_str(), definition.source_range))
            .collect::<Vec<_>>(),
        [(
            "rust_item_dependencies_compiler_qualification::<TrackedImpl as Tracked>::call",
            marker_range_after(source, "impl Tracked for TrackedImpl", "fn call()"),
        )]
    );

    let mut associated_const_uses = report
        .required_const_uses
        .iter()
        .filter(|use_| {
            use_.request_definition.ends_with("::Table::FUNCTIONS")
                && matches!(
                    use_.request_arguments.first().map(String::as_str),
                    Some("Defaulted" | "Overridden")
                )
        })
        .collect::<Vec<_>>();
    associated_const_uses
        .sort_by(|left, right| left.request_arguments.cmp(&right.request_arguments));
    assert_eq!(associated_const_uses.len(), 2, "{associated_const_uses:#?}");
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.request_definition.as_str())
            .collect::<Vec<_>>(),
        [
            "rust_item_dependencies_compiler_qualification::Table::FUNCTIONS",
            "rust_item_dependencies_compiler_qualification::Table::FUNCTIONS",
        ]
    );
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.request_arguments.as_slice())
            .collect::<Vec<_>>(),
        [
            ["Defaulted", "u16", "3_usize",],
            ["Overridden", "u32", "5_usize",],
        ]
    );
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.target.arguments.as_slice())
            .collect::<Vec<_>>(),
        vec![&["Defaulted", "u16", "3_usize"][..], &[][..]],
        "the default retains trait substitutions while the concrete override has no own parameters"
    );
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.target.definition.as_str())
            .collect::<Vec<_>>(),
        [
            "rust_item_dependencies_compiler_qualification::Table::FUNCTIONS",
            "rust_item_dependencies_compiler_qualification::<Overridden as Table<u32, 5>>::FUNCTIONS",
        ]
    );
    assert!(
        associated_const_uses
            .iter()
            .all(|use_| use_.target.promoted.is_none())
    );
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.collection)
            .collect::<Vec<_>>(),
        [ProbeCollection::Used, ProbeCollection::Used]
    );
    let associated_const_site =
        MonoSiteProbe::Source(marker_range(source, "<T as Table<A, K>>::FUNCTIONS"));
    assert_eq!(
        associated_const_uses
            .iter()
            .map(|use_| use_.site.clone())
            .collect::<Vec<_>>(),
        [associated_const_site.clone(), associated_const_site]
    );
    for (function_use, const_use) in function_uses.iter().zip(&associated_const_uses) {
        assert_eq!(function_use.body, const_use.target);
    }

    let mut multi_site_uses = report
        .required_const_uses
        .iter()
        .filter(|use_| {
            use_.request_definition.ends_with("::Table::FUNCTIONS")
                && use_.request_arguments == ["MultiSite", "u8", "2_usize"]
        })
        .collect::<Vec<_>>();
    multi_site_uses.sort_by(|left, right| left.site.cmp(&right.site));
    assert_eq!(multi_site_uses.len(), 2, "{multi_site_uses:#?}");
    let mut multi_site_ranges = marker_ranges_between(
        source,
        "fn from_two_sites",
        "fn from_promoted",
        "<T as Table<A, K>>::FUNCTIONS",
    )
    .into_iter()
    .map(MonoSiteProbe::Source)
    .collect::<Vec<_>>();
    multi_site_ranges.sort();
    assert_eq!(
        multi_site_uses
            .iter()
            .map(|use_| use_.site.clone())
            .collect::<Vec<_>>(),
        multi_site_ranges
    );
    assert_eq!(multi_site_uses[0].owner, multi_site_uses[1].owner);
    assert_eq!(multi_site_uses[0].target, multi_site_uses[1].target);

    let multi_site_body_uses = report
        .const_trait_function_uses
        .iter()
        .filter(|use_| {
            use_.item.ends_with("::Table::make") && use_.arguments == ["MultiSite", "u8", "2_usize"]
        })
        .collect::<Vec<_>>();
    assert_eq!(multi_site_body_uses.len(), 1, "{multi_site_body_uses:#?}");
    assert_eq!(multi_site_body_uses[0].body, multi_site_uses[0].target);
    assert_eq!(
        multi_site_body_uses[0]
            .local_impls
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range(source, "impl Table<u8, 2> for MultiSite")]
    );
    assert_eq!(
        multi_site_body_uses[0]
            .local_leaves
            .iter()
            .map(|definition| definition.source_range)
            .collect::<Vec<_>>(),
        [marker_range_after(
            source,
            "impl Table<u8, 2> for MultiSite",
            "fn make()",
        )]
    );

    assert_eq!(
        report
            .const_trait_function_uses
            .iter()
            .filter(|use_| {
                use_.arguments
                    .first()
                    .is_some_and(|argument| argument == "Unused")
            })
            .count(),
        0
    );
    assert_eq!(
        report
            .required_const_uses
            .iter()
            .filter(|use_| {
                use_.request_arguments
                    .first()
                    .is_some_and(|argument| argument == "Unused")
            })
            .count(),
        0
    );
}

#[cfg(rust_item_dependencies_patched)]
fn assert_import_provenance_oracle(source: &str, report: &QualificationReport) {
    let run_owner = "rust_item_dependencies_compiler_qualification::explicit_case::run";
    let outer_value_range = marker_range_in_statement(source, "use f::{", "ExportedValue");
    let facade_value_range = marker_range_in_statement(source, "pub use crate::origin::{", "Value");
    let outer_action_range = marker_range_in_statement(source, "use f::{", "ExportedAction");
    let facade_action_range =
        marker_range_in_statement(source, "pub use crate::origin::{", "Action");
    let alias_type_start = source
        .find("Option<ValueAlias>")
        .expect("fixture must contain the imported alias type")
        + "Option<".len();
    let alias_type_site = unique_import_use(&report.resolved_import_uses, |record| {
        record.owner == run_owner
            && record.namespace == "TypeNS"
            && record.target.ends_with("::origin::Value")
            && record.segment_range
                == (
                    alias_type_start as u32,
                    alias_type_start as u32 + "ValueAlias".len() as u32,
                )
    });
    assert_eq!(
        alias_type_site
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![ImportKindProbe::Single, ImportKindProbe::Single]
    );
    assert_eq!(
        alias_type_site.import_chain[0].source_range,
        Some(outer_value_range),
        "the selected body path must identify the Value leaf, not a sibling in the use tree"
    );
    assert_eq!(
        alias_type_site.import_chain[1].source_range,
        Some(facade_value_range),
        "the selected body path must identify the Value re-export leaf"
    );

    let outer_value_definition = alias_type_site.import_chain[0]
        .definition
        .as_deref()
        .expect("the outer Value leaf must have a local definition");
    let value_prefix = unique_import_use(&report.resolved_import_uses, |record| {
        record.owner == outer_value_definition
            && record.namespace == "TypeNS"
            && record.target.ends_with("::facade")
            && record.segment_range == marker_range_in_statement(source, "use f::{", "f")
    });
    assert_eq!(value_prefix.import_chain.len(), 1);
    assert_eq!(
        value_prefix.import_chain[0].source_range,
        Some(marker_range_in_statement(
            source,
            "use crate::facade as f;",
            "crate::facade"
        )),
        "the selected nested leaf must retain the alias used by its prefix"
    );

    let pattern_start = source
        .rfind("ValueAlias =>")
        .expect("fixture must contain the imported constructor pattern")
        as u32;
    let pattern_site = unique_import_use(&report.resolved_import_uses, |record| {
        record.owner == run_owner
            && record.namespace == "ValueNS"
            && record.segment_range == (pattern_start, pattern_start + "ValueAlias".len() as u32)
    });
    assert_eq!(
        pattern_site
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![ImportKindProbe::Single, ImportKindProbe::Single],
        "a single-identifier constructor pattern must use the same exact leaf chain"
    );

    let glob_site = unique_import_use(&report.resolved_import_uses, |record| {
        record.owner.ends_with("::glob_case::run")
            && record.namespace == "TypeNS"
            && record.target.ends_with("::origin::GlobValue")
    });
    assert_eq!(
        glob_site
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![ImportKindProbe::Glob, ImportKindProbe::Glob]
    );
    assert_range_inside(
        glob_site.import_chain[0]
            .source_range
            .expect("the use-site glob must be local"),
        source_range(source, "use crate::glob_facade::*;"),
    );
    assert_range_inside(
        glob_site.import_chain[1]
            .source_range
            .expect("the facade glob must be local"),
        source_range(source, "pub use crate::origin::*;"),
    );

    let selected = report
        .selected_trait_imports
        .iter()
        .filter(|record| record.owner == run_owner)
        .collect::<Vec<_>>();
    assert_eq!(
        selected.len(),
        3,
        "two dot calls and one type-relative associated call must remain distinct: {selected:?}"
    );
    assert_eq!(
        selected
            .iter()
            .filter(|record| record.selected_item.ends_with("::origin::Action::act"))
            .count(),
        2
    );
    assert_eq!(
        selected
            .iter()
            .filter(|record| record
                .selected_item
                .ends_with("::origin::Action::static_value"))
            .count(),
        1
    );
    for record in selected {
        assert_eq!(record.import_chain.len(), 2, "{record:?}");
        assert_eq!(record.import_chain[0].source_range, outer_action_range);
        assert_eq!(record.import_chain[1].source_range, facade_action_range);
    }
    let mut selected_sites = report
        .selected_trait_imports
        .iter()
        .filter(|record| record.owner == run_owner)
        .map(|record| record.site_range)
        .collect::<Vec<_>>();
    selected_sites.sort();
    let mut expected_sites = all_marker_ranges(source, "value.act()");
    expected_sites.push(marker_range(source, "ValueAlias::static_value"));
    expected_sites.sort();
    assert_eq!(
        selected_sites, expected_sites,
        "each selected trait-import chain must remain attached to its exact resolution site"
    );

    assert!(
        report
            .resolved_import_uses
            .iter()
            .filter(|record| record.owner == run_owner)
            .all(|record| !record.target.contains("Unused")),
        "the unused sibling leaf must not leak into the run body's selected chains"
    );

    assert!(
        report
            .resolved_import_uses
            .iter()
            .all(|record| !record.owner.ends_with("::primitive_case::run")),
        "an imported std module rejected by primitive fallback is not a semantic dependency"
    );
    let primitive_module_owner =
        "rust_item_dependencies_compiler_qualification::primitive_module_case::run";
    let primitive_module_path = marker_range(source, "u8::MAX");
    let primitive_module_site = unique_import_use(&report.resolved_import_uses, |record| {
        record.owner == primitive_module_owner
            && record.namespace == "TypeNS"
            && record.path_range == primitive_module_path
            && record.segment_range == (primitive_module_path.0, primitive_module_path.0 + 2)
    });
    assert_eq!(
        primitive_module_site
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![ImportKindProbe::Single],
        "a real std::u8 module resolution must survive the primitive fallback transaction"
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_restores_typeck_observations_from_incremental_cache() {
    let source = include_str!("fixtures/compiler/import_provenance.rs");
    let (seed, loaded) = probe_incremental_import_cache(source, &local_probe_config())
        .expect("both complete compiler runs must preserve the on-disk query result");

    assert_eq!(
        loaded.selected_trait_imports, seed.selected_trait_imports,
        "the loaded typeck_root result must preserve every selected trait-import fact"
    );
    assert_eq!(
        loaded.typeck_impl_dependencies, seed.typeck_impl_dependencies,
        "the loaded typeck_root result must preserve every impl dependency, including its source span"
    );

    let semantic_dependencies = seed
        .typeck_impl_dependencies
        .iter()
        .map(|dependency| {
            (
                dependency.source_owner.as_str(),
                dependency.implementation.as_str(),
                dependency.associated_item.as_deref(),
            )
        })
        .collect::<BTreeSet<_>>();
    let run = "rust_item_dependencies_compiler_qualification::explicit_case::run";
    let action_impl =
        "rust_item_dependencies_compiler_qualification::<origin::Value as origin::Action>";
    let act =
        "rust_item_dependencies_compiler_qualification::<origin::Value as origin::Action>::act";
    let static_value =
        "rust_item_dependencies_compiler_qualification::origin::Action::static_value";
    assert_eq!(
        semantic_dependencies,
        BTreeSet::from([
            (action_impl, action_impl, None),
            (run, action_impl, None),
            (run, action_impl, Some(act)),
            (run, action_impl, Some(static_value)),
        ]),
        "the cached field must contain the fixture's exact nonempty semantic dependency set"
    );
    assert_eq!(
        seed.typeck_impl_dependencies
            .iter()
            .filter(|dependency| dependency.associated_item.is_some())
            .map(|dependency| (
                dependency.source_owner.as_str(),
                dependency.source_range,
                dependency.implementation.as_str(),
                dependency.associated_item.as_deref(),
            ))
            .collect::<Vec<_>>(),
        vec![
            (
                run,
                marker_range_after(source, "let first", "value.act()"),
                action_impl,
                Some(act),
            ),
            (
                run,
                marker_range_after(source, "let second", "value.act()"),
                action_impl,
                Some(act),
            ),
            (
                run,
                marker_range(source, "ValueAlias::static_value"),
                action_impl,
                Some(static_value),
            ),
        ],
        "each cached associated dependency must retain its exact source site and selected leaf"
    );
    assert_eq!(
        seed.typeck_impl_dependencies
            .iter()
            .filter(|dependency| dependency.associated_item.is_none())
            .map(|dependency| (
                dependency.source_owner.as_str(),
                dependency.source_range,
                dependency.implementation.as_str(),
            ))
            .collect::<Vec<_>>(),
        vec![
            (
                action_impl,
                marker_range_after(source, "impl Action for", "Value"),
                action_impl,
            ),
            (
                run,
                marker_range_after(source, "let first", "act"),
                action_impl,
            ),
            (
                run,
                marker_range_after(source, "let second", "act"),
                action_impl,
            ),
            (
                run,
                marker_range(source, "ValueAlias::static_value()"),
                action_impl,
            ),
        ],
        "each cached impl-shell dependency must retain its exact owner and source site"
    );
    assert_import_provenance_oracle(source, &seed);
    assert_import_provenance_oracle(source, &loaded);
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_preserves_complete_macro_invocation_origins() {
    let source = include_str!("fixtures/compiler/expansion_origin.rs");
    let report = probe_source(source, &local_probe_config())
        .expect("the patched compiler must expose expansion origins after analysis");

    let mut written = report
        .macro_invocations
        .iter()
        .filter(|record| record.discovered_in.is_none())
        .map(|record| {
            (
                record.kind.as_str(),
                record.written_invocation_range,
                record.written_node_range,
                record.written_target_range,
            )
        })
        .collect::<Vec<_>>();
    written.sort_by_key(|record| record.1);
    assert_eq!(
        written,
        vec![
            (
                "make_items!",
                Some(marker_range(source, "make_items!()")),
                Some(marker_range(source, "make_items!();")),
                None,
            ),
            (
                "outer!",
                Some(marker_range(source, "outer!()")),
                Some(marker_range(source, "outer!();")),
                None,
            ),
            (
                "forward!",
                Some(marker_range(source, "forward!(forwarded!();)")),
                Some(marker_range(source, "forward!(forwarded!(););")),
                None,
            ),
            (
                "define_late!",
                Some(marker_range(source, "define_late!()")),
                Some(marker_range(source, "define_late!();")),
                None,
            ),
            (
                "concat!",
                Some(marker_range(source, "concat!(late!())")),
                Some(marker_range(source, "concat!(late!())")),
                None,
            ),
            (
                "concat!",
                Some(marker_range(source, "concat!(\"line=\", line!())")),
                Some(marker_range(source, "concat!(\"line=\", line!())")),
                None,
            ),
            (
                "#[derive]",
                Some(marker_range(source, "#[derive(Clone)]")),
                Some(range_between(source, "#[derive(Clone)]", "struct Derived;",)),
                Some(marker_range(source, "struct Derived;")),
            ),
            (
                "println!",
                Some(marker_range(source, "println!(\"expansion-origin\")")),
                Some(marker_range(source, "println!(\"expansion-origin\");")),
                None,
            ),
        ],
        "the observer must inventory every macro invocation written in main.rs"
    );

    let make_items = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "make_items!" && record.discovered_in.is_none()
    });
    assert_eq!(
        make_items.macro_definition.as_deref(),
        Some("rust_item_dependencies_compiler_qualification::make_items")
    );
    assert_eq!(make_items.fragment_kind, "Items");
    assert_eq!(make_items.implementation_kind, "Declarative");
    assert_eq!(
        make_items.generated_definitions,
        vec![
            "rust_item_dependencies_compiler_qualification::generated_one",
            "rust_item_dependencies_compiler_qualification::generated_two",
        ],
        "stock expn_that_defined must invert both sibling definitions into the item invocation"
    );

    let outer = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "outer!" && record.discovered_in.is_none()
    });
    assert!(
        outer.generated_definitions.is_empty(),
        "the outer expansion directly generates an invocation, not the inner function"
    );
    assert_eq!(outer.fragment_kind, "Items");
    assert_eq!(outer.implementation_kind, "Declarative");
    let inner = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "inner!" && record.discovered_in == Some(outer.expansion)
    });
    assert_eq!(inner.parent, Some(outer.expansion));
    assert_eq!(inner.fragment_kind, "Items");
    assert_eq!(inner.implementation_kind, "Declarative");
    assert_eq!(
        inner.generated_definitions,
        vec!["rust_item_dependencies_compiler_qualification::nested_generated"],
        "the innermost expansion must own its directly generated definition"
    );
    assert_eq!(
        inner.macro_definition.as_deref(),
        Some("rust_item_dependencies_compiler_qualification::inner")
    );
    assert_eq!(inner.written_invocation_range, None);
    assert_eq!(inner.written_node_range, None);

    let forward = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "forward!" && record.discovered_in.is_none()
    });
    let forwarded = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "forwarded!" && record.discovered_in == Some(forward.expansion)
    });
    assert_eq!(forwarded.parent, Some(forward.expansion));
    assert_eq!(forwarded.source_call_parent, None);
    assert_eq!(
        forwarded.discovered_in_kind,
        Some(
            rust_item_dependencies::qualification::ExpansionKindProbe::Macro("forward!".to_owned())
        )
    );
    assert_eq!(
        forwarded.source_node_range,
        Some(marker_range(source, "forwarded!();"))
    );
    assert_eq!(
        forwarded.generated_definitions,
        vec!["rust_item_dependencies_compiler_qualification::forwarded_generated"]
    );

    let define_late = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "define_late!" && record.discovered_in.is_none()
    });
    assert_eq!(
        define_late.generated_definitions,
        vec!["rust_item_dependencies_compiler_qualification::late"]
    );
    let retry_concat = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "concat!"
            && record.written_invocation_range == Some(marker_range(source, "concat!(late!())"))
    });
    let late = unique_macro_invocation(&report.macro_invocations, |record| record.kind == "late!");
    assert_eq!(late.discovered_in, Some(retry_concat.expansion));
    assert_eq!(
        late.discovered_in_kind,
        Some(
            rust_item_dependencies::qualification::ExpansionKindProbe::Macro("concat!".to_owned())
        )
    );
    assert_eq!(late.parent, None);
    assert_eq!(late.source_call_parent, None);
    assert_eq!(late.fragment_kind, "Expr");
    assert_eq!(late.implementation_kind, "Declarative");
    let (retry_concat_start, _) = marker_range(source, "concat!(late!())");
    assert_eq!(
        late.source_node_range,
        Some((retry_concat_start + 8, retry_concat_start + 15))
    );

    let eager_concat = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "concat!"
            && record.written_invocation_range
                == Some(marker_range(source, "concat!(\"line=\", line!())"))
    });
    let line = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "line!" && record.discovered_in == Some(eager_concat.expansion)
    });
    assert_eq!(line.parent, None);
    assert_eq!(line.source_call_parent, None);
    assert_eq!(
        line.discovered_in_kind,
        Some(
            rust_item_dependencies::qualification::ExpansionKindProbe::Macro("concat!".to_owned())
        )
    );
    assert_eq!(line.fragment_kind, "Expr");
    assert_eq!(line.implementation_kind, "Builtin");
    assert_eq!(
        line.source_node_range,
        Some(marker_range(source, "line!()"))
    );

    let println = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "println!" && record.discovered_in.is_none()
    });
    assert!(
        println
            .macro_definition
            .as_deref()
            .is_some_and(|definition| definition.ends_with("::println")),
        "println! must resolve to its external declarative macro: {println:?}"
    );
    assert_eq!(println.fragment_kind, "Stmts");
    assert_eq!(println.implementation_kind, "Declarative");
    assert!(
        println.generated_definitions.is_empty(),
        "an invocation inventory cannot depend on generated LocalDefIds"
    );
    let format_args = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "$crate::format_args_nl!" && record.discovered_in == Some(println.expansion)
    });
    assert_eq!(format_args.parent, Some(println.expansion));
    assert_eq!(format_args.source_call_parent, Some(println.expansion));
    assert_eq!(
        format_args.discovered_in_kind,
        Some(
            rust_item_dependencies::qualification::ExpansionKindProbe::Macro("println!".to_owned())
        )
    );
    assert_eq!(format_args.fragment_kind, "OptExpr");
    assert_eq!(format_args.implementation_kind, "Builtin");
    assert_eq!(format_args.written_invocation_range, None);
    assert_eq!(format_args.written_node_range, None);
    assert!(format_args.generated_definitions.is_empty());

    let derive_container = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "#[derive]" && record.discovered_in.is_none()
    });
    let clone_derive = unique_macro_invocation(&report.macro_invocations, |record| {
        record.kind == "#[derive(Clone)]"
            && record.discovered_in == Some(derive_container.expansion)
    });
    assert_eq!(derive_container.fragment_kind, "Items");
    assert_eq!(derive_container.implementation_kind, "Builtin");
    assert_eq!(clone_derive.fragment_kind, "Items");
    assert_eq!(clone_derive.implementation_kind, "Builtin");
    assert_eq!(clone_derive.parent, Some(derive_container.expansion));
    assert_eq!(clone_derive.written_invocation_range, None);
    assert!(
        clone_derive
            .generated_definitions
            .iter()
            .any(|definition| definition.ends_with("::clone")),
        "the stock definition inverse must attach the generated Clone method: {clone_derive:?}"
    );
    assert!(
        clone_derive
            .macro_definition
            .as_deref()
            .is_some_and(|definition| definition.ends_with("::Clone")),
        "the builtin derive must retain its external definition: {clone_derive:?}"
    );
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn patched_driver_preserves_final_macro_import_paths() {
    let source = include_str!("fixtures/compiler/macro_import_provenance.rs");
    let report = probe_source(source, &local_probe_config())
        .expect("the patched compiler must expose finalized macro import paths");

    let local_alias = unique_macro_invocation(&report.macro_invocations, |record| {
        record.written_invocation_range == Some(marker_range(source, "local_alias!()"))
    });
    assert!(
        local_alias
            .macro_definition
            .as_deref()
            .is_some_and(|definition| definition.ends_with("::origin::value"))
    );
    let local_use = unique_macro_import(&local_alias.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
            && record.segment_range
                == Some(marker_range_in_statement(
                    source,
                    "local_alias!();",
                    "local_alias",
                ))
    });
    assert_eq!(
        local_use
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![
            ImportKindProbe::Single,
            ImportKindProbe::Single,
            ImportKindProbe::Single,
        ]
    );
    assert_eq!(
        local_use
            .import_chain
            .iter()
            .map(|step| step.source_range)
            .collect::<Vec<_>>(),
        vec![
            Some(marker_range_in_statement(
                source,
                "use crate::facade::{",
                "second"
            )),
            Some(marker_range_in_statement(
                source,
                "pub(crate) use crate::origin::{",
                "first"
            )),
            Some(marker_range_in_statement(
                source,
                "pub(crate) use value as first;",
                "value"
            )),
        ],
        "macro import steps must remain ordered from the invocation-visible leaf to the definition"
    );

    let print_alias = unique_macro_invocation(&report.macro_invocations, |record| {
        record.written_invocation_range == Some(marker_range(source, "print_alias!(\"alias\")"))
    });
    let print_use = unique_macro_import(&print_alias.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
            && record.segment_range
                == Some(marker_range_in_statement(
                    source,
                    "print_alias!(\"alias\");",
                    "print_alias",
                ))
    });
    assert_eq!(print_use.import_chain.len(), 1);
    assert_eq!(print_use.import_chain[0].kind, ImportKindProbe::Single);
    assert_eq!(
        print_use.import_chain[0].source_range,
        Some(marker_range_in_statement(source, "use std::{", "println"))
    );

    let prelude = unique_macro_invocation(&report.macro_invocations, |record| {
        record.written_invocation_range == Some(marker_range(source, "println!(\"prelude\")"))
    });
    assert!(
        prelude.resolved_import_uses.is_empty(),
        "a macro-prelude resolution must not invent a local import dependency"
    );

    let prefix = unique_macro_invocation(&report.macro_invocations, |record| {
        record.written_invocation_range == Some(marker_range(source, "facade_alias::second!()"))
    });
    assert_eq!(prefix.resolved_import_uses.len(), 2, "{prefix:#?}");
    let prefix_module = unique_macro_import(&prefix.resolved_import_uses, |record| {
        record.namespace == "TypeNS"
            && record.segment_range
                == Some(marker_range_in_statement(
                    source,
                    "facade_alias::second!();",
                    "facade_alias",
                ))
    });
    assert_eq!(
        prefix_module.import_chain[0].source_range,
        Some(marker_range_in_statement(
            source,
            "use crate::facade as facade_alias;",
            "crate::facade"
        ))
    );
    let prefix_macro = unique_macro_import(&prefix.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
            && record.segment_range
                == Some(marker_range_in_statement(
                    source,
                    "facade_alias::second!();",
                    "second",
                ))
    });
    assert_eq!(prefix_macro.import_chain.len(), 2);
    assert_eq!(
        prefix_macro
            .import_chain
            .iter()
            .map(|step| step.source_range)
            .collect::<Vec<_>>(),
        vec![
            Some(marker_range_in_statement(
                source,
                "pub(crate) use crate::origin::{",
                "first"
            )),
            Some(marker_range_in_statement(
                source,
                "pub(crate) use value as first;",
                "value"
            )),
        ]
    );

    assert!(
        report.macro_invocations.iter().all(|invocation| {
            invocation.resolved_import_uses.iter().all(|record| {
                record.import_chain.iter().all(|step| {
                    step.definition.as_deref().is_none_or(|definition| {
                        !definition.contains("unused") && !definition.contains("unused_std")
                    })
                })
            })
        }),
        "unused sibling import leaves must not leak into macro provenance"
    );

    let export_source = include_str!("fixtures/compiler/macro_export_provenance.rs");
    let export_report = probe_source(export_source, &local_probe_config())
        .expect("the patched compiler must retain MacroExport source identity");
    let alias = unique_macro_invocation(&export_report.macro_invocations, |record| {
        record.written_invocation_range == Some(marker_range(export_source, "alias!()"))
    });
    let export_use = unique_macro_import(&alias.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
    });
    assert_eq!(
        export_use
            .import_chain
            .iter()
            .map(|step| step.kind)
            .collect::<Vec<_>>(),
        vec![ImportKindProbe::Single, ImportKindProbe::MacroExport]
    );
    assert!(
        export_use.import_chain[1]
            .definition
            .as_deref()
            .is_some_and(|definition| definition.ends_with("::exported")),
        "MacroExport must retain the macro definition instead of an anonymous source step"
    );

    let macro_use_source = include_str!("fixtures/compiler/macro_use_provenance.rs");
    let mut macro_use_config = local_probe_config();
    macro_use_config.edition = "2015".to_owned();
    let macro_use_report = probe_source(macro_use_source, &macro_use_config)
        .expect("the patched compiler must retain MacroUse source identity");
    let println = unique_macro_invocation(&macro_use_report.macro_invocations, |record| {
        record.written_invocation_range
            == Some(marker_range(macro_use_source, "println!(\"macro-use\")"))
    });
    let macro_use = unique_macro_import(&println.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
    });
    assert_eq!(macro_use.import_chain.len(), 1, "{macro_use:#?}");
    assert_eq!(macro_use.import_chain[0].kind, ImportKindProbe::MacroUse);
    assert!(
        macro_use.import_chain[0]
            .definition
            .as_deref()
            .is_some_and(|definition| definition.ends_with("::std")),
        "MacroUse must retain the extern crate definition: {macro_use:#?}"
    );
    assert_range_inside(
        macro_use.import_chain[0]
            .source_range
            .expect("MacroUse must retain a local source range"),
        range_between(macro_use_source, "#[macro_use]", "extern crate std;"),
    );

    let retry_source = include_str!("fixtures/compiler/macro_import_retry.rs");
    let retry_report = probe_source(retry_source, &local_probe_config())
        .expect("the final retry result must retain its generated import path");
    let late_alias = unique_macro_invocation(&retry_report.macro_invocations, |record| {
        record.written_invocation_range
            == Some(marker_range(retry_source, "late_alias!(\"retry\")"))
    });
    let retry_use = unique_macro_import(&late_alias.resolved_import_uses, |record| {
        record.namespace == "MacroNS"
            && record.segment_range
                == Some(marker_range_in_statement(
                    retry_source,
                    "late_alias!(\"retry\");",
                    "late_alias",
                ))
    });
    assert_eq!(retry_use.import_chain.len(), 1, "{retry_use:#?}");
    assert_eq!(retry_use.import_chain[0].kind, ImportKindProbe::Single);
    assert_eq!(
        retry_use.import_chain[0].source_range,
        Some(marker_range_in_statement(
            retry_source,
            "use std::eprintln as late_alias;",
            "std::eprintln",
        )),
        "the retry must commit the generated import exactly once"
    );
}

#[cfg(rust_item_dependencies_patched)]
fn unique_import_use(
    records: &[ResolvedImportUseProbe],
    predicate: impl Fn(&ResolvedImportUseProbe) -> bool,
) -> &ResolvedImportUseProbe {
    let matches = records
        .iter()
        .filter(|record| predicate(record))
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "expected exactly one matching import use: {matches:?}"
    );
    matches[0]
}

#[cfg(rust_item_dependencies_patched)]
fn unique_macro_invocation(
    records: &[MacroInvocationProbe],
    predicate: impl Fn(&MacroInvocationProbe) -> bool,
) -> &MacroInvocationProbe {
    let matches = records
        .iter()
        .filter(|record| predicate(record))
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "expected exactly one matching macro invocation; matches={matches:?}; all={records:#?}"
    );
    matches[0]
}

#[cfg(rust_item_dependencies_patched)]
fn unique_macro_import(
    records: &[MacroResolvedImportUseProbe],
    predicate: impl Fn(&MacroResolvedImportUseProbe) -> bool,
) -> &MacroResolvedImportUseProbe {
    let matches = records
        .iter()
        .filter(|record| predicate(record))
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "expected exactly one matching macro import use; matches={matches:?}; all={records:#?}"
    );
    matches[0]
}

#[cfg(rust_item_dependencies_patched)]
fn source_range(source: &str, marker: &str) -> (u32, u32) {
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing fixture marker: {marker}"));
    let end = source[start..]
        .find(';')
        .map(|offset| start + offset + 1)
        .unwrap_or(start + marker.len());
    (start as u32, end as u32)
}

#[cfg(rust_item_dependencies_patched)]
fn marker_range(source: &str, marker: &str) -> (u32, u32) {
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing fixture marker: {marker}"));
    (start as u32, (start + marker.len()) as u32)
}

#[cfg(rust_item_dependencies_patched)]
fn marker_range_after(source: &str, anchor: &str, marker: &str) -> (u32, u32) {
    let anchor_start = source
        .find(anchor)
        .unwrap_or_else(|| panic!("missing fixture anchor: {anchor}"));
    let relative_start = source[anchor_start..]
        .find(marker)
        .unwrap_or_else(|| panic!("missing marker {marker:?} after {anchor:?}"));
    let start = anchor_start + relative_start;
    (start as u32, (start + marker.len()) as u32)
}

#[cfg(rust_item_dependencies_patched)]
fn marker_ranges_between(source: &str, first: &str, last: &str, marker: &str) -> Vec<(u32, u32)> {
    let first_start = source
        .find(first)
        .unwrap_or_else(|| panic!("missing fixture marker: {first}"));
    let last_start = source[first_start..]
        .find(last)
        .map(|offset| first_start + offset)
        .unwrap_or_else(|| panic!("missing fixture marker after {first}: {last}"));
    source[first_start..last_start]
        .match_indices(marker)
        .map(|(offset, _)| {
            let start = first_start + offset;
            (start as u32, (start + marker.len()) as u32)
        })
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn range_between(source: &str, first: &str, last: &str) -> (u32, u32) {
    let first_start = source
        .find(first)
        .unwrap_or_else(|| panic!("missing fixture marker: {first}"));
    let last_start = source[first_start..]
        .find(last)
        .map(|offset| first_start + offset)
        .unwrap_or_else(|| panic!("missing fixture marker after {first}: {last}"));
    (first_start as u32, (last_start + last.len()) as u32)
}

#[cfg(rust_item_dependencies_patched)]
fn marker_range_in_statement(source: &str, statement: &str, marker: &str) -> (u32, u32) {
    let (statement_start, statement_end) = source_range(source, statement);
    let statement_source = &source[statement_start as usize..statement_end as usize];
    let relative_start = statement_source
        .find(marker)
        .unwrap_or_else(|| panic!("missing marker {marker:?} inside {statement:?}"));
    let start = statement_start as usize + relative_start;
    (start as u32, (start + marker.len()) as u32)
}

#[cfg(rust_item_dependencies_patched)]
fn all_marker_ranges(source: &str, marker: &str) -> Vec<(u32, u32)> {
    source
        .match_indices(marker)
        .map(|(start, matched)| (start as u32, (start + matched.len()) as u32))
        .collect()
}

#[cfg(rust_item_dependencies_patched)]
fn assert_range_inside(actual: (u32, u32), expected_container: (u32, u32)) {
    assert!(
        actual.0 >= expected_container.0 && actual.1 <= expected_container.1,
        "range {actual:?} must be inside {expected_container:?}"
    );
}

fn local_probe_config() -> ProbeConfig {
    let sysroot = rustc_output(&["--print", "sysroot"]);
    let verbose_version = rustc_output(&["-Vv"]);
    let target = verbose_version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc -Vv must contain host")
        .to_owned();

    ProbeConfig {
        sysroot: PathBuf::from(sysroot.trim()),
        target,
        edition: "2024".to_owned(),
    }
}

fn rustc_output(arguments: &[&str]) -> String {
    let output = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .args(arguments)
        .output()
        .expect("the pinned rustc must be executable");
    assert!(
        output.status.success(),
        "rustc invocation failed: {output:?}"
    );
    String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
}
