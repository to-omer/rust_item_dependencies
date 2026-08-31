#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
mod patched {
    use std::ffi::OsString;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};
    use std::sync::atomic::{AtomicU64, Ordering};

    use rust_item_dependencies::{
        AnalysisError, Analyzer, CompilationOptions, Edition, EntryPoint, OptimizationLevel,
        Reduction, SourceInput, UnsupportedReason, error::DiagnosticLevel, source::ByteRange,
    };

    const LEAF_SOURCE: &str = include_str!("fixtures/external_crates/leaf.rs");
    const WRAPPER_SOURCE: &str = include_str!("fixtures/external_crates/wrapper.rs");
    const LEAF_DIRECT_SOURCE: &str = include_str!("fixtures/external_crates/leaf_direct.rs");
    const LEAF_DIRECT_2015_SOURCE: &str =
        include_str!("fixtures/external_crates/leaf_direct_2015.rs");
    const CASES: &[Case] = &[
        Case {
            name: "Rust 2018 extern prelude",
            edition: Edition::Rust2018,
            source: include_str!("fixtures/external_crates/input_2018.rs"),
            expected: include_str!("fixtures/external_crates/expected_2018.rs"),
        },
        Case {
            name: "Rust 2015 extern crate",
            edition: Edition::Rust2015,
            source: include_str!("fixtures/external_crates/input_2015.rs"),
            expected: include_str!("fixtures/external_crates/expected_2015.rs"),
        },
    ];

    struct Case {
        name: &'static str,
        edition: Edition,
        source: &'static str,
        expected: &'static str,
    }

    struct TestDirectory {
        path: PathBuf,
    }

    impl TestDirectory {
        fn new() -> Self {
            static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

            let parent = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("target")
                .join("tests")
                .join("external-crates");
            fs::create_dir_all(&parent)
                .expect("the external-crate test directory must be writable");
            for _ in 0..1_024 {
                let path = parent.join(format!(
                    "{}-{}",
                    std::process::id(),
                    NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self { path },
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => {
                        panic!("the isolated external-crate test directory must be new: {error}")
                    }
                }
            }
            panic!("cannot allocate an isolated external-crate test directory")
        }

        fn path(&self) -> &Path {
            &self.path
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    struct ExternalArtifacts {
        _directory: TestDirectory,
        leaf: PathBuf,
        wrapper: PathBuf,
    }

    impl ExternalArtifacts {
        fn build() -> Self {
            let directory = TestDirectory::new();
            let leaf_source = directory.path().join("external_leaf.rs");
            let wrapper_source = directory.path().join("external_wrapper.rs");
            let leaf = directory.path().join("libexternal_leaf.rlib");
            let wrapper = directory.path().join("libexternal_wrapper.rlib");
            fs::write(&leaf_source, LEAF_SOURCE).expect("the leaf source must be writable");
            fs::write(&wrapper_source, WRAPPER_SOURCE)
                .expect("the wrapper source must be writable");

            compile_library("external_leaf", &leaf_source, &leaf, &[]);
            compile_library(
                "external_wrapper",
                &wrapper_source,
                &wrapper,
                &[
                    "--extern".into(),
                    format!("external_leaf={}", leaf.display()),
                    "-L".into(),
                    format!("dependency={}", directory.path().display()),
                ],
            );

            Self {
                _directory: directory,
                leaf,
                wrapper,
            }
        }

        fn options(&self) -> CompilationOptions {
            CompilationOptions::new()
                .with_external_crate("external_wrapper", &self.wrapper)
                .with_dependency_artifact(&self.leaf)
        }

        fn directory(&self) -> &Path {
            self.leaf
                .parent()
                .expect("the leaf artifact must have a parent directory")
        }
    }

    #[test]
    fn two_level_external_crates_reduce_link_and_run_in_2015_and_2018() {
        let artifacts = ExternalArtifacts::build();
        let options = artifacts.options();
        let analyzer = Analyzer::new_with_options(options)
            .expect("the direct and transitive rlibs must be accepted");
        let target = host_target();

        for case in CASES {
            let original = input(case.source, case.edition, &target);
            let reduction = analyzer
                .reduce(&original)
                .unwrap_or_else(|error| panic!("{}: {error:?}", case.name));
            assert_reduction(case, &reduction);

            let reduced = input(reduction.reduced_source(), case.edition, &target);
            let fixed = analyzer
                .reduce(&reduced)
                .unwrap_or_else(|error| panic!("{} fixed point: {error:?}", case.name));
            assert_eq!(
                fixed.reduced_source(),
                reduction.reduced_source(),
                "{}",
                case.name
            );

            let original_output = compile_and_run(
                &original,
                &artifacts,
                &format!("{}_original", edition_name(case.edition)),
            );
            let reduced_output = compile_and_run(
                &reduced,
                &artifacts,
                &format!("{}_reduced", edition_name(case.edition)),
            );
            assert!(original_output.status.success(), "{}", case.name);
            assert_eq!(original_output.stdout, b"21\n", "{}", case.name);
            assert!(original_output.stderr.is_empty(), "{}", case.name);
            assert_eq!(
                reduced_output.status, original_output.status,
                "{}",
                case.name
            );
            assert_eq!(
                reduced_output.stdout, original_output.stdout,
                "{}",
                case.name
            );
            assert_eq!(
                reduced_output.stderr, original_output.stderr,
                "{}",
                case.name
            );
        }
    }

    #[test]
    fn cross_crate_inlining_preserves_selected_associated_overrides() {
        let artifacts = ExternalArtifacts::build();
        let options = artifacts
            .options()
            .with_optimization_level(OptimizationLevel::O3);
        let analyzer = Analyzer::new_with_options(options)
            .expect("the optimized external-crate context must be accepted");
        let target = host_target();
        let source = concat!(
            "struct Local;\n",
            "impl external_wrapper::ExternalStorage for Local {\n",
            "    #[inline(always)]\n",
            "    fn normalize(value: u32) -> u32 { value + 6 }\n",
            "}\n",
            "fn unused() {}\n",
            "fn main() {\n",
            "    assert_eq!(external_wrapper::external_get::<Local>(1), 7);\n",
            "}\n",
        );
        let original = input(source, Edition::Rust2021, &target);

        let reduction = analyzer
            .reduce(&original)
            .expect("the external associated selection must survive inlining");
        assert!(!reduction.reduced_source().contains("fn unused"));
        assert!(reduction.reduced_source().contains("fn normalize"));

        let reduced = input(reduction.reduced_source(), Edition::Rust2021, &target);
        let fixed = analyzer
            .reduce(&reduced)
            .expect("the external associated selection must reach a fixed point");
        assert_eq!(fixed.reduced_source(), reduction.reduced_source());

        let original_output = compile_and_run(&original, &artifacts, "external_inline_original");
        let reduced_output = compile_and_run(&reduced, &artifacts, "external_inline_reduced");
        assert!(original_output.status.success());
        assert_eq!(reduced_output.status, original_output.status);
        assert_eq!(reduced_output.stdout, original_output.stdout);
        assert_eq!(reduced_output.stderr, original_output.stderr);
    }

    #[test]
    fn empty_external_declarative_macro_is_removed_and_reaches_a_fixed_point() {
        let artifacts = ExternalArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.options()).unwrap();
        let target = host_target();
        let expected = "fn main(){println!(\"ok\");}";
        for (name, edition, source) in [
            (
                "2018",
                Edition::Rust2018,
                "external_wrapper::external_empty!();fn main(){println!(\"ok\");}",
            ),
            (
                "2015",
                Edition::Rust2015,
                "#[macro_use]extern crate external_wrapper;external_empty!();fn main(){println!(\"ok\");}",
            ),
        ] {
            let original = input(source, edition, &target);
            let reduction = analyzer.reduce(&original).unwrap();
            assert_eq!(reduction.reduced_source(), expected, "{name}");

            let reduced = input(expected, edition, &target);
            let fixed = analyzer.reduce(&reduced).unwrap();
            assert_eq!(fixed.reduced_source(), expected, "{name}");

            let original_output =
                compile_and_run(&original, &artifacts, &format!("empty_{name}_original"));
            let reduced_output =
                compile_and_run(&reduced, &artifacts, &format!("empty_{name}_reduced"));
            assert!(original_output.status.success(), "{name}");
            assert_eq!(original_output.stdout, b"ok\n", "{name}");
            assert_eq!(reduced_output.status, original_output.status, "{name}");
            assert_eq!(reduced_output.stdout, original_output.stdout, "{name}");
            assert_eq!(reduced_output.stderr, original_output.stderr, "{name}");
        }
    }

    #[test]
    fn direct_and_transitive_external_native_link_metadata_are_rejected() {
        let directory = TestDirectory::new();
        let native_source = directory.path().join("native_dependency.rs");
        let native = directory.path().join("libnative_dependency.rlib");
        let wrapper_source = directory.path().join("native_wrapper.rs");
        let wrapper = directory.path().join("libnative_wrapper.rlib");
        fs::write(
            &native_source,
            concat!(
                "#![no_std]\n",
                "#[link(name = \"rid_external_native_fixture\")]\n",
                "unsafe extern \"C\" {}\n",
                "pub fn marker() {}\n",
            ),
        )
        .unwrap();
        fs::write(
            &wrapper_source,
            "#![no_std]\npub fn marker() { native_dependency::marker(); }\n",
        )
        .unwrap();
        compile_library("native_dependency", &native_source, &native, &[]);
        compile_library(
            "native_wrapper",
            &wrapper_source,
            &wrapper,
            &[
                "--extern".into(),
                format!("native_dependency={}", native.display()),
                "-L".into(),
                format!("dependency={}", directory.path().display()),
            ],
        );

        for (name, direct_name, direct, transitive) in [
            ("direct", "native_dependency", &native, None),
            ("transitive", "native_wrapper", &wrapper, Some(&native)),
        ] {
            let mut options = CompilationOptions::new().with_external_crate(direct_name, direct);
            if let Some(transitive) = transitive {
                options = options.with_dependency_artifact(transitive);
            }
            let analyzer = Analyzer::new_with_options(options).unwrap();
            let source = format!("fn dead() {{ {direct_name}::marker(); }}\npub fn entry() {{}}\n");
            let input = SourceInput::library(
                source,
                Edition::Rust2024,
                host_target(),
                format!("native_{name}"),
            )
            .with_entry_point(EntryPoint::new(format!("native_{name}::entry")));

            assert_eq!(
                analyzer.reduce(&input),
                Err(AnalysisError::UnsupportedInput {
                    reason: UnsupportedReason::ExternalNativeLink,
                    range: None,
                }),
                "{name}",
            );
        }
    }

    #[test]
    fn panic_handler_provider_keeps_only_the_smallest_source_activation() {
        let directory = TestDirectory::new();
        let provider_source = directory.path().join("panic_provider.rs");
        let provider = directory.path().join("libpanic_provider.rlib");
        let wrapper_source = directory.path().join("panic_wrapper.rs");
        let wrapper = directory.path().join("libpanic_wrapper.rlib");
        fs::write(
            &provider_source,
            concat!(
                "#![no_std]\n",
                "#[panic_handler]\n",
                "fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }\n",
                "pub fn marker() {}\n",
            ),
        )
        .unwrap();
        fs::write(
            &wrapper_source,
            "#![no_std]\npub fn marker() { panic_provider::marker(); }\n",
        )
        .unwrap();
        compile_library("panic_provider", &provider_source, &provider, &[]);
        compile_library(
            "panic_wrapper",
            &wrapper_source,
            &wrapper,
            &[
                "--extern".into(),
                format!("panic_provider={}", provider.display()),
                "-L".into(),
                format!("dependency={}", directory.path().display()),
            ],
        );

        let cases = [
            RuntimeProviderCase {
                name: "direct provider",
                direct_name: "panic_provider",
                direct_artifact: &provider,
                dependency_artifact: None,
                source: concat!(
                    "#![no_std]\n",
                    "fn long_activation() {\n",
                    "    panic_provider::marker();\n",
                    "    let _ = 0;\n",
                    "}\n",
                    "fn a() { panic_provider::marker(); }\n",
                    "pub fn entry() -> u8 { 7 }\n",
                ),
                kept: "fn a() { panic_provider::marker(); }",
            },
            RuntimeProviderCase {
                name: "transitive provider",
                direct_name: "panic_wrapper",
                direct_artifact: &wrapper,
                dependency_artifact: Some(&provider),
                source: concat!(
                    "#![no_std]\n",
                    "fn long_activation() {\n",
                    "    panic_wrapper::marker();\n",
                    "    let _ = 0;\n",
                    "}\n",
                    "fn a() { panic_wrapper::marker(); }\n",
                    "pub fn entry() -> u8 { 7 }\n",
                ),
                kept: "fn a() { panic_wrapper::marker(); }",
            },
        ];
        let target = host_target();
        let missing_provider_source = directory.path().join("missing-provider.rs");
        let missing_provider = directory.path().join("libmissing-provider.rlib");
        fs::write(
            &missing_provider_source,
            "#![no_std]\npub fn entry() -> u8 { 7 }\n",
        )
        .unwrap();
        compile_library_with_edition(
            "runtime_input",
            &missing_provider_source,
            &missing_provider,
            "2024",
            &[],
        );
        let missing_provider_downstream = compile_no_std_downstream(
            directory.path(),
            "missing-provider",
            "control",
            &missing_provider,
            &target,
        );
        assert!(
            !missing_provider_downstream.status.success(),
            "the control input must fail without a panic provider"
        );

        for case in cases {
            let mut options = CompilationOptions::new()
                .with_external_crate(case.direct_name, case.direct_artifact);
            if let Some(dependency) = case.dependency_artifact {
                options = options.with_dependency_artifact(dependency);
            }
            let analyzer = Analyzer::new_with_options(options).unwrap();
            let input = SourceInput::library(
                case.source,
                Edition::Rust2024,
                target.clone(),
                "runtime_input",
            )
            .with_entry_point(EntryPoint::new("runtime_input::entry"));
            let reduction = analyzer
                .reduce(&input)
                .unwrap_or_else(|error| panic!("{}: {error:?}", case.name));
            assert!(
                reduction.reduced_source().contains(case.kept),
                "{}: {}",
                case.name,
                reduction.reduced_source()
            );
            assert!(!reduction.reduced_source().contains("long_activation"));

            let mut fixed_input = input.clone();
            fixed_input.source = reduction.reduced_source().to_owned();
            let fixed = analyzer.reduce(&fixed_input).unwrap();
            assert_eq!(fixed.reduced_source(), reduction.reduced_source());

            for (variant, source) in [
                ("original", case.source),
                ("reduced", reduction.reduced_source()),
            ] {
                let source_path = directory
                    .path()
                    .join(format!("{}-{variant}.rs", case.direct_name));
                let artifact = directory
                    .path()
                    .join(format!("lib{}-{variant}.rlib", case.direct_name));
                fs::write(&source_path, source).unwrap();
                compile_library_with_edition(
                    "runtime_input",
                    &source_path,
                    &artifact,
                    "2024",
                    &[
                        "--extern".into(),
                        format!("{}={}", case.direct_name, case.direct_artifact.display()),
                        "-L".into(),
                        format!("dependency={}", directory.path().display()),
                    ],
                );
                let downstream = compile_no_std_downstream(
                    directory.path(),
                    case.direct_name,
                    variant,
                    &artifact,
                    &target,
                );
                assert!(
                    downstream.status.success(),
                    "{} {variant}:\n{}",
                    case.name,
                    String::from_utf8_lossy(&downstream.stderr)
                );
            }
        }
    }

    struct RuntimeProviderCase<'a> {
        name: &'static str,
        direct_name: &'static str,
        direct_artifact: &'a Path,
        dependency_artifact: Option<&'a Path>,
        source: &'static str,
        kept: &'static str,
    }

    #[test]
    fn a_dependency_artifact_does_not_enter_the_inputs_extern_prelude() {
        let artifacts = ExternalArtifacts::build();
        let error = Analyzer::new_with_options(artifacts.options())
            .unwrap()
            .analyze(&input(
                LEAF_DIRECT_SOURCE,
                Edition::Rust2018,
                &host_target(),
            ))
            .expect_err("a transitive dependency must not enter the extern prelude");
        let AnalysisError::OriginalCompilationFailed(diagnostics) = error else {
            panic!("unexpected error: {error:?}")
        };
        let [resolution, abort] = diagnostics.diagnostics() else {
            panic!("unexpected compiler diagnostics: {diagnostics:?}")
        };
        assert_eq!(resolution.level, DiagnosticLevel::Error);
        assert_eq!(
            resolution.message,
            "cannot find module or crate `external_leaf` in this scope"
        );
        assert_eq!(resolution.range, Some(ByteRange { start: 75, end: 88 }));
        assert_eq!(abort.level, DiagnosticLevel::Error);
        assert_eq!(abort.message, "aborting due to 1 previous error");
        assert_eq!(abort.range, None);

        let error = Analyzer::new_with_options(artifacts.options())
            .unwrap()
            .analyze(&input(
                LEAF_DIRECT_2015_SOURCE,
                Edition::Rust2015,
                &host_target(),
            ))
            .expect_err("a transitive dependency must not be an allowed extern crate");
        assert_eq!(
            error,
            AnalysisError::UnsupportedInput {
                reason: UnsupportedReason::ExternalDependency,
                range: Some(ByteRange { start: 31, end: 58 }),
            }
        );
    }

    #[test]
    fn only_code_generated_by_an_external_macro_may_import_a_transitive_dependency() {
        let artifacts = ExternalArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.options()).unwrap();
        let target = host_target();

        for (source, reason, snippet) in [
            (
                concat!(
                    "macro_rules! import_leaf { () => { extern crate external_leaf; }; }\n",
                    "import_leaf!();\n",
                    "fn main() {}\n",
                ),
                UnsupportedReason::ExternalDependency,
                "import_leaf!()",
            ),
            (
                concat!(
                    "external_wrapper::external_passthrough! {\n",
                    "    extern crate external_leaf;\n",
                    "}\n",
                    "fn main() {}\n",
                ),
                UnsupportedReason::ExternalDependency,
                "extern crate external_leaf;",
            ),
            (
                concat!(
                    "external_wrapper::external_proc_macro_dependency!();\n",
                    "fn main() {}\n",
                ),
                UnsupportedReason::ProcMacro,
                "external_wrapper::external_proc_macro_dependency!()",
            ),
        ] {
            let error = analyzer
                .analyze(&input(source, Edition::Rust2018, &target))
                .expect_err("input-originated imports and proc_macro must remain unsupported");
            assert_eq!(
                error,
                AnalysisError::UnsupportedInput {
                    reason,
                    range: Some(range_of(source, snippet)),
                }
            );
        }
    }

    #[test]
    fn recipe_uses_artifact_contents_names_and_roles_but_not_paths_or_order() {
        let artifacts = ExternalArtifacts::build();
        let copied_directory = TestDirectory::new();
        let copied_leaf = copied_directory.path().join("libexternal_leaf.rlib");
        let copied_wrapper = copied_directory.path().join("libexternal_wrapper.rlib");
        let renamed_wrapper = copied_directory.path().join("librenamed_wrapper.rlib");
        let explicit_wrapper = copied_directory.path().join("lib-.rlib");
        fs::copy(&artifacts.leaf, &copied_leaf).unwrap();
        fs::copy(&artifacts.wrapper, &copied_wrapper).unwrap();
        fs::copy(&artifacts.wrapper, &renamed_wrapper).unwrap();
        fs::copy(&artifacts.wrapper, &explicit_wrapper).unwrap();
        let target = host_target();
        let original = input(CASES[0].source, Edition::Rust2018, &target);

        let expected = Analyzer::new_with_options(artifacts.options())
            .unwrap()
            .analyze(&original)
            .unwrap()
            .recipe();
        let copied = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_dependency_artifact(&copied_leaf)
                .with_external_crate("external_wrapper", &copied_wrapper)
                .with_dependency_artifact(&copied_leaf)
                .with_external_crate("external_wrapper", &copied_wrapper),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_eq!(copied, expected);

        let repeated_direct_artifact = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", &artifacts.wrapper)
                .with_dependency_artifact(&artifacts.wrapper)
                .with_dependency_artifact(&artifacts.leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_eq!(repeated_direct_artifact, expected);

        let explicit_path = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", &explicit_wrapper)
                .with_dependency_artifact(&copied_leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        let repeated_explicit_path = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", &explicit_wrapper)
                .with_dependency_artifact(&explicit_wrapper)
                .with_dependency_artifact(&copied_leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_eq!(repeated_explicit_path, explicit_path);

        let renamed_file = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", renamed_wrapper)
                .with_dependency_artifact(&copied_leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_ne!(renamed_file, expected);

        let different_role = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", &artifacts.wrapper)
                .with_external_crate("external_leaf", &artifacts.leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_ne!(different_role, expected);

        let renamed_source = CASES[0]
            .source
            .replace("external_wrapper", "renamed_wrapper");
        let renamed = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("renamed_wrapper", &artifacts.wrapper)
                .with_dependency_artifact(&artifacts.leaf),
        )
        .unwrap()
        .analyze(&input(&renamed_source, Edition::Rust2018, &target))
        .unwrap()
        .recipe();
        assert_ne!(renamed, expected);

        let changed_directory = TestDirectory::new();
        let changed_source = changed_directory.path().join("external_wrapper.rs");
        let changed_wrapper = changed_directory.path().join("libexternal_wrapper.rlib");
        fs::write(
            &changed_source,
            format!("{WRAPPER_SOURCE}\npub fn additional_public_item() {{}}\n"),
        )
        .unwrap();
        compile_library(
            "external_wrapper",
            &changed_source,
            &changed_wrapper,
            &[
                "--extern".into(),
                format!("external_leaf={}", artifacts.leaf.display()),
                "-L".into(),
                format!("dependency={}", artifacts.directory().display()),
            ],
        );
        let changed = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("external_wrapper", changed_wrapper)
                .with_dependency_artifact(&artifacts.leaf),
        )
        .unwrap()
        .analyze(&original)
        .unwrap()
        .recipe();
        assert_ne!(changed, expected);
    }

    #[test]
    fn cargo_rid_builds_external_crates_and_reduces_with_them() {
        let directory = TestDirectory::new();
        let leaf_source = directory.path().join("public_leaf.rs");
        let wrapper_source = directory.path().join("public_wrapper.rs");
        let input_path = directory.path().join("public_input.rs");
        let leaf = directory.path().join("libexternal_leaf.rlib");
        let wrapper = directory.path().join("libexternal_wrapper.rlib");
        let reduced = directory.path().join("public_reduced.rs");
        let executable = directory
            .path()
            .join(format!("public_reduced{}", std::env::consts::EXE_SUFFIX));
        fs::write(&leaf_source, LEAF_SOURCE).unwrap();
        fs::write(&wrapper_source, WRAPPER_SOURCE).unwrap();
        fs::write(&input_path, CASES[0].source).unwrap();
        let target = host_target();

        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                leaf_source.into_os_string(),
                OsString::from("--crate-name"),
                OsString::from("external_leaf"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2021"),
                OsString::from("--target"),
                OsString::from(&target),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                leaf.clone().into_os_string(),
            ]),
            "building the leaf through cargo rid",
        );
        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                wrapper_source.into_os_string(),
                OsString::from("--crate-name"),
                OsString::from("external_wrapper"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2021"),
                OsString::from("--target"),
                OsString::from(&target),
                OsString::from("--extern"),
                prefixed_path("external_leaf=", &leaf),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                wrapper.clone().into_os_string(),
            ]),
            "building the wrapper through cargo rid",
        );
        assert_command_success(
            cargo_rid([
                OsString::from("--extern"),
                prefixed_path("external_wrapper=", &wrapper),
                OsString::from("--dependency-artifact"),
                leaf.clone().into_os_string(),
                OsString::from("--edition"),
                OsString::from("2018"),
                OsString::from("--target"),
                OsString::from(&target),
                input_path.into_os_string(),
                OsString::from("-o"),
                reduced.clone().into_os_string(),
            ]),
            "reducing through cargo rid",
        );
        assert_eq!(fs::read_to_string(&reduced).unwrap(), CASES[0].expected);

        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                reduced.into_os_string(),
                OsString::from("--crate-name"),
                OsString::from("public_reduced"),
                OsString::from("--crate-type=bin"),
                OsString::from("--edition=2018"),
                OsString::from("--target"),
                OsString::from(&target),
                OsString::from("--extern"),
                prefixed_path("external_wrapper=", &wrapper),
                OsString::from("-L"),
                prefixed_path("dependency=", directory.path()),
                OsString::from("-L"),
                prefixed_path("crate=", directory.path()),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                executable.clone().into_os_string(),
            ]),
            "linking the reduced program through cargo rid",
        );
        let output = Command::new(executable)
            .output()
            .expect("the linked program must start");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"21\n");
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn cargo_rid_reduces_std_and_no_std_sources_for_a_cross_target() {
        let directory = TestDirectory::new();
        let target = "wasm32-unknown-unknown";
        let installed_before = installed_target_libraries(target);

        let std_source = directory.path().join("cross_std.rs");
        let std_reduced = directory.path().join("cross_std_reduced.rs");
        let std_fixed = directory.path().join("cross_std_fixed.rs");
        let std_rlib = directory.path().join("libcross_std.rlib");
        fs::write(
            &std_source,
            concat!(
                "pub fn entry() -> usize {\n",
                "    [\"metadata\"].into_iter().map(String::from).map(|value| value.len()).sum()\n",
                "}\n",
                "fn unused() -> usize { 100 }\n",
            ),
        )
        .unwrap();
        let std_library_arguments = [
            OsString::from("--crate-type"),
            OsString::from("lib"),
            OsString::from("--crate-name"),
            OsString::from("cross_std"),
            OsString::from("--entry"),
            OsString::from("cross_std::entry"),
        ];
        let std_reduction = reduce_cross_to_fixed_point(
            &std_source,
            &std_reduced,
            &std_fixed,
            target,
            &std_library_arguments,
        );
        assert!(!std_reduction.contains("unused"));

        let host_source = directory.path().join("host_after_cross_preparation.rs");
        let host_rlib = directory
            .path()
            .join("libhost_after_cross_preparation.rlib");
        fs::write(
            &host_source,
            "pub fn entry() -> usize { String::from(\"host\").len() }\n",
        )
        .unwrap();
        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                OsString::from("--target"),
                OsString::from(host_target()),
                host_source.into_os_string(),
                OsString::from("--crate-name=host_after_cross_preparation"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2024"),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                host_rlib.into_os_string(),
            ]),
            "building a host std rlib after cross-target preparation",
        );

        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                OsString::from("--target"),
                OsString::from(target),
                std_reduced.clone().into_os_string(),
                OsString::from("--crate-name=cross_std"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2024"),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                std_rlib.as_os_str().to_owned(),
            ]),
            "building a cross-target std rlib through cargo rid rustc",
        );

        let consumer_source = directory.path().join("cross_consumer.rs");
        let consumer_reduced = directory.path().join("cross_consumer_reduced.rs");
        let consumer_fixed = directory.path().join("cross_consumer_fixed.rs");
        fs::write(
            &consumer_source,
            concat!(
                "fn unused() -> usize { 100 }\n",
                "fn main() { core::hint::black_box(cross_std::entry()); }\n",
            ),
        )
        .unwrap();
        let consumer_arguments = [
            OsString::from("--extern"),
            prefixed_path("cross_std=", &std_rlib),
        ];
        let consumer_reduction = reduce_cross_to_fixed_point(
            &consumer_source,
            &consumer_reduced,
            &consumer_fixed,
            target,
            &consumer_arguments,
        );
        assert!(!consumer_reduction.contains("unused"));

        let no_std_source = directory.path().join("cross_no_std.rs");
        let no_std_reduced = directory.path().join("cross_no_std_reduced.rs");
        let no_std_fixed = directory.path().join("cross_no_std_fixed.rs");
        let no_std_rlib = directory.path().join("libcross_no_std.rlib");
        fs::write(
            &no_std_source,
            concat!(
                "#![no_std]\n",
                "pub fn entry() -> usize { core::mem::size_of::<usize>() }\n",
                "fn unused() -> usize { 100 }\n",
            ),
        )
        .unwrap();
        let library_arguments = [
            OsString::from("--crate-type"),
            OsString::from("lib"),
            OsString::from("--crate-name"),
            OsString::from("cross_no_std"),
            OsString::from("--entry"),
            OsString::from("cross_no_std::entry"),
        ];
        let no_std_reduction = reduce_cross_to_fixed_point(
            &no_std_source,
            &no_std_reduced,
            &no_std_fixed,
            target,
            &library_arguments,
        );
        assert!(!no_std_reduction.contains("unused"));
        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                OsString::from("--target=wasm32-unknown-unknown"),
                no_std_reduced.into_os_string(),
                OsString::from("--crate-name=cross_no_std"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2024"),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                no_std_rlib.into_os_string(),
            ]),
            "building a reduced cross-target no_std rlib through cargo rid rustc",
        );
        assert_eq!(installed_target_libraries(target), installed_before);
    }

    #[test]
    fn cargo_rid_prepares_apple_target_metadata_without_installing_target_libraries() {
        let directory = TestDirectory::new();
        let target = "aarch64-apple-ios";
        let installed_before = installed_target_libraries(target);
        let source = directory.path().join("apple_library.rs");
        let artifact = directory.path().join("libapple_library.rlib");
        fs::write(
            &source,
            "pub fn entry() -> usize { String::from(\"apple\").len() }\n",
        )
        .unwrap();

        assert_command_success(
            cargo_rid([
                OsString::from("rustc"),
                OsString::from("--target"),
                OsString::from(target),
                source.into_os_string(),
                OsString::from("--crate-name=apple_library"),
                OsString::from("--crate-type=rlib"),
                OsString::from("--edition=2024"),
                OsString::from("-Awarnings"),
                OsString::from("-o"),
                artifact.into_os_string(),
            ]),
            "building an Apple-target rlib from generated metadata",
        );
        assert_eq!(installed_target_libraries(target), installed_before);
    }

    fn reduce_cross_source(
        input: &Path,
        output: &Path,
        target: &str,
        extra_arguments: &[OsString],
    ) {
        let mut arguments = vec![OsString::from("--target"), OsString::from(target)];
        arguments.extend_from_slice(extra_arguments);
        arguments.push(input.as_os_str().to_owned());
        arguments.push(OsString::from("-o"));
        arguments.push(output.as_os_str().to_owned());
        assert_command_success(cargo_rid(arguments), "reducing a cross-target source");
    }

    fn reduce_cross_to_fixed_point(
        input: &Path,
        reduced: &Path,
        fixed: &Path,
        target: &str,
        extra_arguments: &[OsString],
    ) -> String {
        reduce_cross_source(input, reduced, target, extra_arguments);
        reduce_cross_source(reduced, fixed, target, extra_arguments);
        let reduced = fs::read_to_string(reduced).unwrap();
        assert_eq!(reduced, fs::read_to_string(fixed).unwrap());
        reduced
    }

    fn compile_library(crate_name: &str, source: &Path, artifact: &Path, extra_args: &[String]) {
        compile_library_with_edition(crate_name, source, artifact, "2021", extra_args);
    }

    fn compile_library_with_edition(
        crate_name: &str,
        source: &Path,
        artifact: &Path,
        edition: &str,
        extra_args: &[String],
    ) {
        let compiled = Command::new(compiler())
            .arg(source)
            .args(["--crate-name", crate_name, "--crate-type=rlib"])
            .arg(format!("--edition={edition}"))
            .args(["--target", &host_target()])
            .args(extra_args)
            .args(["-Awarnings", "-o"])
            .arg(artifact)
            .output()
            .expect("the dependency compiler must finish");
        assert!(
            compiled.status.success(),
            "building {crate_name} failed:\n{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
    }

    fn compile_no_std_downstream(
        directory: &Path,
        case_name: &str,
        variant: &str,
        input_artifact: &Path,
        target: &str,
    ) -> Output {
        let source = directory.join(format!("{case_name}-{variant}-downstream.rs"));
        let metadata = directory.join(format!("{case_name}-{variant}-downstream.rmeta"));
        fs::write(
            &source,
            concat!(
                "#![no_std]\n",
                "#![no_main]\n",
                "extern crate runtime_input;\n",
                "#[unsafe(no_mangle)]\n",
                "pub extern \"C\" fn _start() -> ! {\n",
                "    let _ = runtime_input::entry();\n",
                "    loop {}\n",
                "}\n",
            ),
        )
        .unwrap();
        Command::new(compiler())
            .arg(source)
            .args([
                "--crate-name",
                "runtime_downstream",
                "--crate-type=bin",
                "--edition=2024",
                "--target",
                target,
                "-Cpanic=abort",
                "--emit=metadata",
                "--extern",
            ])
            .arg(format!("runtime_input={}", input_artifact.display()))
            .arg("-L")
            .arg(format!("dependency={}", directory.display()))
            .args(["-Awarnings", "-o"])
            .arg(metadata)
            .output()
            .expect("the no_std downstream compiler must finish")
    }

    fn cargo_rid(arguments: impl IntoIterator<Item = OsString>) -> Output {
        Command::new(std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")))
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .arg("rid")
            .args(arguments)
            .output()
            .expect("cargo rid must finish")
    }

    fn installed_target_libraries(target: &str) -> Option<Vec<OsString>> {
        let output = Command::new(compiler())
            .args(["--target", target, "--print", "target-libdir"])
            .output()
            .expect("rustc --print target-libdir must finish");
        assert!(output.status.success());
        let directory = PathBuf::from(
            String::from_utf8(output.stdout)
                .expect("the target library path must be UTF-8")
                .trim(),
        );
        let entries = match fs::read_dir(directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return None,
            Err(error) => panic!("the target library directory must be readable: {error}"),
        };
        let mut entries = entries
            .map(|entry| entry.unwrap().file_name())
            .collect::<Vec<_>>();
        entries.sort();
        Some(entries)
    }

    fn assert_command_success(output: Output, action: &str) {
        assert!(
            output.status.success(),
            "{action} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn prefixed_path(prefix: &str, path: &Path) -> OsString {
        let mut argument = OsString::from(prefix);
        argument.push(path);
        argument
    }

    fn compile_and_run(
        input: &SourceInput,
        artifacts: &ExternalArtifacts,
        artifact_name: &str,
    ) -> Output {
        let source = artifacts.directory().join(format!("{artifact_name}.rs"));
        let executable = artifacts
            .directory()
            .join(format!("{artifact_name}{}", std::env::consts::EXE_SUFFIX));
        fs::write(&source, &input.source).expect("the program source must be writable");
        let compiled = Command::new(compiler())
            .arg(&source)
            .args(["--crate-name", artifact_name, "--crate-type=bin"])
            .arg(format!("--edition={}", edition_name(input.edition)))
            .args(["--target", &input.target])
            .arg("--extern")
            .arg(format!("external_wrapper={}", artifacts.wrapper.display()))
            .arg("-L")
            .arg(format!("dependency={}", artifacts.directory().display()))
            .arg("-L")
            .arg(format!("crate={}", artifacts.directory().display()))
            .args(["-Awarnings", "-o"])
            .arg(&executable)
            .output()
            .expect("the program compiler must finish");
        assert!(
            compiled.status.success(),
            "linking {artifact_name} failed:\n{}",
            String::from_utf8_lossy(&compiled.stderr)
        );

        Command::new(executable)
            .output()
            .expect("the linked program must start")
    }

    fn assert_reduction(case: &Case, reduction: &Reduction) {
        assert_eq!(reduction.reduced_source(), case.expected, "{}", case.name);
        assert_eq!(
            reduction
                .pieces()
                .iter()
                .map(|piece| {
                    &case.source
                        [piece.original_range.start as usize..piece.original_range.end as usize]
                })
                .collect::<String>(),
            case.expected,
            "{}",
            case.name
        );
    }

    fn input(source: &str, edition: Edition, target: &str) -> SourceInput {
        SourceInput::binary(source.to_owned(), edition, target)
    }

    fn edition_name(edition: Edition) -> &'static str {
        match edition {
            Edition::Rust2015 => "2015",
            Edition::Rust2018 => "2018",
            Edition::Rust2021 => "2021",
            Edition::Rust2024 => "2024",
            unsupported => panic!("unsupported external-crate test edition: {unsupported:?}"),
        }
    }

    fn range_of(source: &str, snippet: &str) -> ByteRange {
        let start = source.find(snippet).expect("snippet must occur in source");
        ByteRange {
            start: u32::try_from(start).unwrap(),
            end: u32::try_from(start + snippet.len()).unwrap(),
        }
    }

    fn host_target() -> String {
        let output = Command::new(compiler())
            .arg("-Vv")
            .output()
            .expect("rustc -Vv must start");
        assert!(output.status.success());
        String::from_utf8(output.stdout)
            .expect("rustc -Vv must be UTF-8")
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .expect("rustc -Vv must report the host")
            .to_owned()
    }

    fn compiler() -> &'static str {
        env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC")
    }
}
