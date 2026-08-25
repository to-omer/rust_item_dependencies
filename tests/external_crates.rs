#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
mod patched {
    use std::ffi::OsString;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};
    use std::sync::atomic::{AtomicU64, Ordering};

    use rust_item_dependencies::{
        AnalysisError, Analyzer, CompilationOptions, Edition, SourceInput, UnsupportedReason,
        VerifiedReduction, error::DiagnosticLevel, source::ByteRange,
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
            let verified = analyzer
                .reduce_and_verify(&original)
                .unwrap_or_else(|error| panic!("{}: {error:?}", case.name));
            assert_verified(case, &verified);

            let reduced = input(verified.reduced_source(), case.edition, &target);
            let fixed = analyzer
                .reduce_and_verify(&reduced)
                .unwrap_or_else(|error| panic!("{} fixed point: {error:?}", case.name));
            assert_eq!(
                fixed.reduced_source(),
                verified.reduced_source(),
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

    fn compile_library(crate_name: &str, source: &Path, artifact: &Path, extra_args: &[String]) {
        let compiled = Command::new(compiler())
            .arg(source)
            .args(["--crate-name", crate_name, "--crate-type=rlib"])
            .arg("--edition=2021")
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

    fn cargo_rid(arguments: impl IntoIterator<Item = OsString>) -> Output {
        Command::new(std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")))
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .arg("rid")
            .args(arguments)
            .output()
            .expect("cargo rid must finish")
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

    fn assert_verified(case: &Case, verified: &VerifiedReduction) {
        assert_eq!(verified.reduced_source(), case.expected, "{}", case.name);
        assert_eq!(
            verified.verification().original_snapshot_hash(),
            verified.verification().reduced_snapshot_hash(),
            "{}",
            case.name
        );
        assert_eq!(
            verified
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
