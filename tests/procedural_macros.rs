#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
mod patched {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};
    use std::sync::atomic::{AtomicU64, Ordering};

    use rust_item_dependencies::{
        AnalysisError, Analyzer, CompilationOptions, Edition, SourceInput, UnsupportedReason,
    };

    const MACRO_SOURCE: &str = include_str!("fixtures/procedural_macros/macros.rs");
    const WRAPPER_SOURCE: &str = include_str!("fixtures/procedural_macros/wrapper.rs");
    const INPUT_SOURCE: &str = include_str!("fixtures/procedural_macros/input.rs");
    const EXPECTED_SOURCE: &str = include_str!("fixtures/procedural_macros/expected.rs");

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);

            let parent =
                Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tests/procedural-macros");
            fs::create_dir_all(&parent).expect("the procedural macro test parent must exist");
            for _ in 0..1_024 {
                let path = parent.join(format!(
                    "{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => {
                        panic!("cannot create a procedural macro test directory: {error}")
                    }
                }
            }
            panic!("cannot allocate a procedural macro test directory")
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct ProcMacroArtifacts {
        _directory: TestDirectory,
        direct: PathBuf,
        denied: PathBuf,
        wrapper: PathBuf,
    }

    impl ProcMacroArtifacts {
        fn build() -> Self {
            let directory = TestDirectory::new();
            let macro_source = directory.path().join("macros.rs");
            let wrapper_source = directory.path().join("wrapper.rs");
            let direct = dynamic_library_path(directory.path(), "proc_fixture");
            let denied = dynamic_library_path(directory.path(), "denied_fixture");
            let wrapper = directory.path().join("libproc_wrapper.rlib");
            fs::write(&macro_source, MACRO_SOURCE).expect("the macro source must be writable");
            fs::write(&wrapper_source, WRAPPER_SOURCE)
                .expect("the wrapper source must be writable");

            compile_proc_macro("proc_fixture", &macro_source, &direct);
            compile_proc_macro("denied_fixture", &macro_source, &denied);
            assert_success(
                Command::new(compiler())
                    .arg(&wrapper_source)
                    .args(["--crate-name", "proc_wrapper", "--crate-type=rlib"])
                    .arg("--edition=2024")
                    .args(["--target", &host_target()])
                    .arg("--extern")
                    .arg(format!("proc_fixture={}", direct.display()))
                    .arg("-L")
                    .arg(format!("dependency={}", directory.path().display()))
                    .args(["-Awarnings", "-o"])
                    .arg(&wrapper)
                    .output()
                    .expect("the wrapper compiler must finish"),
                "building the proc-macro re-export wrapper",
            );

            Self {
                _directory: directory,
                direct,
                denied,
                wrapper,
            }
        }

        fn direct_options(&self) -> CompilationOptions {
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &self.direct)
                .allow_proc_macro_execution(&self.direct)
        }

        fn transitive_options(&self) -> CompilationOptions {
            CompilationOptions::new()
                .with_external_crate("proc_wrapper", &self.wrapper)
                .with_dependency_artifact(&self.direct)
                .allow_proc_macro_execution(&self.direct)
        }

        fn directory(&self) -> &Path {
            self.direct
                .parent()
                .expect("the macro artifact must have a parent")
        }
    }

    #[test]
    fn permitted_proc_macros_reduce_as_atomic_inputs_compile_and_reach_a_fixed_point() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let original = input(INPUT_SOURCE);

        let verified = analyzer.reduce_and_verify(&original).unwrap();
        assert_eq!(verified.reduced_source(), EXPECTED_SOURCE);
        assert_eq!(
            verified.verification().original_snapshot_hash(),
            verified.verification().reduced_snapshot_hash()
        );

        let reduced = input(verified.reduced_source());
        let fixed = analyzer.reduce_and_verify(&reduced).unwrap();
        assert_eq!(fixed.reduced_source(), verified.reduced_source());

        let cli_input = artifacts.directory().join("cli-input.rs");
        let cli_output = artifacts.directory().join("cli-output.rs");
        fs::write(&cli_input, INPUT_SOURCE).unwrap();
        assert_success(
            Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
                .args(["--edition", "2024", "--extern"])
                .arg(format!("proc_fixture={}", artifacts.direct.display()))
                .arg("--allow-proc-macro")
                .arg(&artifacts.direct)
                .arg(&cli_input)
                .arg("-o")
                .arg(&cli_output)
                .output()
                .expect("the public CLI must finish"),
            "reducing through the public CLI",
        );
        assert_eq!(fs::read_to_string(cli_output).unwrap(), EXPECTED_SOURCE);

        let original_output = compile_and_run(&original.source, &artifacts, "original", false);
        let reduced_output = compile_and_run(&reduced.source, &artifacts, "reduced", false);
        assert!(original_output.status.success());
        assert_eq!(original_output.stdout, b"42\n");
        assert_eq!(reduced_output.status, original_output.status);
        assert_eq!(reduced_output.stdout, original_output.stdout);
        assert_eq!(reduced_output.stderr, original_output.stderr);
    }

    #[test]
    fn generated_and_stacked_proc_macros_keep_their_written_outer_input() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let generated = concat!(
            "macro_rules! make_bang { () => { fn bang() -> i32 { proc_fixture::one!() } } }\n",
            "macro_rules! make_attr { ($item:item) => { #[proc_fixture::passthrough] $item } }\n",
            "macro_rules! make_derive { ($item:item) => { #[derive(proc_fixture::Answer)] $item } }\n",
            "make_bang!();\n",
            "make_attr!(struct Attributed;);\n",
            "make_derive!(struct Marker;);\n",
            "fn main() { let _ = Attributed; println!(\"{}\", bang() + Marker::answer()); }\n",
        );

        let generated_reduction = analyzer.reduce_and_verify(&input(generated)).unwrap();
        assert_eq!(generated_reduction.reduced_source(), generated);
        let generated_output = compile_and_run(
            generated_reduction.reduced_source(),
            &artifacts,
            "generated",
            false,
        );
        assert!(generated_output.status.success());
        assert_eq!(generated_output.stdout, b"2\n");
        assert!(generated_output.stderr.is_empty());

        let stacked = concat!(
            "#[proc_fixture::passthrough]\n",
            "#[derive(proc_fixture::Answer)]\n",
            "struct Marker;\n",
            "fn main() { println!(\"{}\", Marker::answer()); }\n",
        );
        let stacked_reduction = analyzer.reduce_and_verify(&input(stacked)).unwrap();
        assert_eq!(stacked_reduction.reduced_source(), stacked);
        let stacked_output = compile_and_run(
            stacked_reduction.reduced_source(),
            &artifacts,
            "stacked",
            false,
        );
        assert!(stacked_output.status.success());
        assert_eq!(stacked_output.stdout, b"1\n");
        assert!(stacked_output.stderr.is_empty());
    }

    #[test]
    fn a_transitively_reexported_proc_macro_uses_the_same_permission_boundary() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.transitive_options()).unwrap();
        let source = concat!(
            "#[proc_wrapper::passthrough]\n",
            "fn main() { println!(\"7\"); }\n",
        );

        let reduced = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(reduced.reduced_source(), source);
        let output = compile_and_run(reduced.reduced_source(), &artifacts, "transitive", true);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"7\n");
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn unpermitted_proc_macros_are_rejected_at_each_written_invocation() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(
            CompilationOptions::new().with_external_crate("proc_fixture", &artifacts.direct),
        )
        .unwrap();

        for (source, invocation, macro_name) in [
            (
                "fn main() { let _ = proc_fixture::panic_bang!(); }\n",
                "proc_fixture::panic_bang!()",
                "panic_bang",
            ),
            (
                "#[proc_fixture::panic_attr]\nfn main() {}\n",
                "#[proc_fixture::panic_attr]",
                "panic_attr",
            ),
            (
                "#[derive(proc_fixture::PanicDerive)]\nstruct Marker;\nfn main() {}\n",
                "#[derive(proc_fixture::PanicDerive)]",
                "PanicDerive",
            ),
        ] {
            let error = analyzer
                .analyze(&input(source))
                .expect_err("an unpermitted macro must be rejected before execution");
            let AnalysisError::UnsupportedInput {
                reason: UnsupportedReason::ProcMacro,
                range: Some(range),
            } = error
            else {
                panic!("unexpected error for {macro_name}: {error:?}")
            };
            let invocation_start = source.find(invocation).unwrap();
            let invocation_end = invocation_start + invocation.len();
            assert!(
                invocation_start <= range.start as usize && range.end as usize <= invocation_end,
                "{macro_name}: {range:?} is outside {invocation_start}..{invocation_end}"
            );
            assert!(!range.is_empty(), "{macro_name}: {range:?}");
        }
    }

    #[test]
    fn a_permitted_proc_macro_failure_is_an_original_compilation_failure() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = input("fn main() { let _ = proc_fixture::panic_bang!(); }\n");

        assert!(matches!(
            analyzer.analyze(&source),
            Err(AnalysisError::OriginalCompilationFailed(_))
        ));
    }

    #[test]
    fn a_permission_for_one_artifact_does_not_authorize_another_artifact() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &artifacts.direct)
                .with_external_crate("denied_fixture", &artifacts.denied)
                .allow_proc_macro_execution(&artifacts.direct),
        )
        .unwrap();
        let source = "fn main() { let _ = denied_fixture::panic_bang!(); }\n";

        assert!(matches!(
            analyzer.analyze(&input(source)),
            Err(AnalysisError::UnsupportedInput {
                reason: UnsupportedReason::ProcMacro,
                ..
            })
        ));
    }

    #[test]
    fn proc_macro_recipe_normalizes_paths_and_order_and_tracks_roles_contents_and_permissions() {
        let artifacts = ProcMacroArtifacts::build();
        let copied_directory = TestDirectory::new();
        let copied_direct = copied_directory
            .path()
            .join(artifacts.direct.file_name().unwrap());
        let copied_denied = copied_directory
            .path()
            .join(artifacts.denied.file_name().unwrap());
        fs::copy(&artifacts.direct, &copied_direct).unwrap();
        fs::copy(&artifacts.denied, &copied_denied).unwrap();
        let source = input("fn main() {}\n");
        let expected = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &artifacts.direct)
                .with_dependency_artifact(&artifacts.denied)
                .allow_proc_macro_execution(&artifacts.direct)
                .allow_proc_macro_execution(&artifacts.denied),
        )
        .unwrap()
        .analyze(&source)
        .unwrap()
        .recipe();
        let copied = Analyzer::new_with_options(
            CompilationOptions::new()
                .allow_proc_macro_execution(&copied_denied)
                .with_dependency_artifact(&copied_denied)
                .allow_proc_macro_execution(&copied_direct)
                .with_external_crate("proc_fixture", &copied_direct)
                .allow_proc_macro_execution(&copied_direct)
                .with_dependency_artifact(&copied_denied),
        )
        .unwrap()
        .analyze(&source)
        .unwrap()
        .recipe();
        assert_eq!(copied, expected);

        let different_roles = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &artifacts.denied)
                .with_dependency_artifact(&artifacts.direct)
                .allow_proc_macro_execution(&artifacts.direct)
                .allow_proc_macro_execution(&artifacts.denied),
        )
        .unwrap()
        .analyze(&source)
        .unwrap()
        .recipe();
        assert_ne!(different_roles, expected);

        fs::copy(&artifacts.denied, &copied_direct).unwrap();
        let different_contents = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &copied_direct)
                .with_dependency_artifact(&copied_denied)
                .allow_proc_macro_execution(&copied_direct)
                .allow_proc_macro_execution(&copied_denied),
        )
        .unwrap()
        .analyze(&source)
        .unwrap()
        .recipe();
        assert_ne!(different_contents, expected);

        let without_permission = Analyzer::new_with_options(
            CompilationOptions::new()
                .with_external_crate("proc_fixture", &artifacts.direct)
                .with_dependency_artifact(&artifacts.denied),
        )
        .unwrap()
        .analyze(&source)
        .unwrap()
        .recipe();
        assert_ne!(without_permission, expected);
    }

    #[test]
    fn proc_macro_execution_uses_the_artifact_snapshot_owned_by_the_analyzer() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        fs::write(&artifacts.direct, b"not a dynamic library").unwrap();

        let source = input("fn main() { println!(\"{}\", proc_fixture::one!()); }\n");
        let reduced = analyzer.reduce_and_verify(&source).unwrap();

        assert_eq!(reduced.reduced_source(), source.source);
    }

    #[test]
    fn loaded_proc_macro_snapshot_is_removed_after_last_analyzer_drops() {
        const CHILD_PROCESS: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_CLEANUP_CHILD";
        const TEST_NAME: &str =
            "patched::loaded_proc_macro_snapshot_is_removed_after_last_analyzer_drops";

        if let Some(snapshot_parent) = std::env::var_os(CHILD_PROCESS) {
            let snapshot_parent = fs::canonicalize(PathBuf::from(snapshot_parent)).unwrap();
            assert_eq!(
                fs::canonicalize(std::env::temp_dir()).unwrap(),
                snapshot_parent
            );
            let artifacts = ProcMacroArtifacts::build();
            let snapshots_before = directory_entries(&snapshot_parent);
            let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
            let mut created_snapshots = directory_entries(&snapshot_parent);
            created_snapshots.retain(|path| !snapshots_before.contains(path));
            created_snapshots.retain(|path| {
                path.join(artifacts.direct.file_name().unwrap())
                    .try_exists()
                    .unwrap()
            });
            assert_eq!(created_snapshots.len(), 1, "unexpected analyzer snapshots");
            let snapshot = created_snapshots.pop().unwrap();

            analyzer
                .analyze(&input("fn main() { let _ = proc_fixture::one!(); }\n"))
                .unwrap();
            assert!(
                snapshot.try_exists().unwrap(),
                "the analyzer snapshot was not created"
            );

            let last_owner = analyzer.clone();
            drop(analyzer);
            assert!(
                snapshot.try_exists().unwrap(),
                "a live analyzer lost its procedural macro snapshot"
            );

            drop(last_owner);
            assert!(
                !snapshot.try_exists().unwrap(),
                "the loaded procedural macro snapshot remains at {}",
                snapshot.display()
            );
            return;
        }

        let snapshot_parent = TestDirectory::new();
        let output = Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg(TEST_NAME)
            .arg("--nocapture")
            .env(CHILD_PROCESS, snapshot_parent.path())
            .env("TMPDIR", snapshot_parent.path())
            .env("TMP", snapshot_parent.path())
            .env("TEMP", snapshot_parent.path())
            .env("SystemTemp", snapshot_parent.path())
            .output()
            .expect("the isolated cleanup test must finish");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "checking procedural macro snapshot cleanup failed:\n{stdout}\n{stderr}"
        );
        assert!(
            stdout.contains("1 passed"),
            "the isolated cleanup test did not run:\n{stdout}\n{stderr}"
        );
    }

    fn directory_entries(parent: &Path) -> Vec<PathBuf> {
        let mut entries = Vec::new();
        for entry in fs::read_dir(parent).unwrap() {
            let entry = match entry {
                Ok(entry) => entry,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => panic!("cannot read the snapshot parent: {error}"),
            };
            match entry.file_type() {
                Ok(file_type) if file_type.is_dir() => entries.push(entry.path()),
                Ok(_) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => panic!("cannot inspect a snapshot candidate: {error}"),
            }
        }
        entries.sort();
        entries
    }

    #[test]
    fn proc_macro_permission_must_refer_to_a_declared_host_dynamic_library() {
        let artifacts = ProcMacroArtifacts::build();
        assert!(matches!(
            Analyzer::new_with_options(
                CompilationOptions::new().allow_proc_macro_execution(&artifacts.direct)
            ),
            Err(AnalysisError::InvalidProcMacroExecutionArtifact { .. })
        ));
        assert!(matches!(
            Analyzer::new_with_options(
                CompilationOptions::new()
                    .with_external_crate("proc_wrapper", &artifacts.wrapper)
                    .allow_proc_macro_execution(&artifacts.wrapper)
            ),
            Err(AnalysisError::InvalidProcMacroExecutionArtifact { .. })
        ));
    }

    fn compile_proc_macro(crate_name: &str, source: &Path, artifact: &Path) {
        assert_success(
            Command::new(compiler())
                .arg(source)
                .args(["--crate-name", crate_name, "--crate-type=proc-macro"])
                .arg("--edition=2024")
                .args(["-Awarnings", "-o"])
                .arg(artifact)
                .output()
                .expect("the procedural macro compiler must finish"),
            "building a procedural macro",
        );
    }

    fn compile_and_run(
        source: &str,
        artifacts: &ProcMacroArtifacts,
        name: &str,
        transitive: bool,
    ) -> Output {
        let source_path = artifacts.directory().join(format!("{name}.rs"));
        let executable = artifacts
            .directory()
            .join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
        fs::write(&source_path, source).expect("the program source must be writable");
        let mut command = Command::new(compiler());
        command
            .arg(&source_path)
            .args(["--crate-name", name, "--crate-type=bin"])
            .arg("--edition=2024")
            .args(["--target", &host_target()])
            .arg("--extern");
        if transitive {
            command.arg(format!("proc_wrapper={}", artifacts.wrapper.display()));
        } else {
            command.arg(format!("proc_fixture={}", artifacts.direct.display()));
        }
        assert_success(
            command
                .arg("-L")
                .arg(format!("dependency={}", artifacts.directory().display()))
                .args(["-Awarnings", "-o"])
                .arg(&executable)
                .output()
                .expect("the program compiler must finish"),
            "linking a program that uses procedural macros",
        );
        Command::new(executable)
            .output()
            .expect("the linked program must start")
    }

    fn assert_success(output: Output, action: &str) {
        assert!(
            output.status.success(),
            "{action} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn input(source: &str) -> SourceInput {
        SourceInput {
            source: source.to_owned(),
            edition: Edition::Rust2024,
            target: host_target(),
        }
    }

    fn dynamic_library_path(directory: &Path, crate_name: &str) -> PathBuf {
        directory.join(format!(
            "{}{crate_name}{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        ))
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
