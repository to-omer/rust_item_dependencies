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
    const SNAPSHOT_PARENT_LOCK_FILE: &str = ".rust-item-dependencies-parent-lock";

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

    struct DependentProcMacroArtifacts {
        _directory: TestDirectory,
        proc_macro: PathBuf,
        unused_proc_macro: PathBuf,
        dependency: PathBuf,
    }

    impl DependentProcMacroArtifacts {
        fn build() -> Self {
            let directory = TestDirectory::new();
            let dependency_source = directory.path().join("lifetime_support.rs");
            let dependency = directory.path().join("liblifetime_support.rlib");
            let macro_source = directory.path().join("lifetime_macros.rs");
            let proc_macro = dynamic_library_path(directory.path(), "lifetime_macros");
            let unused_proc_macro =
                dynamic_library_path(directory.path(), "lifetime_unused_macros");
            fs::write(
                &dependency_source,
                "pub fn expression() -> &'static str { \"40 + 2\" }\n",
            )
            .unwrap();
            fs::write(
                &macro_source,
                concat!(
                    "extern crate proc_macro;\n",
                    "extern crate lifetime_support;\n",
                    "use proc_macro::TokenStream;\n",
                    "#[proc_macro]\n",
                    "pub fn from_support(_: TokenStream) -> TokenStream {\n",
                    "    lifetime_support::expression().parse().unwrap()\n",
                    "}\n",
                    "#[proc_macro]\n",
                    "pub fn panic_after_load(_: TokenStream) -> TokenStream {\n",
                    "    let _ = lifetime_support::expression();\n",
                    "    panic!(\"the loaded macro panicked\")\n",
                    "}\n",
                ),
            )
            .unwrap();
            assert_success(
                Command::new(compiler())
                    .arg(&dependency_source)
                    .args([
                        "--crate-name",
                        "lifetime_support",
                        "--crate-type=rlib",
                        "--edition=2024",
                        "--target",
                        &host_target(),
                        "-Awarnings",
                        "-o",
                    ])
                    .arg(&dependency)
                    .output()
                    .expect("the procedural macro dependency compiler must finish"),
                "building a procedural macro dependency",
            );
            for (crate_name, artifact) in [
                ("lifetime_macros", &proc_macro),
                ("lifetime_unused_macros", &unused_proc_macro),
            ] {
                assert_success(
                    Command::new(compiler())
                        .arg(&macro_source)
                        .args(["--crate-name", crate_name, "--crate-type=proc-macro"])
                        .arg("--edition=2024")
                        .args(["--target", &host_target()])
                        .arg("--extern")
                        .arg(format!("lifetime_support={}", dependency.display()))
                        .arg("-L")
                        .arg(format!("dependency={}", directory.path().display()))
                        .args(["-Awarnings", "-o"])
                        .arg(artifact)
                        .output()
                        .expect("the dependent procedural macro compiler must finish"),
                    "building a dependent procedural macro",
                );
            }
            Self {
                _directory: directory,
                proc_macro,
                unused_proc_macro,
                dependency,
            }
        }

        fn options(&self) -> CompilationOptions {
            CompilationOptions::new()
                .with_external_crate("lifetime_macros", &self.proc_macro)
                .with_dependency_artifact(&self.dependency)
                .allow_proc_macro_execution(&self.proc_macro)
        }

        fn options_with_unused_permission(&self) -> CompilationOptions {
            self.options()
                .with_external_crate("lifetime_unused_macros", &self.unused_proc_macro)
                .allow_proc_macro_execution(&self.unused_proc_macro)
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

        let cargo_output = artifacts.directory().join("cargo-rid-output.rs");
        let snapshots = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/rid/snapshots");
        let snapshots_before = directory_entries(&snapshots);
        assert_success(
            Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
                .current_dir(env!("CARGO_MANIFEST_DIR"))
                .arg("rid")
                .args(["--edition", "2024", "--extern"])
                .arg(format!("proc_fixture={}", artifacts.direct.display()))
                .arg("--allow-proc-macro")
                .arg(&artifacts.direct)
                .arg(&cli_input)
                .arg("-o")
                .arg(&cargo_output)
                .output()
                .expect("cargo rid must finish"),
            "reducing through cargo rid",
        );
        assert_eq!(fs::read_to_string(cargo_output).unwrap(), EXPECTED_SOURCE);
        let mut new_snapshots = directory_entries(&snapshots);
        new_snapshots.retain(|snapshot| !snapshots_before.contains(snapshot));
        assert!(
            new_snapshots.is_empty(),
            "cargo rid left process snapshots behind: {new_snapshots:?}"
        );

        let failing_input = artifacts.directory().join("cargo-rid-failing-input.rs");
        let failing_output = artifacts.directory().join("cargo-rid-failing-output.rs");
        fs::write(
            &failing_input,
            "fn main() { let _ = proc_fixture::panic_bang!(); }\n",
        )
        .unwrap();
        let failed = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .arg("rid")
            .args(["--edition", "2024", "--extern"])
            .arg(format!("proc_fixture={}", artifacts.direct.display()))
            .arg("--allow-proc-macro")
            .arg(&artifacts.direct)
            .arg(&failing_input)
            .arg("-o")
            .arg(&failing_output)
            .output()
            .expect("failing cargo rid must finish");
        assert!(!failed.status.success());
        assert!(
            String::from_utf8_lossy(&failed.stderr).contains("proc macro panicked at bytes"),
            "cargo rid failed before executing the permitted macro:\n{}",
            String::from_utf8_lossy(&failed.stderr)
        );
        let mut new_snapshots = directory_entries(&snapshots);
        new_snapshots.retain(|snapshot| !snapshots_before.contains(snapshot));
        assert!(
            new_snapshots.is_empty(),
            "failed cargo rid left process snapshots behind: {new_snapshots:?}"
        );

        let original_output = compile_and_run(&original.source, &artifacts, "original", false);
        let reduced_output = compile_and_run(&reduced.source, &artifacts, "reduced", false);
        assert!(original_output.status.success());
        assert_eq!(original_output.stdout, b"42\n");
        assert_eq!(reduced_output.status, original_output.status);
        assert_eq!(reduced_output.stdout, original_output.stdout);
        assert_eq!(reduced_output.stderr, original_output.stderr);
    }

    #[test]
    fn proc_macro_generated_assembly_uses_the_same_opaque_source_constraint() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = concat!(
            "proc_fixture::make_assembly!();\n",
            "fn unused() {}\n",
            "fn main() { generated_assembly(); println!(\"ok\"); }\n",
        );

        let verified = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(verified.reduced_source(), source);

        let fixed = analyzer
            .reduce_and_verify(&input(verified.reduced_source()))
            .unwrap();
        assert_eq!(fixed.reduced_source(), source);

        let output = compile_and_run(source, &artifacts, "proc_macro_assembly", false);
        assert!(output.status.success(), "{output:?}");
        assert_eq!(output.stdout, b"ok\n");
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn empty_function_like_proc_macro_is_removed_and_reaches_a_fixed_point() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = "proc_fixture::empty!();fn main(){println!(\"ok\");}";
        let expected = "fn main(){println!(\"ok\");}";

        let verified = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(verified.reduced_source(), expected);
        assert_eq!(
            verified.verification().original_snapshot_hash(),
            verified.verification().reduced_snapshot_hash()
        );

        let fixed = analyzer.reduce_and_verify(&input(expected)).unwrap();
        assert_eq!(fixed.reduced_source(), expected);

        let original_output = compile_and_run(source, &artifacts, "empty_original", false);
        let reduced_output = compile_and_run(expected, &artifacts, "empty_reduced", false);
        assert!(original_output.status.success(), "{original_output:?}");
        assert_eq!(original_output.stdout, b"ok\n");
        assert_eq!(reduced_output.status, original_output.status);
        assert_eq!(reduced_output.stdout, original_output.stdout);
        assert_eq!(reduced_output.stderr, original_output.stderr);
    }

    #[test]
    fn empty_attribute_proc_macro_removes_its_item_and_reaches_a_fixed_point() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = concat!(
            "#[proc_fixture::empty_attribute]fn removed(){panic!(\"removed\");}",
            "fn main(){println!(\"ok\");}",
        );
        let expected = "fn main(){println!(\"ok\");}";

        let verified = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(verified.reduced_source(), expected);
        assert_eq!(
            verified.verification().original_snapshot_hash(),
            verified.verification().reduced_snapshot_hash()
        );

        let fixed = analyzer.reduce_and_verify(&input(expected)).unwrap();
        assert_eq!(fixed.reduced_source(), expected);

        let original_output =
            compile_and_run(source, &artifacts, "empty_attribute_original", false);
        let reduced_output =
            compile_and_run(expected, &artifacts, "empty_attribute_reduced", false);
        assert!(original_output.status.success(), "{original_output:?}");
        assert_eq!(original_output.stdout, b"ok\n");
        assert_eq!(reduced_output.status, original_output.status);
        assert_eq!(reduced_output.stdout, original_output.stdout);
        assert_eq!(reduced_output.stderr, original_output.stderr);
    }

    #[test]
    fn input_spanned_proc_output_cannot_refine_local_macro_templates() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let cases = [
            concat!(
                "macro_rules! local { () => { fn generated() -> i32 { 42 } fn dead_generated() {} }; }\n",
                "proc_fixture::emit_input_spanned_local!(marker);\n",
                "fn main() { println!(\"{}\", generated()); }\n",
            ),
            concat!(
                "macro_rules! local { () => { fn generated() -> i32 { 42 } fn dead_generated() {} }; }\n",
                "macro_rules! relay { ($($tokens:tt)*) => { $($tokens)* }; }\n",
                "proc_fixture::emit_input_spanned_relay!(marker);\n",
                "fn main() { println!(\"{}\", generated()); }\n",
            ),
        ];

        for source in cases {
            let reduced = analyzer.reduce_and_verify(&input(source)).unwrap();
            assert_eq!(reduced.reduced_source(), source);
            let fixed = analyzer
                .reduce_and_verify(&input(reduced.reduced_source()))
                .unwrap();
            assert_eq!(fixed.reduced_source(), source);
        }
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
    fn no_effect_cfg_attrs_follow_proc_macro_input_configuration() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let cases = [
            (
                "function-like",
                concat!(
                    "#[cfg_attr(any(),allow(dead_code))]",
                    "proc_fixture::configured_bang!();",
                    "fn main(){assert_eq!(generated(),1)}",
                ),
                concat!(
                    "proc_fixture::configured_bang!();",
                    "fn main(){assert_eq!(generated(),1)}",
                ),
            ),
            (
                "attribute",
                concat!(
                    "#[cfg_attr(any(),allow(dead_code))]",
                    "#[proc_fixture::require_nested_cfg_attr]",
                    "struct Subject{#[cfg(any())]removed:u8,#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
                concat!(
                    "#[proc_fixture::require_nested_cfg_attr]",
                    "struct Subject{#[cfg(any())]removed:u8,#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
            ),
            (
                "derive",
                concat!(
                    "#[cfg_attr(any(),allow(dead_code))]",
                    "#[derive(proc_fixture::ConfiguredInput)]",
                    "struct Subject{#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
                concat!(
                    "#[cfg_attr(any(),allow(dead_code))]",
                    "#[derive(proc_fixture::ConfiguredInput)]",
                    "struct Subject{#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
            ),
            (
                "attribute and derive",
                concat!(
                    "#[cfg_attr(any(),allow(dead_code))]",
                    "#[proc_fixture::require_nested_cfg_attr]",
                    "#[derive(proc_fixture::ConfiguredInput)]",
                    "struct Subject{#[cfg(any())]removed:u8,#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
                concat!(
                    "#[proc_fixture::require_nested_cfg_attr]",
                    "#[derive(proc_fixture::ConfiguredInput)]",
                    "struct Subject{#[cfg(any())]removed:u8,#[cfg_attr(any(),allow(dead_code))]value:u8}",
                    "fn main(){assert_eq!(Subject{value:1}.value,1)}",
                ),
            ),
        ];

        for (case, source, expected) in cases {
            let verified = analyzer
                .reduce_and_verify(&input(source))
                .unwrap_or_else(|error| panic!("{case}: {error:?}"));
            assert_eq!(verified.reduced_source(), expected, "{case}");
            assert_eq!(
                verified.verification().original_snapshot_hash(),
                verified.verification().reduced_snapshot_hash(),
                "{case}",
            );

            let fixed = analyzer
                .reduce_and_verify(&input(expected))
                .unwrap_or_else(|error| panic!("{case} fixed point: {error:?}"));
            assert_eq!(fixed.reduced_source(), expected, "{case}");
        }
    }

    #[test]
    fn procedural_derive_targets_preserve_cfg_token_punctuation_and_spacing() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = concat!(
            "#[derive(proc_fixture::ConfiguredPunctuation)]",
            "struct Subject{live:u8,#[cfg_attr(any(),allow(dead_code))]",
            "tail:[u8;{fn nested(#[cfg(any())] dead:u8,live:u8){}0}]}",
            "fn main(){assert_eq!(Subject{live:1,tail:[]}.live,1)}",
        );

        let verified = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(verified.reduced_source(), source);

        let fixed = analyzer
            .reduce_and_verify(&input(verified.reduced_source()))
            .unwrap();
        assert_eq!(fixed.reduced_source(), source);
    }

    #[test]
    fn declarative_macro_repetitions_preserve_proc_macro_punctuation_spacing() {
        let artifacts = ProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.direct_options()).unwrap();
        let source = concat!(
            "macro_rules! observe_tt {",
            "($( $name:ident => $punct:tt),*) => {",
            "$(fn $name() -> &'static str { proc_fixture::punct_spacing!($punct) })*",
            "};",
            "}",
            "macro_rules! observe_expr {",
            "($( $name:ident => $expr:expr),*) => {",
            "$(fn $name() -> &'static str { proc_fixture::last_punct_spacing!($expr) })*",
            "};",
            "}",
            "macro_rules! observe_prefix {",
            "($head:tt $($tail:ident)* @) => {",
            "fn kept_prefix() -> &'static str { proc_fixture::punct_spacing!($head) }",
            "$(fn $tail() {})*",
            "};",
            "}",
            "observe_tt!(kept_tt => +, dead_tt => -);",
            "observe_expr!(kept_expr => 1.., dead_expr => 2..);",
            "observe_prefix!(+dead_prefix@);",
            "fn main() { println!(\"{} {} {}\", kept_tt(), kept_expr(), kept_prefix()); }",
        );

        let verified = analyzer.reduce_and_verify(&input(source)).unwrap();
        assert_eq!(verified.reduced_source(), source);

        let fixed = analyzer
            .reduce_and_verify(&input(verified.reduced_source()))
            .unwrap();
        assert_eq!(fixed.reduced_source(), source);

        let original = compile_and_run(source, &artifacts, "spacing_original", false);
        let reduced = compile_and_run(
            verified.reduced_source(),
            &artifacts,
            "spacing_reduced",
            false,
        );
        assert!(original.status.success(), "{original:?}");
        assert_eq!(original.stdout, b"Joint Joint Alone\n");
        assert_eq!(reduced.status, original.status);
        assert_eq!(reduced.stdout, original.stdout);
        assert_eq!(reduced.stderr, original.stderr);
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

    const SNAPSHOT_TEST_PHASE_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_TEST_PHASE";
    const SNAPSHOT_PARENT_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT";

    #[test]
    fn loaded_proc_macro_snapshots_follow_the_loader_process_lifetime() {
        run_snapshot_lifetime_case(
            "patched::loaded_proc_macro_snapshots_follow_the_loader_process_lifetime",
            loaded_dependent_proc_macro_case,
        );
    }

    #[test]
    fn a_proc_macro_panic_still_pins_the_loaded_library() {
        run_snapshot_lifetime_case(
            "patched::a_proc_macro_panic_still_pins_the_loaded_library",
            panicking_proc_macro_case,
        );
    }

    fn run_snapshot_lifetime_case(test_name: &str, owner_case: fn(&Path) -> Option<PathBuf>) {
        match std::env::var(SNAPSHOT_TEST_PHASE_ENV).ok().as_deref() {
            Some("reap") => {
                drop(Analyzer::new().unwrap());
                return;
            }
            Some("owner") => {
                let snapshot_parent = fs::canonicalize(
                    std::env::var_os(SNAPSHOT_PARENT_ENV)
                        .expect("snapshot parent must be configured"),
                )
                .unwrap();
                if let Some(snapshot) = owner_case(&snapshot_parent) {
                    println!("SNAPSHOT:{}", snapshot.display());
                }
                return;
            }
            Some(phase) => panic!("unexpected snapshot test phase: {phase}"),
            None => {}
        }

        let snapshot_parent = TestDirectory::new();
        let output = run_snapshot_phase(
            test_name,
            SNAPSHOT_TEST_PHASE_ENV,
            "owner",
            snapshot_parent.path(),
        );
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
        let snapshot = stdout
            .lines()
            .find_map(|line| line.strip_prefix("SNAPSHOT:"))
            .map(PathBuf::from);
        #[cfg(not(windows))]
        assert!(
            snapshot.is_none(),
            "Unix must remove its analyzer-owned snapshot: {snapshot:?}"
        );
        let Some(snapshot) = snapshot else {
            return;
        };
        assert!(
            snapshot.try_exists().unwrap(),
            "the process-owned snapshot disappeared before it could be reaped"
        );

        let reap = run_snapshot_phase(
            test_name,
            SNAPSHOT_TEST_PHASE_ENV,
            "reap",
            snapshot_parent.path(),
        );
        assert_success(reap, "reaping a finished procedural macro snapshot");
        assert!(
            !snapshot.try_exists().unwrap(),
            "the finished process snapshot remains at {}",
            snapshot.display()
        );
    }

    fn loaded_dependent_proc_macro_case(snapshot_parent: &Path) -> Option<PathBuf> {
        let artifacts = DependentProcMacroArtifacts::build();
        let analyzer =
            Analyzer::new_with_options(artifacts.options_with_unused_permission()).unwrap();
        let macro_snapshot =
            unique_directory_containing(snapshot_parent, artifacts.proc_macro.file_name().unwrap());
        let unused_macro_snapshot = unique_directory_containing(
            snapshot_parent,
            artifacts.unused_proc_macro.file_name().unwrap(),
        );
        let dependency_snapshot =
            unique_directory_containing(snapshot_parent, artifacts.dependency.file_name().unwrap());
        #[cfg(windows)]
        {
            assert_ne!(macro_snapshot, unused_macro_snapshot);
            assert_ne!(macro_snapshot, dependency_snapshot);
            assert_ne!(unused_macro_snapshot, dependency_snapshot);
        }
        #[cfg(not(windows))]
        {
            assert_eq!(macro_snapshot, unused_macro_snapshot);
            assert_eq!(macro_snapshot, dependency_snapshot);
        }

        let source = input("fn main() { println!(\"{}\", lifetime_macros::from_support!()); }\n");
        let verified = analyzer.reduce_and_verify(&source).unwrap();
        assert_eq!(verified.reduced_source(), source.source);

        let last_owner = analyzer.clone();
        drop(analyzer);
        assert!(macro_snapshot.try_exists().unwrap());
        let reap = run_snapshot_phase(
            "patched::loaded_proc_macro_snapshots_follow_the_loader_process_lifetime",
            SNAPSHOT_TEST_PHASE_ENV,
            "reap",
            snapshot_parent,
        );
        assert_success(reap, "checking an active procedural macro snapshot");
        assert!(macro_snapshot.try_exists().unwrap());

        drop(last_owner);
        #[cfg(windows)]
        {
            assert!(macro_snapshot.try_exists().unwrap());
            assert!(!unused_macro_snapshot.try_exists().unwrap());
            assert!(!dependency_snapshot.try_exists().unwrap());
            let reused = Analyzer::new_with_options(artifacts.options()).unwrap();
            assert_eq!(
                unique_directory_containing(
                    snapshot_parent,
                    artifacts.proc_macro.file_name().unwrap()
                ),
                macro_snapshot,
                "a loaded procedural macro must reuse its process-owned snapshot"
            );
            drop(reused);
            assert!(macro_snapshot.try_exists().unwrap());
            Some(macro_snapshot)
        }
        #[cfg(not(windows))]
        {
            assert!(!macro_snapshot.try_exists().unwrap());
            None
        }
    }

    fn panicking_proc_macro_case(snapshot_parent: &Path) -> Option<PathBuf> {
        let artifacts = DependentProcMacroArtifacts::build();
        let analyzer = Analyzer::new_with_options(artifacts.options()).unwrap();
        let macro_snapshot =
            unique_directory_containing(snapshot_parent, artifacts.proc_macro.file_name().unwrap());
        let dependency_snapshot =
            unique_directory_containing(snapshot_parent, artifacts.dependency.file_name().unwrap());
        assert!(matches!(
            analyzer.analyze(&input(
                "fn main() { let _ = lifetime_macros::panic_after_load!(); }\n"
            )),
            Err(AnalysisError::OriginalCompilationFailed(_))
        ));
        drop(analyzer);
        #[cfg(windows)]
        {
            assert!(macro_snapshot.try_exists().unwrap());
            assert!(!dependency_snapshot.try_exists().unwrap());
            Some(macro_snapshot)
        }
        #[cfg(not(windows))]
        {
            assert_eq!(macro_snapshot, dependency_snapshot);
            assert!(!macro_snapshot.try_exists().unwrap());
            None
        }
    }

    fn run_snapshot_phase(test_name: &str, phase_env: &str, phase: &str, parent: &Path) -> Output {
        Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg(test_name)
            .arg("--nocapture")
            .env(phase_env, phase)
            .env("RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT", parent)
            .output()
            .expect("the isolated snapshot test must finish")
    }

    fn unique_directory_containing(parent: &Path, file_name: &std::ffi::OsStr) -> PathBuf {
        let mut pending = vec![parent.to_owned()];
        let mut matches = Vec::new();
        while let Some(directory) = pending.pop() {
            for entry in fs::read_dir(&directory).unwrap() {
                let entry = entry.unwrap();
                let file_type = entry.file_type().unwrap();
                if file_type.is_dir() {
                    if entry.path().join(file_name).is_file() {
                        matches.push(entry.path());
                    } else {
                        pending.push(entry.path());
                    }
                }
            }
        }
        assert_eq!(matches.len(), 1, "unexpected analyzer snapshots");
        matches.pop().unwrap()
    }

    fn directory_entries(parent: &Path) -> Vec<PathBuf> {
        let mut entries = match fs::read_dir(parent) {
            Ok(entries) => entries
                .filter_map(Result::ok)
                .filter(|entry| entry.file_name() != SNAPSHOT_PARENT_LOCK_FILE)
                .map(|entry| entry.path())
                .collect(),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            Err(error) => panic!("cannot read {}: {error}", parent.display()),
        };
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
        SourceInput::binary(source.to_owned(), Edition::Rust2024, host_target())
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
