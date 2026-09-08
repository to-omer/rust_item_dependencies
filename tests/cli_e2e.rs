#![feature(rustc_private)]

#[cfg(rust_item_dependencies_patched)]
#[test]
fn reduced_cli_output_compiles_and_preserves_program_output() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let work = std::env::temp_dir().join(format!(
        "rust-item-dependencies-cli-e2e-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir(&work).unwrap();

    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let input = repository.join("tests/fixtures/compiler/driver_smoke.rs");
    let reduced = work.join("reduced.rs");
    let reduction = std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .arg(&input)
        .arg("-o")
        .arg(&reduced)
        .output()
        .unwrap();
    assert!(
        reduction.status.success(),
        "{}",
        String::from_utf8_lossy(&reduction.stderr)
    );
    assert!(reduction.stdout.is_empty());
    assert_eq!(
        std::fs::read_to_string(&reduced).unwrap(),
        include_str!("fixtures/compiler/driver_smoke.expected.rs")
    );

    let binary = work.join(format!("reduced{}", std::env::consts::EXE_SUFFIX));
    let compilation = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("--edition=2024")
        .arg(&reduced)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let execution = std::process::Command::new(&binary).output().unwrap();
    assert!(execution.status.success());
    assert_eq!(execution.stdout, b"3\n");
    assert!(execution.stderr.is_empty());

    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn no_main_cli_output_keeps_the_external_entry_and_compiles() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let work = repository.join("target/tests").join(format!(
        "rust-item-dependencies-cli-no-main-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&work).unwrap();

    let input = work.join("input.rs");
    let reduced = work.join("reduced.rs");
    std::fs::write(
        &input,
        concat!(
            "#![no_main]\n",
            "\n",
            "fn dead() {}\n",
            "\n",
            "#[unsafe(no_mangle)]\n",
            "pub extern \"C\" fn main(\n",
            "    _argc: core::ffi::c_int,\n",
            "    _argv: *const *const core::ffi::c_char,\n",
            ") -> core::ffi::c_int {\n",
            "    0\n",
            "}\n",
        ),
    )
    .unwrap();

    let reduction = std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .arg(&input)
        .arg("-o")
        .arg(&reduced)
        .output()
        .unwrap();
    assert!(
        reduction.status.success(),
        "{}",
        String::from_utf8_lossy(&reduction.stderr)
    );
    assert!(reduction.stdout.is_empty());
    assert_eq!(
        std::fs::read_to_string(&reduced).unwrap(),
        concat!(
            "#![no_main]\n",
            "\n",
            "\n",
            "\n",
            "#[unsafe(no_mangle)]\n",
            "pub extern \"C\" fn main(\n",
            "    _argc: core::ffi::c_int,\n",
            "    _argv: *const *const core::ffi::c_char,\n",
            ") -> core::ffi::c_int {\n",
            "    0\n",
            "}\n",
        )
    );

    let binary = work.join(format!("reduced{}", std::env::consts::EXE_SUFFIX));
    let compilation = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("--edition=2024")
        .arg(&reduced)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let execution = std::process::Command::new(&binary).output().unwrap();
    assert!(execution.status.success());
    assert!(execution.stdout.is_empty());
    assert!(execution.stderr.is_empty());

    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn library_cli_keeps_unicode_entries_and_emits_a_compilable_rlib() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let work = repository.join("target/tests").join(format!(
        "rust-item-dependencies-cli-library-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&work).unwrap();

    let input = work.join("library.rs");
    let reduced = work.join("reduced.rs");
    std::fs::write(
        &input,
        concat!(
            "pub fn cafe\u{0301}() -> u8 { helper() }\n",
            "fn helper() -> u8 { 7 }\n",
            "pub fn dead() -> u8 { 0 }\n",
        ),
    )
    .unwrap();

    let reduction = std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .args([
            "--crate-type",
            "lib",
            "--crate-name",
            "cli_library",
            "--entry",
            "cli_library::cafe\u{0301}",
        ])
        .arg(&input)
        .arg("-o")
        .arg(&reduced)
        .output()
        .unwrap();
    assert!(
        reduction.status.success(),
        "{}",
        String::from_utf8_lossy(&reduction.stderr)
    );
    assert!(reduction.stdout.is_empty());
    assert_eq!(
        std::fs::read_to_string(&reduced).unwrap(),
        concat!(
            "pub fn cafe\u{0301}() -> u8 { helper() }\n",
            "fn helper() -> u8 { 7 }\n",
            "\n",
        )
    );

    let library = work.join("libcli_library.rlib");
    let compilation = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg(&reduced)
        .args([
            "--crate-name=cli_library",
            "--crate-type=rlib",
            "--edition=2024",
            "-o",
        ])
        .arg(&library)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    assert!(library.is_file());

    let fixed = work.join("fixed.rs");
    let second = std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .args([
            "--crate-type",
            "lib",
            "--crate-name",
            "cli_library",
            "--entry",
            "cli_library::r#café",
        ])
        .arg(&reduced)
        .arg("-o")
        .arg(&fixed)
        .output()
        .unwrap();
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    assert_eq!(
        std::fs::read(&fixed).unwrap(),
        std::fs::read(&reduced).unwrap()
    );

    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn cli_applies_optimization_and_explicit_cfg_to_the_reduction() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let work = repository.join("target/tests").join(format!(
        "rust-item-dependencies-cli-options-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&work).unwrap();

    let input = repository.join("tests/fixtures/retention/compilation_context.input.rs");
    let reduced = work.join("reduced.rs");

    let reduction = std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .arg("-O")
        .arg("--cfg")
        .arg("ONLINE_JUDGE")
        .arg("--cfg")
        .arg("fn")
        .arg(&input)
        .arg("-o")
        .arg(&reduced)
        .output()
        .unwrap();
    assert!(
        reduction.status.success(),
        "{}",
        String::from_utf8_lossy(&reduction.stderr)
    );
    assert!(reduction.stdout.is_empty());
    assert_eq!(
        std::fs::read_to_string(&reduced).unwrap(),
        include_str!("fixtures/retention/compilation_context.expected.rs")
    );

    let binary = work.join(format!("reduced{}", std::env::consts::EXE_SUFFIX));
    let compilation = std::process::Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("--edition=2024")
        .arg("-O")
        .arg("--cfg=r#ONLINE_JUDGE")
        .arg("--cfg=r#fn")
        .arg(&reduced)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let execution = std::process::Command::new(&binary).output().unwrap();
    assert!(execution.status.success());
    assert_eq!(execution.stdout, b"7\n");
    assert!(execution.stderr.is_empty());

    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn cli_failures_report_reasons_ranges_and_all_compiler_diagnostics() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let work = repository.join("target/tests").join(format!(
        "rust-item-dependencies-cli-errors-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&work).unwrap();

    let unsupported_input = work.join("unsupported.rs");
    let unsupported_output = work.join("unsupported-output.rs");
    std::fs::write(&unsupported_input, "#![no_main]\nfn main() {}\n").unwrap();
    let unsupported = run_cli(&unsupported_input, &unsupported_output);
    assert!(!unsupported.status.success());
    assert!(unsupported.stdout.is_empty());
    assert!(!unsupported_output.exists());
    let unsupported_error = String::from_utf8(unsupported.stderr).unwrap();
    assert!(
        unsupported_error.starts_with(
            "error: the input is outside the supported source boundary: MissingTargetEntry"
        ),
        "{unsupported_error}"
    );

    let invalid_source = concat!(
        "fn main() {\n",
        "    let _: u32 = \"first\";\n",
        "    let _: bool = 0;\n",
        "}\n",
    );
    let invalid_input = work.join("invalid.rs");
    let invalid_output = work.join("invalid-output.rs");
    std::fs::write(&invalid_input, invalid_source).unwrap();
    let invalid = run_cli(&invalid_input, &invalid_output);
    assert!(!invalid.status.success());
    assert!(invalid.stdout.is_empty());
    assert!(!invalid_output.exists());
    let invalid_error = String::from_utf8(invalid.stderr).unwrap();
    assert!(
        invalid_error.starts_with("error: the original source did not compile\n"),
        "{invalid_error}"
    );
    assert_eq!(invalid_error.matches("mismatched types").count(), 2);
    for message in [
        "note: expected `u32`, found `&str`",
        "note: expected `bool`, found integer",
    ] {
        assert!(invalid_error.contains(message), "{invalid_error}");
    }
    for marker in ["\"first\"", "0"] {
        let start = invalid_source.find(marker).unwrap();
        assert!(
            invalid_error.contains(&format!("at bytes {start}..{}", start + marker.len())),
            "{invalid_error}"
        );
    }

    let borrowing_source =
        "fn consume(_: &str) {}\nfn main() { let value = String::new(); consume(value); }\n";
    std::fs::write(&invalid_input, borrowing_source).unwrap();
    let borrowing = run_cli(&invalid_input, &invalid_output);
    assert!(!borrowing.status.success());
    assert!(!invalid_output.exists());
    let borrowing_error = String::from_utf8(borrowing.stderr).unwrap();
    let position = borrowing_source.rfind("value").unwrap();
    assert!(
        borrowing_error.contains(&format!(
            "help: consider borrowing here at bytes {position}..{position}"
        )),
        "{borrowing_error}"
    );

    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
fn run_cli(input: &std::path::Path, output: &std::path::Path) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .arg(input)
        .arg("-o")
        .arg(output)
        .output()
        .unwrap()
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn cli_uses_given_source_paths_for_reduction_and_verification() {
    use std::path::PathBuf;
    use std::process::Command;

    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let work = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target/tests")
        .join(format!("source-filenames-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&work).unwrap();
    let paths = [
        (PathBuf::from("named.rs"), PathBuf::from("reduced.rs")),
        (work.join("absolute.rs"), work.join("absolute-reduced.rs")),
    ];
    for (case, (input, reduced)) in paths.iter().enumerate() {
        std::fs::write(
            work.join(input),
            include_str!("fixtures/compiler/source_filename.rs"),
        )
        .unwrap();
        let reduction = Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
            .current_dir(&work)
            .arg(input)
            .arg("-o")
            .arg(reduced)
            .output()
            .unwrap();
        assert!(
            reduction.status.success(),
            "case {case}: {}",
            String::from_utf8_lossy(&reduction.stderr)
        );
        let text = std::fs::read_to_string(work.join(reduced)).unwrap();
        assert!(text.contains("impl Pick for Flag<false>"));
        assert!(!text.contains("impl Pick for Flag<true>"));

        for source_path in [input, reduced] {
            let binary = work.join(format!("program{case}{}", std::env::consts::EXE_SUFFIX));
            let compilation = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
                .current_dir(&work)
                .args(["--edition=2024", "--crate-name=main"])
                .arg(source_path)
                .arg("-o")
                .arg(&binary)
                .output()
                .unwrap();
            assert!(
                compilation.status.success(),
                "{}",
                String::from_utf8_lossy(&compilation.stderr)
            );
            let execution = Command::new(&binary).output().unwrap();
            assert!(execution.status.success());
            assert_eq!(
                String::from_utf8(execution.stdout).unwrap(),
                format!("2 {}\n", source_path.display())
            );
        }

        let second_path = format!("again{case}.rs");
        let second = Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
            .current_dir(&work)
            .arg(reduced)
            .args(["-o", &second_path])
            .output()
            .unwrap();
        assert!(
            second.status.success(),
            "{}",
            String::from_utf8_lossy(&second.stderr)
        );
        assert_eq!(
            std::fs::read_to_string(work.join(second_path)).unwrap(),
            text
        );
    }
    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(all(rust_item_dependencies_patched, target_os = "linux"))]
#[test]
fn cli_reads_and_writes_non_utf8_source_paths() {
    use std::os::unix::ffi::OsStringExt;

    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let work = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/tests")
        .join(format!(
            "non-utf8-source-paths-{}-{nonce}",
            std::process::id()
        ));
    std::fs::create_dir_all(&work).unwrap();
    let input = work.join(std::ffi::OsString::from_vec(b"named-\xff.rs".to_vec()));
    let reduced = work.join(std::ffi::OsString::from_vec(b"output-\xfe.rs".to_vec()));
    let second = work.join("second.rs");
    let original = include_str!("fixtures/compiler/source_filename.rs");
    std::fs::write(&input, original).unwrap();

    // The normal reduction validates both sources with rustc's driver. The
    // standalone rustc executable requires UTF-8 arguments for its input path.
    let result = run_cli(&input, &reduced);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let source = std::fs::read_to_string(&reduced).unwrap();
    assert!(source.contains("impl Pick for Flag<false>"));
    assert!(!source.contains("impl Pick for Flag<true>"));
    assert_eq!(std::fs::read_to_string(&input).unwrap(), original);
    let result = run_cli(&reduced, &second);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(std::fs::read_to_string(second).unwrap(), source);
    std::fs::remove_dir_all(work).unwrap();
}

#[cfg(rust_item_dependencies_patched)]
#[test]
fn cli_rejects_output_filenames_that_change_required_impls() {
    use std::process::Command;

    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let work = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/tests")
        .join(format!(
            "source-filename-errors-{}-{nonce}",
            std::process::id()
        ));
    std::fs::create_dir_all(&work).unwrap();
    let source = include_str!("fixtures/compiler/source_filename.rs");
    for keep_both in [false, true] {
        let source = if keep_both {
            source.replace(
                "fn main() {",
                "fn main() { let _ = (<Flag<true> as Pick>::value, <Flag<false> as Pick>::value);",
            )
        } else {
            source.to_owned()
        };
        std::fs::write(work.join("main.rs"), source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
            .current_dir(&work)
            .args(["main.rs", "-o", "other.rs"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(!work.join("other.rs").exists());
        let error = String::from_utf8(output.stderr).unwrap();
        let expected = if keep_both {
            "the reduced compiler decisions differ from the original"
        } else {
            "the reduced source did not compile"
        };
        assert!(error.contains(expected), "{error}");
        if keep_both {
            for detail in ["original:", "reduced:"] {
                assert!(error.contains(detail), "{error}");
            }
        }
    }
    std::fs::remove_dir_all(work).unwrap();
}
