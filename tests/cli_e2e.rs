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
fn library_cli_keeps_the_selected_entry_and_emits_a_compilable_rlib() {
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
            "pub fn kept() -> u8 { helper() }\n",
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
            "cli_library::kept",
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
            "pub fn kept() -> u8 { helper() }\n",
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
    for marker in ["\"first\"", "0"] {
        let start = invalid_source.find(marker).unwrap();
        assert!(
            invalid_error.contains(&format!("at bytes {start}..{}", start + marker.len())),
            "{invalid_error}"
        );
    }

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
