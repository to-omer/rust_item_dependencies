use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=rustc-patches");
    println!("cargo:rerun-if-changed=tests/fixtures/compiler/patch_abi.rs");
    println!("cargo:rerun-if-changed=rustc-patches/queue-digest");
    println!("cargo:rustc-check-cfg=cfg(rust_item_dependencies_patched)");

    let expected_revision = std::fs::read_to_string("rustc-patches/base-revision")
        .expect("rustc-patches/base-revision must be readable");
    let expected_revision = expected_revision.trim();
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc"));

    let version = rustc_output(&rustc, &["-Vv"]);
    let actual_revision = version
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .expect("rustc -Vv must report commit-hash");
    let host = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("rustc -Vv must report host");
    let sysroot = PathBuf::from(rustc_output(&rustc, &["--print", "sysroot"]).trim());
    let compiler_library_directory = if host.contains("windows") {
        sysroot.join("bin")
    } else {
        sysroot.join("lib")
    };

    if actual_revision != expected_revision {
        let compiler_metadata = validate_patched_compiler(&rustc, &sysroot, host);
        println!("cargo:rustc-cfg=rust_item_dependencies_patched");
        println!(
            "cargo:rustc-env=RUST_ITEM_DEPENDENCIES_BUILD_SYSROOT={}",
            sysroot.display()
        );
        println!(
            "cargo:rustc-link-search=dependency={}",
            compiler_library_directory.display()
        );
        println!(
            "cargo:rustc-link-search=dependency={}",
            compiler_metadata.display()
        );
    }

    println!(
        "cargo:rustc-env=RUST_ITEM_DEPENDENCIES_BUILD_RUSTC={}",
        PathBuf::from(&rustc).display()
    );

    // rustc_driver links against the compiler's shared LLVM library, which is
    // not in the default native link-search path for external crates.
    println!(
        "cargo:rustc-link-search=native={}",
        compiler_library_directory.display()
    );
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() == Ok("unix") {
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            compiler_library_directory.display()
        );
    }
}

fn validate_patched_compiler(rustc: &OsString, sysroot: &Path, host: &str) -> PathBuf {
    let build_directory = sysroot
        .parent()
        .expect("a patched stage2 sysroot must have a build directory");
    let compiler_metadata = build_directory
        .join("stage1")
        .join("lib/rustlib")
        .join(host)
        .join("lib");
    assert!(
        compiler_metadata.is_dir(),
        "stage1 compiler metadata is missing: {}",
        compiler_metadata.display()
    );

    let compiler_library_directory = if host.contains("windows") {
        sysroot.join("bin")
    } else {
        sysroot.join("lib")
    };
    let rustc_driver = unique_rustc_driver(&compiler_metadata);
    let output = PathBuf::from(
        std::env::var_os("OUT_DIR").expect("Cargo must set OUT_DIR for the build script"),
    )
    .join(format!("patch-abi{}", std::env::consts::EXE_SUFFIX));

    let mut compile = Command::new(rustc);
    compile
        .arg("--sysroot")
        .arg(sysroot)
        .arg("--edition=2024")
        .arg("--extern")
        .arg(format!("rustc_driver={}", rustc_driver.display()))
        .arg("-C")
        .arg("prefer-dynamic")
        .arg("-L")
        .arg(format!("dependency={}", compiler_metadata.display()))
        .arg("-L")
        .arg(format!("native={}", compiler_library_directory.display()));
    if std::env::var("CARGO_CFG_TARGET_FAMILY").as_deref() == Ok("unix") {
        compile.arg("-C").arg(format!(
            "link-arg=-Wl,-rpath,{}",
            compiler_library_directory.display()
        ));
    }
    let status = compile
        .arg("tests/fixtures/compiler/patch_abi.rs")
        .arg("-o")
        .arg(&output)
        .status()
        .expect("the patched rustc ABI probe must start");
    assert!(status.success(), "the patched rustc ABI probe must compile");

    let mut probe = Command::new(&output);
    if cfg!(windows) {
        let inherited_path = std::env::var_os("PATH");
        let paths = std::iter::once(compiler_library_directory.to_path_buf()).chain(
            inherited_path
                .as_deref()
                .map(std::env::split_paths)
                .into_iter()
                .flatten(),
        );
        probe.env(
            "PATH",
            std::env::join_paths(paths).expect("the compiler library path must be valid"),
        );
    }
    let status = probe
        .status()
        .expect("the patched rustc ABI probe must run");
    assert!(status.success(), "the patched rustc ABI probe must pass");

    compiler_metadata
}

fn unique_rustc_driver(directory: &Path) -> PathBuf {
    let prefix = format!("{}rustc_driver-", std::env::consts::DLL_PREFIX);
    let mut candidates = std::fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", directory.display()))
        .map(|entry| {
            entry
                .expect("compiler library entry must be readable")
                .path()
        })
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.starts_with(&prefix) && name.ends_with(std::env::consts::DLL_SUFFIX)
                })
        })
        .collect::<Vec<_>>();
    candidates.sort();
    assert_eq!(
        candidates.len(),
        1,
        "expected exactly one rustc_driver in {}",
        directory.display()
    );
    candidates.pop().unwrap()
}

fn rustc_output(rustc: &OsString, arguments: &[&str]) -> String {
    let output = Command::new(rustc)
        .args(arguments)
        .output()
        .expect("the pinned rustc must be executable");
    assert!(
        output.status.success(),
        "rustc invocation failed: {output:?}"
    );
    String::from_utf8(output.stdout).expect("rustc output must be UTF-8")
}
