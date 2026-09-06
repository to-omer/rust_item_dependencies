#![cfg(rust_item_dependencies_patched)]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

struct Project(tempfile::TempDir);

impl Project {
    fn new() -> Self {
        let parent = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tests");
        fs::create_dir_all(&parent).unwrap();
        Self(
            tempfile::Builder::new()
                .prefix("cargo-project-")
                .tempdir_in(parent)
                .unwrap(),
        )
    }

    fn write(&self, path: &str, source: &str) {
        let path = self.0.path().join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn read(&self, path: &str) -> String {
        fs::read_to_string(self.0.path().join(path)).unwrap()
    }

    fn command(&self, executable: impl AsRef<std::ffi::OsStr>) -> Command {
        let mut command = Command::new(executable);
        command
            .current_dir(self.0.path())
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env_remove("CARGO_TARGET_DIR")
            .env_remove("CARGO_BUILD_TARGET")
            .env_remove("RUSTC")
            .env("RUSTC_WRAPPER", "")
            .env("RUSTC_WORKSPACE_WRAPPER", "");
        command
    }

    fn reduce(&self) -> Command {
        let mut command = self.command(env!("CARGO_BIN_EXE_rust-item-dependencies"));
        command.arg("--offline");
        command
    }

    fn cargo(&self) -> Command {
        let mut command = self.command(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
        command.env("RUSTC", env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"));
        command
    }
}

fn success(output: Output) -> Output {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn fixture() -> Project {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        r#"
[workspace]
members = ["app", "helper", "maker"]
default-members = ["app"]
resolver = "3"
[profile.submission]
inherits = "release"
debug-assertions = true
opt-level = 2
"#,
    );
    project.write(
        "app/Cargo.toml",
        r#"
[package]
name = "app-main"
version = "0.1.0"
edition = "2021"
[features]
selected = []
[dependencies]
helper = { path = "../helper" }
maker = { path = "../maker" }
"#,
    );
    project.write(
        "app/build.rs",
        r#"fn main() {
        println!("cargo::rustc-check-cfg=cfg(from_build)");
        println!("cargo::rustc-cfg=from_build");
        println!("cargo::rustc-env=BUILD_VALUE=5");
    }"#,
    );
    project.write(
        "app/src/lib.rs",
        "pub fn value() -> u32 { helper::value() }\n",
    );
    project.write(
        "helper/Cargo.toml",
        "[package]\nname='helper'\nversion='0.1.0'\nedition='2024'\n",
    );
    project.write("helper/src/lib.rs", "pub fn value() -> u32 { 4 }\n");
    project.write(
        "maker/Cargo.toml",
        "[package]\nname='maker'\nversion='0.1.0'\nedition='2024'\n[lib]\nproc-macro=true\n",
    );
    project.write("maker/src/lib.rs", "use proc_macro::TokenStream;\n#[proc_macro] pub fn number(_: TokenStream) -> TokenStream { \"3u32\".parse().unwrap() }\n");
    project.write(
        "app/src/main.rs",
        r#"
#[cfg(not(feature = "selected"))] compile_error!("missing selected feature");
#[cfg(not(from_build))] compile_error!("missing build script cfg");
#[cfg(not(debug_assertions))] compile_error!("missing profile debug assertions");
const _: [(); 5] = [(); (env!("BUILD_VALUE").as_bytes()[0] - b'0') as usize];
fn dead() -> u32 { 99 }
fn kept() -> u32 { app_main::value() + maker::number!() }
fn main() { println!("{}:{}:{}", env!("CARGO_PKG_NAME"), kept(), file!()); }
#[cfg(test)] mod tests { #[test] fn check() { assert_eq!(super::dead(), 99); } }
"#,
    );
    project
}

#[test]
fn cargo_conditions_dependencies_and_build_environment_reach_the_normal_reduction() {
    let project = fixture();
    let source = project.read("app/src/main.rs");
    let library = project.read("app/src/lib.rs");
    let dependency = project.read("helper/src/lib.rs");
    let flags = ["--features", "selected", "--profile", "submission"];
    let built = success(
        project
            .cargo()
            .args([
                "build",
                "--message-format=json",
                "--offline",
                "--bin",
                "app-main",
            ])
            .args(flags)
            .output()
            .unwrap(),
    );
    success(project.reduce().args(flags).output().unwrap());
    let reduced = project.read("app/src/main.rs");
    assert_ne!(reduced, source);
    assert!(!reduced.contains("fn dead"));
    assert!(!reduced.contains("mod tests"));
    assert!(reduced.contains("fn kept"));
    assert_eq!(project.read("app/src/lib.rs"), library);
    assert_eq!(project.read("helper/src/lib.rs"), dependency);
    success(
        project
            .cargo()
            .args(["build", "--offline", "--bin", "app-main"])
            .args(flags)
            .output()
            .unwrap(),
    );
    let binary = project
        .0
        .path()
        .join("target/submission")
        .join(format!("app-main{}", std::env::consts::EXE_SUFFIX));
    let output = success(Command::new(binary).output().unwrap());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().replace('\\', "/"),
        "app-main:7:app/src/main.rs\n"
    );
    let modified = fs::metadata(project.0.path().join("app/src/main.rs"))
        .unwrap()
        .modified()
        .unwrap();
    let library_artifact = built
        .stdout
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<serde_json::Value>(line).ok())
        .filter(|message| {
            message["reason"] == "compiler-artifact" && message["target"]["name"] == "helper"
        })
        .flat_map(|message| {
            message["filenames"]
                .as_array()
                .unwrap()
                .iter()
                .map(|path| path.as_str().unwrap().to_owned())
                .collect::<Vec<_>>()
        })
        .find(|path| path.ends_with(".rlib"))
        .unwrap();
    success(project.reduce().args(flags).output().unwrap());
    let dependency_modified = fs::metadata(&library_artifact).unwrap().modified().unwrap();
    success(project.reduce().args(flags).output().unwrap());
    assert_eq!(project.read("app/src/main.rs"), reduced);
    assert_eq!(
        fs::metadata(project.0.path().join("app/src/main.rs"))
            .unwrap()
            .modified()
            .unwrap(),
        modified
    );
    assert_eq!(
        fs::metadata(library_artifact).unwrap().modified().unwrap(),
        dependency_modified
    );
}

#[test]
fn ambiguous_or_invalid_cargo_selections_preserve_every_source() {
    let project = fixture();
    project.write("app/src/bin/other.rs", "fn dead() {}\nfn main() {}\n");
    let first = project.read("app/src/main.rs");
    let second = project.read("app/src/bin/other.rs");
    for flags in [
        vec![],
        vec!["--bin", "missing"],
        vec!["--profile", "test"],
        vec!["--bin", "app-main"],
    ] {
        assert!(
            !project
                .reduce()
                .args(flags)
                .output()
                .unwrap()
                .status
                .success()
        );
        assert_eq!(project.read("app/src/main.rs"), first);
        assert_eq!(project.read("app/src/bin/other.rs"), second);
    }
    success(
        project
            .reduce()
            .args(["-p", "app-main", "--bin", "other"])
            .output()
            .unwrap(),
    );
    assert_eq!(project.read("app/src/main.rs"), first);
    assert!(!project.read("app/src/bin/other.rs").contains("fn dead"));
}

#[test]
fn failed_original_compilation_never_updates_the_selected_file() {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        "[package]\nname='broken'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    let source = "fn dead() {}\nfn main() { let _: u8 = false; }\n";
    project.write("src/main.rs", source);
    let output = project.reduce().output().unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("mismatched types"));
    assert_eq!(project.read("src/main.rs"), source);
}

#[test]
fn explicit_target_directory_is_used_and_multiple_targets_are_rejected() {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        "[package]\nname='target-options'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    let source = "fn dead() {}\nfn main() {}\n";
    project.write("src/main.rs", source);
    project.write("target", "ordinary file");
    assert!(
        !project
            .reduce()
            .args([
                "--target-dir",
                "build",
                "--target",
                "wasm32-unknown-unknown",
                "--target",
                "x86_64-unknown-linux-gnu"
            ])
            .output()
            .unwrap()
            .status
            .success()
    );
    assert_eq!(project.read("src/main.rs"), source);
    success(
        project
            .reduce()
            .args(["--target-dir", "build"])
            .output()
            .unwrap(),
    );
    assert!(!project.read("src/main.rs").contains("fn dead"));
    assert_eq!(project.read("target"), "ordinary file");
}

#[test]
fn compiler_queries_are_identical_to_the_configured_rustc() {
    let project = Project::new();
    for arguments in [
        vec!["-vV"],
        vec!["--help"],
        vec!["-Whelp"],
        vec!["--print", "sysroot"],
    ] {
        let expected = project
            .command(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .args(&arguments)
            .output()
            .unwrap();
        let actual = project
            .command(env!("CARGO_BIN_EXE_rust-item-dependencies"))
            .args(&arguments)
            .env("RUST_ITEM_DEPENDENCIES_ADAPTER_CONFIG", "unused-for-query")
            .output()
            .unwrap();
        assert_eq!(
            actual.status.code(),
            expected.status.code(),
            "{arguments:?}"
        );
        assert_eq!(actual.stdout, expected.stdout, "{arguments:?}");
        assert_eq!(actual.stderr, expected.stderr, "{arguments:?}");
    }
}

#[test]
fn cargo_and_wrapper_resources_remain_alive_through_macro_execution() {
    let project = fixture();
    project.write("maker/src/lib.rs", r#"
use proc_macro::TokenStream;
#[proc_macro] pub fn select(_: TokenStream) -> TokenStream {
    let live = std::process::Command::new(std::env::var_os("RUSTC").unwrap())
        .arg("--version").output().unwrap().status.success()
        && std::env::var_os("CARGO_MAKEFLAGS").is_some()
        && std::env::var_os("WRAPPER_RESOURCE").is_some_and(|path| std::fs::read_to_string(path).is_ok_and(|value| value == "live"));
    if live { "kept_with_resources" } else { "kept_without_resources" }.parse().unwrap()
}
"#);
    project.write("app/src/main.rs", "fn kept_with_resources() -> u32 { 7 }\nfn kept_without_resources() -> u32 { 9 }\nfn main() { println!(\"{}\", maker::select!()()); }\n");
    project.write(
        "target/resource_wrapper.rs",
        r#"
use std::{env, fs, io::{self, Write}, process::{Command, exit}};
fn main() {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let resource = env::current_dir().unwrap().join("target/wrapper-resource");
    let target = env::var("CARGO_BIN_NAME").as_deref() == Ok("app-main");
    let mut command = Command::new(&args[0]);
    command.args(&args[1..]);
    if target {
        assert!(Command::new(&args[0]).args(["--print", "sysroot"]).output().unwrap().status.success());
        fs::write(&resource, "live").unwrap(); command.env("WRAPPER_RESOURCE", &resource);
    }
    let output = command.output().unwrap();
    if target { fs::remove_file(&resource).unwrap(); }
    io::stdout().write_all(&output.stdout).unwrap();
    io::stderr().write_all(&output.stderr).unwrap();
    exit(output.status.code().unwrap_or(1));
}
"#,
    );
    let wrapper = project
        .0
        .path()
        .join("target")
        .join(format!("resource-wrapper{}", std::env::consts::EXE_SUFFIX));
    success(
        project
            .command(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .arg("target/resource_wrapper.rs")
            .arg("-o")
            .arg(&wrapper)
            .output()
            .unwrap(),
    );
    let build = || {
        project
            .cargo()
            .args(["build", "--offline", "--bin", "app-main"])
            .env("RUSTC_WRAPPER", &wrapper)
            .output()
            .unwrap()
    };
    success(build());
    success(
        project
            .reduce()
            .env("RUSTC_WRAPPER", &wrapper)
            .output()
            .unwrap(),
    );
    let reduced = project.read("app/src/main.rs");
    assert!(reduced.contains("fn kept_with_resources"));
    assert!(!reduced.contains("fn kept_without_resources"));
    assert!(!project.0.path().join("target/wrapper-resource").exists());
    success(build());
    let binary = project
        .0
        .path()
        .join("target/debug")
        .join(format!("app-main{}", std::env::consts::EXE_SUFFIX));
    assert_eq!(
        success(Command::new(binary).output().unwrap()).stdout,
        b"7\n"
    );
    success(
        project
            .reduce()
            .env("RUSTC_WRAPPER", &wrapper)
            .output()
            .unwrap(),
    );
    assert_eq!(project.read("app/src/main.rs"), reduced);
}

#[test]
fn cargo_build_scripts_cannot_make_the_parent_overwrite_a_changed_source() {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        "[package]\nname='changed-source'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    project.write("src/main.rs", "fn dead() {}\nfn main() {}\n");
    let changed = "fn changed_while_building() {}\nfn main() {}\n";
    project.write(
        "build.rs",
        &format!("fn main() {{ std::fs::write(\"src/main.rs\", {changed:?}).unwrap(); }}\n"),
    );
    assert!(!project.reduce().output().unwrap().status.success());
    assert_eq!(project.read("src/main.rs"), changed);
}

#[cfg(unix)]
#[test]
fn cargo_selected_symlinks_are_rejected_before_build_scripts_run() {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        "[package]\nname='symlink-source'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    let original = "fn dead() {}\nfn main() {}\n";
    project.write("real.rs", original);
    project.write(
        "build.rs",
        "fn main() { std::fs::write(\"build-ran\", \"\").unwrap(); }\n",
    );
    fs::create_dir_all(project.0.path().join("src")).unwrap();
    std::os::unix::fs::symlink("../real.rs", project.0.path().join("src/main.rs")).unwrap();
    assert!(!project.reduce().output().unwrap().status.success());
    assert_eq!(project.read("real.rs"), original);
    assert!(!project.0.path().join("build-ran").exists());
}

#[cfg(unix)]
#[test]
fn the_compiler_environment_preserves_non_unicode_values_for_proc_macros() {
    use std::os::unix::ffi::OsStringExt;
    let project = fixture();
    project.write(
        "maker/src/lib.rs",
        r#"
use proc_macro::TokenStream;
#[proc_macro] pub fn number(_: TokenStream) -> TokenStream {
    use std::os::unix::ffi::OsStrExt;
    let value = std::env::var_os("RID_NON_UNICODE").unwrap();
    assert_eq!(value.as_os_str().as_bytes(), &[255]);
    "3u32".parse().unwrap()
}
"#,
    );
    success(
        project
            .reduce()
            .args(["--features", "selected", "--profile", "submission"])
            .env("RID_NON_UNICODE", std::ffi::OsString::from_vec(vec![255]))
            .output()
            .unwrap(),
    );
    assert!(!project.read("app/src/main.rs").contains("fn dead"));
}

#[test]
fn wrappers_and_transient_response_files_keep_the_actual_compiler_conditions() {
    let project = Project::new();
    project.write(
        "Cargo.toml",
        "[package]\nname='wrapped'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    let source = r#"
#[cfg(not(outer))] compile_error!("lost outer wrapper");
#[cfg(not(inner))] compile_error!("lost workspace wrapper");
const _: [(); 3] = [(); (env!("WRAPPER_VALUE").as_bytes()[0] - b'0') as usize];
fn dead() {}
fn main() {}
"#;
    project.write("src/main.rs", source);
    project.write("target/wrapper.rs", r#"
use std::{env, fs, process::{Command, exit}};
fn main() {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let program = &args[0];
    let mut args = args[1..].to_vec();
    let target = args.iter().any(|arg| arg == "--rust-item-dependencies-reduce-bin");
    if target && env::var("WRAPPER_MODE").as_deref() == Ok("skip") { return; }
    if target && env::var("WRAPPER_MODE").as_deref() == Ok("fail") { exit(42); }
    let mut command = Command::new(program);
    let mut response = None;
    if target {
        let executable = env::current_exe().unwrap();
        let name = executable.file_stem().unwrap().to_str().unwrap();
        args.push(format!("--cfg={name}").into());
        args.push(format!("--check-cfg=cfg({name})").into());
        if name == "inner" {
            command.env("WRAPPER_VALUE", "3");
            let path = env::current_dir().unwrap().join("target/transient-arguments");
            fs::write(&path, args.iter().map(|arg| arg.to_str().unwrap()).collect::<Vec<_>>().join("\n")).unwrap();
            command.arg(format!("@{}", path.display()));
            response = Some(path);
        } else { command.args(args); }
    } else { command.args(args); }
    let status = command.status().unwrap();
    if let Some(path) = response { fs::remove_file(path).unwrap(); }
    exit(status.code().unwrap_or(1));
}
"#);
    let outer = project
        .0
        .path()
        .join("target")
        .join(format!("outer{}", std::env::consts::EXE_SUFFIX));
    let inner = project
        .0
        .path()
        .join("target")
        .join(format!("inner{}", std::env::consts::EXE_SUFFIX));
    success(
        project
            .command(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .arg("target/wrapper.rs")
            .arg("-o")
            .arg(&outer)
            .output()
            .unwrap(),
    );
    fs::copy(&outer, &inner).unwrap();
    let reduce = |mode| {
        project
            .reduce()
            .env("RUSTC_WRAPPER", &outer)
            .env("RUSTC_WORKSPACE_WRAPPER", &inner)
            .env("WRAPPER_MODE", mode)
            .output()
            .unwrap()
    };
    for mode in ["skip", "fail"] {
        assert!(!reduce(mode).status.success());
        assert_eq!(project.read("src/main.rs"), source);
    }
    success(reduce("run"));
    assert!(!project.read("src/main.rs").contains("fn dead"));
    assert!(!project.0.path().join("target/transient-arguments").exists());
    let reduced = project.read("src/main.rs");
    success(reduce("run"));
    assert_eq!(project.read("src/main.rs"), reduced);
}
