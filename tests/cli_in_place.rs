#![cfg(rust_item_dependencies_patched)]

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn work() -> tempfile::TempDir {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tests");
    fs::create_dir_all(&root).unwrap();
    tempfile::Builder::new()
        .prefix("cli-in-place-")
        .tempdir_in(root)
        .unwrap()
}

fn reduce(path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rust-item-dependencies"))
        .arg(path)
        .output()
        .unwrap()
}

fn success(output: Output) -> Output {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn compile(path: &Path, binary: &Path) {
    success(
        Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .arg("--edition=2024")
            .arg(path)
            .arg("-o")
            .arg(binary)
            .output()
            .unwrap(),
    );
}

#[test]
fn installed_launcher_updates_relative_inputs_from_an_independent_directory() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    let install = work();
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    success(
        Command::new(&cargo)
            .current_dir(repository)
            .args([
                "install",
                "--offline",
                "--locked",
                "--path",
                "tools",
                "--root",
            ])
            .arg(install.path())
            .arg("--target-dir")
            .arg(repository.join("target/rid-tool-install"))
            .env_remove("RUSTC")
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .output()
            .unwrap(),
    );

    // Cargo searches ancestor directories for aliases. Keep this fixture
    // outside the checkout so it must find the installed subcommand.
    let parent = std::env::temp_dir().join("rust-item-dependencies/target");
    fs::create_dir_all(&parent).unwrap();
    let project = tempfile::Builder::new()
        .prefix("cargo-rid-external-")
        .tempdir_in(parent)
        .unwrap();
    let source = "fn dead() {}\nfn main() { println!(\"{}\", file!()); }\n";
    let input = project.path().join("input.rs");
    fs::write(&input, source).unwrap();
    let inherited_path = std::env::var_os("PATH").unwrap();
    let path = std::env::join_paths(
        std::iter::once(install.path().join("bin")).chain(std::env::split_paths(&inherited_path)),
    )
    .unwrap();
    let reduce = || {
        Command::new(&cargo)
            .current_dir(project.path())
            .args(["rid", "input.rs"])
            .env("PATH", &path)
            .env("RUSTFLAGS", "--must-not-apply-to-the-reducer-build")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env("CARGO_BUILD_TARGET", "wasm32-unknown-unknown")
            .output()
            .unwrap()
    };
    success(reduce());
    let reduced = fs::read_to_string(&input).unwrap();
    assert!(!reduced.contains("fn dead"));
    assert!(reduced.contains("fn main"));
    let modified = fs::metadata(&input).unwrap().modified().unwrap();
    success(reduce());
    assert_eq!(fs::read_to_string(&input).unwrap(), reduced);
    assert_eq!(fs::metadata(&input).unwrap().modified().unwrap(), modified);

    let binary = project
        .path()
        .join(format!("program{}", std::env::consts::EXE_SUFFIX));
    success(
        Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .current_dir(project.path())
            .args(["--edition=2024", "input.rs", "-o"])
            .arg(&binary)
            .output()
            .unwrap(),
    );
    assert_eq!(
        success(Command::new(binary).output().unwrap()).stdout,
        b"input.rs\n"
    );

    fs::write(&input, "fn main() { let _: u8 = false; }\n").unwrap();
    let original = fs::read(&input).unwrap();
    assert!(!reduce().status.success());
    assert_eq!(fs::read(&input).unwrap(), original);

    fs::create_dir_all(project.path().join("src")).unwrap();
    fs::create_dir_all(project.path().join("helper/src")).unwrap();
    fs::create_dir_all(project.path().join(".cargo")).unwrap();
    fs::write(project.path().join("Cargo.toml"), "[package]\nname='cross-project'\nversion='0.1.0'\nedition='2024'\n[dependencies]\nhelper={path='helper'}\n[workspace]\n").unwrap();
    fs::write(
        project.path().join("helper/Cargo.toml"),
        "[package]\nname='helper'\nversion='0.1.0'\nedition='2024'\n",
    )
    .unwrap();
    fs::write(
        project.path().join("helper/src/lib.rs"),
        "pub fn value() -> usize { vec![1u8, 2, 3].len() }\n",
    )
    .unwrap();
    fs::write(
        project.path().join("build.rs"),
        "fn main() { println!(\"cargo::rustc-env=HOST_BUILD_VALUE=5\"); }\n",
    )
    .unwrap();
    fs::write(
        project.path().join(".cargo/config.toml"),
        "[build]\ntarget='wasm32-unknown-unknown'\n",
    )
    .unwrap();
    fs::write(
        project.path().join("src/main.rs"),
        r#"
#[cfg(not(target_arch = "wasm32"))] compile_error!("lost configured target");
const _: [(); 4] = [(); core::mem::size_of::<usize>()];
const _: [(); 5] = [(); (env!("HOST_BUILD_VALUE").as_bytes()[0] - b'0') as usize];
fn dead() {}
fn main() { core::hint::black_box(helper::value()); }
"#,
    )
    .unwrap();
    let reduce_project = || {
        Command::new(&cargo)
            .current_dir(project.path())
            .args(["rid", "--offline"])
            .env("PATH", &path)
            .env_remove("RUSTC")
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env_remove("CARGO_TARGET_DIR")
            .env_remove("CARGO_BUILD_TARGET")
            .output()
            .unwrap()
    };
    success(reduce_project());
    let reduced = fs::read_to_string(project.path().join("src/main.rs")).unwrap();
    assert!(!reduced.contains("fn dead"));
    assert!(reduced.contains("helper::value"));
    success(reduce_project());
    assert_eq!(
        fs::read_to_string(project.path().join("src/main.rs")).unwrap(),
        reduced
    );
}

#[test]
fn updates_the_input_compiles_and_reaches_a_fixed_point() {
    let work = work();
    let path = work.path().join("input.rs");
    let source = "fn unused() {}\nfn value() -> u32 { 3 }\nfn main() { println!(\"{}\", value()); }\n#[cfg(test)] mod tests { #[test] fn value_is_three() { assert_eq!(super::value(), 3); } }\n";
    fs::write(&path, source).unwrap();
    let tests = work
        .path()
        .join(format!("tests{}", std::env::consts::EXE_SUFFIX));
    success(
        Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .arg("--edition=2024")
            .arg("--test")
            .arg(&path)
            .arg("-o")
            .arg(&tests)
            .output()
            .unwrap(),
    );
    let tested = success(Command::new(&tests).output().unwrap());
    assert!(String::from_utf8_lossy(&tested.stdout).contains("1 passed"));

    success(
        Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .arg("rid")
            .arg(&path)
            .output()
            .unwrap(),
    );
    let reduced = fs::read_to_string(&path).unwrap();
    assert!(!reduced.contains("unused"));
    assert!(!reduced.contains("mod tests"));
    assert!(reduced.contains("fn value()"));
    assert!(reduced.contains("fn main()"));
    let binary = work
        .path()
        .join(format!("program{}", std::env::consts::EXE_SUFFIX));
    compile(&path, &binary);
    assert_eq!(
        success(Command::new(binary).output().unwrap()).stdout,
        b"3\n"
    );

    let modified = fs::metadata(&path).unwrap().modified().unwrap();
    assert!(success(reduce(&path)).stdout.is_empty());
    assert_eq!(fs::read_to_string(&path).unwrap(), reduced);
    assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
    assert!(!fs::read_dir(work.path()).unwrap().any(|entry| {
        entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".rid-")
    }));
}

#[test]
fn uses_the_same_filename_before_and_after_updating() {
    let work = work();
    let path = work.path().join("source.rs");
    fs::write(&path, include_str!("fixtures/compiler/source_filename.rs")).unwrap();
    success(reduce(&path));
    let reduced = fs::read_to_string(&path).unwrap();
    assert!(reduced.contains("impl Pick for Flag<false>"));
    assert!(!reduced.contains("impl Pick for Flag<true>"));
    let binary = work
        .path()
        .join(format!("program{}", std::env::consts::EXE_SUFFIX));
    compile(&path, &binary);
    assert_eq!(
        success(Command::new(binary).output().unwrap()).stdout,
        format!("2 {}\n", path.display()).as_bytes()
    );
    success(reduce(&path));
    assert_eq!(fs::read_to_string(&path).unwrap(), reduced);
}

#[test]
fn rejected_reductions_leave_the_original_bytes_unchanged() {
    let cases = [
        (
            "fn main() { let _: u32 = false; }\n",
            "original source did not compile",
        ),
        (
            "fn dead() {\n    let _ = 0;\n}\nfn main() {\n    let _: [(); 5] = [(); line!() as usize];\n}\n",
            "reduced source did not compile",
        ),
        (
            concat!(
                "trait Pick { fn value() -> u32; }\n",
                "struct Line<const N: u32>;\n",
                "macro_rules! impls { () => { impl Pick for Line<6> { fn value()->u32{6} } impl Pick for Line<8> { fn value()->u32{8} } }; }\n",
                "impls!();\n",
                "fn dead() {\n    let _ = 0;\n}\n",
                "fn main() { let _ = (<Line<6> as Pick>::value, <Line<8> as Pick>::value); let _ = <Line<{ line!() }> as Pick>::value(); }\n",
            ),
            "compiler decisions differ",
        ),
    ];
    for (source, message) in cases {
        let work = work();
        let path = work.path().join("input.rs");
        fs::write(&path, source).unwrap();
        let output = reduce(&path);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(message), "{stderr}");
        assert_eq!(fs::read_to_string(&path).unwrap(), source);
        assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
    }
}
