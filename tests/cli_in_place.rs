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
