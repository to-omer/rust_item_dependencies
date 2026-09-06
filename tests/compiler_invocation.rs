#![cfg(rust_item_dependencies_patched)]
#![feature(rustc_private)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use rust_item_dependencies::{AnalysisError, CompilerInvocation};

struct Fixture {
    directory: tempfile::TempDir,
    source: String,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parent = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tests");
        fs::create_dir_all(&parent).unwrap();
        let directory = tempfile::Builder::new()
            .prefix("compiler-invocation-")
            .tempdir_in(parent)
            .unwrap();
        fs::write(directory.path().join("main.rs"), source).unwrap();
        Self {
            directory,
            source: source.to_owned(),
        }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.directory.path().join(name)
    }

    fn arguments(&self) -> Vec<String> {
        vec![
            self.path("main.rs").display().to_string(),
            "--edition=2024".into(),
            "--crate-type=bin".into(),
            "--crate-name=program".into(),
        ]
    }

    fn library(&self, emit: &str, identity: &str, output: &str) {
        fs::write(self.path("leaf.rs"), "pub fn value() -> u8 { 1 }\n").unwrap();
        success(
            Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
                .arg(self.path("leaf.rs"))
                .args([
                    "--crate-type=rlib",
                    "--crate-name=leaf",
                    "--emit",
                    emit,
                    "-C",
                ])
                .arg(format!("metadata={identity}"))
                .arg("-o")
                .arg(self.path(output))
                .output()
                .unwrap(),
        );
    }

    fn original(&self, arguments: &[String]) -> Output {
        Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
            .args(arguments)
            .arg("-o")
            .arg(self.path("program"))
            .output()
            .unwrap()
    }

    fn reduce(&self, arguments: Vec<String>) -> Result<String, AnalysisError> {
        CompilerInvocation::new(&self.source, arguments)
            .reduce()
            .map(|result| result.reduced_source().to_owned())
    }
}

fn success(output: Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn preserving_codegen_checks_rejects_conflicting_rlib_and_rmeta() {
    let fixture = Fixture::new(
        "extern crate leaf;\nfn dead() {}\nfn main() { assert_eq!(leaf::value(), 1); }\n",
    );
    fixture.library("metadata", "metadata", "libleaf.rmeta");
    fixture.library("link", "codegen", "libleaf.rlib");
    let mut arguments = fixture.arguments();
    arguments.extend([
        "-L".into(),
        format!("crate={}", fixture.directory.path().display()),
    ]);
    let original = fixture.original(&arguments);
    assert!(!original.status.success());
    assert!(String::from_utf8_lossy(&original.stderr).contains("E0464"));
    assert!(matches!(
        fixture.reduce(arguments.clone()),
        Err(AnalysisError::OriginalCompilationFailed(_))
    ));

    fixture.library("metadata,link", "paired", "libleaf.rlib");
    success(fixture.original(&arguments));
    let reduced = fixture.reduce(arguments.clone()).unwrap();
    assert!(!reduced.contains("fn dead"));
    assert!(reduced.contains("leaf::value"));
    fs::write(fixture.path("main.rs"), &reduced).unwrap();
    success(fixture.original(&arguments));
    assert_eq!(
        CompilerInvocation::new(&reduced, arguments)
            .reduce()
            .unwrap()
            .reduced_source(),
        reduced
    );
}

#[test]
fn search_kind_and_extern_prelude_are_not_widened() {
    let fixture = Fixture::new("extern crate leaf; fn main() { leaf::value(); }\n");
    fixture.library("link", "leaf", "libleaf.rlib");
    let mut arguments = fixture.arguments();
    arguments.extend([
        "-L".into(),
        format!("dependency={}", fixture.directory.path().display()),
    ]);
    assert!(!fixture.original(&arguments).status.success());
    assert!(fixture.reduce(arguments).is_err());

    let source = "fn main() { leaf::value(); }\n";
    fs::write(fixture.path("main.rs"), source).unwrap();
    let mut arguments = fixture.arguments();
    arguments.extend([
        "-Zunstable-options".into(),
        "--extern".into(),
        format!("noprelude:leaf={}", fixture.path("libleaf.rlib").display()),
    ]);
    assert!(!fixture.original(&arguments).status.success());
    assert!(CompilerInvocation::new(source, arguments).reduce().is_err());
}

#[test]
fn source_interface_candidates_are_reported_instead_of_discarded() {
    let fixture = Fixture::new("extern crate leaf; fn main() { leaf::value(); }\n");
    fixture.library("link", "leaf", "libleaf.rlib");
    fs::write(
        fixture.path("libleaf.rs"),
        "#![crate_type=\"rlib\"] pub fn value() -> u8 { 3 }\n",
    )
    .unwrap();
    let mut arguments = fixture.arguments();
    arguments.extend([
        "-L".into(),
        format!("crate={}", fixture.directory.path().display()),
    ]);
    assert!(!fixture.original(&arguments).status.success());
    assert!(
        fixture
            .reduce(arguments)
            .unwrap_err()
            .to_string()
            .contains("source dylib interfaces")
    );
}

#[cfg(unix)]
#[test]
fn canonical_candidate_aliases_are_not_changed_into_independent_files() {
    let fixture = Fixture::new("extern crate leaf; fn main() { leaf::value(); }\n");
    fixture.library("metadata", "leaf", "libleaf.rmeta");
    std::os::unix::fs::symlink("libleaf.rmeta", fixture.path("libleaf.rlib")).unwrap();
    let mut arguments = fixture.arguments();
    arguments.extend([
        "-L".into(),
        format!("crate={}", fixture.directory.path().display()),
    ]);
    assert!(!fixture.original(&arguments).status.success());
    assert!(
        fixture
            .reduce(arguments)
            .unwrap_err()
            .to_string()
            .contains("aliased compiler artifact")
    );
}

#[test]
fn expanded_response_tokens_are_not_expanded_again() {
    let fixture = Fixture::new("fn dead() {}\nfn main() {}\n");
    fs::write(fixture.path("cfg"), "enabled\n").unwrap();
    let mut arguments = fixture.arguments();
    arguments.extend([
        "--cfg".into(),
        format!("@{}", fixture.path("cfg").display()),
    ]);
    // A response file contains literal tokens after its one permitted expansion.
    let response = arguments.join("\n");
    fs::write(fixture.path("arguments"), response).unwrap();
    assert!(
        !fixture
            .original(&[format!("@{}", fixture.path("arguments").display())])
            .status
            .success()
    );
    assert!(fixture.reduce(arguments).is_err());
}
