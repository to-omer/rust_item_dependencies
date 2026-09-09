use super::*;

fn work() -> tempfile::TempDir {
    let parent = Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/container-unit-tests");
    fs::create_dir_all(&parent).unwrap();
    tempfile::tempdir_in(parent).unwrap()
}

#[test]
fn maps_container_paths_without_following_the_final_link() {
    let work = work();
    let root = fs::canonicalize(work.path()).unwrap();
    fs::create_dir(root.join("src")).unwrap();
    for path in [
        "src/main.rs",
        "/workspace/src/main.rs",
        "./src/../src/main.rs",
    ] {
        assert_eq!(
            host_path(&root, path).unwrap(),
            root.join(path.strip_prefix("/workspace/").unwrap_or(path))
        );
    }
    for path in [
        "../outside.rs",
        "/tmp/input.rs",
        "/workspace/../outside.rs",
        "/workspace",
    ] {
        assert!(host_path(&root, path).is_err(), "{path}");
    }
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("src/main.rs", root.join("link.rs")).unwrap();
        let mapped = host_path(&root, "link.rs").unwrap();
        assert!(fs::symlink_metadata(mapped).unwrap().is_symlink());
        std::os::unix::fs::symlink(root.parent().unwrap(), root.join("outside")).unwrap();
        assert!(host_path(&root, "outside/input.rs").is_err());
    }
    #[cfg(windows)]
    for path in [
        "C:/input.rs",
        r"src\main.rs",
        "input.rs:stream",
        "input.rs.",
        "input.rs ",
    ] {
        assert!(host_path(&root, path).is_err(), "{path}");
    }
}

#[cfg(unix)]
#[test]
fn detects_a_parent_link_replaced_after_the_source_was_read() {
    let work = work();
    let root = fs::canonicalize(work.path()).unwrap();
    for directory in ["before", "after"] {
        fs::create_dir(root.join(directory)).unwrap();
        fs::write(root.join(directory).join("input.rs"), "fn main() {}\n").unwrap();
    }
    std::os::unix::fs::symlink("before", root.join("source")).unwrap();
    let input = host_path(&root, "source/input.rs").unwrap();
    let source = SourceFile::read(&input).unwrap();
    fs::remove_file(root.join("source")).unwrap();
    std::os::unix::fs::symlink("after", root.join("source")).unwrap();
    assert!(source.replace("fn main() { panic!() }\n").is_err());
    for directory in ["before", "after"] {
        assert_eq!(
            fs::read_to_string(root.join(directory).join("input.rs")).unwrap(),
            "fn main() {}\n"
        );
    }
}

#[test]
fn refuses_a_result_for_changed_source_or_a_different_format() {
    let work = work();
    let root = fs::canonicalize(work.path()).unwrap();
    fs::write(root.join("input.rs"), "fn main() {}\n").unwrap();
    for (version, original) in [(VERSION, "old"), (VERSION + 1, "fn main() {}\n")] {
        let result = ContainerResult {
            version,
            input: "input.rs".to_owned(),
            output: None,
            original: original.to_owned(),
            reduced: "replacement".to_owned(),
        };
        assert!(apply_result(&root, result).is_err());
        assert_eq!(
            fs::read_to_string(root.join("input.rs")).unwrap(),
            "fn main() {}\n"
        );
    }
}

#[test]
fn separate_output_accepts_readonly_input_and_preserves_existing_output() {
    let work = work();
    let root = fs::canonicalize(work.path()).unwrap();
    let input = root.join("input.rs");
    fs::write(&input, "original").unwrap();
    let writable = fs::metadata(&input).unwrap().permissions();
    let mut readonly = writable.clone();
    readonly.set_readonly(true);
    fs::set_permissions(&input, readonly).unwrap();
    let result = || ContainerResult {
        version: VERSION,
        input: "input.rs".to_owned(),
        output: Some("output.rs".to_owned()),
        original: "original".to_owned(),
        reduced: "reduced".to_owned(),
    };
    apply_result(&root, result()).unwrap();
    assert_eq!(fs::read_to_string(&input).unwrap(), "original");
    assert_eq!(
        fs::read_to_string(root.join("output.rs")).unwrap(),
        "reduced"
    );
    assert!(apply_result(&root, result()).is_err());
    assert_eq!(
        fs::read_to_string(root.join("output.rs")).unwrap(),
        "reduced"
    );
    fs::set_permissions(&input, writable).unwrap();
}
