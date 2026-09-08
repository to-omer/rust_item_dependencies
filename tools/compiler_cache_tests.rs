use std::collections::BTreeMap;
use std::time::{Instant, SystemTime};

use super::*;

fn compiler_artifacts(host_build: &Path) -> BTreeMap<PathBuf, (u64, SystemTime)> {
    let mut artifacts = BTreeMap::new();
    for directory in ["stage1-rustc", "stage2-rustc", "stage1-std"] {
        let root = host_build.join(directory);
        let mut libraries = 0;
        for entry in walkdir::WalkDir::new(&root) {
            let entry = entry.unwrap();
            if !entry.file_type().is_file() {
                continue;
            }
            let path = entry.path();
            libraries += usize::from(path.extension().is_some_and(|ext| ext == "rlib"));
            let metadata = entry.metadata().unwrap();
            artifacts.insert(
                path.strip_prefix(host_build).unwrap().to_owned(),
                (metadata.len(), metadata.modified().unwrap()),
            );
        }
        assert!(libraries > 0, "no compiled libraries in {}", root.display());
    }
    artifacts
}

#[test]
#[ignore = "prepares the patched compiler; CI runs this after restoring its cache"]
fn cargo_rid_preserves_restored_compiler_artifacts() {
    let cache_hit = match env::var("RUST_ITEM_DEPENDENCIES_TEST_COMPILER_CACHE_HIT").as_deref() {
        Ok("true") => true,
        Ok("false") => false,
        _ => panic!("set RUST_ITEM_DEPENDENCIES_TEST_COMPILER_CACHE_HIT to true or false"),
    };
    let repository_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let host = compiler_host(Path::new("rustc")).unwrap();
    let host_build = repository_root.join("target/rid/rustc/build").join(host);
    let before = cache_hit.then(|| compiler_artifacts(&host_build));
    let output = TestDirectory::new();
    let reduced = output.path().join("reduced.rs");
    let start = Instant::now();

    run_command(
        Command::new(env!("CARGO"))
            .current_dir(repository_root)
            .args(["rid", "tests/fixtures/compiler/driver_smoke.rs", "-o"])
            .arg(&reduced),
        "reduce the compiler smoke fixture through cargo rid",
    )
    .unwrap();
    assert!(
        reduced.is_file(),
        "cargo rid did not produce reduced source"
    );
    println!(
        "cargo rid preparation and reduction completed in {:?}",
        start.elapsed()
    );

    if let Some(before) = before {
        let after = compiler_artifacts(&host_build);
        assert_eq!(
            after.len(),
            before.len(),
            "cached compiler file set changed"
        );
        for (path, state) in &before {
            assert_eq!(
                after.get(path),
                Some(state),
                "cached artifact changed: {}",
                path.display()
            );
        }
        println!(
            "Reused {} compiler and standard-library files without updates",
            before.len()
        );
    } else {
        println!("Cache miss: completed compiler preparation through cargo rid");
    }
}
