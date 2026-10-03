use super::*;

struct Checkout {
    directory: TestDirectory,
    source: PathBuf,
    previous: String,
    patched: String,
}

impl Checkout {
    fn new(change_base: bool) -> Self {
        let directory = TestDirectory::new();
        let source = directory.path().join("rust-source");
        fs::create_dir_all(&source).unwrap();
        git(&source, &["init", "--quiet"]);
        git(&source, &["config", "core.autocrlf", "false"]);
        git(&source, &["remote", "add", "origin", RUST_REPOSITORY]);
        fs::write(
            source.join(".gitignore"),
            "/build/\n/bootstrap.toml\n/reserved\n",
        )
        .unwrap();
        fs::write(source.join("source.rs"), "pub fn answer() -> u32 { 1 }\n").unwrap();
        git(&source, &["add", "."]);
        git(&source, &["commit", "--quiet", "-m", "original base"]);
        let base = git_output(&source, &["rev-parse", "HEAD"]).unwrap();
        fs::write(source.join("source.rs"), "pub fn answer() -> u32 { 7 }\n").unwrap();
        git(&source, &["commit", "--quiet", "-am", "previous patches"]);
        let previous = git_output(&source, &["rev-parse", "HEAD"]).unwrap();
        git(&source, &["checkout", "--quiet", "--detach", &base]);
        if change_base {
            fs::write(source.join("source.rs"), "pub fn answer() -> u32 { 2 }\n").unwrap();
            git(&source, &["commit", "--quiet", "-am", "new base"]);
        }
        let base = git_output(&source, &["rev-parse", "HEAD"]).unwrap();
        fs::write(source.join("source.rs"), "pub fn answer() -> u32 { 42 }\n").unwrap();
        git(&source, &["commit", "--quiet", "-am", "current patches"]);
        let patched = git_output(&source, &["rev-parse", "HEAD"]).unwrap();
        let patch = git_output(
            &source,
            &["format-patch", "--stdout", "--no-signature", "-1"],
        )
        .unwrap();
        let patches = directory.path().join("rustc-patches");
        fs::create_dir(&patches).unwrap();
        fs::write(patches.join("base-revision"), format!("{base}\n")).unwrap();
        fs::write(patches.join("patched-revision"), format!("{patched}\n")).unwrap();
        fs::write(patches.join("queue-digest"), "new digest\n").unwrap();
        fs::write(patches.join("series"), "current.patch\n").unwrap();
        fs::write(patches.join("current.patch"), format!("{patch}\n")).unwrap();
        git(&source, &["checkout", "--quiet", "--detach", &previous]);
        fs::create_dir(source.join("build")).unwrap();
        fs::write(source.join("build/artifact"), "previous compiler").unwrap();
        fs::write(
            source.join("build").join(COMPILER_BUILD_IDENTITY_FILE),
            format!("{previous}\nprevious digest\n"),
        )
        .unwrap();
        fs::write(source.join("bootstrap.toml"), "[build]\njobs = 2\n").unwrap();
        Self {
            directory,
            source,
            previous,
            patched,
        }
    }

    fn prepare(&self) -> Result<(), String> {
        ensure_patched_checkout(self.directory.path(), &self.source)
    }

    fn assert_previous_is_preserved(&self) {
        assert_eq!(
            git_output(&self.source, &["rev-parse", "HEAD"]).unwrap(),
            self.previous
        );
        assert_eq!(
            fs::read(self.source.join("build/artifact")).unwrap(),
            b"previous compiler"
        );
        assert_eq!(
            fs::read(self.source.join("bootstrap.toml")).unwrap(),
            b"[build]\njobs = 2\n"
        );
    }
}

fn git(source: &Path, arguments: &[&str]) {
    let output = Command::new("git")
        .arg("-C")
        .arg(source)
        .args([
            "-c",
            "user.name=rust-item-dependencies",
            "-c",
            "user.email=rust-item-dependencies@invalid.example",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(arguments)
        .env("GIT_AUTHOR_DATE", "2000-01-01T00:00:00+00:00")
        .env("GIT_COMMITTER_DATE", "2000-01-01T00:00:00+00:00")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{arguments:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn updates_the_generated_source_and_preserves_configuration() {
    for change_base in [false, true] {
        let checkout = Checkout::new(change_base);
        checkout.prepare().unwrap();
        assert_eq!(
            git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
            checkout.patched
        );
        assert_eq!(
            fs::read(checkout.source.join("source.rs")).unwrap(),
            b"pub fn answer() -> u32 { 42 }\n"
        );
        assert_eq!(
            fs::read(checkout.source.join("bootstrap.toml")).unwrap(),
            b"[build]\njobs = 2\n"
        );
        assert_eq!(
            fs::read(checkout.source.join("build/artifact")).unwrap(),
            b"previous compiler"
        );
        assert!(
            !compiler_build_identity_matches(checkout.directory.path(), &checkout.source).unwrap()
        );
        let reflog = git_output(&checkout.source, &["reflog", "--format=%H"]).unwrap();
        checkout.prepare().unwrap();
        assert_eq!(
            git_output(&checkout.source, &["reflog", "--format=%H"]).unwrap(),
            reflog
        );
    }
}

#[test]
fn updates_a_compiler_built_by_the_previous_launcher() {
    let checkout = Checkout::new(true);
    fs::rename(
        checkout
            .source
            .join("build")
            .join(COMPILER_BUILD_IDENTITY_FILE),
        checkout
            .source
            .join("build")
            .join(PREVIOUS_COMPILER_BUILD_IDENTITY_FILE),
    )
    .unwrap();
    checkout.prepare().unwrap();
    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("bootstrap.toml")).unwrap(),
        b"[build]\njobs = 2\n"
    );
}

#[test]
fn preserves_manual_changes_including_committed_changes() {
    for mode in ["modified", "untracked", "committed"] {
        let checkout = Checkout::new(true);
        let path = if mode == "untracked" {
            "manual.rs"
        } else {
            "source.rs"
        };
        fs::write(checkout.source.join(path), "manual change\n").unwrap();
        if mode == "committed" {
            git(
                &checkout.source,
                &["commit", "--quiet", "-am", "manual change"],
            );
        }
        let original = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
        let error = checkout.prepare().unwrap_err();
        assert!(
            error.contains(if mode == "committed" {
                "unrecorded revision"
            } else {
                "not clean"
            }),
            "{error}"
        );
        assert_eq!(
            git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
            original
        );
        assert_eq!(
            fs::read(checkout.source.join(path)).unwrap(),
            b"manual change\n"
        );
        assert_eq!(
            fs::read(checkout.source.join("build/artifact")).unwrap(),
            b"previous compiler"
        );
    }
}

#[test]
fn refuses_an_unexpected_origin_without_replacing_source() {
    let checkout = Checkout::new(true);
    git(
        &checkout.source,
        &[
            "remote",
            "set-url",
            "origin",
            "https://example.invalid/rust.git",
        ],
    );
    assert!(
        checkout
            .prepare()
            .unwrap_err()
            .contains("unexpected origin")
    );
    checkout.assert_previous_is_preserved();
}

#[test]
fn preserves_ignored_files_that_conflict_with_the_new_base() {
    let mut checkout = Checkout::new(true);
    let base = fs::read_to_string(
        checkout
            .directory
            .path()
            .join("rustc-patches/base-revision"),
    )
    .unwrap();
    git(
        &checkout.source,
        &["checkout", "--quiet", "--detach", base.trim()],
    );
    fs::write(checkout.source.join("reserved"), "upstream contents\n").unwrap();
    git(&checkout.source, &["add", "--force", "reserved"]);
    git(
        &checkout.source,
        &["commit", "--quiet", "-m", "new tracked file"],
    );
    let base = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/base-revision"),
        format!("{base}\n"),
    )
    .unwrap();
    fs::write(
        checkout.source.join("source.rs"),
        "pub fn answer() -> u32 { 42 }\n",
    )
    .unwrap();
    git(
        &checkout.source,
        &["commit", "--quiet", "-am", "current patches"],
    );
    checkout.patched = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    let patch = git_output(
        &checkout.source,
        &["format-patch", "--stdout", "--no-signature", "-1"],
    )
    .unwrap();
    let patches = checkout.directory.path().join("rustc-patches");
    fs::write(
        patches.join("patched-revision"),
        format!("{}\n", checkout.patched),
    )
    .unwrap();
    fs::write(patches.join("current.patch"), format!("{patch}\n")).unwrap();
    git(
        &checkout.source,
        &["checkout", "--quiet", "--detach", &checkout.previous],
    );
    fs::write(checkout.source.join("reserved"), "manual contents\n").unwrap();
    assert!(
        checkout
            .prepare()
            .unwrap_err()
            .contains("check out the pinned Rust source")
    );
    checkout.assert_previous_is_preserved();
    assert_eq!(
        fs::read(checkout.source.join("reserved")).unwrap(),
        b"manual contents\n"
    );
}

#[test]
fn restores_the_previous_source_after_partial_patch_failure() {
    let checkout = Checkout::new(true);
    let patches = checkout.directory.path().join("rustc-patches");
    fs::copy(patches.join("current.patch"), patches.join("invalid.patch")).unwrap();
    fs::write(patches.join("series"), "current.patch\ninvalid.patch\n").unwrap();
    assert!(
        checkout
            .prepare()
            .unwrap_err()
            .contains("apply invalid.patch")
    );
    checkout.assert_previous_is_preserved();
    assert_eq!(
        fs::read(checkout.source.join("source.rs")).unwrap(),
        b"pub fn answer() -> u32 { 7 }\n"
    );
    assert_eq!(
        git_output(&checkout.source, &["status", "--porcelain"]).unwrap(),
        ""
    );
    fs::write(patches.join("series"), "current.patch\n").unwrap();
    checkout.prepare().unwrap();
    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
}

#[test]
fn initially_checks_out_source_without_overwriting_existing_configuration() {
    let checkout = Checkout::new(true);
    git(
        &checkout.source,
        &["symbolic-ref", "HEAD", "refs/heads/new-checkout"],
    );
    git(&checkout.source, &["read-tree", "--empty"]);
    fs::remove_file(checkout.source.join("source.rs")).unwrap();
    fs::remove_file(checkout.source.join(".gitignore")).unwrap();
    checkout.prepare().unwrap();
    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("bootstrap.toml")).unwrap(),
        b"[build]\njobs = 2\n"
    );
}

#[test]
fn resumes_after_the_patch_worktree_was_abandoned_mid_application() {
    let mut checkout = Checkout::new(true);
    let base = fs::read_to_string(
        checkout
            .directory
            .path()
            .join("rustc-patches/base-revision"),
    )
    .unwrap();
    let worktree = checkout.source.with_file_name("rustc-patch-interrupted");
    git(
        &checkout.source,
        &[
            "worktree",
            "add",
            "--detach",
            worktree.to_str().unwrap(),
            base.trim(),
        ],
    );
    fs::write(
        worktree.join("source.rs"),
        "pub fn answer() -> u32 { 21 }\n",
    )
    .unwrap();
    git(&worktree, &["commit", "--quiet", "-am", "first patch"]);
    let prefix = git_output(&worktree, &["rev-parse", "HEAD"]).unwrap();
    fs::write(
        worktree.join("source.rs"),
        "pub fn answer() -> u32 { 42 }\n",
    )
    .unwrap();
    git(&worktree, &["commit", "--quiet", "-am", "second patch"]);
    checkout.patched = git_output(&worktree, &["rev-parse", "HEAD"]).unwrap();
    let patch = git_output(
        &worktree,
        &["format-patch", "--stdout", "--no-signature", "-2"],
    )
    .unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/current.patch"),
        format!("{patch}\n"),
    )
    .unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/patched-revision"),
        format!("{}\n", checkout.patched),
    )
    .unwrap();
    git(&worktree, &["checkout", "--quiet", "--detach", &prefix]);
    fs::write(worktree.join("source.rs"), "unfinished patch\n").unwrap();
    git(
        &checkout.source,
        &[
            "worktree",
            "lock",
            "--reason",
            "initializing",
            worktree.to_str().unwrap(),
        ],
    );
    checkout.assert_previous_is_preserved();

    checkout.prepare().unwrap();

    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("source.rs")).unwrap(),
        b"pub fn answer() -> u32 { 42 }\n"
    );
    assert_eq!(
        fs::read(worktree.join("source.rs")).unwrap(),
        b"unfinished patch\n"
    );
    let worktrees = git_output(&checkout.source, &["worktree", "list", "--porcelain"]).unwrap();
    assert_eq!(
        worktrees
            .lines()
            .filter(|line| line.starts_with("worktree "))
            .count(),
        2
    );
}

#[test]
fn preserves_existing_directories_repositories_and_worktrees() {
    for mode in ["directory", "repository", "worktree"] {
        let checkout = Checkout::new(true);
        let existing = checkout.source.with_file_name("rustc-patch-worktree");
        if mode == "worktree" {
            git(
                &checkout.source,
                &[
                    "worktree",
                    "add",
                    "--detach",
                    existing.to_str().unwrap(),
                    &checkout.previous,
                ],
            );
        } else {
            fs::create_dir(&existing).unwrap();
            if mode == "repository" {
                git(&existing, &["init", "--quiet"]);
            }
        }
        fs::write(existing.join("user.txt"), "user data\n").unwrap();

        checkout.prepare().unwrap();

        assert_eq!(fs::read(existing.join("user.txt")).unwrap(), b"user data\n");
        assert_eq!(
            git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
            checkout.patched
        );
        if mode == "worktree" {
            assert_eq!(
                git_output(&existing, &["rev-parse", "HEAD"]).unwrap(),
                checkout.previous
            );
        }
    }
}

#[test]
fn source_identity_survives_build_failure_or_cache_removal() {
    let mut checkout = Checkout::new(true);
    checkout.prepare().unwrap();
    let original = checkout.patched.clone();
    fs::remove_dir_all(checkout.source.join("build")).unwrap();
    fs::write(
        checkout.source.join("source.rs"),
        "pub fn answer() -> u32 { 43 }\n",
    )
    .unwrap();
    git(
        &checkout.source,
        &["commit", "--quiet", "-am", "next patches"],
    );
    checkout.patched = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    let base = fs::read_to_string(
        checkout
            .directory
            .path()
            .join("rustc-patches/base-revision"),
    )
    .unwrap();
    let patch = git_output(
        &checkout.source,
        &[
            "format-patch",
            "--stdout",
            "--no-signature",
            &format!("{}..HEAD", base.trim()),
        ],
    )
    .unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/current.patch"),
        format!("{patch}\n"),
    )
    .unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/patched-revision"),
        format!("{}\n", checkout.patched),
    )
    .unwrap();
    git(
        &checkout.source,
        &["checkout", "--quiet", "--detach", &original],
    );

    checkout.prepare().unwrap();

    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("source.rs")).unwrap(),
        b"pub fn answer() -> u32 { 43 }\n"
    );
    assert_eq!(
        git_output(
            &checkout.source,
            &["config", "--get", COMPILER_CHECKOUT_REVISION_KEY]
        )
        .unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("bootstrap.toml")).unwrap(),
        b"[build]\njobs = 2\n"
    );
}

fn checkout_with_submodule() -> (Checkout, String) {
    let mut checkout = Checkout::new(true);
    let upstream = checkout.directory.path().join("llvm-upstream");
    fs::create_dir(&upstream).unwrap();
    git(&upstream, &["init", "--quiet"]);
    fs::create_dir(upstream.join("llvm")).unwrap();
    fs::write(upstream.join(".gitignore"), "/llvm/CMakeUserPresets.json\n").unwrap();
    fs::write(upstream.join("llvm/source.cpp"), "previous source\n").unwrap();
    git(&upstream, &["add", "."]);
    git(&upstream, &["commit", "--quiet", "-m", "previous LLVM"]);
    git(
        &checkout.source,
        &[
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            upstream.to_str().unwrap(),
            "src/llvm-project",
        ],
    );
    git(
        &checkout.source,
        &["commit", "--quiet", "-am", "previous submodule"],
    );
    checkout.previous = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    fs::write(
        checkout
            .source
            .join("build")
            .join(COMPILER_BUILD_IDENTITY_FILE),
        format!("{}\nprevious digest\n", checkout.previous),
    )
    .unwrap();

    let submodule = checkout.source.join("src/llvm-project");
    let previous_llvm = git_output(&submodule, &["rev-parse", "HEAD"]).unwrap();
    fs::write(submodule.join("llvm/source.cpp"), "new source\n").unwrap();
    git(&submodule, &["commit", "--quiet", "-am", "new LLVM"]);
    git(
        &checkout.source,
        &["commit", "--quiet", "-am", "new submodule"],
    );
    let new_base = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    fs::write(
        checkout
            .directory
            .path()
            .join("rustc-patches/base-revision"),
        format!("{new_base}\n"),
    )
    .unwrap();
    fs::write(
        checkout.source.join("source.rs"),
        "pub fn answer() -> u32 { 42 }\n",
    )
    .unwrap();
    git(
        &checkout.source,
        &["commit", "--quiet", "-am", "current patches"],
    );
    checkout.patched = git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap();
    let patch = git_output(
        &checkout.source,
        &["format-patch", "--stdout", "--no-signature", "-1"],
    )
    .unwrap();
    let patches = checkout.directory.path().join("rustc-patches");
    fs::write(
        patches.join("patched-revision"),
        format!("{}\n", checkout.patched),
    )
    .unwrap();
    fs::write(patches.join("current.patch"), format!("{patch}\n")).unwrap();
    git(
        &checkout.source,
        &["checkout", "--quiet", "--detach", &checkout.previous],
    );
    git(
        &submodule,
        &["checkout", "--quiet", "--detach", &previous_llvm],
    );
    (checkout, previous_llvm)
}

#[test]
fn preserves_ignored_user_configuration_in_initialized_submodules() {
    let (checkout, previous_llvm) = checkout_with_submodule();
    let submodule = checkout.source.join("src/llvm-project");
    let configuration = submodule.join("llvm/CMakeUserPresets.json");
    fs::write(&configuration, "{\"version\": 3}\n").unwrap();
    assert_eq!(
        git_output(&checkout.source, &["status", "--porcelain"]).unwrap(),
        ""
    );

    assert!(
        checkout
            .prepare()
            .unwrap_err()
            .contains("local files in a submodule")
    );

    checkout.assert_previous_is_preserved();
    assert_eq!(
        git_output(&submodule, &["rev-parse", "HEAD"]).unwrap(),
        previous_llvm
    );
    assert_eq!(fs::read(configuration).unwrap(), b"{\"version\": 3}\n");
}

#[test]
fn source_update_is_repeatable_before_bootstrap_updates_submodules() {
    let (checkout, _) = checkout_with_submodule();

    checkout.prepare().unwrap();
    checkout.prepare().unwrap();

    assert_eq!(
        git_output(&checkout.source, &["rev-parse", "HEAD"]).unwrap(),
        checkout.patched
    );
    assert_eq!(
        fs::read(checkout.source.join("source.rs")).unwrap(),
        b"pub fn answer() -> u32 { 42 }\n"
    );
    assert_eq!(
        git_output(&checkout.source, &["status", "--porcelain"]).unwrap(),
        ""
    );
    assert_eq!(
        fs::read(checkout.source.join("bootstrap.toml")).unwrap(),
        b"[build]\njobs = 2\n"
    );
}
