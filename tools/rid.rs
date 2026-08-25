---cargo
[package]
edition = "2024"
---

use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus, Stdio};

mod cli;

use cli::{Parsed, parse_arguments, reducer_usage, render_path, validate_output};

const RUST_REPOSITORY: &str = "https://github.com/rust-lang/rust.git";
const USAGE_COMMAND: &str =
    "Usage: cargo rid [OPTIONS] INPUT.rs\n       cargo rid rustc [RUSTC_OPTIONS]...";
const SNAPSHOT_PARENT_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT";
const SNAPSHOT_OWNER_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_OWNER";
const PROCESS_OWNER_PREFIX: &str = ".rust-item-dependencies-owner-";
const PROCESS_ROOT_PREFIX: &str = "rust-item-dependencies-process-";
const SNAPSHOT_OWNER_ATTEMPTS: u64 = 1_024;
#[cfg(windows)]
const SNAPSHOT_PARENT_LOCK_FILE: &str = ".rust-item-dependencies-parent-lock";
const RUSTC_PRIVATE_CRATES: &[&str] = &[
    "rustc_ast",
    "rustc_data_structures",
    "rustc_errors",
    "rustc_expand",
    "rustc_feature",
    "rustc_hir",
    "rustc_interface",
    "rustc_lexer",
    "rustc_middle",
    "rustc_serialize",
    "rustc_session",
    "rustc_span",
    "rustc_target",
];

fn main() -> ExitCode {
    match run() {
        Ok(RunOutcome::Success) => ExitCode::SUCCESS,
        Ok(RunOutcome::Rustc(status)) if status.success() => ExitCode::SUCCESS,
        Ok(RunOutcome::Rustc(status)) => match status.code() {
            Some(code) => std::process::exit(code),
            None => ExitCode::FAILURE,
        },
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

enum RunOutcome {
    Success,
    Rustc(ExitStatus),
}

fn run() -> Result<RunOutcome, String> {
    let arguments = env::args_os().skip(1).collect::<Vec<_>>();
    let rustc_arguments = if arguments
        .first()
        .is_some_and(|argument| argument == "rustc")
    {
        Some(arguments[1..].to_vec())
    } else {
        let usage = reducer_usage(USAGE_COMMAND);
        match parse_arguments(arguments.iter().cloned(), &usage)? {
            Parsed::Run(cli) => validate_output(&cli)?,
            Parsed::Help => {
                println!("{usage}");
                return Ok(RunOutcome::Success);
            }
        }
        None
    };

    let tools_directory = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repository_root = tools_directory
        .parent()
        .ok_or_else(|| "cannot locate the repository root".to_owned())?;
    let generated = repository_root.join("target/rid");
    let rust_source = generated.join("rustc");
    fs::create_dir_all(&generated)
        .map_err(|error| format!("cannot create {}: {error}", render_path(&generated)))?;

    ensure_patched_checkout(repository_root, &rust_source)?;
    let host = active_host()?;
    let stage2 = rust_source.join("build").join(&host).join("stage2");
    let stage2_rustc = stage2
        .join("bin")
        .join(format!("rustc{}", env::consts::EXE_SUFFIX));
    if !stage2_rustc.is_file() {
        build_compiler(repository_root, &rust_source)?;
    }
    if let Some(arguments) = rustc_arguments {
        let status = Command::new(&stage2_rustc)
            .args(arguments)
            .status()
            .map_err(|error| format!("cannot start the configured rustc: {error}"))?;
        return Ok(RunOutcome::Rustc(status));
    }
    let (rustc, compiler_library, compiler_metadata, rustc_driver) = compiler_paths(&stage2)?;
    run_reducer(
        repository_root,
        &generated,
        &rustc,
        &compiler_library,
        &compiler_metadata,
        &rustc_driver,
        &arguments,
    )?;
    Ok(RunOutcome::Success)
}

fn ensure_patched_checkout(repository_root: &Path, rust_source: &Path) -> Result<(), String> {
    let base_revision = read_trimmed(repository_root.join("rustc-patches/base-revision"))?;
    let patched_revision = read_trimmed(repository_root.join("rustc-patches/patched-revision"))?;

    if !rust_source.join(".git").exists() {
        fs::create_dir_all(rust_source)
            .map_err(|error| format!("cannot create {}: {error}", render_path(rust_source)))?;
        run_command(
            Command::new("git").arg("init").arg(rust_source),
            "initialize the Rust checkout",
        )?;
    }

    match git_output(rust_source, &["remote", "get-url", "origin"]) {
        Ok(origin) if origin == RUST_REPOSITORY => {}
        Ok(origin) => {
            return Err(format!(
                "the generated Rust checkout has an unexpected origin: {origin}"
            ));
        }
        Err(_) => {
            run_command(
                Command::new("git").args(["-C"]).arg(rust_source).args([
                    "remote",
                    "add",
                    "origin",
                    RUST_REPOSITORY,
                ]),
                "configure the Rust repository",
            )?;
        }
    }

    if git_output(rust_source, &["rev-parse", "--verify", "HEAD"]).is_err() {
        run_command(
            Command::new("git").args(["-C"]).arg(rust_source).args([
                "fetch",
                "--depth",
                "1",
                "origin",
                &base_revision,
            ]),
            "download the pinned Rust source",
        )?;
        run_command(
            Command::new("git").args(["-C"]).arg(rust_source).args([
                "checkout",
                "--detach",
                "FETCH_HEAD",
            ]),
            "check out the pinned Rust source",
        )?;
    }

    let revision = git_output(rust_source, &["rev-parse", "HEAD"])?;
    let changes = git_output(rust_source, &["status", "--porcelain"])?;
    if !changes.is_empty() {
        return Err(format!(
            "the generated Rust checkout is not clean: {}",
            render_path(rust_source)
        ));
    }
    if revision == patched_revision {
        return Ok(());
    }
    if revision != base_revision {
        return Err(format!(
            "the generated Rust checkout has an unexpected revision; remove {} and run the command again",
            render_path(rust_source)
        ));
    }

    let patch_directory = repository_root.join("rustc-patches");
    let series = fs::read_to_string(patch_directory.join("series"))
        .map_err(|error| format!("cannot read the patch series: {error}"))?;
    for patch_name in series
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
    {
        let patch = patch_directory.join(patch_name);
        if !patch.is_file() {
            return Err(format!("patch does not exist: {}", render_path(&patch)));
        }
        let result = run_command(
            Command::new("git")
                .args(["-C"])
                .arg(rust_source)
                .args([
                    "-c",
                    "user.name=rust-item-dependencies",
                    "-c",
                    "user.email=rust-item-dependencies@invalid.example",
                    "am",
                    "--no-gpg-sign",
                    "--no-verify",
                    "--committer-date-is-author-date",
                ])
                .arg(&patch),
            &format!("apply {patch_name}"),
        );
        if let Err(error) = result {
            let _ = Command::new("git")
                .args(["-C"])
                .arg(rust_source)
                .args(["am", "--abort"])
                .status();
            return Err(error);
        }
    }

    let revision = git_output(rust_source, &["rev-parse", "HEAD"])?;
    if revision != patched_revision {
        return Err(format!(
            "patched Rust revision mismatch: expected {patched_revision}, got {revision}"
        ));
    }
    Ok(())
}

fn build_compiler(repository_root: &Path, rust_source: &Path) -> Result<(), String> {
    eprintln!("Preparing the patched Rust compiler. This takes a while on the first run.");
    let queue_digest = read_trimmed(repository_root.join("rustc-patches/queue-digest"))?;
    let (python, prefix_arguments) = find_python()?;
    let mut command = Command::new(python);
    command
        .args(prefix_arguments)
        .arg(rust_source.join("x.py"))
        .args([
            "build",
            "--ci=false",
            "--stage",
            "2",
            "compiler/rustc",
            "library",
        ])
        .current_dir(rust_source)
        .env("RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST", queue_digest)
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    run_command(&mut command, "build the patched Rust compiler")
}

fn find_python() -> Result<(OsString, Vec<OsString>), String> {
    let candidates: &[(&str, &[&str])] = if cfg!(windows) {
        &[("py", &["-3"]), ("python", &[]), ("python3", &[])]
    } else {
        &[("python3", &[]), ("python", &[])]
    };
    for (executable, arguments) in candidates {
        let available = Command::new(executable)
            .args(*arguments)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success());
        if available {
            return Ok((
                OsString::from(executable),
                arguments.iter().map(OsString::from).collect(),
            ));
        }
    }
    Err("Python 3 is required to build the patched Rust compiler".to_owned())
}

fn active_host() -> Result<String, String> {
    let version = command_output(Command::new("rustc").arg("-Vv"), "query the Rust host")?;
    version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::to_owned)
        .ok_or_else(|| "rustc did not report its host".to_owned())
}

fn compiler_paths(stage2: &Path) -> Result<(PathBuf, PathBuf, PathBuf, PathBuf), String> {
    let rustc = stage2
        .join("bin")
        .join(format!("rustc{}", env::consts::EXE_SUFFIX));
    if !rustc.is_file() {
        return Err(format!("stage2 rustc is missing: {}", render_path(&rustc)));
    }
    let version = command_output(Command::new(&rustc).arg("-Vv"), "query stage2 rustc")?;
    let host = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .ok_or_else(|| "stage2 rustc did not report its host".to_owned())?;
    let compiler_library = if host.contains("windows") {
        stage2.join("bin")
    } else {
        stage2.join("lib")
    };
    let compiler_metadata = stage2
        .parent()
        .ok_or_else(|| "stage2 has no build directory".to_owned())?
        .join("stage1/lib/rustlib")
        .join(host)
        .join("lib");
    if !compiler_metadata.is_dir() {
        return Err(format!(
            "stage1 compiler metadata is missing: {}",
            render_path(&compiler_metadata)
        ));
    }
    let driver_prefix = format!("{}rustc_driver-", env::consts::DLL_PREFIX);
    let rustc_driver = unique_file(&compiler_metadata, |name| {
        name.starts_with(&driver_prefix) && name.ends_with(env::consts::DLL_SUFFIX)
    })?;
    Ok((rustc, compiler_library, compiler_metadata, rustc_driver))
}

fn run_reducer(
    repository_root: &Path,
    generated: &Path,
    rustc: &Path,
    compiler_library: &Path,
    compiler_metadata: &Path,
    rustc_driver: &Path,
    arguments: &[OsString],
) -> Result<(), String> {
    let snapshot_parent = generated.join("snapshots");
    fs::create_dir_all(&snapshot_parent)
        .map_err(|error| format!("cannot create {}: {error}", render_path(&snapshot_parent)))?;
    let snapshot_owner = unique_snapshot_owner(&snapshot_parent)?;
    let mut rustflags = vec![
        OsString::from("--extern"),
        prefixed_path("rustc_driver=", rustc_driver),
    ];
    for crate_name in RUSTC_PRIVATE_CRATES {
        let prefix = format!("lib{crate_name}-");
        let metadata = unique_file(compiler_metadata, |name| {
            name.starts_with(&prefix) && name.ends_with(".rmeta")
        })?;
        rustflags.push(OsString::from("--extern"));
        rustflags.push(prefixed_path(&format!("{crate_name}="), &metadata));
    }
    rustflags.push(OsString::from("-L"));
    rustflags.push(prefixed_path("dependency=", compiler_metadata));
    let mut encoded = OsString::new();
    for argument in rustflags {
        if !encoded.is_empty() {
            encoded.push("\u{1f}");
        }
        encoded.push(argument);
    }

    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let mut command = Command::new(cargo);
    command
        .current_dir(repository_root)
        .env("RUSTC", rustc)
        .env("CARGO_ENCODED_RUSTFLAGS", encoded)
        .env("CARGO_TARGET_DIR", generated.join("cargo"))
        .env(SNAPSHOT_PARENT_ENV, &snapshot_parent)
        .env(SNAPSHOT_OWNER_ENV, &snapshot_owner)
        .env_remove("RUSTFLAGS")
        .args([
            "run",
            "--quiet",
            "--release",
            "--locked",
            "--bin",
            "rust-item-dependencies",
            "--",
        ])
        .args(arguments);
    if cfg!(windows) {
        prepend_path(&mut command, compiler_library)?;
    }
    let result = command
        .status()
        .map_err(|error| format!("cannot run rust-item-dependencies: {error}"))
        .and_then(|status| {
            status.success().then_some(()).ok_or_else(|| {
                format!("cannot run rust-item-dependencies: process exited with {status}")
            })
        });
    let cleanup = remove_reducer_snapshot(&snapshot_parent, &snapshot_owner);
    match (result, cleanup) {
        (Ok(()), Ok(())) => Ok(()),
        (Err(error), Ok(())) | (Ok(()), Err(error)) => Err(error),
        (Err(error), Err(cleanup)) => Err(format!("{error}; {cleanup}")),
    }
}

fn unique_snapshot_owner(parent: &Path) -> Result<String, String> {
    let process = std::process::id();
    let mut last_owner = String::new();
    for nonce in 0..SNAPSHOT_OWNER_ATTEMPTS {
        let owner = format!("{process}-{nonce}");
        let owner_path = parent.join(format!("{PROCESS_OWNER_PREFIX}{owner}"));
        let root = parent.join(format!("{PROCESS_ROOT_PREFIX}{owner}"));
        let owner_exists = owner_path
            .try_exists()
            .map_err(|error| format!("cannot inspect {}: {error}", render_path(&owner_path)))?;
        let root_exists = root
            .try_exists()
            .map_err(|error| format!("cannot inspect {}: {error}", render_path(&root)))?;
        if !owner_exists && !root_exists {
            return Ok(owner);
        }
        last_owner = owner;
    }
    Err(format!(
        "cannot allocate a snapshot owner after {SNAPSHOT_OWNER_ATTEMPTS} attempts: {last_owner}"
    ))
}

fn remove_reducer_snapshot(parent: &Path, owner: &str) -> Result<(), String> {
    #[cfg(windows)]
    let _parent_lock = lock_snapshot_parent(parent)?;
    let root = parent.join(format!("{PROCESS_ROOT_PREFIX}{owner}"));
    let owner = parent.join(format!("{PROCESS_OWNER_PREFIX}{owner}"));
    #[cfg(windows)]
    let owner_lock = {
        let mut options = fs::OpenOptions::new();
        options.read(true).write(true);
        match options.open(&owner) {
            Ok(file) => match file.try_lock() {
                Ok(()) => Some(file),
                Err(fs::TryLockError::WouldBlock) => return Ok(()),
                Err(fs::TryLockError::Error(error)) => {
                    return Err(format!("cannot lock {}: {error}", render_path(&owner)));
                }
            },
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => {
                return Err(format!("cannot open {}: {error}", render_path(&owner)));
            }
        }
    };
    remove_snapshot_path(&root, true)?;
    #[cfg(windows)]
    drop(owner_lock);
    remove_snapshot_path(&owner, false)
}

fn remove_snapshot_path(path: &Path, directory: bool) -> Result<(), String> {
    let result = if directory {
        fs::remove_dir_all(path)
    } else {
        fs::remove_file(path)
    };
    match result {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("cannot remove {}: {error}", render_path(path))),
    }
}

#[cfg(windows)]
fn lock_snapshot_parent(parent: &Path) -> Result<fs::File, String> {
    let path = parent.join(SNAPSHOT_PARENT_LOCK_FILE);
    let mut options = fs::OpenOptions::new();
    options.read(true).write(true).create(true);
    let file = options
        .open(&path)
        .map_err(|error| format!("cannot open {}: {error}", render_path(&path)))?;
    file.lock()
        .map_err(|error| format!("cannot lock {}: {error}", render_path(&path)))?;
    Ok(file)
}

#[cfg(all(test, windows))]
mod snapshot_tests {
    use std::io::{BufRead, BufReader, Write};

    use super::*;

    const HOLDER_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_TEST_HOLDER";
    const TEST_NAME: &str = "snapshot_tests::cleanup_defers_to_a_live_reducer";

    #[test]
    fn cleanup_defers_to_a_live_reducer() {
        if let Some(parent) = env::var_os(HOLDER_ENV) {
            let parent = PathBuf::from(parent);
            let owner = parent.join(format!("{PROCESS_OWNER_PREFIX}test"));
            let root = parent.join(format!("{PROCESS_ROOT_PREFIX}test"));
            fs::create_dir(&root).unwrap();
            fs::write(root.join("artifact.dll"), b"loaded").unwrap();
            let mut options = fs::OpenOptions::new();
            options.read(true).write(true).create_new(true);
            let owner = options.open(owner).unwrap();
            owner.lock().unwrap();
            println!("LOCKED");
            std::io::stdout().flush().unwrap();
            std::io::stdin().read_line(&mut String::new()).unwrap();
            return;
        }

        let directory = TestDirectory::new();
        let mut child = Command::new(env::current_exe().unwrap())
            .args(["--exact", TEST_NAME, "--nocapture"])
            .env(HOLDER_ENV, directory.path())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let stdout = child.stdout.take().unwrap();
        let mut stdout = BufReader::new(stdout);
        let mut ready = String::new();
        while !ready.contains("LOCKED") {
            ready.clear();
            assert_ne!(stdout.read_line(&mut ready).unwrap(), 0);
        }

        remove_reducer_snapshot(directory.path(), "test").unwrap();
        assert!(
            directory
                .path()
                .join(format!("{PROCESS_ROOT_PREFIX}test"))
                .is_dir()
        );
        assert!(
            directory
                .path()
                .join(format!("{PROCESS_OWNER_PREFIX}test"))
                .is_file()
        );

        writeln!(child.stdin.take().unwrap(), "release").unwrap();
        assert!(child.wait().unwrap().success());
        remove_reducer_snapshot(directory.path(), "test").unwrap();
        assert_eq!(
            fs::read_dir(directory.path()).unwrap().count(),
            1,
            "only the parent lock file may remain"
        );
    }

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let parent = Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .unwrap()
                .join("target/rid-tool-tests");
            fs::create_dir_all(&parent).unwrap();
            for nonce in 0..SNAPSHOT_OWNER_ATTEMPTS {
                let path = parent.join(format!("{}-{nonce}", std::process::id()));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(error) => panic!("cannot create test directory: {error}"),
                }
            }
            panic!("cannot allocate test directory")
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
}

fn prefixed_path(prefix: &str, path: &Path) -> OsString {
    let mut value = OsString::from(prefix);
    value.push(path);
    value
}

fn prepend_path(command: &mut Command, directory: &Path) -> Result<(), String> {
    let inherited = env::var_os("PATH");
    let paths = std::iter::once(directory.to_path_buf()).chain(
        inherited
            .as_deref()
            .map(env::split_paths)
            .into_iter()
            .flatten(),
    );
    let path = env::join_paths(paths).map_err(|error| format!("cannot update PATH: {error}"))?;
    command.env("PATH", path);
    Ok(())
}

fn unique_file(directory: &Path, predicate: impl Fn(&str) -> bool) -> Result<PathBuf, String> {
    let mut matches = fs::read_dir(directory)
        .map_err(|error| format!("cannot read {}: {error}", render_path(directory)))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(OsStr::to_str)
                .is_some_and(&predicate)
        })
        .collect::<Vec<_>>();
    matches.sort();
    if matches.len() != 1 {
        return Err(format!(
            "expected exactly one compiler artifact in {}",
            render_path(directory)
        ));
    }
    Ok(matches.remove(0))
}

fn read_trimmed(path: PathBuf) -> Result<String, String> {
    fs::read_to_string(&path)
        .map(|value| value.trim().to_owned())
        .map_err(|error| format!("cannot read {}: {error}", render_path(&path)))
}

fn git_output(repository: &Path, arguments: &[&str]) -> Result<String, String> {
    command_output(
        Command::new("git")
            .args(["-C"])
            .arg(repository)
            .args(arguments),
        "query the Rust checkout",
    )
    .map(|output| output.trim().to_owned())
}

fn command_output(command: &mut Command, action: &str) -> Result<String, String> {
    let output = command
        .output()
        .map_err(|error| format!("cannot {action}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "cannot {action}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout).map_err(|_| format!("cannot {action}: non-UTF-8 output"))
}

fn run_command(command: &mut Command, action: &str) -> Result<(), String> {
    let status = command
        .status()
        .map_err(|error| format!("cannot {action}: {error}"))?;
    status
        .success()
        .then_some(())
        .ok_or_else(|| format!("cannot {action}: process exited with {status}"))
}
