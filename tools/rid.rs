---cargo
[package]
edition = "2024"
---

#![feature(fs_set_times)]

use std::cmp::Reverse;
use std::collections::BTreeSet;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, FileTimes, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus, Stdio};
use std::time::SystemTime;

mod cli;
#[path = "../src/target_libraries.rs"]
mod target_libraries;

use cli::{Parsed, parse_arguments, reducer_usage, render_path, validate_output};
use target_libraries::{
    TargetLibrarySource, select_ready_target_libraries, target_metadata_directory,
};

const RUST_REPOSITORY: &str = "https://github.com/rust-lang/rust.git";
const USAGE_COMMAND: &str =
    "Usage: cargo rid [OPTIONS] INPUT.rs\n       cargo rid rustc [RUSTC_OPTIONS]...";
const SNAPSHOT_PARENT_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT";
const SNAPSHOT_OWNER_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_OWNER";
const PROCESS_OWNER_PREFIX: &str = ".rust-item-dependencies-owner-";
const PROCESS_ROOT_PREFIX: &str = "rust-item-dependencies-process-";
const SNAPSHOT_OWNER_ATTEMPTS: u64 = 1_024;
const BOOTSTRAP_CARGO_FLAGS: &str = "-Zchecksum-freshness";
const COMPILER_BUILD_IDENTITY_FILE: &str = ".rust-item-dependencies-build-identity-v1";
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
    let (rustc_arguments, reducer_target) = if arguments
        .first()
        .is_some_and(|argument| argument == "rustc")
    {
        (Some(arguments[1..].to_vec()), None)
    } else {
        let usage = reducer_usage(USAGE_COMMAND);
        match parse_arguments(arguments.iter().cloned(), &usage)? {
            Parsed::Run(cli) => {
                validate_output(&cli)?;
                (None, cli.target.clone())
            }
            Parsed::Help => {
                println!("{usage}");
                return Ok(RunOutcome::Success);
            }
        }
    };

    let tools_directory = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repository_root = tools_directory
        .parent()
        .ok_or_else(|| "cannot locate the repository root".to_owned())?;
    let generated = repository_root.join("target/rid");
    let rust_source = generated.join("rustc");
    let restored_build_without_checkout =
        rust_source.join("build").is_dir() && !rust_source.join(".git").exists();
    fs::create_dir_all(&generated)
        .map_err(|error| format!("cannot create {}: {error}", render_path(&generated)))?;

    let preparation_lock = lock_exclusive(&generated.join("preparation.lock"))?;
    ensure_patched_checkout(repository_root, &rust_source)?;
    let build_identity_matches = compiler_build_identity_matches(repository_root, &rust_source)?;
    if restored_build_without_checkout && build_identity_matches {
        // Cached Cargo outputs predate this checkout. Validate its contents first, then restore
        // the source-time ordering expected by Cargo and native build scripts.
        normalize_tracked_source_mtimes(&rust_source)?;
    }
    let host = active_host()?;
    let stage2 = rust_source.join("build").join(&host).join("stage2");
    let stage2_rustc = stage2
        .join("bin")
        .join(format!("rustc{}", env::consts::EXE_SUFFIX));
    if !stage2_rustc.is_file() || !build_identity_matches {
        remove_compiler_build_identity(&rust_source)?;
        build_compiler(repository_root, &rust_source)?;
        record_compiler_build_identity(repository_root, &rust_source)?;
    }
    if let Some(arguments) = rustc_arguments {
        let target = match direct_builtin_target_candidate(&arguments) {
            Some(target) if is_builtin_target(&stage2_rustc, target)? => Some(target),
            _ => None,
        };
        let target_libraries = match target {
            Some(target) => Some(prepare_target_libraries(
                repository_root,
                &rust_source,
                &stage2,
                &stage2_rustc,
                &host,
                target,
            )?),
            None => None,
        };
        drop(preparation_lock);
        let mut command = Command::new(&stage2_rustc);
        command
            .args(target_library_search_arguments(target_libraries.as_ref()))
            .args(arguments);
        let status = command
            .status()
            .map_err(|error| format!("cannot start the configured rustc: {error}"))?;
        return Ok(RunOutcome::Rustc(status));
    }

    if let Some(target) = reducer_target {
        if !is_builtin_target(&stage2_rustc, &target)? {
            return Err(format!("unsupported Rust target: {target}"));
        }
        prepare_target_libraries(
            repository_root,
            &rust_source,
            &stage2,
            &stage2_rustc,
            &host,
            &target,
        )?;
    }
    drop(preparation_lock);
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

fn direct_builtin_target_candidate(arguments: &[OsString]) -> Option<&str> {
    let arguments = arguments
        .iter()
        .map(|argument| argument.to_str())
        .collect::<Option<Vec<_>>>()?;
    if arguments.iter().any(|argument| {
        *argument == "--"
            || argument.starts_with('@')
            || *argument == "--sysroot"
            || argument.starts_with("--sysroot=")
    }) {
        return None;
    }
    let (target, remaining) = match arguments.as_slice() {
        ["--target", target, remaining @ ..] if !target.is_empty() => (*target, remaining),
        [first, remaining @ ..] => (first.strip_prefix("--target=")?, remaining),
        [] => return None,
    };
    if target.is_empty()
        || remaining
            .iter()
            .any(|argument| *argument == "--target" || argument.starts_with("--target="))
    {
        return None;
    }
    Some(target)
}

fn is_builtin_target(rustc: &Path, target: &str) -> Result<bool, String> {
    let targets = command_output(
        Command::new(rustc).args(["--print", "target-list"]),
        "query built-in Rust targets",
    )?;
    Ok(targets.lines().any(|candidate| candidate == target))
}

fn prepare_target_libraries(
    repository_root: &Path,
    rust_source: &Path,
    stage2: &Path,
    stage2_rustc: &Path,
    host: &str,
    target: &str,
) -> Result<TargetLibrarySource, String> {
    let installed = target_library_directory(stage2_rustc, target)?;
    let generated = target_metadata_directory(stage2, target)
        .ok_or_else(|| "stage2 has no build directory".to_owned())?;
    if let Some(source) = select_ready_target_libraries(&installed, &generated, target == host)
        .map_err(|error| error.to_string())?
    {
        return Ok(source);
    }
    prepare_target_metadata(repository_root, rust_source, target)?;
    match select_ready_target_libraries(&installed, &generated, target == host)
        .map_err(|error| error.to_string())?
    {
        Some(source) => Ok(source),
        None => Err(format!(
            "target metadata is missing after preparation: {}",
            render_path(&generated)
        )),
    }
}

fn target_library_directory(rustc: &Path, target: &str) -> Result<PathBuf, String> {
    let output = command_output(
        Command::new(rustc).args(["--target", target, "--print", "target-libdir"]),
        "query the target library directory",
    )?;
    let path = output.trim_end_matches(['\r', '\n']);
    if path.is_empty() {
        return Err("rustc reported an empty target library directory".to_owned());
    }
    Ok(PathBuf::from(path))
}

fn lock_exclusive(path: &Path) -> Result<File, String> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)
        .map_err(|error| format!("cannot open {}: {error}", render_path(path)))?;
    file.lock()
        .map_err(|error| format!("cannot lock {}: {error}", render_path(path)))?;
    Ok(file)
}

fn target_library_search_arguments(source: Option<&TargetLibrarySource>) -> Vec<OsString> {
    let mut arguments = Vec::new();
    for (kind, directory) in source
        .into_iter()
        .flat_map(TargetLibrarySource::search_paths)
    {
        arguments.push(OsString::from("-L"));
        arguments.push(prefixed_path(&format!("{kind}="), directory));
    }
    arguments
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

fn normalize_tracked_source_mtimes(rust_source: &Path) -> Result<(), String> {
    let tracked = command_output(
        Command::new("git")
            .args(["-C"])
            .arg(rust_source)
            .args(["ls-files", "-z"]),
        "list tracked Rust source files",
    )?;
    let mut directories = BTreeSet::new();
    for relative in tracked.split('\0').filter(|relative| !relative.is_empty()) {
        let relative = Path::new(relative);
        let path = rust_source.join(relative);
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(format!("cannot inspect {}: {error}", render_path(&path)));
            }
        };
        if !metadata.file_type().is_file() {
            continue;
        }
        set_modified_to_epoch(&path)?;
        directories.extend(relative.ancestors().skip(1).map(Path::to_path_buf));
    }
    let mut directories = directories.into_iter().collect::<Vec<_>>();
    directories.sort_by_key(|path| Reverse(path.components().count()));
    for relative in directories {
        let path = rust_source.join(relative);
        match fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.file_type().is_dir() => set_modified_to_epoch(&path)?,
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!("cannot inspect {}: {error}", render_path(&path)));
            }
        }
    }
    Ok(())
}

fn compiler_build_identity(
    repository_root: &Path,
    rust_source: &Path,
) -> Result<(PathBuf, String), String> {
    let patched_revision = read_trimmed(repository_root.join("rustc-patches/patched-revision"))?;
    let queue_digest = read_trimmed(repository_root.join("rustc-patches/queue-digest"))?;
    Ok((
        rust_source.join("build").join(COMPILER_BUILD_IDENTITY_FILE),
        format!("{patched_revision}\n{queue_digest}\n"),
    ))
}

fn compiler_build_identity_matches(
    repository_root: &Path,
    rust_source: &Path,
) -> Result<bool, String> {
    let (path, expected) = compiler_build_identity(repository_root, rust_source)?;
    match fs::read_to_string(&path) {
        Ok(actual) => Ok(actual == expected),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!("cannot read {}: {error}", render_path(&path))),
    }
}

fn record_compiler_build_identity(
    repository_root: &Path,
    rust_source: &Path,
) -> Result<(), String> {
    let (path, identity) = compiler_build_identity(repository_root, rust_source)?;
    fs::write(&path, identity)
        .map_err(|error| format!("cannot write {}: {error}", render_path(&path)))
}

fn remove_compiler_build_identity(rust_source: &Path) -> Result<(), String> {
    let path = rust_source.join("build").join(COMPILER_BUILD_IDENTITY_FILE);
    match fs::remove_file(&path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("cannot remove {}: {error}", render_path(&path))),
    }
}

fn set_modified_to_epoch(path: &Path) -> Result<(), String> {
    fs::set_times(path, FileTimes::new().set_modified(SystemTime::UNIX_EPOCH)).map_err(|error| {
        format!(
            "cannot normalize the modification time of {}: {error}",
            render_path(path)
        )
    })
}

fn build_compiler(repository_root: &Path, rust_source: &Path) -> Result<(), String> {
    eprintln!("Preparing the patched Rust compiler. This takes a while on the first run.");
    let mut command = bootstrap_command(repository_root, rust_source)?;
    command.args([
        "build",
        "--ci=false",
        "--stage",
        "2",
        "compiler/rustc",
        "library",
    ]);
    run_command(&mut command, "build the patched Rust compiler")
}

fn prepare_target_metadata(
    repository_root: &Path,
    rust_source: &Path,
    target: &str,
) -> Result<(), String> {
    eprintln!("Preparing Rust metadata for {target}.");
    let mut command = bootstrap_command(repository_root, rust_source)?;
    command
        .args([
            "check",
            "--ci=false",
            "--stage",
            "2",
            "--target",
            target,
            "rid-target-metadata",
        ])
        .stdin(Stdio::null());
    run_command(&mut command, &format!("prepare Rust metadata for {target}"))
}

fn bootstrap_command(repository_root: &Path, rust_source: &Path) -> Result<Command, String> {
    let queue_digest = read_trimmed(repository_root.join("rustc-patches/queue-digest"))?;
    let (python, prefix_arguments) = find_python()?;
    let mut command = Command::new(python);
    command
        .args(prefix_arguments)
        .arg(rust_source.join("x.py"))
        .current_dir(rust_source)
        .env("RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST", queue_digest)
        .env("CARGOFLAGS", BOOTSTRAP_CARGO_FLAGS)
        .env_remove("CARGOFLAGS_BOOTSTRAP")
        .env_remove("CARGOFLAGS_NOT_BOOTSTRAP")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    Ok(command)
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
        OsString::from("-C"),
        OsString::from("prefer-dynamic"),
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
    let _parent_lock = lock_exclusive(&parent.join(SNAPSHOT_PARENT_LOCK_FILE))?;
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

#[cfg(test)]
mod target_tests {
    use super::*;

    #[test]
    fn compiler_build_identity_must_match_both_patch_inputs() {
        let directory = TestDirectory::new();
        let repository_root = directory.path();
        let rust_source = repository_root.join("rust-source");
        fs::create_dir_all(repository_root.join("rustc-patches")).unwrap();
        fs::create_dir_all(rust_source.join("build")).unwrap();
        fs::write(
            repository_root.join("rustc-patches/patched-revision"),
            "revision\n",
        )
        .unwrap();
        fs::write(
            repository_root.join("rustc-patches/queue-digest"),
            "digest\n",
        )
        .unwrap();

        assert!(!compiler_build_identity_matches(repository_root, &rust_source).unwrap());
        record_compiler_build_identity(repository_root, &rust_source).unwrap();
        assert!(compiler_build_identity_matches(repository_root, &rust_source).unwrap());

        fs::write(
            repository_root.join("rustc-patches/queue-digest"),
            "changed\n",
        )
        .unwrap();
        assert!(!compiler_build_identity_matches(repository_root, &rust_source).unwrap());

        fs::write(
            repository_root.join("rustc-patches/queue-digest"),
            "digest\n",
        )
        .unwrap();
        fs::write(
            repository_root.join("rustc-patches/patched-revision"),
            "changed\n",
        )
        .unwrap();
        assert!(!compiler_build_identity_matches(repository_root, &rust_source).unwrap());
    }

    #[test]
    fn cached_build_normalizes_tracked_files_and_ancestor_directories() {
        let directory = TestDirectory::new();
        run_command(
            Command::new("git")
                .args(["init", "-q"])
                .arg(directory.path()),
            "initialize test repository",
        )
        .unwrap();
        let tracked_directory = directory.path().join("crate/src");
        let untracked_directory = directory.path().join("untracked");
        fs::create_dir_all(&tracked_directory).unwrap();
        fs::create_dir(&untracked_directory).unwrap();
        let crate_directory = directory.path().join("crate");
        let tracked = tracked_directory.join("lib.rs");
        let untracked = untracked_directory.join("data.rs");
        fs::write(&tracked, "pub fn tracked() {}\n").unwrap();
        fs::write(&untracked, "pub fn untracked() {}\n").unwrap();
        run_command(
            Command::new("git")
                .args(["-C"])
                .arg(directory.path())
                .args(["add", "crate/src/lib.rs"]),
            "index test source",
        )
        .unwrap();
        let untracked_time = SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(10);
        for path in [
            directory.path(),
            crate_directory.as_path(),
            tracked_directory.as_path(),
            tracked.as_path(),
            untracked_directory.as_path(),
            untracked.as_path(),
        ] {
            fs::set_times(path, FileTimes::new().set_modified(untracked_time)).unwrap();
        }

        normalize_tracked_source_mtimes(directory.path()).unwrap();

        for path in [
            directory.path(),
            crate_directory.as_path(),
            tracked_directory.as_path(),
            tracked.as_path(),
        ] {
            assert_eq!(
                fs::metadata(path).unwrap().modified().unwrap(),
                SystemTime::UNIX_EPOCH
            );
        }
        for path in [untracked_directory.as_path(), untracked.as_path()] {
            assert_eq!(
                fs::metadata(path).unwrap().modified().unwrap(),
                untracked_time
            );
        }
    }

    #[test]
    fn bootstrap_uses_checksum_freshness_without_inherited_cargo_flags() {
        let repository_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let command = bootstrap_command(repository_root, Path::new("rust-source")).unwrap();
        let configured = command.get_envs().collect::<Vec<_>>();

        assert!(configured.contains(&(
            OsStr::new("CARGOFLAGS"),
            Some(OsStr::new(BOOTSTRAP_CARGO_FLAGS)),
        )));
        assert!(configured.contains(&(OsStr::new("CARGOFLAGS_BOOTSTRAP"), None)));
        assert!(configured.contains(&(OsStr::new("CARGOFLAGS_NOT_BOOTSTRAP"), None)));
    }

    #[test]
    fn direct_target_requires_an_unambiguous_leading_argument() {
        assert_eq!(
            direct_builtin_target_candidate(&arguments(&[
                "--target",
                "wasm32-unknown-unknown",
                "input.rs",
            ])),
            Some("wasm32-unknown-unknown")
        );
        assert_eq!(
            direct_builtin_target_candidate(&arguments(&["--target=wasm32-unknown-unknown", "-",])),
            Some("wasm32-unknown-unknown")
        );

        for rejected in [
            arguments(&["input.rs", "--target", "wasm32-unknown-unknown"]),
            arguments(&["--crate-name", "--target=wasm32-unknown-unknown"]),
            arguments(&["--target"]),
            arguments(&["--target", ""]),
            arguments(&["--target="]),
            arguments(&[
                "--target=wasm32-unknown-unknown",
                "--target=wasm32-unknown-unknown",
            ]),
            arguments(&[
                "--target",
                "wasm32-unknown-unknown",
                "--target",
                "x86_64-unknown-linux-gnu",
            ]),
            arguments(&["--target=wasm32-unknown-unknown", "@arguments"]),
            arguments(&["--target=wasm32-unknown-unknown", "--sysroot", "custom"]),
            arguments(&["--target=wasm32-unknown-unknown", "--sysroot=custom"]),
            arguments(&["--target=wasm32-unknown-unknown", "--", "input.rs"]),
        ] {
            assert_eq!(direct_builtin_target_candidate(&rejected), None);
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_rustc_arguments_are_not_rewritten() {
        use std::os::unix::ffi::OsStringExt;

        let arguments = vec![
            OsString::from("--target=wasm32-unknown-unknown"),
            OsString::from_vec(vec![0xff]),
        ];
        assert_eq!(direct_builtin_target_candidate(&arguments), None);
    }

    #[cfg(windows)]
    #[test]
    fn non_utf8_rustc_arguments_are_not_rewritten() {
        use std::os::windows::ffi::OsStringExt;

        let arguments = vec![
            OsString::from("--target=wasm32-unknown-unknown"),
            OsString::from_wide(&[0xd800]),
        ];
        assert_eq!(direct_builtin_target_candidate(&arguments), None);
    }

    #[test]
    fn target_search_paths_do_not_enable_native_library_search() {
        let source = TargetLibrarySource::GeneratedMetadata(PathBuf::from("metadata"));
        assert_eq!(
            target_library_search_arguments(Some(&source)),
            vec![
                OsString::from("-L"),
                OsString::from("crate=metadata"),
                OsString::from("-L"),
                OsString::from("dependency=metadata"),
            ]
        );
        assert!(
            target_library_search_arguments(Some(&TargetLibrarySource::InstalledSysroot))
                .is_empty()
        );
        assert!(target_library_search_arguments(None).is_empty());
    }

    fn arguments(arguments: &[&str]) -> Vec<OsString> {
        arguments.iter().map(OsString::from).collect()
    }
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
}

#[cfg(test)]
struct TestDirectory(PathBuf);

#[cfg(test)]
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

#[cfg(test)]
impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
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
