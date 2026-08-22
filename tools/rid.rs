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
    run_command(&mut command, "run rust-item-dependencies")
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
