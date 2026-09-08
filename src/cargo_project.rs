use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::Command;

use cargo_metadata::{MetadataCommand, PackageId};
use serde::{Deserialize, Serialize};

use crate::cli::ProjectCli;
use crate::file_output::SourceFile;

const ADAPTER_CONFIG: &str = "RUST_ITEM_DEPENDENCIES_ADAPTER_CONFIG";
const REDUCE_MARKER: &str = "--rust-item-dependencies-reduce-bin";
const LAUNCHER: &str = "RUST_ITEM_DEPENDENCIES_LAUNCHER";

#[derive(Deserialize, Serialize)]
struct AdapterConfig {
    manifest: PathBuf,
    bin: String,
    source_path: PathBuf,
    source: String,
    result: PathBuf,
}

pub(crate) fn run_internal(arguments: &[OsString]) -> Option<Result<(), String>> {
    if let Some(config) = std::env::var_os(ADAPTER_CONFIG) {
        return Some(adapter(arguments, Path::new(&config)));
    }
    None
}

pub(crate) fn reduce(cli: ProjectCli) -> Result<(), String> {
    let mut metadata_command = MetadataCommand::new();
    metadata_command.cargo_path(cargo().get_program());
    metadata_command.no_deps().other_options(
        cli.common_options
            .iter()
            .chain(&cli.metadata_options)
            .cloned()
            .collect::<Vec<_>>(),
    );
    if let Some(manifest) = &cli.manifest {
        metadata_command.manifest_path(manifest);
    }
    if let Some(directory) = &cli.target_directory {
        metadata_command.env("CARGO_TARGET_DIR", directory);
    }
    let metadata = metadata_command
        .exec()
        .map_err(|error| format!("cannot read Cargo metadata: {error}"))?;
    if metadata.workspace_default_members.is_missing() {
        return Err("Cargo metadata did not report default workspace members".to_owned());
    }
    let members = if let Some(package) = &cli.package {
        let mut command = cargo();
        command.args(["pkgid", "--package"]).arg(package);
        with_manifest(&mut command, &cli);
        command.args(&cli.common_options);
        let output = command
            .output()
            .map_err(|error| format!("cannot select Cargo package: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "Cargo package selection failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let repr = String::from_utf8(output.stdout)
            .map_err(|error| error.to_string())?
            .trim()
            .to_owned();
        let id = PackageId { repr };
        if !metadata.workspace_members.contains(&id) {
            return Err("the selected package is not a workspace member".to_owned());
        }
        vec![id]
    } else {
        metadata.workspace_default_members.to_vec()
    };
    let candidates = metadata
        .packages
        .iter()
        .filter(|package| members.contains(&package.id))
        .flat_map(|package| package.targets.iter().map(move |target| (package, target)))
        .filter(|(_, target)| target.is_bin())
        .filter(|(_, target)| {
            cli.bin
                .as_ref()
                .is_none_or(|bin| bin == OsStr::new(&target.name))
        })
        .collect::<Vec<_>>();
    let [(package, target)] = candidates.as_slice() else {
        return Err("select exactly one workspace binary with --package and/or --bin".to_owned());
    };
    let original = SourceFile::read(target.src_path.as_std_path())
        .map_err(|error| format!("cannot update {}: {error}", target.src_path))?;
    let temporary_parent = metadata.target_directory.join("rid");
    fs::create_dir_all(&temporary_parent).map_err(|error| error.to_string())?;
    let temporary = tempfile::Builder::new()
        .prefix("invocation-")
        .tempdir_in(temporary_parent)
        .map_err(|error| error.to_string())?;
    let config = AdapterConfig {
        manifest: package.manifest_path.clone().into_std_path_buf(),
        bin: target.name.clone(),
        source_path: target.src_path.clone().into_std_path_buf(),
        source: original.source().to_owned(),
        result: temporary.path().join("reduced.rs"),
    };
    let config_path = temporary.path().join("adapter.json");
    write_json_new(&config_path, &config)?;
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let mut command = cargo();
    command
        .args(["rustc", "--package"])
        .arg(&package.id.repr)
        .arg("--bin")
        .arg(&target.name)
        .env("RUSTC", &executable)
        .env("RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT", temporary.path())
        .env(ADAPTER_CONFIG, &config_path);
    with_manifest(&mut command, &cli);
    command
        .args(&cli.common_options)
        .args(&cli.cargo_options)
        .args(["--", REDUCE_MARKER]);
    let status = command
        .status()
        .map_err(|error| format!("cannot run Cargo: {error}"))?;
    if !status.success() {
        return Err(format!("Cargo failed: {status}"));
    }
    let reduced = fs::read_to_string(&config.result)
        .map_err(|error| format!("Cargo did not reduce the selected binary: {error}"))?;
    original
        .replace(&reduced)
        .map_err(|error| format!("cannot update {}: {error}", target.src_path))
}

fn adapter(arguments: &[OsString], config: &Path) -> Result<(), String> {
    let diagnostics = rustc_session::EarlyDiagCtxt::new(Default::default());
    let raw_arguments = arguments
        .iter()
        .map(|argument| {
            argument
                .clone()
                .into_string()
                .map_err(|_| "non-Unicode rustc argument".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let arguments = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::args::arg_expand_all(&diagnostics, &raw_arguments)
    })
    .map_err(|_| "cannot expand compiler response files".to_owned())?;
    if !arguments.iter().any(|argument| argument == REDUCE_MARKER) {
        let mut raw = vec!["rustc".to_owned()];
        raw.extend(raw_arguments);
        return rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(&raw, &mut TargetPreparation)
        })
        .map_err(|_| "rustc compilation failed".to_owned());
    }
    if arguments
        .iter()
        .filter(|argument| *argument == REDUCE_MARKER)
        .count()
        != 1
    {
        return Err("Cargo passed the selected binary reduction marker more than once".to_owned());
    }
    let arguments = arguments
        .into_iter()
        .filter(|argument| argument != REDUCE_MARKER)
        .collect::<Vec<_>>();
    let parsed = rustc_driver::catch_fatal_errors(|| {
        let mut diagnostics = rustc_session::EarlyDiagCtxt::new(Default::default());
        match rustc_driver::handle_options(&diagnostics, &arguments) {
            rustc_driver::HandledOptions::Normal(matches) => {
                let options =
                    rustc_session::config::build_session_options(&mut diagnostics, &matches);
                Some((matches.free, options))
            }
            _ => None,
        }
    })
    .map_err(|_| "invalid compiler invocation".to_owned())?;
    let Some((inputs, options)) = parsed else {
        return Err("the selected target invocation was not a compilation".to_owned());
    };
    let target_libraries = prepare_target(&options)?;
    {
        let config: AdapterConfig = read_json(config)?;
        if std::env::var_os("CARGO_MANIFEST_PATH").as_deref() != Some(config.manifest.as_os_str())
            || std::env::var("CARGO_BIN_NAME").as_deref() != Ok(&config.bin)
            || inputs.len() != 1
            || fs::canonicalize(&inputs[0]).map_err(|error| error.to_string())?
                != fs::canonicalize(&config.source_path).map_err(|error| error.to_string())?
        {
            return Err("Cargo invoked a different target than the selected binary".to_owned());
        }
        let arguments = target_libraries
            .iter()
            .flat_map(|libraries| libraries.search_paths())
            .flat_map(|(kind, path)| ["-L".to_owned(), format!("{kind}={}", path.display())])
            .chain(arguments)
            .collect();
        let reduction = rust_item_dependencies::CompilerInvocation::new(config.source, arguments)
            .reduce()
            .map_err(crate::render_analysis_error)?;
        crate::file_output::write_new(&config.result, reduction.reduced_source())
            .map_err(|error| format!("cannot record the selected binary reduction: {error}"))
    }
}

struct TargetPreparation;

impl rustc_driver::Callbacks for TargetPreparation {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        let sysroot = option_env!("RUST_ITEM_DEPENDENCIES_BUILD_SYSROOT")
            .map(PathBuf::from)
            .unwrap_or_else(|| config.opts.sysroot.default.clone());
        config.opts.sysroot.default = sysroot;
        let libraries = prepare_target(&config.opts).unwrap_or_else(|error| {
            rustc_session::EarlyDiagCtxt::new(Default::default()).early_fatal(error)
        });
        if let Some(libraries) = libraries {
            for (kind, path) in libraries
                .search_paths()
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                let kind = if kind == "crate" {
                    rustc_session::search_paths::PathKind::Crate
                } else {
                    rustc_session::search_paths::PathKind::Dependency
                };
                config.opts.search_paths.insert(
                    0,
                    rustc_session::search_paths::SearchPath {
                        kind,
                        dir: path.into(),
                    },
                );
            }
        }
    }
}

fn prepare_target(
    options: &rustc_session::config::Options,
) -> Result<Option<crate::target_libraries::TargetLibrarySource>, String> {
    let target = options.target_triple.tuple();
    if target == rustc_session::config::host_tuple() {
        return Ok(None);
    }
    let sysroot = PathBuf::from(
        option_env!("RUST_ITEM_DEPENDENCIES_BUILD_SYSROOT")
            .ok_or("the patched compiler is required")?,
    );
    if options
        .sysroot
        .explicit
        .as_ref()
        .is_some_and(|explicit| fs::canonicalize(explicit).ok() != fs::canonicalize(&sysroot).ok())
    {
        return Err("cross compilation uses a different compiler sysroot".to_owned());
    }
    let installed = rustc_session::filesearch::make_target_lib_path(&sysroot, target);
    let generated = crate::target_libraries::target_metadata_directory(&sysroot, target)
        .ok_or("cannot locate target libraries")?;
    let ready = || {
        crate::target_libraries::select_ready_target_libraries(&installed, &generated, false)
            .map_err(|error| error.to_string())
    };
    if ready()?.is_none() {
        let launcher = std::env::var_os(LAUNCHER)
            .ok_or("target libraries are missing; run cargo rid through the installed launcher")?;
        let status = Command::new(launcher)
            .args(["--rust-item-dependencies-prepare-target", target])
            .env_remove(ADAPTER_CONFIG)
            .status()
            .map_err(|error| format!("cannot prepare target libraries: {error}"))?;
        if !status.success() {
            return Err(format!("target library preparation failed: {status}"));
        }
    }
    let libraries = ready()?.ok_or("target library preparation produced no usable libraries")?;
    Ok(Some(libraries))
}

fn cargo() -> Command {
    Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
}

fn with_manifest(command: &mut Command, cli: &ProjectCli) {
    if let Some(manifest) = &cli.manifest {
        command.arg("--manifest-path").arg(manifest);
    }
}

fn write_json_new(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let file = options
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    serde_json::to_writer(file, value)
        .map_err(|error| format!("cannot record compiler invocation: {error}"))
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, String> {
    let file =
        fs::File::open(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    serde_json::from_reader(file)
        .map_err(|error| format!("invalid compiler invocation record: {error}"))
}
