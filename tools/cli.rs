use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use clap::{Args, CommandFactory, FromArgMatches, Parser, ValueEnum};

pub fn reducer_usage(command: &str) -> String {
    let help = Arguments::command()
        .help_template("{all-args}")
        .render_help();
    format!("{command}\n\n{help}")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum CliEdition {
    #[value(name = "2015")]
    Rust2015,
    #[value(name = "2018")]
    Rust2018,
    #[value(name = "2021")]
    Rust2021,
    #[value(name = "2024")]
    Rust2024,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum CliOptimizationLevel {
    #[value(name = "0")]
    O0,
    #[value(name = "1")]
    O1,
    #[value(name = "2")]
    O2,
    #[value(name = "3")]
    O3,
    #[value(name = "s")]
    Size,
    #[value(name = "z")]
    SizeMin,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum CliCrateType {
    #[value(name = "bin")]
    Binary,
    #[value(name = "lib")]
    Library,
}

#[derive(Debug, Eq, PartialEq)]
pub struct CliExternalCrate {
    pub extern_name: String,
    pub artifact: PathBuf,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Cli {
    pub input: PathBuf,
    pub output: Option<PathBuf>,
    pub edition: CliEdition,
    pub target: Option<String>,
    pub crate_type: CliCrateType,
    pub crate_name: String,
    pub entry_points: Vec<String>,
    pub optimization_level: CliOptimizationLevel,
    pub cfg_names: Vec<String>,
    pub external_crates: Vec<CliExternalCrate>,
    pub dependency_artifacts: Vec<PathBuf>,
    pub allowed_proc_macro_artifacts: Vec<PathBuf>,
}

#[derive(Debug)]
pub enum Parsed {
    Run(Box<Cli>),
    // The launcher validates this variant; only the reducer consumes the payload.
    #[allow(dead_code)]
    Project(ProjectCli),
    Help,
}

#[derive(Debug, Default)]
// These fields are consumed by the reducer after the launcher validates them.
#[allow(dead_code)]
pub struct ProjectCli {
    pub manifest: Option<PathBuf>,
    pub package: Option<OsString>,
    pub bin: Option<OsString>,
    pub cargo_options: Vec<OsString>,
    pub metadata_options: Vec<String>,
    pub common_options: Vec<String>,
    pub target_directory: Option<PathBuf>,
}

#[derive(Parser)]
#[command(name = "cargo rid", no_binary_name = true, term_width = 0)]
struct Arguments {
    /// Source file to update; omit to select a Cargo binary
    #[arg(value_name = "INPUT.rs")]
    input: Option<PathBuf>,
    /// Compilation target [default: compiler host or Cargo configuration]
    #[arg(long, value_name = "TRIPLE", value_parser = clap::builder::NonEmptyStringValueParser::new())]
    target: Vec<String>,
    #[command(
        flatten,
        next_help_heading = "Cargo project options (when INPUT.rs is omitted)"
    )]
    project: ProjectArguments,
    #[command(flatten, next_help_heading = "Standalone file options")]
    standalone: StandaloneArguments,
}

#[derive(Args)]
#[group(id = "project", multiple = true, conflicts_with = "input")]
struct ProjectArguments {
    /// Select a workspace package
    #[arg(short = 'p', long, value_name = "SPEC")]
    package: Option<OsString>,
    /// Select a binary target
    #[arg(long, value_name = "NAME")]
    bin: Option<OsString>,
    #[arg(long, value_name = "PATH")]
    manifest_path: Option<PathBuf>,
    #[arg(short = 'F', long, value_name = "FEATURES")]
    features: Vec<String>,
    #[arg(long)]
    all_features: bool,
    #[arg(long)]
    no_default_features: bool,
    #[arg(short = 'r', long)]
    release: bool,
    #[arg(long, value_name = "NAME")]
    profile: Option<OsString>,
    #[arg(long, value_name = "PATH")]
    target_dir: Option<PathBuf>,
    #[arg(long)]
    locked: bool,
    #[arg(long)]
    offline: bool,
    #[arg(long)]
    frozen: bool,
    #[arg(long, value_name = "KEY=VALUE|PATH")]
    config: Vec<String>,
    #[arg(short = 'j', long, value_name = "N", allow_negative_numbers = true)]
    jobs: Option<OsString>,
    #[arg(short = 'v', long, action = clap::ArgAction::Count)]
    verbose: u8,
    #[arg(short = 'q', long)]
    quiet: bool,
}

#[derive(Args)]
#[group(id = "standalone", multiple = true, requires = "input")]
struct StandaloneArguments {
    /// Write to a new file instead of updating INPUT.rs
    #[arg(short = 'o', long, value_name = "OUTPUT", overrides_with = "output")]
    output: Option<PathBuf>,
    /// Rust edition [default: 2024]
    #[arg(long, value_name = "YEAR", overrides_with = "edition")]
    edition: Option<CliEdition>,
    /// Crate type [default: bin]
    #[arg(long, value_name = "TYPE", overrides_with = "crate_type")]
    crate_type: Option<CliCrateType>,
    /// Crate name [default: main]
    #[arg(long, value_name = "NAME", overrides_with = "crate_name")]
    crate_name: Option<String>,
    /// Preserve a fully qualified function or static; may be repeated
    #[arg(long, value_name = "PATH")]
    entry: Vec<String>,
    /// Same as --opt-level 3
    #[arg(short = 'O', overrides_with_all = ["opt_level", "optimize"])]
    optimize: bool,
    /// Optimization level [default: 0]
    #[arg(long, value_name = "LEVEL", overrides_with_all = ["optimize", "opt_level"])]
    opt_level: Option<CliOptimizationLevel>,
    /// Enable a name-only cfg; may be repeated
    #[arg(long, value_name = "NAME")]
    cfg: Vec<String>,
    /// Add a direct Rust dependency; may be repeated
    #[arg(long = "extern", value_name = "NAME=PATH")]
    external: Vec<OsString>,
    /// Add a transitive Rust dependency; may be repeated
    #[arg(long, value_name = "PATH")]
    dependency_artifact: Vec<PathBuf>,
    /// Permit a declared procedural macro; may be repeated
    #[arg(long, value_name = "PATH")]
    allow_proc_macro: Vec<PathBuf>,
}

pub fn parse_arguments(
    arguments: impl IntoIterator<Item = OsString>,
    usage: &str,
) -> Result<Parsed, String> {
    let Arguments {
        input,
        mut target,
        project,
        standalone,
    } = match Arguments::command()
        .override_usage(usage.strip_prefix("Usage: ").unwrap_or(usage).to_owned())
        .try_get_matches_from(arguments)
        .and_then(|matches| Arguments::from_arg_matches(&matches))
    {
        Ok(arguments) => arguments,
        Err(error) if error.kind() == clap::error::ErrorKind::DisplayHelp => {
            return Ok(Parsed::Help);
        }
        Err(error) => {
            return Err(error
                .to_string()
                .trim_start_matches("error: ")
                .trim_end()
                .to_owned());
        }
    };
    let Some(input) = input else {
        if target.len() > 1 {
            return Err("cargo rid requires a single --target".to_owned());
        }
        if project.profile.as_ref().is_some_and(|profile| {
            ["test", "bench", "check"]
                .iter()
                .any(|name| profile == name)
        }) {
            return Err("cargo rid reduces ordinary binaries; test, bench, and check profiles are unsupported".to_owned());
        }
        let mut cli = ProjectCli {
            manifest: project.manifest_path,
            package: project.package,
            bin: project.bin,
            target_directory: project.target_dir.clone(),
            ..ProjectCli::default()
        };
        for feature in project.features {
            cli.metadata_options.extend(["--features".into(), feature]);
        }
        for (option, enabled) in [
            ("--all-features", project.all_features),
            ("--no-default-features", project.no_default_features),
        ] {
            if enabled {
                cli.metadata_options.push(option.into());
            }
        }
        cli.cargo_options
            .extend(cli.metadata_options.iter().map(OsString::from));
        for (option, value) in [
            ("--profile", project.profile),
            ("--target-dir", project.target_dir.map(OsString::from)),
            ("--jobs", project.jobs),
            ("--target", target.pop().map(OsString::from)),
        ] {
            if let Some(value) = value {
                cli.cargo_options.extend([option.into(), value]);
            }
        }
        for (option, enabled) in [("--release", project.release), ("--quiet", project.quiet)] {
            if enabled {
                cli.cargo_options.push(option.into());
            }
        }
        cli.cargo_options.extend(std::iter::repeat_n(
            OsString::from("--verbose"),
            usize::from(project.verbose),
        ));
        for config in project.config {
            cli.common_options.extend(["--config".into(), config]);
        }
        for (option, enabled) in [
            ("--locked", project.locked),
            ("--offline", project.offline),
            ("--frozen", project.frozen),
        ] {
            if enabled {
                cli.common_options.push(option.into());
            }
        }
        return Ok(Parsed::Project(cli));
    };
    let external_crates = standalone
        .external
        .into_iter()
        .map(parse_external_crate)
        .collect::<Result<_, _>>()?;
    Ok(Parsed::Run(Box::new(Cli {
        input,
        output: standalone.output,
        edition: standalone.edition.unwrap_or(CliEdition::Rust2024),
        target: target.pop(),
        crate_type: standalone.crate_type.unwrap_or(CliCrateType::Binary),
        crate_name: standalone.crate_name.unwrap_or_else(|| "main".to_owned()),
        entry_points: standalone.entry,
        optimization_level: if standalone.optimize {
            CliOptimizationLevel::O3
        } else {
            standalone.opt_level.unwrap_or(CliOptimizationLevel::O0)
        },
        cfg_names: standalone.cfg,
        external_crates,
        dependency_artifacts: standalone.dependency_artifact,
        allowed_proc_macro_artifacts: standalone.allow_proc_macro,
    })))
}

pub fn validate_output(cli: &Cli) -> Result<(), String> {
    let Some(output) = &cli.output else {
        return Ok(());
    };
    if same_file(&cli.input, output) {
        return Err("input and output must be different files".to_owned());
    }
    match std::fs::symlink_metadata(output) {
        Ok(_) => Err(format!("output already exists: {}", render_path(output))),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "cannot inspect output {}: {error}",
            render_path(output)
        )),
    }
}

pub fn render_path(path: &Path) -> String {
    format!("{path:?}")
}

fn parse_external_crate(value: OsString) -> Result<CliExternalCrate, String> {
    let bytes = value.as_encoded_bytes();
    let separator = bytes
        .iter()
        .position(|byte| *byte == b'=')
        .ok_or_else(|| "--extern requires NAME=PATH".to_owned())?;
    // SAFETY: both slices come from this OsString and are split immediately around ASCII `=`.
    let (name, artifact) = unsafe {
        (
            OsStr::from_encoded_bytes_unchecked(&bytes[..separator]),
            OsStr::from_encoded_bytes_unchecked(&bytes[separator + 1..]),
        )
    };
    if name.is_empty() {
        return Err("--extern requires a nonempty NAME in NAME=PATH".to_owned());
    }
    let name = name
        .to_str()
        .ok_or_else(|| "--extern requires a UTF-8 NAME in NAME=PATH".to_owned())?;
    if artifact.is_empty() {
        return Err("--extern requires a nonempty PATH in NAME=PATH".to_owned());
    }
    Ok(CliExternalCrate {
        extern_name: name.to_owned(),
        artifact: artifact.into(),
    })
}

fn same_file(input: &std::path::Path, output: &std::path::Path) -> bool {
    input == output
        || std::fs::canonicalize(input)
            .ok()
            .zip(std::fs::canonicalize(output).ok())
            .is_some_and(|(input, output)| input == output)
}
