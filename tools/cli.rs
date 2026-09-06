use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

pub fn reducer_usage(command: &str) -> String {
    format!(
        r#"{command}

Cargo project options (when INPUT.rs is omitted):
  -p, --package SPEC      Select a workspace package
      --bin NAME         Select a binary target
      --manifest-path PATH
      --features FEATURES, --all-features, --no-default-features
      --release, --profile NAME, --target TRIPLE, --target-dir PATH
      --locked, --offline, --frozen, --config KEY=VALUE, --jobs N

Standalone file options:
  -o, --output OUTPUT    Write to a new file instead of updating INPUT.rs
      --edition YEAR     Rust edition: 2015, 2018, 2021, or 2024 [default: 2024]
      --target TRIPLE    Compilation target [default: compiler host]
      --crate-type TYPE  Crate type: bin or lib [default: bin]
      --crate-name NAME  Crate name [default: main]
      --entry PATH       Preserve a fully qualified function or static; may be repeated
  -O                     Same as --opt-level 3
      --opt-level LEVEL  Optimization level: 0, 1, 2, 3, s, or z [default: 0]
      --cfg NAME         Enable a name-only cfg; may be repeated
      --extern NAME=PATH Add a direct Rust dependency; may be repeated
      --dependency-artifact PATH
                         Add a transitive Rust dependency; may be repeated
      --allow-proc-macro PATH
                         Permit a declared procedural macro; may be repeated
  -h, --help             Print help"#
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CliEdition {
    Rust2015,
    Rust2018,
    Rust2021,
    Rust2024,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CliOptimizationLevel {
    O0,
    O1,
    O2,
    O3,
    Size,
    SizeMin,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CliCrateType {
    Binary,
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
pub struct ProjectCli {
    pub manifest: Option<PathBuf>,
    pub package: Option<OsString>,
    pub bin: Option<OsString>,
    pub cargo_options: Vec<OsString>,
    pub metadata_options: Vec<OsString>,
    pub common_options: Vec<OsString>,
    pub target_directory: Option<PathBuf>,
}

pub fn parse_arguments(
    arguments: impl IntoIterator<Item = OsString>,
    usage: &str,
) -> Result<Parsed, String> {
    let mut arguments: Box<dyn Iterator<Item = OsString>> =
        Box::new(arguments.into_iter().collect::<Vec<_>>().into_iter());
    let mut project = ProjectCli::default();
    let mut standalone_option = false;
    let mut project_option = false;
    let mut input = None;
    let mut output = None;
    let mut edition = CliEdition::Rust2024;
    let mut target = None;
    let mut repeated_target = false;
    let mut crate_type = CliCrateType::Binary;
    let mut crate_name = "main".to_owned();
    let mut entry_points = Vec::new();
    let mut optimization_level = CliOptimizationLevel::O0;
    let mut cfg_names = Vec::new();
    let mut external_crates = Vec::new();
    let mut dependency_artifacts = Vec::new();
    let mut allowed_proc_macro_artifacts = Vec::new();
    let mut positional_only = false;

    while let Some(mut argument) = arguments.next() {
        if !positional_only {
            if let Some((name, value)) = argument
                .to_str()
                .filter(|value| value.starts_with("--"))
                .and_then(|value| value.split_once('='))
            {
                let name = OsString::from(name);
                let value = OsString::from(value);
                arguments = Box::new(std::iter::once(value).chain(arguments));
                argument = name;
            }
            if let Some(name) = argument.to_str() {
                match name {
                    "--manifest-path" | "-p" | "--package" | "--bin" => {
                        project_option = true;
                        let value = next_value(&mut arguments, name)?;
                        let previous = match name {
                            "--manifest-path" => project.manifest.replace(value.into()).is_some(),
                            "--bin" => project.bin.replace(value).is_some(),
                            _ => project.package.replace(value).is_some(),
                        };
                        if previous {
                            return Err(format!("{name} may only be specified once"));
                        }
                        continue;
                    }
                    "--features" | "-F" | "--profile" | "--target-dir" | "--config" | "-j"
                    | "--jobs" => {
                        project_option = true;
                        let value = next_value(&mut arguments, name)?;
                        if name == "--profile"
                            && ["test", "bench", "check"]
                                .iter()
                                .any(|profile| value == *profile)
                        {
                            return Err("cargo rid reduces ordinary binaries; test, bench, and check profiles are unsupported".to_owned());
                        }
                        if name == "--target-dir"
                            && project
                                .target_directory
                                .replace(PathBuf::from(&value))
                                .is_some()
                        {
                            return Err("--target-dir may only be specified once".to_owned());
                        }
                        if name == "--config" {
                            project.common_options.extend([argument, value]);
                            continue;
                        }
                        if matches!(name, "--features" | "-F") {
                            project
                                .metadata_options
                                .extend([argument.clone(), value.clone()]);
                        }
                        project.cargo_options.extend([argument, value]);
                        continue;
                    }
                    "--all-features"
                    | "--no-default-features"
                    | "--locked"
                    | "--offline"
                    | "--frozen"
                    | "--release"
                    | "-r"
                    | "--verbose"
                    | "-v"
                    | "--quiet"
                    | "-q" => {
                        project_option = true;
                        if matches!(name, "--locked" | "--offline" | "--frozen") {
                            project.common_options.push(argument);
                            continue;
                        }
                        if matches!(name, "--all-features" | "--no-default-features") {
                            project.metadata_options.push(argument.clone());
                        }
                        project.cargo_options.push(argument);
                        continue;
                    }
                    "--target" | "-h" | "--help" | "--" => {}
                    _ if name.starts_with('-') => standalone_option = true,
                    _ => {}
                }
            }
            match argument.to_str() {
                Some("-h" | "--help") => return Ok(Parsed::Help),
                Some("--") => {
                    positional_only = true;
                    continue;
                }
                Some("-o" | "--output") => {
                    output = Some(next_value(&mut arguments, "--output")?.into());
                    continue;
                }
                Some("--edition") => {
                    edition = parse_edition(next_utf8(&mut arguments, "--edition")?)?;
                    continue;
                }
                Some("--target") => {
                    let value = next_utf8(&mut arguments, "--target")?;
                    if value.is_empty() {
                        return Err("--target requires a nonempty value".to_owned());
                    }
                    repeated_target |= target.replace(value).is_some();
                    continue;
                }
                Some("--crate-type") => {
                    crate_type = parse_crate_type(next_utf8(&mut arguments, "--crate-type")?)?;
                    continue;
                }
                Some("--crate-name") => {
                    crate_name = next_utf8(&mut arguments, "--crate-name")?;
                    continue;
                }
                Some("--entry") => {
                    entry_points.push(next_utf8(&mut arguments, "--entry")?);
                    continue;
                }
                Some("-O") => {
                    optimization_level = CliOptimizationLevel::O3;
                    continue;
                }
                Some("--opt-level") => {
                    optimization_level =
                        parse_optimization_level(next_utf8(&mut arguments, "--opt-level")?)?;
                    continue;
                }
                Some("--cfg") => {
                    cfg_names.push(next_utf8(&mut arguments, "--cfg")?);
                    continue;
                }
                Some("--extern") => {
                    external_crates.push(parse_external_crate(next_value(
                        &mut arguments,
                        "--extern",
                    )?)?);
                    continue;
                }
                Some("--dependency-artifact") => {
                    let artifact = next_value(&mut arguments, "--dependency-artifact")?;
                    if artifact.is_empty() {
                        return Err("--dependency-artifact requires a nonempty path".to_owned());
                    }
                    dependency_artifacts.push(artifact.into());
                    continue;
                }
                Some("--allow-proc-macro") => {
                    let artifact = next_value(&mut arguments, "--allow-proc-macro")?;
                    if artifact.is_empty() {
                        return Err("--allow-proc-macro requires a nonempty path".to_owned());
                    }
                    allowed_proc_macro_artifacts.push(artifact.into());
                    continue;
                }
                Some(value) if value.starts_with('-') => {
                    return Err(format!("unknown option: {value}\n\n{usage}"));
                }
                _ => {}
            }
        }

        if input.replace(PathBuf::from(argument)).is_some() {
            return Err(format!("expected exactly one input file\n\n{usage}"));
        }
    }

    let Some(input) = input else {
        if repeated_target {
            return Err("cargo rid requires a single --target".to_owned());
        }
        if standalone_option {
            return Err(format!(
                "standalone compiler options require an input file\n\n{usage}"
            ));
        }
        if let Some(target) = target {
            project
                .cargo_options
                .extend(["--target".into(), target.into()]);
        }
        return Ok(Parsed::Project(project));
    };
    if project_option {
        return Err(
            "Cargo project options cannot be combined with a standalone input file".to_owned(),
        );
    }
    Ok(Parsed::Run(Box::new(Cli {
        input,
        output,
        edition,
        target,
        crate_type,
        crate_name,
        entry_points,
        optimization_level,
        cfg_names,
        external_crates,
        dependency_artifacts,
        allowed_proc_macro_artifacts,
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

fn next_value(
    arguments: &mut impl Iterator<Item = OsString>,
    option: &str,
) -> Result<OsString, String> {
    arguments
        .next()
        .ok_or_else(|| format!("{option} requires a value"))
}

fn next_utf8(
    arguments: &mut impl Iterator<Item = OsString>,
    option: &str,
) -> Result<String, String> {
    next_value(arguments, option)?
        .into_string()
        .map_err(|_| format!("{option} requires a UTF-8 value"))
}

fn parse_edition(value: String) -> Result<CliEdition, String> {
    match value.as_str() {
        "2015" => Ok(CliEdition::Rust2015),
        "2018" => Ok(CliEdition::Rust2018),
        "2021" => Ok(CliEdition::Rust2021),
        "2024" => Ok(CliEdition::Rust2024),
        _ => Err(format!("unsupported Rust edition: {value}")),
    }
}

fn parse_optimization_level(value: String) -> Result<CliOptimizationLevel, String> {
    match value.as_str() {
        "0" => Ok(CliOptimizationLevel::O0),
        "1" => Ok(CliOptimizationLevel::O1),
        "2" => Ok(CliOptimizationLevel::O2),
        "3" => Ok(CliOptimizationLevel::O3),
        "s" => Ok(CliOptimizationLevel::Size),
        "z" => Ok(CliOptimizationLevel::SizeMin),
        _ => Err(format!(
            "unsupported optimization level: {value}; expected 0, 1, 2, 3, s, or z"
        )),
    }
}

fn parse_crate_type(value: String) -> Result<CliCrateType, String> {
    match value.as_str() {
        "bin" => Ok(CliCrateType::Binary),
        "lib" => Ok(CliCrateType::Library),
        _ => Err(format!(
            "unsupported crate type: {value}; expected bin or lib"
        )),
    }
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
