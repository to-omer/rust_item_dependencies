use std::ffi::OsString;
use std::path::PathBuf;

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

#[derive(Debug, Eq, PartialEq)]
pub struct Cli {
    pub input: PathBuf,
    pub output: PathBuf,
    pub edition: CliEdition,
    pub target: Option<String>,
    pub optimization_level: CliOptimizationLevel,
    pub cfg_names: Vec<String>,
}

#[derive(Debug)]
pub enum Parsed {
    Run(Cli),
    Help,
}

pub fn parse_arguments(
    arguments: impl IntoIterator<Item = OsString>,
    usage: &str,
) -> Result<Parsed, String> {
    let mut arguments = arguments.into_iter();
    let mut input = None;
    let mut output = None;
    let mut edition = CliEdition::Rust2024;
    let mut target = None;
    let mut optimization_level = CliOptimizationLevel::O0;
    let mut cfg_names = Vec::new();
    let mut positional_only = false;

    while let Some(argument) = arguments.next() {
        if !positional_only {
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
                    target = Some(value);
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

    let input = input.ok_or_else(|| format!("missing input file\n\n{usage}"))?;
    let output = output.ok_or_else(|| format!("missing --output\n\n{usage}"))?;
    Ok(Parsed::Run(Cli {
        input,
        output,
        edition,
        target,
        optimization_level,
        cfg_names,
    }))
}

pub fn validate_output(cli: &Cli) -> Result<(), String> {
    if same_file(&cli.input, &cli.output) {
        return Err("input and output must be different files".to_owned());
    }
    match std::fs::symlink_metadata(&cli.output) {
        Ok(_) => Err(format!("output already exists: {}", cli.output.display())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "cannot inspect output {}: {error}",
            cli.output.display()
        )),
    }
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

fn same_file(input: &std::path::Path, output: &std::path::Path) -> bool {
    input == output
        || std::fs::canonicalize(input)
            .ok()
            .zip(std::fs::canonicalize(output).ok())
            .is_some_and(|(input, output)| input == output)
}
