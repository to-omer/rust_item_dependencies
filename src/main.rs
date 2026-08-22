#![feature(rustc_private)]

use std::ffi::OsString;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::process::{Command, ExitCode};

use rust_item_dependencies::{
    AnalysisError, Analyzer, CompilationOptions, Edition, OptimizationLevel, SourceInput,
};

#[path = "../tools/cli.rs"]
mod cli;

#[cfg(test)]
use cli::Cli;
use cli::{CliEdition, CliOptimizationLevel, Parsed, parse_arguments, validate_output};

const USAGE: &str = r#"Usage: rust-item-dependencies [OPTIONS] INPUT.rs

Options:
  -o, --output OUTPUT    Write reduced source to OUTPUT
      --edition YEAR     Rust edition: 2015, 2018, 2021, or 2024 [default: 2024]
      --target TRIPLE    Compilation target [default: compiler host]
  -O                     Same as --opt-level 3
      --opt-level LEVEL  Optimization level: 0, 1, 2, 3, s, or z [default: 0]
      --cfg NAME         Enable a name-only cfg; may be repeated
  -h, --help             Print help"#;

fn main() -> ExitCode {
    match run(std::env::args_os().skip(1)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(arguments: impl IntoIterator<Item = OsString>) -> Result<(), String> {
    let Parsed::Run(cli) = parse_arguments(arguments, USAGE)? else {
        println!("{USAGE}");
        return Ok(());
    };
    validate_output(&cli)?;

    let source = std::fs::read_to_string(&cli.input)
        .map_err(|error| format!("cannot read {}: {error}", cli.input.display()))?;
    let target = cli.target.map_or_else(host_target, Ok)?;
    let options = cli.cfg_names.into_iter().fold(
        CompilationOptions::new().with_optimization_level(cli.optimization_level.into()),
        CompilationOptions::with_cfg,
    );
    let analyzer = Analyzer::new_with_options(options).map_err(render_analysis_error)?;
    let reduction = analyzer
        .reduce(&SourceInput {
            source,
            edition: cli.edition.into(),
            target,
        })
        .map_err(render_analysis_error)?;

    write_output(&cli.output, reduction.reduced_source())
        .map_err(|error| format!("cannot write {}: {error}", cli.output.display()))
}

fn render_analysis_error(error: AnalysisError) -> String {
    let mut rendered = error.to_string();
    match &error {
        AnalysisError::InvalidCfgName { name } => {
            rendered.push_str(&format!(": {name:?}"));
        }
        AnalysisError::UnsupportedInput { reason, range } => {
            rendered.push_str(&format!(": {reason:?}"));
            append_range(&mut rendered, *range);
        }
        AnalysisError::OriginalCompilationFailed(diagnostics)
        | AnalysisError::ReducedCompilationFailed(diagnostics) => {
            for diagnostic in diagnostics.diagnostics() {
                rendered.push_str("\n  ");
                rendered.push_str(&diagnostic.message);
                append_range(&mut rendered, diagnostic.range);
            }
        }
        _ => {}
    }
    rendered
}

fn append_range(output: &mut String, range: Option<rust_item_dependencies::source::ByteRange>) {
    if let Some(range) = range {
        output.push_str(&format!(" at bytes {}..{}", range.start, range.end));
    }
}

fn write_output(path: &Path, source: &str) -> std::io::Result<()> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?
        .write_all(source.as_bytes())
}

impl From<CliEdition> for Edition {
    fn from(edition: CliEdition) -> Self {
        match edition {
            CliEdition::Rust2015 => Self::Rust2015,
            CliEdition::Rust2018 => Self::Rust2018,
            CliEdition::Rust2021 => Self::Rust2021,
            CliEdition::Rust2024 => Self::Rust2024,
        }
    }
}

impl From<CliOptimizationLevel> for OptimizationLevel {
    fn from(level: CliOptimizationLevel) -> Self {
        match level {
            CliOptimizationLevel::O0 => Self::O0,
            CliOptimizationLevel::O1 => Self::O1,
            CliOptimizationLevel::O2 => Self::O2,
            CliOptimizationLevel::O3 => Self::O3,
            CliOptimizationLevel::Size => Self::Size,
            CliOptimizationLevel::SizeMin => Self::SizeMin,
        }
    }
}

fn host_target() -> Result<String, String> {
    let output = Command::new(env!("RUST_ITEM_DEPENDENCIES_BUILD_RUSTC"))
        .arg("-Vv")
        .output()
        .map_err(|error| format!("cannot start the configured rustc: {error}"))?;
    if !output.status.success() {
        return Err("the configured rustc could not report its host target".to_owned());
    }
    let version = String::from_utf8(output.stdout)
        .map_err(|_| "the configured rustc returned non-UTF-8 version output".to_owned())?;
    version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::to_owned)
        .ok_or_else(|| "the configured rustc did not report its host target".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_item_dependencies::{UnsupportedReason, source::ByteRange};

    fn parse(arguments: &[&str]) -> Result<Parsed, String> {
        parse_arguments(arguments.iter().map(OsString::from), USAGE)
    }

    #[test]
    fn parses_the_public_options_and_defaults() {
        let Parsed::Run(defaults) = parse(&["input.rs", "-o", "output.rs"]).unwrap() else {
            panic!("input must run the reducer")
        };
        assert_eq!(
            defaults,
            Cli {
                input: "input.rs".into(),
                output: "output.rs".into(),
                edition: CliEdition::Rust2024,
                target: None,
                optimization_level: CliOptimizationLevel::O0,
                cfg_names: Vec::new(),
            }
        );

        let Parsed::Run(explicit) = parse(&[
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "-o",
            "output.rs",
            "input.rs",
        ])
        .unwrap() else {
            panic!("valid options must run the reducer")
        };
        assert_eq!(explicit.input, Path::new("input.rs"));
        assert_eq!(explicit.output, Path::new("output.rs"));
        assert_eq!(explicit.edition, CliEdition::Rust2021);
        assert_eq!(explicit.target.as_deref(), Some("x86_64-unknown-linux-gnu"));
        assert_eq!(explicit.optimization_level, CliOptimizationLevel::O0);
        assert!(explicit.cfg_names.is_empty());
    }

    #[test]
    fn parses_optimization_and_repeated_cfg_options() {
        let Parsed::Run(cli) = parse(&[
            "--opt-level",
            "s",
            "--cfg",
            "LOCAL",
            "-O",
            "--cfg",
            "ONLINE_JUDGE",
            "input.rs",
            "-o",
            "output.rs",
        ])
        .unwrap() else {
            panic!("valid options must run the reducer")
        };

        assert_eq!(cli.optimization_level, CliOptimizationLevel::O3);
        assert_eq!(cli.cfg_names, ["LOCAL", "ONLINE_JUDGE"]);

        let Parsed::Run(cli) =
            parse(&["-O", "--opt-level", "z", "input.rs", "-o", "output.rs"]).unwrap()
        else {
            panic!("valid options must run the reducer")
        };
        assert_eq!(cli.optimization_level, CliOptimizationLevel::SizeMin);
    }

    #[test]
    fn parses_each_explicit_optimization_level() {
        for (value, expected) in [
            ("0", CliOptimizationLevel::O0),
            ("1", CliOptimizationLevel::O1),
            ("2", CliOptimizationLevel::O2),
            ("3", CliOptimizationLevel::O3),
            ("s", CliOptimizationLevel::Size),
            ("z", CliOptimizationLevel::SizeMin),
        ] {
            let Parsed::Run(cli) =
                parse(&["--opt-level", value, "input.rs", "-o", "output.rs"]).unwrap()
            else {
                panic!("valid options must run the reducer")
            };
            assert_eq!(cli.optimization_level, expected, "{value}");
        }
    }

    #[test]
    fn rejects_missing_or_invalid_compilation_options() {
        assert_eq!(
            parse(&["--opt-level"]).unwrap_err(),
            "--opt-level requires a value"
        );
        assert_eq!(
            parse(&["--opt-level", "fast"]).unwrap_err(),
            "unsupported optimization level: fast; expected 0, 1, 2, 3, s, or z"
        );
        assert_eq!(parse(&["--cfg"]).unwrap_err(), "--cfg requires a value");
    }

    #[test]
    fn rejects_ambiguous_or_destructive_arguments() {
        assert_eq!(
            parse(&[]).unwrap_err(),
            format!("missing input file\n\n{USAGE}")
        );
        assert_eq!(
            parse(&["input.rs"]).unwrap_err(),
            format!("missing --output\n\n{USAGE}")
        );
        assert_eq!(
            parse(&["first.rs", "second.rs"]).unwrap_err(),
            format!("expected exactly one input file\n\n{USAGE}")
        );
        assert_eq!(
            parse(&["--edition", "2000", "input.rs"]).unwrap_err(),
            "unsupported Rust edition: 2000"
        );
        let Parsed::Run(same_output) = parse(&["input.rs", "-o", "input.rs"]).unwrap() else {
            panic!("input must run the reducer")
        };
        assert_eq!(
            validate_output(&same_output),
            Err("input and output must be different files".to_owned())
        );
    }

    #[test]
    fn renders_structured_analysis_error_details() {
        assert_eq!(
            render_analysis_error(AnalysisError::InvalidCfgName {
                name: "feature=\"judge\"".to_owned(),
            }),
            "an explicit cfg name is invalid: \"feature=\\\"judge\\\"\""
        );
        assert_eq!(
            render_analysis_error(AnalysisError::UnsupportedInput {
                reason: UnsupportedReason::ProcMacro,
                range: Some(ByteRange { start: 4, end: 15 }),
            }),
            "the input is outside the supported source boundary: ProcMacro at bytes 4..15"
        );
    }

    #[test]
    fn never_overwrites_an_existing_output() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "rust-item-dependencies-output-{}-{nonce}.rs",
            std::process::id()
        ));

        write_output(&path, "first").unwrap();
        let cli = Cli {
            input: path.with_extension("input.rs"),
            output: path.clone(),
            edition: CliEdition::Rust2024,
            target: None,
            optimization_level: CliOptimizationLevel::O0,
            cfg_names: Vec::new(),
        };
        assert_eq!(
            validate_output(&cli),
            Err(format!("output already exists: {}", path.display()))
        );
        let error = write_output(&path, "second").unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
        std::fs::remove_file(path).unwrap();
    }
}
