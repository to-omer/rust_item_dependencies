#![feature(rustc_private)]

use std::ffi::OsString;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::process::{Command, ExitCode};

use rust_item_dependencies::{
    AnalysisError, Analyzer, CompilationOptions, Edition, EntryPoint, OptimizationLevel,
    SourceInput,
};

#[path = "../tools/cli.rs"]
mod cli;

#[cfg(test)]
use cli::Cli;
use cli::{
    CliCrateType, CliEdition, CliOptimizationLevel, Parsed, parse_arguments, reducer_usage,
    render_path, validate_output,
};

const USAGE_COMMAND: &str = "Usage: rust-item-dependencies [OPTIONS] INPUT.rs";

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
    let usage = reducer_usage(USAGE_COMMAND);
    let cli = match parse_arguments(arguments, &usage)? {
        Parsed::Run(cli) => cli,
        Parsed::Help => {
            println!("{usage}");
            return Ok(());
        }
    };
    validate_output(&cli)?;

    let source = std::fs::read_to_string(&cli.input)
        .map_err(|error| format!("cannot read {}: {error}", render_path(&cli.input)))?;
    let target = cli.target.map_or_else(host_target, Ok)?;
    let mut options = cli.cfg_names.into_iter().fold(
        CompilationOptions::new().with_optimization_level(cli.optimization_level.into()),
        CompilationOptions::with_cfg,
    );
    for external_crate in cli.external_crates {
        options = options.with_external_crate(external_crate.extern_name, external_crate.artifact);
    }
    for artifact in cli.dependency_artifacts {
        options = options.with_dependency_artifact(artifact);
    }
    for artifact in cli.allowed_proc_macro_artifacts {
        options = options.allow_proc_macro_execution(artifact);
    }
    let input = match cli.crate_type {
        CliCrateType::Binary => {
            SourceInput::binary(source, cli.edition.into(), target).with_crate_name(cli.crate_name)
        }
        CliCrateType::Library => {
            SourceInput::library(source, cli.edition.into(), target, cli.crate_name)
        }
    };
    let input = cli.entry_points.into_iter().fold(input, |input, path| {
        input.with_entry_point(EntryPoint::new(path))
    });
    let analyzer = Analyzer::new_with_options(options).map_err(render_analysis_error)?;
    let reduction = analyzer.reduce(&input).map_err(render_analysis_error)?;

    write_output(&cli.output, reduction.reduced_source())
        .map_err(|error| format!("cannot write {}: {error}", render_path(&cli.output)))
}

fn render_analysis_error(error: AnalysisError) -> String {
    let mut rendered = error.to_string();
    match &error {
        AnalysisError::InvalidCfgName { name } => {
            rendered.push_str(&format!(": {name:?}"));
        }
        AnalysisError::InvalidCrateName { name } => {
            rendered.push_str(&format!(": {name:?}"));
        }
        AnalysisError::InvalidEntryPoint { path, reason } => {
            rendered.push_str(&format!(": {path:?}: {reason}"));
        }
        AnalysisError::InvalidExternalCrateName { name } => {
            rendered.push_str(&format!(": {name:?}"));
        }
        AnalysisError::ConflictingExternalCrate {
            name,
            first_path,
            second_path,
        } => {
            rendered.push_str(&format!(": {name:?}: {first_path:?} and {second_path:?}",));
        }
        AnalysisError::ExternalCrateArtifactUnreadable { path, error }
        | AnalysisError::ExternalCrateSnapshotFailure { path, error } => {
            rendered.push_str(&format!(": {path:?}: {error}"));
        }
        AnalysisError::UnsupportedExternalCrateArtifact { path } => {
            rendered.push_str(&format!(": {path:?}"));
        }
        AnalysisError::InvalidProcMacroExecutionArtifact { path } => {
            rendered.push_str(&format!(": {path:?}"));
        }
        AnalysisError::ConflictingExternalCrateArtifactName {
            file_name,
            first_path,
            second_path,
        } => {
            rendered.push_str(&format!(
                ": {file_name:?}: {first_path:?} and {second_path:?}",
            ));
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

fn append_range(output: &mut String, range: Option<rust_item_dependencies::ByteRange>) {
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
    use rust_item_dependencies::{ByteRange, EntryPointError, UnsupportedReason};

    fn parse(arguments: &[&str]) -> Result<Parsed, String> {
        parse_arguments(
            arguments.iter().map(OsString::from),
            &reducer_usage(USAGE_COMMAND),
        )
    }

    #[test]
    fn parses_the_public_options_and_defaults() {
        let Parsed::Run(defaults) = parse(&["input.rs", "-o", "output.rs"]).unwrap() else {
            panic!("input must run the reducer")
        };
        assert_eq!(
            *defaults,
            Cli {
                input: "input.rs".into(),
                output: "output.rs".into(),
                edition: CliEdition::Rust2024,
                target: None,
                crate_type: CliCrateType::Binary,
                crate_name: "main".to_owned(),
                entry_points: Vec::new(),
                optimization_level: CliOptimizationLevel::O0,
                cfg_names: Vec::new(),
                external_crates: Vec::new(),
                dependency_artifacts: Vec::new(),
                allowed_proc_macro_artifacts: Vec::new(),
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
        assert_eq!(explicit.crate_type, CliCrateType::Binary);
        assert_eq!(explicit.crate_name, "main");
        assert!(explicit.entry_points.is_empty());
        assert_eq!(explicit.optimization_level, CliOptimizationLevel::O0);
        assert!(explicit.cfg_names.is_empty());
        assert!(explicit.external_crates.is_empty());
        assert!(explicit.dependency_artifacts.is_empty());
        assert!(explicit.allowed_proc_macro_artifacts.is_empty());
    }

    #[test]
    fn parses_library_crate_name_and_repeated_entry_points() {
        let Parsed::Run(cli) = parse(&[
            "--crate-type",
            "lib",
            "--crate-name",
            "competitive",
            "--entry",
            "competitive::largest_rectangle",
            "--entry",
            "competitive::LIMIT",
            "input.rs",
            "-o",
            "output.rs",
        ])
        .unwrap() else {
            panic!("valid library options must run the reducer")
        };

        assert_eq!(cli.crate_type, CliCrateType::Library);
        assert_eq!(cli.crate_name, "competitive");
        assert_eq!(
            cli.entry_points,
            ["competitive::largest_rectangle", "competitive::LIMIT"]
        );
    }

    #[test]
    fn parses_repeated_dependency_artifacts_and_proc_macro_permissions() {
        let Parsed::Run(cli) = parse(&[
            "--extern",
            "wrapper=target/deps/libwrapper.rlib",
            "--dependency-artifact",
            "target/deps/libleaf.rlib",
            "--allow-proc-macro",
            "target/deps/libderive.dylib",
            "--extern",
            "support=target/deps/libsupport=version.rlib",
            "input.rs",
            "-o",
            "output.rs",
        ])
        .unwrap() else {
            panic!("valid dependency options must run the reducer")
        };

        assert_eq!(
            cli.external_crates,
            [
                cli::CliExternalCrate {
                    extern_name: "wrapper".to_owned(),
                    artifact: "target/deps/libwrapper.rlib".into(),
                },
                cli::CliExternalCrate {
                    extern_name: "support".to_owned(),
                    artifact: "target/deps/libsupport=version.rlib".into(),
                },
            ]
        );
        assert_eq!(
            cli.dependency_artifacts,
            [std::path::PathBuf::from("target/deps/libleaf.rlib")]
        );
        assert_eq!(
            cli.allowed_proc_macro_artifacts,
            [std::path::PathBuf::from("target/deps/libderive.dylib")]
        );
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
        assert_eq!(
            parse(&["--crate-type"]).unwrap_err(),
            "--crate-type requires a value"
        );
        assert_eq!(
            parse(&["--crate-type", "rlib", "input.rs", "-o", "output.rs"]).unwrap_err(),
            "unsupported crate type: rlib; expected bin or lib"
        );
        assert_eq!(
            parse(&["--crate-name"]).unwrap_err(),
            "--crate-name requires a value"
        );
        assert_eq!(parse(&["--entry"]).unwrap_err(), "--entry requires a value");
        assert_eq!(
            parse(&["--extern"]).unwrap_err(),
            "--extern requires a value"
        );
        assert_eq!(
            parse(&["--dependency-artifact"]).unwrap_err(),
            "--dependency-artifact requires a value"
        );
        assert_eq!(
            parse(&["--dependency-artifact", ""]).unwrap_err(),
            "--dependency-artifact requires a nonempty path"
        );
        assert_eq!(
            parse(&["--allow-proc-macro"]).unwrap_err(),
            "--allow-proc-macro requires a value"
        );
        assert_eq!(
            parse(&["--allow-proc-macro", ""]).unwrap_err(),
            "--allow-proc-macro requires a nonempty path"
        );
    }

    #[test]
    fn rejects_malformed_direct_dependencies() {
        assert_eq!(
            parse(&["--extern", "wrapper", "input.rs", "-o", "output.rs"]).unwrap_err(),
            "--extern requires NAME=PATH"
        );
        assert_eq!(
            parse(&[
                "--extern",
                "=libwrapper.rlib",
                "input.rs",
                "-o",
                "output.rs"
            ])
            .unwrap_err(),
            "--extern requires a nonempty NAME in NAME=PATH"
        );
        assert_eq!(
            parse(&["--extern", "wrapper=", "input.rs", "-o", "output.rs"]).unwrap_err(),
            "--extern requires a nonempty PATH in NAME=PATH"
        );
    }

    #[test]
    fn rejects_ambiguous_or_destructive_arguments() {
        assert_eq!(
            parse(&[]).unwrap_err(),
            format!("missing input file\n\n{}", reducer_usage(USAGE_COMMAND))
        );
        assert_eq!(
            parse(&["input.rs"]).unwrap_err(),
            format!("missing --output\n\n{}", reducer_usage(USAGE_COMMAND))
        );
        assert_eq!(
            parse(&["first.rs", "second.rs"]).unwrap_err(),
            format!(
                "expected exactly one input file\n\n{}",
                reducer_usage(USAGE_COMMAND)
            )
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
            render_analysis_error(AnalysisError::InvalidCrateName {
                name: "bad-name".to_owned(),
            }),
            "the crate name is invalid: \"bad-name\""
        );
        assert_eq!(
            render_analysis_error(AnalysisError::MissingLibraryEntryPoint),
            "a library input requires at least one entry point"
        );
        assert_eq!(
            render_analysis_error(AnalysisError::InvalidEntryPoint {
                path: "competitive::missing".to_owned(),
                reason: EntryPointError::NotFound,
            }),
            concat!(
                "an explicit entry point is invalid: \"competitive::missing\": ",
                "the path does not resolve to an item",
            )
        );
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

        for (error, expected) in [
            (
                AnalysisError::InvalidExternalCrateName {
                    name: "bad-name".to_owned(),
                },
                "an external crate name is invalid: \"bad-name\"",
            ),
            (
                AnalysisError::ConflictingExternalCrate {
                    name: "wrapper".to_owned(),
                    first_path: "first/libwrapper.rlib".into(),
                    second_path: "second/libwrapper.rlib".into(),
                },
                concat!(
                    "an external crate name refers to conflicting artifacts: ",
                    "\"wrapper\": \"first/libwrapper.rlib\" and \"second/libwrapper.rlib\"",
                ),
            ),
            (
                AnalysisError::ExternalCrateArtifactUnreadable {
                    path: "missing/libwrapper.rlib".into(),
                    error: std::io::ErrorKind::PermissionDenied,
                },
                concat!(
                    "an external crate artifact could not be read: ",
                    "\"missing/libwrapper.rlib\": permission denied",
                ),
            ),
            (
                AnalysisError::UnsupportedExternalCrateArtifact {
                    path: "libwrapper.rmeta".into(),
                },
                concat!(
                    "an external crate artifact format is not supported: ",
                    "\"libwrapper.rmeta\"",
                ),
            ),
            (
                AnalysisError::InvalidProcMacroExecutionArtifact {
                    path: "libwrapper.rlib".into(),
                },
                concat!(
                    "a procedural macro execution permission does not refer to a declared ",
                    "host dynamic library: \"libwrapper.rlib\"",
                ),
            ),
            (
                AnalysisError::ConflictingExternalCrateArtifactName {
                    file_name: "libwrapper.rlib".to_owned(),
                    first_path: "first/libwrapper.rlib".into(),
                    second_path: "second/libwrapper.rlib".into(),
                },
                concat!(
                    "external crate artifacts have a conflicting file name: ",
                    "\"libwrapper.rlib\": \"first/libwrapper.rlib\" and ",
                    "\"second/libwrapper.rlib\"",
                ),
            ),
            (
                AnalysisError::ExternalCrateSnapshotFailure {
                    path: "libwrapper.rlib".into(),
                    error: std::io::ErrorKind::PermissionDenied,
                },
                concat!(
                    "the external crate snapshot could not be prepared: ",
                    "\"libwrapper.rlib\": permission denied",
                ),
            ),
        ] {
            assert_eq!(render_analysis_error(error), expected);
        }
    }

    #[cfg(unix)]
    #[test]
    fn escapes_non_utf8_external_artifact_paths_in_errors() {
        use std::os::unix::ffi::OsStringExt;

        let path = std::path::PathBuf::from(OsString::from_vec(
            b"artifact-with-newline\n-and-\xff.rlib".to_vec(),
        ));
        let rendered =
            render_analysis_error(AnalysisError::UnsupportedExternalCrateArtifact { path });

        assert!(!rendered.contains('\n'));
        assert!(rendered.contains("\\n"));
        assert!(rendered.contains("\\xFF"));
    }

    #[cfg(unix)]
    #[test]
    fn escapes_non_utf8_input_paths_in_errors() {
        use std::os::unix::ffi::OsStringExt;

        let input = OsString::from_vec(b"target/tests/missing-with-newline\n-and-\xff.rs".to_vec());
        let error = run([
            input,
            OsString::from("-o"),
            OsString::from("target/tests/nonexistent-output.rs"),
        ])
        .unwrap_err();

        assert!(!error.contains('\n'));
        assert!(error.contains("\\n"));
        assert!(error.contains("\\xFF"));
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
            crate_type: CliCrateType::Binary,
            crate_name: "main".to_owned(),
            entry_points: Vec::new(),
            optimization_level: CliOptimizationLevel::O0,
            cfg_names: Vec::new(),
            external_crates: Vec::new(),
            dependency_artifacts: Vec::new(),
            allowed_proc_macro_artifacts: Vec::new(),
        };
        assert_eq!(
            validate_output(&cli),
            Err(format!("output already exists: {path:?}"))
        );
        let error = write_output(&path, "second").unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "first");
        std::fs::remove_file(path).unwrap();
    }
}
