//! Reduction using the compiler invocation selected by a build system.

use std::path::PathBuf;

use rustc_interface::interface::Config;
use rustc_session::config::{Options, OutputType, OutputTypes};

use crate::api::{Reduction, reduce_in_context};
use crate::artifact::compiler_sysroot;
use crate::error::AnalysisError;
use crate::input::{
    CompilationContext, CompilationOptions, Edition, PreparedCompilationOptions, SourceInput,
};

/// An ordinary binary invocation, with response files already expanded and
/// arguments excluding the compiler executable.
/// Reduction runs in the caller's current directory and environment. The caller
/// must keep both unchanged for the duration of `reduce`. As with rustc, this
/// executes procedural macros resolved from these compiler inputs. Use only
/// trusted inputs, and keep any wrapper-managed resources alive until it returns.
pub struct CompilerInvocation {
    source: String,
    arguments: Vec<String>,
}

impl CompilerInvocation {
    pub fn new(source: impl Into<String>, arguments: Vec<String>) -> Self {
        Self {
            source: source.into(),
            arguments,
        }
    }

    pub fn reduce(&self) -> Result<Reduction, AnalysisError> {
        rustc_driver::catch_fatal_errors(|| self.reduce_inner())
            .map_err(|_| invalid("rustc could not interpret the compiler invocation"))?
    }

    fn reduce_inner(&self) -> Result<Reduction, AnalysisError> {
        let mut diagnostics = rustc_session::EarlyDiagCtxt::new(Default::default());
        let arguments = &self.arguments;
        let rustc_driver::HandledOptions::Normal(matches) =
            rustc_driver::handle_options(&diagnostics, arguments)
        else {
            return Err(invalid("expected an ordinary binary compiler invocation"));
        };
        let mut options = rustc_session::config::build_session_options(&mut diagnostics, &matches);
        if matches.free.len() != 1
            || matches.free[0] == "-"
            || options.test
            || options.crate_types != [rustc_session::config::CrateType::Executable]
            || !matches.opt_strs("print").is_empty()
        {
            return Err(invalid(
                "Cargo reduction requires one ordinary binary source file",
            ));
        }
        let sysroot = compiler_sysroot().map_err(|_| AnalysisError::CompilerArtifactMismatch)?;
        if options.sysroot.explicit.as_ref().is_some_and(|path| {
            std::fs::canonicalize(path).ok() != std::fs::canonicalize(&sysroot).ok()
        }) {
            return Err(invalid("the invocation uses a different compiler sysroot"));
        }
        let source_path = PathBuf::from(&matches.free[0]);
        let edition = match options.edition {
            rustc_span::edition::Edition::Edition2015 => Edition::Rust2015,
            rustc_span::edition::Edition::Edition2018 => Edition::Rust2018,
            rustc_span::edition::Edition::Edition2021 => Edition::Rust2021,
            rustc_span::edition::Edition::Edition2024 => Edition::Rust2024,
            _ => return Err(invalid("unsupported Rust edition")),
        };
        let source = SourceInput::binary(&self.source, edition, options.target_triple.tuple())
            .with_crate_name(
                options
                    .crate_name
                    .clone()
                    .ok_or_else(|| invalid("the invocation has no crate name"))?,
            )
            .with_source_paths(&source_path, &source_path);
        let target_libraries =
            crate::input::select_target_libraries(&sysroot, options.target_triple.tuple())
                .map_err(|error| invalid(format!("unsupported compiler target: {error:?}")))?;
        let trusted = target_libraries
            .search_paths()
            .map(|(_, path)| path.to_owned())
            .collect::<Vec<_>>();
        let external = crate::external::prepare_invocation_external_crates(&mut options, &trusted)?;
        for (kind, directory) in target_libraries.search_paths() {
            let kind = if kind == "crate" {
                rustc_session::search_paths::PathKind::Crate
            } else {
                rustc_session::search_paths::PathKind::Dependency
            };
            if !options
                .search_paths
                .iter()
                .any(|search| search.kind == kind && search.dir.as_ref() == directory)
            {
                options
                    .search_paths
                    .push(rustc_session::search_paths::SearchPath {
                        kind,
                        dir: directory.into(),
                    });
            }
        }
        let compilation = PreparedCompilationOptions::new(CompilationOptions::default(), external);
        let settings = InvocationSettings {
            options,
            crate_cfg: matches.opt_strs("cfg"),
            crate_check_cfg: matches.opt_strs("check-cfg"),
            sysroot,
        };
        let context = CompilationContext::new(&source, &compilation, &settings.sysroot)
            .map_err(|error| invalid(format!("unsupported compiler input: {error:?}")))?
            .with_invocation(&settings);
        reduce_in_context(&self.source, context)
    }
}

#[derive(Clone)]
pub(crate) struct InvocationSettings {
    options: Options,
    crate_cfg: Vec<String>,
    crate_check_cfg: Vec<String>,
    sysroot: PathBuf,
}

impl InvocationSettings {
    pub(crate) fn configure(&self, config: &mut Config) {
        config.opts = self.options.clone();
        config.crate_cfg = self.crate_cfg.clone();
        config.crate_check_cfg = self.crate_check_cfg.clone();
        config.opts.sysroot.explicit = Some(self.sysroot.clone());
        config.opts.incremental = None;
        // Metadata-only analysis skips checks on the codegen artifacts of
        // dependencies. Preserve that mode while suppressing side outputs.
        let outputs = config
            .opts
            .output_types
            .keys()
            .filter(|kind| **kind != OutputType::DepInfo)
            .map(|kind| (*kind, None))
            .collect::<Vec<_>>();
        config.opts.output_types = OutputTypes::new(&outputs);
        config.opts.unstable_opts.temps_dir = None;
        config.output_file = None;
        config.output_dir = None;
    }
}

pub(crate) fn invalid(message: impl Into<String>) -> AnalysisError {
    AnalysisError::InvalidCompilerInvocation {
        message: message.into(),
    }
}
