use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::container_protocol::{ContainerResult, RESULT_PATH, VERSION};
use crate::file_output::{SourceFile, write_new};

pub(crate) struct SourceOutput {
    output: Output,
    report: Option<ResultPaths>,
}

enum Output {
    InPlace(SourceFile),
    Separate { source: String, path: PathBuf },
}

struct ResultPaths {
    input: String,
    output: Option<String>,
}

impl SourceOutput {
    pub(crate) fn read(input: &Path, output: Option<&Path>, container: bool) -> io::Result<Self> {
        let report = if container {
            let path = |path: &Path| {
                path.to_str().map(str::to_owned).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "the source path is not Unicode",
                    )
                })
            };
            Some(ResultPaths {
                input: path(input)?,
                output: output.map(path).transpose()?,
            })
        } else {
            None
        };
        let output = match output {
            Some(path) => Output::Separate {
                source: fs::read_to_string(input)?,
                path: path.to_owned(),
            },
            None => Output::InPlace(SourceFile::read(input)?),
        };
        Ok(Self { output, report })
    }

    pub(crate) fn source(&self) -> &str {
        match &self.output {
            Output::InPlace(original) => original.source(),
            Output::Separate { source, .. } => source,
        }
    }

    pub(crate) fn write(self, reduced: &str) -> io::Result<()> {
        let report = self.report.as_ref().map(|paths| ContainerResult {
            version: VERSION,
            input: paths.input.clone(),
            output: paths.output.clone(),
            original: self.source().to_owned(),
            reduced: reduced.to_owned(),
        });
        match self.output {
            Output::InPlace(original) => original.replace(reduced)?,
            Output::Separate { path, .. } => write_new(&path, reduced)?,
        }
        if let Some(report) = report {
            let path = Path::new(RESULT_PATH);
            fs::create_dir_all(
                path.parent()
                    .expect("the container result path has a parent"),
            )?;
            let json = serde_json::to_string(&report).map_err(io::Error::other)?;
            write_new(path, &json)?;
        }
        Ok(())
    }
}
