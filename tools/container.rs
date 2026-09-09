use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};

use crate::cli::{Parsed, parse_arguments, reducer_usage};
use crate::container_protocol::{ContainerResult, RESULT_ARGUMENT, RESULT_PATH, VERSION};
use crate::file_output::{SourceFile, write_new};

const DEFAULT_IMAGE: &str = "ghcr.io/to-omer/rust_item_dependencies:main";
const USAGE: &str =
    "Usage: cargo rid docker [CARGO_OPTIONS]\n       cargo rid docker [OPTIONS] INPUT.rs";

pub(super) fn run(arguments: &[OsString]) -> Result<ExitStatus, String> {
    let arguments = arguments
        .iter()
        .map(|argument| argument.to_str().ok_or("Docker arguments must be Unicode"))
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(
        parse_arguments(arguments.iter().map(OsString::from), USAGE)?,
        Parsed::Help
    ) {
        println!("{}", reducer_usage(USAGE));
        return Ok(ExitStatus::default());
    }
    reduce(&arguments).map_err(|error| format!("Docker reduction failed: {error}"))
}

fn reduce(arguments: &[&str]) -> io::Result<ExitStatus> {
    let root = fs::canonicalize(std::env::current_dir()?)?;
    if root.to_str().is_none() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "the working directory is not Unicode",
        ));
    }
    let temporary = tempfile::Builder::new().prefix("rid-docker-").tempdir()?;
    let dockerfile = temporary.path().join("Dockerfile");
    fs::write(&dockerfile, build_definition(arguments)?)?;
    // Program inputs may be ignored by an unrelated image's Dockerfile.
    fs::write(temporary.path().join("Dockerfile.dockerignore"), "")?;
    let exported = temporary.path().join("result");
    let destination = exported.to_str().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "the temporary directory is not Unicode",
        )
    })?;
    let mut exporter = csv::Writer::from_writer(Vec::new());
    exporter.write_record(["type=local", &format!("dest={destination}")])?;
    let mut exporter = exporter.into_inner().map_err(io::Error::other)?;
    exporter.pop(); // Docker expects one CSV record without its trailing newline.
    let exporter = String::from_utf8(exporter).map_err(io::Error::other)?;
    let image =
        std::env::var_os("RUST_ITEM_DEPENDENCIES_IMAGE").unwrap_or_else(|| DEFAULT_IMAGE.into());
    let image = image.to_str().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "the Docker image reference is not Unicode",
        )
    })?;
    let status = Command::new("docker")
        // Use the current Docker daemon's image store, including local images.
        .env_remove("BUILDX_BUILDER")
        .env("DOCKER_BUILDKIT", "1")
        .args(["build", "--no-cache", "--progress=plain", "--file"])
        .arg(&dockerfile)
        .arg("--build-arg")
        .arg(format!("RID_IMAGE={image}"))
        .arg("--output")
        .arg(exporter)
        .arg(&root)
        .stdin(Stdio::null())
        .status()?;
    if !status.success() {
        return Ok(status);
    }
    let result = exported.join("result.json");
    if !fs::symlink_metadata(&result)?.file_type().is_file() {
        return Err(io::Error::other("the Docker result is not a regular file"));
    }
    let result: ContainerResult = serde_json::from_slice(&fs::read(result)?)?;
    apply_result(&root, result)?;
    Ok(status)
}

fn build_definition(arguments: &[&str]) -> io::Result<String> {
    let mut command = vec!["/usr/local/bin/rust-item-dependencies", RESULT_ARGUMENT];
    command.extend_from_slice(arguments);
    let command = serde_json::to_string(&command)?;
    Ok(format!(
        "ARG RID_IMAGE\n\
         FROM ${{RID_IMAGE}} AS reduce\n\
         ENV CARGO_HOME=/tmp/rid-cargo-home CARGO_TARGET_DIR=/tmp/rid-target\n\
         COPY --chown=1000:1000 . /workspace/\n\
         WORKDIR /workspace\n\
         USER 1000:1000\n\
         RUN --mount=type=cache,id=rid-cargo-home,target=/tmp/rid-cargo-home,uid=1000,gid=1000,sharing=locked {command}\n\
         FROM scratch\n\
         COPY --from=reduce {RESULT_PATH} /result.json\n"
    ))
}

fn apply_result(root: &Path, result: ContainerResult) -> io::Result<()> {
    if result.version != VERSION {
        return Err(io::Error::other(
            "the image and launcher use incompatible container formats",
        ));
    }
    let input = host_path(root, &result.input)?;
    if !fs::canonicalize(&input)?.starts_with(root) {
        return Err(outside_workspace());
    }
    match result.output {
        None => {
            let original = SourceFile::read(&input)?;
            unchanged(original.source(), &result.original)?;
            validate_parent(root, &input)?;
            original.replace(&result.reduced)
        }
        Some(output) => {
            let output = host_path(root, &output)?;
            unchanged(&fs::read_to_string(&input)?, &result.original)?;
            validate_parent(root, &output)?;
            write_new(&output, &result.reduced)
        }
    }
}

fn unchanged(current: &str, original: &str) -> io::Result<()> {
    if current != original {
        return Err(io::Error::other(
            "the input file changed during reduction; no result was written",
        ));
    }
    Ok(())
}

#[cfg(test)]
#[path = "container_tests.rs"]
mod tests;

fn host_path(root: &Path, container: &str) -> io::Result<PathBuf> {
    let relative = if container.starts_with('/') {
        container
            .strip_prefix("/workspace/")
            .ok_or_else(outside_workspace)?
    } else {
        container
    };
    // Container paths use '/', including when the launcher runs on Windows.
    let mut path = root.to_owned();
    for part in relative.split('/') {
        if part.is_empty() || part == "." {
            continue;
        }
        if part != ".." {
            let mut components = Path::new(part).components();
            if !matches!(components.next(), Some(std::path::Component::Normal(name)) if name == part)
                || components.next().is_some()
            {
                return Err(outside_workspace());
            }
            #[cfg(windows)]
            if part.contains(':') || part.ends_with(['.', ' ']) {
                return Err(outside_workspace());
            }
        }
        path.push(part);
    }
    path.file_name().ok_or_else(outside_workspace)?;
    validate_parent(root, &path)?;
    Ok(path)
}

fn validate_parent(root: &Path, path: &Path) -> io::Result<()> {
    let parent = fs::canonicalize(path.parent().ok_or_else(outside_workspace)?)?;
    if !parent.starts_with(root) {
        return Err(outside_workspace());
    }
    Ok(())
}

fn outside_workspace() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "the source and output must be inside the working directory",
    )
}
