use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub(crate) const TARGET_METADATA_COMPLETE_FILE: &str = ".rust-item-dependencies-complete";

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TargetLibrarySource {
    InstalledSysroot,
    GeneratedMetadata(PathBuf),
}

#[derive(Debug)]
pub(crate) enum TargetLibraryError {
    Read { path: PathBuf, source: io::Error },
    IncompleteInstalled(PathBuf),
    MissingHost(PathBuf),
}

impl fmt::Display for TargetLibraryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, source } => write!(formatter, "cannot read {path:?}: {source}"),
            Self::IncompleteInstalled(path) => {
                write!(formatter, "the target sysroot is incomplete: {path:?}")
            }
            Self::MissingHost(path) => {
                write!(formatter, "the host sysroot is incomplete: {path:?}")
            }
        }
    }
}

impl std::error::Error for TargetLibraryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Read { source, .. } => Some(source),
            Self::IncompleteInstalled(_) | Self::MissingHost(_) => None,
        }
    }
}

impl TargetLibrarySource {
    pub(crate) fn search_paths(&self) -> impl Iterator<Item = (&'static str, &Path)> {
        let directory = match self {
            Self::InstalledSysroot => None,
            Self::GeneratedMetadata(directory) => Some(directory.as_path()),
        };
        directory
            .into_iter()
            .flat_map(|directory| [("crate", directory), ("dependency", directory)])
    }
}

pub(crate) fn target_metadata_directory(sysroot: &Path, target: &str) -> Option<PathBuf> {
    Some(
        sysroot
            .parent()?
            .join("stage2-rid-target-metadata-artifacts")
            .join(target)
            .join(target),
    )
}

pub(crate) fn select_ready_target_libraries(
    installed: &Path,
    generated: &Path,
    is_host: bool,
) -> Result<Option<TargetLibrarySource>, TargetLibraryError> {
    let installed_entries = library_entries(installed)?;
    if contains_library(&installed_entries, "libcore-", ".rlib") {
        return Ok(Some(TargetLibrarySource::InstalledSysroot));
    }
    if !installed_entries.is_empty() {
        return Err(TargetLibraryError::IncompleteInstalled(
            installed.to_path_buf(),
        ));
    }
    if is_host {
        return Err(TargetLibraryError::MissingHost(installed.to_path_buf()));
    }
    if generated_metadata_is_complete(generated)? {
        return Ok(Some(TargetLibrarySource::GeneratedMetadata(
            generated.to_path_buf(),
        )));
    }
    Ok(None)
}

fn generated_metadata_is_complete(directory: &Path) -> Result<bool, TargetLibraryError> {
    let marker = directory.join(TARGET_METADATA_COMPLETE_FILE);
    let marker_exists = match fs::metadata(&marker) {
        Ok(metadata) => metadata.is_file(),
        Err(error) if error.kind() == io::ErrorKind::NotFound => false,
        Err(source) => {
            return Err(TargetLibraryError::Read {
                path: marker,
                source,
            });
        }
    };
    if !marker_exists {
        return Ok(false);
    }
    let entries = library_entries(directory)?;
    Ok(contains_library(&entries, "libcore-", ".rmeta"))
}

fn library_entries(directory: &Path) -> Result<Vec<OsString>, TargetLibraryError> {
    let entries = match fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => {
            return Err(TargetLibraryError::Read {
                path: directory.to_path_buf(),
                source: error,
            });
        }
    };
    entries
        .map(|entry| {
            entry
                .map(|entry| entry.file_name())
                .map_err(|source| TargetLibraryError::Read {
                    path: directory.to_path_buf(),
                    source,
                })
        })
        .collect()
}

fn contains_library(entries: &[OsString], prefix: &str, suffix: &str) -> bool {
    entries.iter().any(|entry| {
        entry
            .to_str()
            .is_some_and(|entry| entry.starts_with(prefix) && entry.ends_with(suffix))
    })
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    #[test]
    fn installed_core_selects_only_the_sysroot() {
        let directory = TestDirectory::new();
        let sysroot = directory.path().join("stage2");
        let installed = sysroot.join("lib/rustlib/target/lib");
        write_library(&installed, "libcore-installed.rlib");

        let generated = target_metadata_directory(&sysroot, "target").unwrap();
        let source = select_ready_target_libraries(&installed, &generated, false).unwrap();
        assert_eq!(source, Some(TargetLibrarySource::InstalledSysroot));
        assert!(source.unwrap().search_paths().next().is_none());
    }

    #[test]
    fn a_partial_sysroot_is_not_mixed_with_generated_metadata() {
        let directory = TestDirectory::new();
        let sysroot = directory.path().join("stage2");
        let installed = sysroot.join("lib/rustlib/target/lib");
        write_library(&installed, "liballoc-partial.rlib");

        assert!(matches!(
            select_ready_target_libraries(
                &installed,
                &target_metadata_directory(&sysroot, "target").unwrap(),
                false
            ),
            Err(TargetLibraryError::IncompleteInstalled(path)) if path == installed
        ));
    }

    #[test]
    fn an_empty_host_sysroot_is_rejected() {
        let directory = TestDirectory::new();
        let sysroot = directory.path().join("stage2");
        let installed = sysroot.join("lib/rustlib/host/lib");

        assert!(matches!(
            select_ready_target_libraries(
                &installed,
                &target_metadata_directory(&sysroot, "host").unwrap(),
                true
            ),
            Err(TargetLibraryError::MissingHost(path)) if path == installed
        ));
    }

    #[test]
    fn generated_metadata_requires_the_marker_and_core() {
        let directory = TestDirectory::new();
        let sysroot = directory.path().join("stage2");
        let installed = sysroot.join("lib/rustlib/target/lib");
        let generated = target_metadata_directory(&sysroot, "target").unwrap();
        assert_eq!(
            select_ready_target_libraries(&installed, &generated, false).unwrap(),
            None
        );

        let core = generated.join("libcore-generated.rmeta");
        write_library(&generated, "libcore-generated.rmeta");
        assert_eq!(
            select_ready_target_libraries(&installed, &generated, false).unwrap(),
            None
        );

        fs::remove_file(&core).unwrap();
        fs::write(generated.join(TARGET_METADATA_COMPLETE_FILE), b"").unwrap();
        assert_eq!(
            select_ready_target_libraries(&installed, &generated, false).unwrap(),
            None
        );

        fs::write(core, b"fixture").unwrap();
        assert_eq!(
            select_ready_target_libraries(&installed, &generated, false).unwrap(),
            Some(TargetLibrarySource::GeneratedMetadata(generated))
        );
    }

    #[test]
    fn generated_metadata_is_searched_only_for_rust_crates() {
        let source = TargetLibrarySource::GeneratedMetadata(PathBuf::from("metadata"));
        assert_eq!(
            source
                .search_paths()
                .map(|(kind, path)| (kind, path.as_os_str().to_owned()))
                .collect::<Vec<_>>(),
            vec![
                ("crate", OsString::from("metadata")),
                ("dependency", OsString::from("metadata")),
            ]
        );
    }

    fn write_library(directory: &Path, name: &str) {
        fs::create_dir_all(directory).unwrap();
        fs::write(directory.join(name), b"fixture").unwrap();
    }

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let repository = if manifest.join("tools/rid.rs").is_file() {
                manifest
            } else {
                manifest.parent().unwrap().to_path_buf()
            };
            let path = repository
                .join("target/target-library-source-tests")
                .join(format!(
                    "{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
}
