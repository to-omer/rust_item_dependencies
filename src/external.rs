//! Explicit, immutable compiler inputs for external Rust crates.

use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::digest::sha256;
use crate::error::AnalysisError;

const AR_MAGIC: &[u8] = b"!<arch>\n";
const RESERVED_EXTERN_NAMES: &[&str] = &[
    "Self",
    "alloc",
    "core",
    "crate",
    "proc_macro",
    "self",
    "std",
    "super",
];
const SNAPSHOT_DIRECTORY_ATTEMPTS: u64 = 1_024;

static SNAPSHOT_NONCE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ExternalCrate {
    extern_name: String,
    artifact: PathBuf,
}

impl ExternalCrate {
    pub(crate) fn new(extern_name: impl Into<String>, artifact: impl Into<PathBuf>) -> Self {
        Self {
            extern_name: extern_name.into(),
            artifact: artifact.into(),
        }
    }

    pub(crate) fn extern_name(&self) -> &str {
        &self.extern_name
    }

    pub(crate) fn artifact(&self) -> &Path {
        &self.artifact
    }
}

#[derive(Debug, Default)]
pub(crate) struct PreparedExternalCrates {
    direct: Vec<PreparedExternalCrate>,
    dependencies: Vec<PreparedDependencyArtifact>,
    snapshot: Option<SnapshotDirectory>,
}

impl PreparedExternalCrates {
    pub(crate) fn direct(&self) -> &[PreparedExternalCrate] {
        &self.direct
    }

    pub(crate) fn dependencies(&self) -> &[PreparedDependencyArtifact] {
        &self.dependencies
    }

    pub(crate) fn search_directory(&self) -> Option<&str> {
        self.snapshot.as_ref().map(SnapshotDirectory::argument)
    }
}

#[derive(Debug)]
pub(crate) struct PreparedExternalCrate {
    extern_name: String,
    file_name: String,
    artifact: PathBuf,
    digest: [u8; 32],
}

impl PreparedExternalCrate {
    pub(crate) fn extern_name(&self) -> &str {
        &self.extern_name
    }

    pub(crate) fn file_name(&self) -> &str {
        &self.file_name
    }

    pub(crate) fn artifact_argument(&self) -> &str {
        self.artifact
            .to_str()
            .expect("prepared external artifact paths are UTF-8")
    }

    pub(crate) fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct PreparedDependencyArtifact {
    file_name: String,
    digest: [u8; 32],
}

impl PreparedDependencyArtifact {
    pub(crate) fn file_name(&self) -> &str {
        &self.file_name
    }

    pub(crate) fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

#[derive(Debug)]
struct SnapshotDirectory {
    path: PathBuf,
    argument: String,
}

impl SnapshotDirectory {
    fn create() -> Result<Self, AnalysisError> {
        let configured_parent = std::env::temp_dir();
        let parent = canonical_snapshot_parent(configured_parent)?;
        let process = std::process::id();
        let mut last_path = parent.clone();
        for _ in 0..SNAPSHOT_DIRECTORY_ATTEMPTS {
            let nonce = SNAPSHOT_NONCE.fetch_add(1, Ordering::Relaxed);
            let path = parent.join(format!("rust-item-dependencies-{process}-{nonce}"));
            let argument = snapshot_argument(&path)?;
            let builder = fs::DirBuilder::new();
            #[cfg(unix)]
            let builder = {
                use std::os::unix::fs::DirBuilderExt;

                let mut builder = builder;
                builder.mode(0o700);
                builder
            };
            match builder.create(&path) {
                Ok(()) => return Ok(Self { path, argument }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    last_path = path;
                }
                Err(error) => {
                    return Err(snapshot_failure(path, error.kind()));
                }
            }
        }
        Err(snapshot_failure(last_path, io::ErrorKind::AlreadyExists))
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn argument(&self) -> &str {
        &self.argument
    }
}

fn canonical_snapshot_parent(configured_parent: PathBuf) -> Result<PathBuf, AnalysisError> {
    fs::canonicalize(&configured_parent)
        .map_err(|error| snapshot_failure(configured_parent, error.kind()))
}

impl Drop for SnapshotDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[derive(Clone)]
struct LoadedArtifact {
    bytes: Arc<[u8]>,
    digest: [u8; 32],
}

#[derive(Clone)]
struct RequestedArtifact {
    original_path: PathBuf,
    file_name: String,
    loaded: LoadedArtifact,
}

pub(crate) fn prepare_external_crates<'a>(
    external_crates: impl Iterator<Item = &'a ExternalCrate>,
    dependency_artifacts: impl Iterator<Item = &'a Path>,
) -> Result<PreparedExternalCrates, AnalysisError> {
    let mut external_crates = external_crates.peekable();
    let mut dependency_artifacts = dependency_artifacts.peekable();
    if external_crates.peek().is_none() && dependency_artifacts.peek().is_none() {
        return Ok(PreparedExternalCrates::default());
    }

    let mut loaded_by_path = BTreeMap::<PathBuf, LoadedArtifact>::new();
    let mut direct_requests = Vec::new();
    for external in external_crates {
        validate_extern_name(external.extern_name())?;
        direct_requests.push((
            external.extern_name().to_owned(),
            load_requested_artifact(external.artifact(), &mut loaded_by_path)?,
        ));
    }
    let mut dependency_requests = dependency_artifacts
        .map(|path| load_requested_artifact(path, &mut loaded_by_path))
        .collect::<Result<Vec<_>, _>>()?;

    validate_direct_names(&direct_requests)?;
    dependency_requests.retain(|dependency| {
        !direct_requests.iter().any(|(_, direct)| {
            direct.file_name == dependency.file_name
                && direct.loaded.digest == dependency.loaded.digest
        })
    });
    for dependency in &dependency_requests {
        validate_dependency_file_name(dependency)?;
    }
    let staged = unique_staged_artifacts(
        direct_requests
            .iter()
            .map(|(_, artifact)| artifact)
            .chain(dependency_requests.iter()),
    )?;

    let snapshot = SnapshotDirectory::create()?;
    let mut written = Vec::new();
    for artifact in staged.values() {
        match write_snapshot_artifact(&snapshot, artifact) {
            Ok(()) => written.push(artifact),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                let Some(previous) = matching_snapshot_artifact(&snapshot, artifact, &written)
                else {
                    return Err(snapshot_failure(
                        snapshot.path().join(&artifact.file_name),
                        error.kind(),
                    ));
                };
                return Err(AnalysisError::ConflictingExternalCrateArtifactName {
                    file_name: artifact.file_name.clone(),
                    first_path: previous.original_path.clone(),
                    second_path: artifact.original_path.clone(),
                });
            }
            Err(error) => {
                return Err(snapshot_failure(
                    snapshot.path().join(&artifact.file_name),
                    error.kind(),
                ));
            }
        }
    }

    let mut direct = direct_requests
        .into_iter()
        .map(|(extern_name, artifact)| PreparedExternalCrate {
            artifact: snapshot.path().join(&artifact.file_name),
            extern_name,
            file_name: artifact.file_name,
            digest: artifact.loaded.digest,
        })
        .collect::<Vec<_>>();
    direct.sort_by(|left, right| {
        (&left.extern_name, &left.file_name, left.digest).cmp(&(
            &right.extern_name,
            &right.file_name,
            right.digest,
        ))
    });
    direct.dedup_by(|left, right| {
        left.extern_name == right.extern_name
            && left.file_name == right.file_name
            && left.digest == right.digest
    });

    let mut dependencies = dependency_requests
        .into_iter()
        .map(|artifact| PreparedDependencyArtifact {
            file_name: artifact.file_name,
            digest: artifact.loaded.digest,
        })
        .collect::<Vec<_>>();
    dependencies.sort_by(|left, right| {
        (&left.file_name, left.digest).cmp(&(&right.file_name, right.digest))
    });
    dependencies.dedup();

    Ok(PreparedExternalCrates {
        direct,
        dependencies,
        snapshot: Some(snapshot),
    })
}

fn validate_extern_name(name: &str) -> Result<(), AnalysisError> {
    let mut bytes = name.bytes();
    let valid = bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && name != "_"
        && !RESERVED_EXTERN_NAMES.contains(&name);
    if valid {
        Ok(())
    } else {
        Err(AnalysisError::InvalidExternalCrateName {
            name: name.to_owned(),
        })
    }
}

fn load_requested_artifact(
    path: &Path,
    loaded_by_path: &mut BTreeMap<PathBuf, LoadedArtifact>,
) -> Result<RequestedArtifact, AnalysisError> {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .filter(|name| !name.is_empty())
        .ok_or_else(|| AnalysisError::UnsupportedExternalCrateArtifact {
            path: path.to_owned(),
        })?
        .to_owned();
    if Path::new(&file_name)
        .extension()
        .and_then(|value| value.to_str())
        != Some("rlib")
        || !file_name.starts_with("lib")
    {
        return Err(AnalysisError::UnsupportedExternalCrateArtifact {
            path: path.to_owned(),
        });
    }

    let canonical =
        fs::canonicalize(path).map_err(|error| artifact_unreadable(path, error.kind()))?;
    let loaded = if let Some(loaded) = loaded_by_path.get(&canonical) {
        loaded.clone()
    } else {
        let loaded = read_artifact(path, &canonical)?;
        loaded_by_path.insert(canonical, loaded.clone());
        loaded
    };
    if !loaded.bytes.starts_with(AR_MAGIC) {
        return Err(AnalysisError::UnsupportedExternalCrateArtifact {
            path: path.to_owned(),
        });
    }
    Ok(RequestedArtifact {
        original_path: path.to_owned(),
        file_name,
        loaded,
    })
}

fn validate_dependency_file_name(artifact: &RequestedArtifact) -> Result<(), AnalysisError> {
    let valid = artifact
        .file_name
        .strip_prefix("lib")
        .and_then(|name| name.bytes().next())
        .is_some_and(|first| first.is_ascii_alphanumeric() || first == b'_');
    if valid {
        Ok(())
    } else {
        Err(AnalysisError::UnsupportedExternalCrateArtifact {
            path: artifact.original_path.clone(),
        })
    }
}

fn read_artifact(path: &Path, canonical: &Path) -> Result<LoadedArtifact, AnalysisError> {
    let metadata =
        fs::metadata(canonical).map_err(|error| artifact_unreadable(path, error.kind()))?;
    if !metadata.is_file() {
        return Err(artifact_unreadable(path, io::ErrorKind::InvalidInput));
    }
    let mut file =
        File::open(canonical).map_err(|error| artifact_unreadable(path, error.kind()))?;
    let metadata = file
        .metadata()
        .map_err(|error| artifact_unreadable(path, error.kind()))?;
    if !metadata.is_file() {
        return Err(artifact_unreadable(path, io::ErrorKind::InvalidInput));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)
        .map_err(|error| artifact_unreadable(path, error.kind()))?;
    let digest = sha256(&bytes);
    Ok(LoadedArtifact {
        bytes: bytes.into(),
        digest,
    })
}

fn validate_direct_names(direct: &[(String, RequestedArtifact)]) -> Result<(), AnalysisError> {
    let mut by_name = BTreeMap::<&str, &RequestedArtifact>::new();
    for (name, artifact) in direct {
        if let Some(previous) = by_name.insert(name, artifact)
            && (previous.file_name != artifact.file_name
                || previous.loaded.digest != artifact.loaded.digest)
        {
            return Err(AnalysisError::ConflictingExternalCrate {
                name: name.clone(),
                first_path: previous.original_path.clone(),
                second_path: artifact.original_path.clone(),
            });
        }
    }
    Ok(())
}

fn unique_staged_artifacts<'a>(
    artifacts: impl Iterator<Item = &'a RequestedArtifact>,
) -> Result<BTreeMap<String, RequestedArtifact>, AnalysisError> {
    let mut by_name = BTreeMap::<String, RequestedArtifact>::new();
    for artifact in artifacts {
        if let Some(previous) = by_name.get(&artifact.file_name) {
            if previous.loaded.digest != artifact.loaded.digest {
                return Err(AnalysisError::ConflictingExternalCrateArtifactName {
                    file_name: artifact.file_name.clone(),
                    first_path: previous.original_path.clone(),
                    second_path: artifact.original_path.clone(),
                });
            }
        } else {
            by_name.insert(artifact.file_name.clone(), artifact.clone());
        }
    }
    Ok(by_name)
}

fn write_snapshot_artifact(
    snapshot: &SnapshotDirectory,
    artifact: &RequestedArtifact,
) -> io::Result<()> {
    let path = snapshot.path().join(&artifact.file_name);
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    file.write_all(&artifact.loaded.bytes)
}

fn matching_snapshot_artifact<'a>(
    snapshot: &SnapshotDirectory,
    artifact: &RequestedArtifact,
    written: &[&'a RequestedArtifact],
) -> Option<&'a RequestedArtifact> {
    let destination = snapshot.path().join(&artifact.file_name);
    written.iter().copied().find(|previous| {
        same_snapshot_file(&destination, &snapshot.path().join(&previous.file_name))
            .unwrap_or(false)
    })
}

fn same_snapshot_file(left: &Path, right: &Path) -> io::Result<bool> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let left_metadata = fs::metadata(left)?;
        let right_metadata = fs::metadata(right)?;
        Ok(left_metadata.dev() == right_metadata.dev()
            && left_metadata.ino() == right_metadata.ino())
    }
    #[cfg(not(unix))]
    {
        Ok(fs::canonicalize(left)?.eq(&fs::canonicalize(right)?))
    }
}

fn snapshot_argument(path: &Path) -> Result<String, AnalysisError> {
    path.to_str()
        .map(str::to_owned)
        .ok_or_else(|| snapshot_failure(path.to_owned(), io::ErrorKind::InvalidInput))
}

fn artifact_unreadable(path: &Path, error: io::ErrorKind) -> AnalysisError {
    AnalysisError::ExternalCrateArtifactUnreadable {
        path: path.to_owned(),
        error,
    }
}

fn snapshot_failure(path: PathBuf, error: io::ErrorKind) -> AnalysisError {
    AnalysisError::ExternalCrateSnapshotFailure { path, error }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);

            let parent =
                Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tests/external-preparation");
            fs::create_dir_all(&parent).unwrap();
            for _ in 0..SNAPSHOT_DIRECTORY_ATTEMPTS {
                let path = parent.join(format!(
                    "{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                    Err(error) => panic!("cannot create external preparation test path: {error}"),
                }
            }
            panic!("cannot allocate an external preparation test path")
        }

        fn artifact(&self, relative: &str, body: &[u8]) -> PathBuf {
            let path = self.0.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            let mut bytes = AR_MAGIC.to_vec();
            bytes.extend_from_slice(body);
            fs::write(&path, bytes).unwrap();
            path
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn prepare(
        direct: &[(&str, &Path)],
        dependencies: &[&Path],
    ) -> Result<PreparedExternalCrates, AnalysisError> {
        let direct = direct
            .iter()
            .map(|(name, artifact)| ExternalCrate::new(*name, *artifact))
            .collect::<Vec<_>>();
        prepare_external_crates(direct.iter(), dependencies.iter().copied())
    }

    #[test]
    fn preparation_snapshots_only_the_declared_artifact_bytes() {
        let directory = TestDirectory::new();
        let direct = directory.artifact("libdirect.rlib", b"direct");
        let dependency = directory.artifact("libdependency.rlib", b"dependency");
        let prepared = prepare(&[("direct", &direct)], &[&dependency]).unwrap();
        let snapshot_directory = PathBuf::from(prepared.search_directory().unwrap());

        fs::write(&direct, b"changed").unwrap();
        fs::write(&dependency, b"changed").unwrap();

        assert_eq!(
            fs::read(&prepared.direct()[0].artifact).unwrap(),
            [AR_MAGIC, b"direct"].concat()
        );
        assert_eq!(
            fs::read(snapshot_directory.join("libdependency.rlib")).unwrap(),
            [AR_MAGIC, b"dependency"].concat()
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let directory_mode = fs::metadata(&snapshot_directory)
                .unwrap()
                .permissions()
                .mode();
            let artifact_mode = fs::metadata(&prepared.direct()[0].artifact)
                .unwrap()
                .permissions()
                .mode();
            assert_eq!(directory_mode & 0o077, 0);
            assert_eq!(artifact_mode & 0o077, 0);
        }
        drop(prepared);
        assert!(!snapshot_directory.exists());
    }

    #[test]
    fn direct_artifact_is_not_repeated_or_revalidated_as_a_dependency() {
        let directory = TestDirectory::new();
        let artifact = directory.artifact("libdirect.rlib", b"direct");

        let prepared = prepare(&[("direct", &artifact)], &[&artifact]).unwrap();

        assert_eq!(prepared.direct().len(), 1);
        assert!(prepared.dependencies().is_empty());

        let non_searchable_name = directory.artifact("lib-.rlib", b"direct");
        let prepared = prepare(&[("direct", &non_searchable_name)], &[&non_searchable_name])
            .expect("a repeated direct artifact adds no search input");
        assert_eq!(prepared.direct().len(), 1);
        assert!(prepared.dependencies().is_empty());
    }

    #[test]
    fn preparation_rejects_invalid_names_and_artifact_formats() {
        let directory = TestDirectory::new();
        let rlib = directory.artifact("libvalid.rlib", b"valid");
        for name in [
            "",
            "_",
            "Self",
            "bad-name",
            "crate",
            "proc_macro",
            "std",
            "super",
        ] {
            assert!(matches!(
                prepare(&[(name, &rlib)], &[]),
                Err(AnalysisError::InvalidExternalCrateName { .. })
            ));
        }

        let rmeta = directory.artifact("libvalid.rmeta", b"metadata");
        assert!(matches!(
            prepare(&[("valid", &rmeta)], &[]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));
        let missing_prefix = directory.artifact("valid.rlib", AR_MAGIC);
        assert!(matches!(
            prepare(&[("valid", &missing_prefix)], &[]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));
        assert!(matches!(
            prepare(&[], &[&missing_prefix]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));
        let direct_only_name = directory.artifact("lib-.rlib", AR_MAGIC);
        prepare(&[("valid", &direct_only_name)], &[])
            .expect("an explicit --extern path does not use crate-name search");
        assert!(matches!(
            prepare(&[], &[&direct_only_name]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));
        let invalid = directory.0.join("libinvalid.rlib");
        fs::write(&invalid, b"not an archive").unwrap();
        assert!(matches!(
            prepare(&[("invalid", &invalid)], &[]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));

        let directory_artifact = directory.0.join("libdirectory.rlib");
        fs::create_dir(&directory_artifact).unwrap();
        assert!(matches!(
            prepare(&[("directory", &directory_artifact)], &[]),
            Err(AnalysisError::ExternalCrateArtifactUnreadable {
                error: io::ErrorKind::InvalidInput,
                ..
            })
        ));
    }

    #[test]
    fn preparation_rejects_alias_and_snapshot_name_collisions() {
        let directory = TestDirectory::new();
        let first = directory.artifact("libfirst.rlib", b"first");
        let second = directory.artifact("libsecond.rlib", b"second");
        assert!(matches!(
            prepare(&[("same", &first), ("same", &second)], &[]),
            Err(AnalysisError::ConflictingExternalCrate { .. })
        ));

        let left = directory.artifact("left/libsame.rlib", b"left");
        let right = directory.artifact("right/libsame.rlib", b"right");
        assert!(matches!(
            prepare(&[("left", &left)], &[&right]),
            Err(AnalysisError::ConflictingExternalCrateArtifactName { .. })
        ));
    }

    #[test]
    fn preparation_handles_file_names_according_to_the_snapshot_filesystem() {
        let directory = TestDirectory::new();
        let lower = directory.artifact("left/libcase.rlib", b"same");
        let upper_same = directory.artifact("right/libCASE.rlib", b"same");
        let same = prepare(&[("lower", &lower)], &[&upper_same]);

        let upper_different = directory.artifact("third/libCASE.rlib", b"different");
        let different = prepare(&[("lower", &lower)], &[&upper_different]);
        if temporary_file_names_distinguish_ascii_case() {
            assert!(same.is_ok());
            assert!(different.is_ok());
        } else {
            assert!(matches!(
                same,
                Err(AnalysisError::ConflictingExternalCrateArtifactName { .. })
            ));
            assert!(matches!(
                different,
                Err(AnalysisError::ConflictingExternalCrateArtifactName { .. })
            ));
        }
    }

    #[cfg(unix)]
    #[test]
    fn snapshot_arguments_reject_non_utf8_paths() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let path = PathBuf::from(OsString::from_vec(b"snapshot-\xff".to_vec()));
        assert!(matches!(
            snapshot_argument(&path),
            Err(AnalysisError::ExternalCrateSnapshotFailure {
                error: io::ErrorKind::InvalidInput,
                ..
            })
        ));
    }

    #[test]
    fn relative_snapshot_parent_is_fixed_to_an_absolute_path() {
        let directory = TestDirectory::new();
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let relative = directory
            .0
            .strip_prefix(manifest)
            .expect("the test directory must be inside the repository");
        assert_eq!(
            fs::canonicalize(".").unwrap(),
            fs::canonicalize(manifest).unwrap()
        );

        let resolved = canonical_snapshot_parent(relative.to_owned()).unwrap();

        assert!(resolved.is_absolute());
        assert_eq!(resolved, fs::canonicalize(&directory.0).unwrap());
    }

    fn temporary_file_names_distinguish_ascii_case() -> bool {
        let snapshot = SnapshotDirectory::create().unwrap();
        fs::write(snapshot.path().join("case-probe"), b"probe").unwrap();
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(snapshot.path().join("CASE-PROBE"))
        {
            Ok(_) => true,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => false,
            Err(error) => panic!("cannot probe temporary filesystem case handling: {error}"),
        }
    }
}
