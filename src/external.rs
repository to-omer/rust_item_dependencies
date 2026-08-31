//! Explicit, immutable compiler inputs for external Rust crates.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(windows)]
use std::sync::{Mutex, OnceLock, Weak};

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
const SNAPSHOT_PARENT_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_PARENT";
const SNAPSHOT_OWNER_ENV: &str = "RUST_ITEM_DEPENDENCIES_SNAPSHOT_OWNER";
const ANALYZER_SNAPSHOT_PREFIX: &str = "rust-item-dependencies-";
const SNAPSHOT_PROBE_PREFIX: &str = "rust-item-dependencies-probe-";
#[cfg(windows)]
const PROCESS_OWNER_PREFIX: &str = ".rust-item-dependencies-owner-";
#[cfg(windows)]
const PROCESS_ROOT_PREFIX: &str = "rust-item-dependencies-process-";
#[cfg(windows)]
const PROCESS_SNAPSHOT_PREFIX: &str = "snapshot-";
#[cfg(windows)]
const SNAPSHOT_PARENT_LOCK_FILE: &str = ".rust-item-dependencies-parent-lock";

static SNAPSHOT_NONCE: AtomicU64 = AtomicU64::new(0);
#[cfg(windows)]
static PROCESS_EXTERNAL_STORES: OnceLock<
    Mutex<BTreeMap<ProcessStoreKey, ProcessExternalArtifactStore>>,
> = OnceLock::new();

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
    proc_macro_execution_artifacts: Vec<PreparedProcMacroExecutionArtifact>,
    snapshot: Option<SnapshotDirectory>,
}

impl PreparedExternalCrates {
    pub(crate) fn direct(&self) -> &[PreparedExternalCrate] {
        &self.direct
    }

    pub(crate) fn proc_macro_execution_artifacts(&self) -> &[PreparedProcMacroExecutionArtifact] {
        &self.proc_macro_execution_artifacts
    }

    pub(crate) fn search_directories(&self) -> impl Iterator<Item = &str> {
        let analyzer = self.snapshot.iter().map(SnapshotDirectory::argument);
        #[cfg(windows)]
        {
            analyzer.chain(
                self.proc_macro_execution_artifacts
                    .iter()
                    .map(|artifact| artifact.snapshot.argument()),
            )
        }
        #[cfg(not(windows))]
        {
            analyzer
        }
    }

    pub(crate) fn artifact_directories(&self) -> impl Iterator<Item = &Path> {
        let analyzer = self.snapshot.iter().map(SnapshotDirectory::path);
        #[cfg(windows)]
        {
            analyzer.chain(
                self.proc_macro_execution_artifacts
                    .iter()
                    .map(|artifact| artifact.snapshot.path()),
            )
        }
        #[cfg(not(windows))]
        {
            analyzer
        }
    }

    pub(crate) fn proc_macro_load_state(&self) -> PreparedProcMacroLoadState {
        let allowed = self
            .proc_macro_execution_artifacts
            .iter()
            .map(|artifact| artifact.artifact.clone())
            .collect();
        #[cfg(windows)]
        let snapshots = self
            .proc_macro_execution_artifacts
            .iter()
            .map(|artifact| (artifact.artifact.clone(), artifact.snapshot.clone()))
            .collect();
        PreparedProcMacroLoadState {
            allowed,
            #[cfg(windows)]
            snapshots,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct PreparedProcMacroLoadState {
    allowed: BTreeSet<PathBuf>,
    #[cfg(windows)]
    snapshots: BTreeMap<PathBuf, ProcessSnapshot>,
}

impl PreparedProcMacroLoadState {
    pub(crate) fn is_allowed(&self, artifact: &Path) -> bool {
        self.allowed.contains(artifact)
    }

    pub(crate) fn loaded(&self, artifact: &Path) {
        #[cfg(windows)]
        self.snapshots
            .get(artifact)
            .expect("an allowed procedural macro must have a prepared snapshot")
            .pin();
        #[cfg(not(windows))]
        let _ = artifact;
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ExternalArtifactKind {
    Rlib,
    HostDynamicLibrary,
}

#[derive(Debug)]
pub(crate) struct PreparedExternalCrate {
    extern_name: String,
    artifact: PathBuf,
}

impl PreparedExternalCrate {
    pub(crate) fn extern_name(&self) -> &str {
        &self.extern_name
    }

    pub(crate) fn artifact_argument(&self) -> &str {
        self.artifact
            .to_str()
            .expect("prepared external artifact paths are UTF-8")
    }
}

#[derive(Debug)]
pub(crate) struct PreparedProcMacroExecutionArtifact {
    artifact: PathBuf,
    #[cfg(windows)]
    snapshot: ProcessSnapshot,
}

impl PreparedProcMacroExecutionArtifact {
    pub(crate) fn artifact(&self) -> &Path {
        &self.artifact
    }
}

#[derive(Clone, Debug)]
struct SnapshotLocation {
    path: PathBuf,
    argument: String,
}

impl SnapshotLocation {
    fn create(parent: &Path, prefix: &str) -> Result<Self, AnalysisError> {
        let process = std::process::id();
        let mut last_path = parent.to_owned();
        for _ in 0..SNAPSHOT_DIRECTORY_ATTEMPTS {
            let nonce = SNAPSHOT_NONCE.fetch_add(1, Ordering::Relaxed);
            let path = parent.join(format!("{prefix}{process}-{nonce}"));
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

#[derive(Debug)]
struct SnapshotDirectory(Option<SnapshotLocation>);

impl SnapshotDirectory {
    fn create(parent: &Path, prefix: &str) -> Result<Self, AnalysisError> {
        Ok(Self(Some(SnapshotLocation::create(parent, prefix)?)))
    }

    fn path(&self) -> &Path {
        self.0
            .as_ref()
            .expect("snapshot location must exist")
            .path()
    }

    fn argument(&self) -> &str {
        self.0
            .as_ref()
            .expect("snapshot location must exist")
            .argument()
    }
}

fn snapshot_parent() -> Result<PathBuf, AnalysisError> {
    let configured_parent = std::env::var_os(SNAPSHOT_PARENT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    canonical_snapshot_parent(configured_parent)
}

fn canonical_snapshot_parent(configured_parent: PathBuf) -> Result<PathBuf, AnalysisError> {
    fs::canonicalize(&configured_parent)
        .map_err(|error| snapshot_failure(configured_parent, error.kind()))
}

impl Drop for SnapshotDirectory {
    fn drop(&mut self) {
        if let Some(location) = self.0.take() {
            let _ = fs::remove_dir_all(location.path);
        }
    }
}

#[cfg(windows)]
#[derive(Clone, Debug)]
struct ProcessSnapshot {
    store: ProcessStoreKey,
    snapshot: Arc<SnapshotDirectory>,
}

#[cfg(windows)]
impl ProcessSnapshot {
    fn path(&self) -> &Path {
        self.snapshot.path()
    }

    fn argument(&self) -> &str {
        self.snapshot.argument()
    }

    fn pin(&self) {
        let stores = PROCESS_EXTERNAL_STORES.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut stores = stores
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let store = stores
            .get_mut(&self.store)
            .expect("a prepared procedural macro store must remain registered");
        if !store
            .loaded
            .iter()
            .any(|snapshot| Arc::ptr_eq(snapshot, &self.snapshot))
        {
            store.loaded.push(Arc::clone(&self.snapshot));
        }
    }
}

#[cfg(windows)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArtifactKey {
    file_name: String,
    kind: ExternalArtifactKind,
    digest: [u8; 32],
}

#[cfg(windows)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProcessStoreKey {
    parent: PathBuf,
    token: Option<String>,
}

#[cfg(windows)]
#[derive(Debug)]
struct ProcessExternalArtifactStore {
    root: PathBuf,
    _owner: File,
    snapshots: BTreeMap<ArtifactKey, Weak<SnapshotDirectory>>,
    loaded: Vec<Arc<SnapshotDirectory>>,
}

#[cfg(windows)]
#[derive(Debug)]
struct SnapshotParentLock(File);

#[cfg(windows)]
impl SnapshotParentLock {
    fn acquire(parent: &Path) -> Result<Self, AnalysisError> {
        let path = parent.join(SNAPSHOT_PARENT_LOCK_FILE);
        let mut options = OpenOptions::new();
        options.read(true).write(true).create(true);
        let file = options
            .open(&path)
            .map_err(|error| snapshot_failure(path.clone(), error.kind()))?;
        file.lock()
            .map_err(|error| snapshot_failure(path, error.kind()))?;
        Ok(Self(file))
    }
}

#[cfg(windows)]
impl ProcessExternalArtifactStore {
    fn create(
        parent: &Path,
        configured_token: Option<&str>,
        _parent_lock: &SnapshotParentLock,
    ) -> Result<Self, AnalysisError> {
        let process = std::process::id();
        let mut last_owner = parent.to_owned();
        let attempts = if configured_token.is_some() {
            1
        } else {
            SNAPSHOT_DIRECTORY_ATTEMPTS
        };
        for _ in 0..attempts {
            let nonce = SNAPSHOT_NONCE.fetch_add(1, Ordering::Relaxed);
            let token = configured_token
                .map(str::to_owned)
                .unwrap_or_else(|| format!("{process}-{nonce}"));
            let owner_path = parent.join(format!("{PROCESS_OWNER_PREFIX}{token}"));
            let root_path = parent.join(format!("{PROCESS_ROOT_PREFIX}{token}"));
            snapshot_argument(&root_path)?;
            let mut owner_options = OpenOptions::new();
            owner_options.read(true).write(true).create_new(true);
            let owner = match owner_options.open(&owner_path) {
                Ok(owner) => owner,
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    last_owner = owner_path;
                    continue;
                }
                Err(error) => return Err(snapshot_failure(owner_path, error.kind())),
            };
            if let Err(error) = owner.lock() {
                drop(owner);
                let _ = fs::remove_file(&owner_path);
                return Err(snapshot_failure(owner_path, error.kind()));
            }
            match fs::create_dir(&root_path) {
                Ok(()) => {
                    return Ok(Self {
                        root: root_path,
                        _owner: owner,
                        snapshots: BTreeMap::new(),
                        loaded: Vec::new(),
                    });
                }
                Err(error) => {
                    drop(owner);
                    let _ = fs::remove_file(&owner_path);
                    if error.kind() == io::ErrorKind::AlreadyExists {
                        last_owner = owner_path;
                        continue;
                    }
                    return Err(snapshot_failure(root_path, error.kind()));
                }
            }
        }
        Err(snapshot_failure(last_owner, io::ErrorKind::AlreadyExists))
    }

    fn snapshot(
        &mut self,
        artifact: &RequestedArtifact,
    ) -> Result<Arc<SnapshotDirectory>, AnalysisError> {
        let key = ArtifactKey {
            file_name: artifact.file_name.clone(),
            kind: artifact.kind,
            digest: artifact.loaded.digest,
        };
        if let Some(snapshot) = self.snapshots.get(&key).and_then(Weak::upgrade) {
            return Ok(snapshot);
        }

        let snapshot = Arc::new(SnapshotDirectory::create(
            &self.root,
            PROCESS_SNAPSHOT_PREFIX,
        )?);
        write_snapshot_artifact(&snapshot, artifact).map_err(|error| {
            snapshot_failure(snapshot.path().join(&artifact.file_name), error.kind())
        })?;
        self.snapshots.insert(key, Arc::downgrade(&snapshot));
        Ok(snapshot)
    }
}

#[cfg(windows)]
fn reap_stale_process_stores(
    parent: &Path,
    _parent_lock: &SnapshotParentLock,
) -> Result<(), AnalysisError> {
    for entry in
        fs::read_dir(parent).map_err(|error| snapshot_failure(parent.to_owned(), error.kind()))?
    {
        let entry = entry.map_err(|error| snapshot_failure(parent.to_owned(), error.kind()))?;
        let file_name = entry.file_name();
        let Some(token) = file_name
            .to_str()
            .and_then(|name| name.strip_prefix(PROCESS_OWNER_PREFIX))
            .filter(|token| !token.is_empty())
        else {
            continue;
        };
        let owner_path = entry.path();
        let mut options = OpenOptions::new();
        options.read(true).write(true);
        let owner = match options.open(&owner_path) {
            Ok(owner) => owner,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(snapshot_failure(owner_path, error.kind())),
        };
        match owner.try_lock() {
            Ok(()) => {}
            Err(fs::TryLockError::WouldBlock) => continue,
            Err(fs::TryLockError::Error(error)) => {
                return Err(snapshot_failure(owner_path, error.kind()));
            }
        }
        let root = parent.join(format!("{PROCESS_ROOT_PREFIX}{token}"));
        match fs::remove_dir_all(&root) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(snapshot_failure(root, error.kind())),
        }
        drop(owner);
        match fs::remove_file(&owner_path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(snapshot_failure(owner_path, error.kind())),
        }
    }
    Ok(())
}

#[cfg(windows)]
fn process_snapshot(
    key: &ProcessStoreKey,
    artifact: &RequestedArtifact,
    parent_lock: &SnapshotParentLock,
) -> Result<ProcessSnapshot, AnalysisError> {
    let stores = PROCESS_EXTERNAL_STORES.get_or_init(|| Mutex::new(BTreeMap::new()));
    let mut stores = stores
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if !stores.contains_key(key) {
        stores.insert(
            key.clone(),
            ProcessExternalArtifactStore::create(&key.parent, key.token.as_deref(), parent_lock)?,
        );
    }
    let snapshot = stores
        .get_mut(key)
        .expect("process external artifact store must exist")
        .snapshot(artifact)?;
    Ok(ProcessSnapshot {
        store: key.clone(),
        snapshot,
    })
}

#[cfg(windows)]
fn process_store_root(
    key: &ProcessStoreKey,
    parent_lock: &SnapshotParentLock,
) -> Result<PathBuf, AnalysisError> {
    let stores = PROCESS_EXTERNAL_STORES.get_or_init(|| Mutex::new(BTreeMap::new()));
    let mut stores = stores
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if !stores.contains_key(key) {
        stores.insert(
            key.clone(),
            ProcessExternalArtifactStore::create(&key.parent, key.token.as_deref(), parent_lock)?,
        );
    }
    Ok(stores
        .get(key)
        .expect("process external artifact store must exist")
        .root
        .clone())
}

#[cfg(windows)]
fn configured_process_store_token() -> Result<Option<String>, AnalysisError> {
    let Some(token) = std::env::var_os(SNAPSHOT_OWNER_ENV) else {
        return Ok(None);
    };
    let path = PathBuf::from(&token);
    let token = token.to_str().filter(|token| {
        !token.is_empty()
            && token
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    });
    token
        .map(|token| Some(token.to_owned()))
        .ok_or_else(|| snapshot_failure(path, io::ErrorKind::InvalidInput))
}

struct PreparedSnapshots {
    analyzer: Option<SnapshotDirectory>,
    #[cfg(windows)]
    proc_macros: BTreeMap<(String, [u8; 32]), ProcessSnapshot>,
}

impl PreparedSnapshots {
    fn artifact_path(&self, artifact: &RequestedArtifact) -> PathBuf {
        #[cfg(windows)]
        if let Some(snapshot) = self
            .proc_macros
            .get(&(artifact.file_name.clone(), artifact.loaded.digest))
        {
            return snapshot.path().join(&artifact.file_name);
        }
        self.analyzer
            .as_ref()
            .expect("every ordinary external artifact must have an analyzer snapshot")
            .path()
            .join(&artifact.file_name)
    }
}

fn prepare_snapshots(
    parent: &Path,
    staged: &BTreeMap<String, RequestedArtifact>,
    proc_macro_execution_artifacts: &BTreeSet<(String, [u8; 32])>,
) -> Result<PreparedSnapshots, AnalysisError> {
    #[cfg(windows)]
    {
        let parent_lock = SnapshotParentLock::acquire(parent)?;
        reap_stale_process_stores(parent, &parent_lock)?;
        let key = ProcessStoreKey {
            parent: parent.to_owned(),
            token: configured_process_store_token()?,
        };
        let root = process_store_root(&key, &parent_lock)?;
        validate_snapshot_file_names(&root, staged)?;
        let ordinary = staged
            .iter()
            .filter(|(_, artifact)| {
                !proc_macro_execution_artifacts
                    .contains(&(artifact.file_name.clone(), artifact.loaded.digest))
            })
            .map(|(name, artifact)| (name.clone(), artifact.clone()))
            .collect::<BTreeMap<_, _>>();
        let analyzer = if ordinary.is_empty() {
            None
        } else {
            let snapshot = SnapshotDirectory::create(&root, ANALYZER_SNAPSHOT_PREFIX)?;
            stage_artifacts(&snapshot, &ordinary)?;
            Some(snapshot)
        };
        let mut proc_macros = BTreeMap::new();
        for artifact in staged.values().filter(|artifact| {
            proc_macro_execution_artifacts
                .contains(&(artifact.file_name.clone(), artifact.loaded.digest))
        }) {
            let snapshot = process_snapshot(&key, artifact, &parent_lock)?;
            proc_macros.insert(
                (artifact.file_name.clone(), artifact.loaded.digest),
                snapshot,
            );
        }
        Ok(PreparedSnapshots {
            analyzer,
            proc_macros,
        })
    }
    #[cfg(not(windows))]
    {
        let _ = proc_macro_execution_artifacts;
        validate_snapshot_file_names(parent, staged)?;
        let analyzer = if staged.is_empty() {
            None
        } else {
            let snapshot = SnapshotDirectory::create(parent, ANALYZER_SNAPSHOT_PREFIX)?;
            stage_artifacts(&snapshot, staged)?;
            Some(snapshot)
        };
        Ok(PreparedSnapshots { analyzer })
    }
}

fn reap_snapshot_parent(parent: &Path) -> Result<(), AnalysisError> {
    #[cfg(windows)]
    {
        let parent_lock = SnapshotParentLock::acquire(parent)?;
        reap_stale_process_stores(parent, &parent_lock)?;
    }
    #[cfg(not(windows))]
    let _ = parent;
    Ok(())
}

#[derive(Clone)]
struct LoadedArtifact {
    bytes: Arc<[u8]>,
    digest: [u8; 32],
}

#[derive(Clone)]
struct RequestedArtifact {
    original_path: PathBuf,
    canonical_path: PathBuf,
    file_name: String,
    loaded: LoadedArtifact,
    kind: ExternalArtifactKind,
}

pub(crate) fn prepare_external_crates<'a>(
    external_crates: impl Iterator<Item = &'a ExternalCrate>,
    dependency_artifacts: impl Iterator<Item = &'a Path>,
    proc_macro_execution_artifacts: impl Iterator<Item = &'a Path>,
) -> Result<PreparedExternalCrates, AnalysisError> {
    let mut external_crates = external_crates.peekable();
    let mut dependency_artifacts = dependency_artifacts.peekable();
    let mut proc_macro_execution_artifacts = proc_macro_execution_artifacts.peekable();
    if external_crates.peek().is_none()
        && dependency_artifacts.peek().is_none()
        && proc_macro_execution_artifacts.peek().is_none()
    {
        if std::env::var_os(SNAPSHOT_PARENT_ENV).is_some() {
            let snapshot_parent = snapshot_parent()?;
            reap_snapshot_parent(&snapshot_parent)?;
        }
        return Ok(PreparedExternalCrates::default());
    }
    let snapshot_parent = snapshot_parent()?;

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
    let proc_macro_execution_artifacts = resolve_proc_macro_execution_artifacts(
        proc_macro_execution_artifacts,
        direct_requests
            .iter()
            .map(|(_, artifact)| artifact)
            .chain(dependency_requests.iter()),
    )?;
    dependency_requests.retain(|dependency| {
        !direct_requests.iter().any(|(_, direct)| {
            direct.kind == dependency.kind
                && direct.file_name == dependency.file_name
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
    let snapshots = prepare_snapshots(&snapshot_parent, &staged, &proc_macro_execution_artifacts)?;

    direct_requests.sort_by(|(left_name, left), (right_name, right)| {
        (left_name, left.kind, &left.file_name, left.loaded.digest).cmp(&(
            right_name,
            right.kind,
            &right.file_name,
            right.loaded.digest,
        ))
    });
    direct_requests.dedup_by(|(left_name, left), (right_name, right)| {
        left_name == right_name
            && left.kind == right.kind
            && left.file_name == right.file_name
            && left.loaded.digest == right.loaded.digest
    });
    let direct = direct_requests
        .into_iter()
        .map(|(extern_name, artifact)| PreparedExternalCrate {
            artifact: snapshots.artifact_path(&artifact),
            extern_name,
        })
        .collect::<Vec<_>>();

    let proc_macro_execution_artifacts = proc_macro_execution_artifacts
        .into_iter()
        .map(|(file_name, digest)| {
            #[cfg(not(windows))]
            let _ = digest;
            #[cfg(windows)]
            let snapshot = snapshots
                .proc_macros
                .get(&(file_name.clone(), digest))
                .expect("every permitted procedural macro must have a process snapshot")
                .clone();
            let artifact = {
                #[cfg(windows)]
                {
                    snapshot.path().join(&file_name)
                }
                #[cfg(not(windows))]
                {
                    snapshots
                        .analyzer
                        .as_ref()
                        .expect("every external artifact must have an analyzer snapshot")
                        .path()
                        .join(&file_name)
                }
            };
            PreparedProcMacroExecutionArtifact {
                artifact,
                #[cfg(windows)]
                snapshot,
            }
        })
        .collect();

    Ok(PreparedExternalCrates {
        direct,
        proc_macro_execution_artifacts,
        snapshot: snapshots.analyzer,
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
    let kind = artifact_kind(&file_name).ok_or_else(|| {
        AnalysisError::UnsupportedExternalCrateArtifact {
            path: path.to_owned(),
        }
    })?;

    let canonical =
        fs::canonicalize(path).map_err(|error| artifact_unreadable(path, error.kind()))?;
    let loaded = if let Some(loaded) = loaded_by_path.get(&canonical) {
        loaded.clone()
    } else {
        let loaded = read_artifact(path, &canonical)?;
        loaded_by_path.insert(canonical.clone(), loaded.clone());
        loaded
    };
    if kind == ExternalArtifactKind::Rlib && !loaded.bytes.starts_with(AR_MAGIC) {
        return Err(AnalysisError::UnsupportedExternalCrateArtifact {
            path: path.to_owned(),
        });
    }
    Ok(RequestedArtifact {
        original_path: path.to_owned(),
        canonical_path: canonical,
        file_name,
        loaded,
        kind,
    })
}

fn artifact_kind(file_name: &str) -> Option<ExternalArtifactKind> {
    if file_name.starts_with("lib")
        && Path::new(file_name)
            .extension()
            .and_then(|value| value.to_str())
            == Some("rlib")
    {
        return Some(ExternalArtifactKind::Rlib);
    }

    file_name
        .strip_prefix(std::env::consts::DLL_PREFIX)
        .and_then(|name| name.strip_suffix(std::env::consts::DLL_SUFFIX))
        .filter(|name| !name.is_empty())
        .map(|_| ExternalArtifactKind::HostDynamicLibrary)
}

fn validate_dependency_file_name(artifact: &RequestedArtifact) -> Result<(), AnalysisError> {
    let crate_name = match artifact.kind {
        ExternalArtifactKind::Rlib => artifact
            .file_name
            .strip_prefix("lib")
            .and_then(|name| name.strip_suffix(".rlib")),
        ExternalArtifactKind::HostDynamicLibrary => artifact
            .file_name
            .strip_prefix(std::env::consts::DLL_PREFIX)
            .and_then(|name| name.strip_suffix(std::env::consts::DLL_SUFFIX)),
    };
    let valid = crate_name
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

fn resolve_proc_macro_execution_artifacts<'a, 'b>(
    artifacts: impl Iterator<Item = &'a Path>,
    registered: impl Iterator<Item = &'b RequestedArtifact>,
) -> Result<BTreeSet<(String, [u8; 32])>, AnalysisError> {
    let registered = registered.collect::<Vec<_>>();
    let mut resolved = BTreeSet::new();
    for path in artifacts {
        let canonical = fs::canonicalize(path).map_err(|_| {
            AnalysisError::InvalidProcMacroExecutionArtifact {
                path: path.to_owned(),
            }
        })?;
        let mut matched = false;
        for artifact in &registered {
            if artifact.kind == ExternalArtifactKind::HostDynamicLibrary
                && artifact.canonical_path == canonical
            {
                resolved.insert((artifact.file_name.clone(), artifact.loaded.digest));
                matched = true;
            }
        }
        if !matched {
            return Err(AnalysisError::InvalidProcMacroExecutionArtifact {
                path: path.to_owned(),
            });
        }
    }
    Ok(resolved)
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
            && (previous.kind != artifact.kind
                || previous.file_name != artifact.file_name
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
            if previous.kind != artifact.kind || previous.loaded.digest != artifact.loaded.digest {
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
    let mut file = create_snapshot_file(&path)?;
    file.write_all(&artifact.loaded.bytes)
}

fn create_snapshot_file(path: &Path) -> io::Result<File> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    options.open(path)
}

fn validate_snapshot_file_names(
    parent: &Path,
    staged: &BTreeMap<String, RequestedArtifact>,
) -> Result<(), AnalysisError> {
    if staged.is_empty() {
        return Ok(());
    }
    let probe = SnapshotDirectory::create(parent, SNAPSHOT_PROBE_PREFIX)?;
    let mut written = Vec::new();
    for artifact in staged.values() {
        match create_snapshot_file(&probe.path().join(&artifact.file_name)) {
            Ok(_) => written.push(artifact),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                let Some(previous) = matching_snapshot_artifact(&probe, artifact, &written) else {
                    return Err(snapshot_failure(
                        probe.path().join(&artifact.file_name),
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
                    probe.path().join(&artifact.file_name),
                    error.kind(),
                ));
            }
        }
    }
    Ok(())
}

fn stage_artifacts(
    snapshot: &SnapshotDirectory,
    staged: &BTreeMap<String, RequestedArtifact>,
) -> Result<(), AnalysisError> {
    let mut written = Vec::new();
    for artifact in staged.values() {
        match write_snapshot_artifact(snapshot, artifact) {
            Ok(()) => written.push(artifact),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                let Some(previous) = matching_snapshot_artifact(snapshot, artifact, &written)
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
    Ok(())
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
            let mut bytes = AR_MAGIC.to_vec();
            bytes.extend_from_slice(body);
            self.file(relative, &bytes)
        }

        fn host_dynamic_library(&self, relative_parent: &str, stem: &str, body: &[u8]) -> PathBuf {
            let file_name = format!(
                "{}{}{}",
                std::env::consts::DLL_PREFIX,
                stem,
                std::env::consts::DLL_SUFFIX
            );
            self.file(Path::new(relative_parent).join(file_name), body)
        }

        fn file(&self, relative: impl AsRef<Path>, body: &[u8]) -> PathBuf {
            let path = self.0.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            fs::write(&path, body).unwrap();
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
        prepare_with_permissions(direct, dependencies, &[])
    }

    fn prepare_with_permissions(
        direct: &[(&str, &Path)],
        dependencies: &[&Path],
        proc_macro_execution_artifacts: &[&Path],
    ) -> Result<PreparedExternalCrates, AnalysisError> {
        let direct = direct
            .iter()
            .map(|(name, artifact)| ExternalCrate::new(*name, *artifact))
            .collect::<Vec<_>>();
        prepare_external_crates(
            direct.iter(),
            dependencies.iter().copied(),
            proc_macro_execution_artifacts.iter().copied(),
        )
    }

    #[test]
    fn preparation_snapshots_only_the_declared_artifact_bytes() {
        let directory = TestDirectory::new();
        let direct = directory.artifact("libdirect.rlib", b"direct");
        let dependency = directory.artifact("libdependency.rlib", b"dependency");
        let prepared = prepare(&[("direct", &direct)], &[&dependency]).unwrap();
        let snapshot_directories = prepared.search_directories().collect::<Vec<_>>();
        assert_eq!(snapshot_directories.len(), 1);
        let snapshot_directory = PathBuf::from(snapshot_directories[0]);

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
    fn preparation_accepts_rlibs_and_host_dynamic_libraries_for_both_roles() {
        let directory = TestDirectory::new();
        let direct_rlib = directory.artifact("libdirect.rlib", b"direct");
        let direct_dynamic = directory.host_dynamic_library("", "direct_macros", b"direct macros");
        let dependency_rlib = directory.artifact("libdependency.rlib", b"dependency");
        let dependency_dynamic =
            directory.host_dynamic_library("", "dependency_macros", b"dependency macros");

        let prepared = prepare(
            &[("direct", &direct_rlib), ("direct_macros", &direct_dynamic)],
            &[&dependency_rlib, &dependency_dynamic],
        )
        .unwrap();

        assert_eq!(
            prepared
                .direct()
                .iter()
                .map(PreparedExternalCrate::extern_name)
                .collect::<Vec<_>>(),
            vec!["direct", "direct_macros"]
        );
        let snapshot = Path::new(prepared.search_directories().next().unwrap());
        assert_eq!(
            fs::read(snapshot.join("libdependency.rlib")).unwrap(),
            [AR_MAGIC, b"dependency"].concat()
        );
        assert_eq!(
            fs::read(snapshot.join(dependency_dynamic.file_name().unwrap())).unwrap(),
            b"dependency macros"
        );
        assert!(prepared.proc_macro_execution_artifacts().is_empty());
    }

    #[test]
    fn execution_permissions_resolve_to_registered_snapshot_artifacts() {
        let directory = TestDirectory::new();
        let dynamic = directory.host_dynamic_library("", "macros", b"trusted native code");

        let prepared =
            prepare_with_permissions(&[("macros", &dynamic)], &[], &[&dynamic, &dynamic]).unwrap();
        let permissions = prepared.proc_macro_execution_artifacts();

        assert_eq!(permissions.len(), 1);
        assert_eq!(
            fs::read(permissions[0].artifact()).unwrap(),
            b"trusted native code"
        );
        assert_ne!(permissions[0].artifact(), dynamic);
        assert!(
            prepared
                .artifact_directories()
                .any(|directory| permissions[0].artifact().parent() == Some(directory))
        );
        let load_state = prepared.proc_macro_load_state();
        assert!(load_state.is_allowed(permissions[0].artifact()));
        assert!(!load_state.is_allowed(&dynamic));
    }

    #[cfg(windows)]
    #[test]
    fn permitted_identical_artifacts_share_a_snapshot_across_sets() {
        let directory = TestDirectory::new();
        let dynamic = directory.host_dynamic_library("", "shared_macros", b"shared native code");
        let first_rlib = directory.artifact("libfirst.rlib", b"first");
        let second_rlib = directory.artifact("libsecond.rlib", b"second");

        let first = prepare_with_permissions(
            &[("macros", &dynamic), ("first", &first_rlib)],
            &[],
            &[&dynamic],
        )
        .unwrap();
        let second = prepare_with_permissions(
            &[("macros", &dynamic), ("second", &second_rlib)],
            &[],
            &[&dynamic],
        )
        .unwrap();
        assert_eq!(
            first.proc_macro_execution_artifacts()[0].artifact(),
            second.proc_macro_execution_artifacts()[0].artifact()
        );
        assert_eq!(
            first.snapshot.as_ref().unwrap().path().parent(),
            first.proc_macro_execution_artifacts()[0]
                .artifact()
                .parent()
                .unwrap()
                .parent()
        );
        assert_ne!(
            first.snapshot.as_ref().unwrap().path(),
            second.snapshot.as_ref().unwrap().path()
        );

        fs::write(&dynamic, b"different trusted native code").unwrap();
        let different =
            prepare_with_permissions(&[("macros", &dynamic)], &[], &[&dynamic]).unwrap();
        assert_ne!(
            first.proc_macro_execution_artifacts()[0].artifact(),
            different.proc_macro_execution_artifacts()[0].artifact()
        );
        assert_eq!(
            fs::read(first.proc_macro_execution_artifacts()[0].artifact()).unwrap(),
            b"shared native code"
        );
    }

    #[cfg(windows)]
    #[test]
    fn partially_overlapping_proc_macro_sets_share_only_identical_artifacts() {
        let directory = TestDirectory::new();
        let shared = directory.host_dynamic_library("", "overlap_shared", b"shared");
        let first_only = directory.host_dynamic_library("", "overlap_first", b"first");
        let second_only = directory.host_dynamic_library("", "overlap_second", b"second");

        let first = prepare_with_permissions(
            &[("shared", &shared), ("first", &first_only)],
            &[],
            &[&shared, &first_only],
        )
        .unwrap();
        let second = prepare_with_permissions(
            &[("shared", &shared), ("second", &second_only)],
            &[],
            &[&shared, &second_only],
        )
        .unwrap();
        let artifact = |prepared: &PreparedExternalCrates, name: &str| {
            prepared
                .proc_macro_execution_artifacts()
                .iter()
                .find(|artifact| {
                    artifact
                        .artifact()
                        .file_name()
                        .and_then(|value| value.to_str())
                        == Some(name)
                })
                .unwrap()
                .artifact()
                .to_owned()
        };

        let first_shared = artifact(&first, shared.file_name().unwrap().to_str().unwrap());
        let second_shared = artifact(&second, shared.file_name().unwrap().to_str().unwrap());
        let first_only = artifact(&first, first_only.file_name().unwrap().to_str().unwrap());
        let second_only = artifact(&second, second_only.file_name().unwrap().to_str().unwrap());
        assert_eq!(first_shared, second_shared);
        assert_ne!(first_shared.parent(), first_only.parent());
        assert_ne!(second_shared.parent(), second_only.parent());
        assert_ne!(first_only.parent(), second_only.parent());
        assert_eq!(first.search_directories().count(), 2);
        assert_eq!(second.search_directories().count(), 2);
    }

    #[cfg(windows)]
    #[test]
    fn unused_permitted_proc_macro_is_removed_with_the_last_lease() {
        let directory = TestDirectory::new();
        let dynamic = directory.host_dynamic_library("", "unused_permitted", b"unused native code");
        let first = prepare_with_permissions(&[("macros", &dynamic)], &[], &[&dynamic]).unwrap();
        let second = prepare_with_permissions(&[("macros", &dynamic)], &[], &[&dynamic]).unwrap();
        let artifact = first.proc_macro_execution_artifacts()[0]
            .artifact()
            .to_owned();
        assert_eq!(
            artifact,
            second.proc_macro_execution_artifacts()[0].artifact()
        );
        let snapshot = artifact.parent().unwrap().to_owned();

        drop(first);
        assert!(artifact.is_file());
        drop(second);
        assert!(!snapshot.exists());
    }

    #[cfg(windows)]
    #[test]
    fn loaded_proc_macro_is_pinned_once_for_the_process() {
        let directory = TestDirectory::new();
        let dynamic = directory.host_dynamic_library("", "loaded_once", b"loaded native code");
        let ordinary = directory.artifact("libloaded_once_dependency.rlib", b"ordinary");
        let prepared = prepare_with_permissions(
            &[("macros", &dynamic), ("ordinary", &ordinary)],
            &[],
            &[&dynamic],
        )
        .unwrap();
        let artifact = prepared.proc_macro_execution_artifacts()[0]
            .artifact()
            .to_owned();
        let analyzer_snapshot = prepared.snapshot.as_ref().unwrap().path().to_owned();
        let process_snapshot = prepared.proc_macro_execution_artifacts()[0]
            .snapshot
            .clone();
        let state = prepared.proc_macro_load_state();
        let before = Arc::strong_count(&process_snapshot.snapshot);

        state.loaded(&artifact);
        assert_eq!(Arc::strong_count(&process_snapshot.snapshot), before + 1);
        state.loaded(&artifact);
        assert_eq!(Arc::strong_count(&process_snapshot.snapshot), before + 1);

        drop(process_snapshot);
        drop(state);
        drop(prepared);
        assert!(artifact.is_file());
        assert!(!analyzer_snapshot.exists());
    }

    #[cfg(windows)]
    #[test]
    fn concurrent_prepare_and_load_share_one_snapshot_and_pin() {
        let directory = TestDirectory::new();
        let dynamic =
            directory.host_dynamic_library("", "concurrent_prepare", b"concurrent native code");
        let prepared = std::thread::scope(|scope| {
            let handles = (0..4)
                .map(|_| {
                    let dynamic = &dynamic;
                    scope.spawn(move || {
                        prepare_with_permissions(&[("macros", dynamic)], &[], &[dynamic]).unwrap()
                    })
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>()
        });
        let artifact = prepared[0].proc_macro_execution_artifacts()[0]
            .artifact()
            .to_owned();
        assert!(prepared.iter().all(|candidate| {
            candidate.proc_macro_execution_artifacts()[0].artifact() == artifact
        }));

        let states = prepared
            .iter()
            .map(PreparedExternalCrates::proc_macro_load_state)
            .collect::<Vec<_>>();
        std::thread::scope(|scope| {
            for state in states {
                let artifact = &artifact;
                scope.spawn(move || state.loaded(artifact));
            }
        });

        let process_snapshot = &prepared[0].proc_macro_execution_artifacts()[0].snapshot;
        let stores = PROCESS_EXTERNAL_STORES.get().unwrap();
        let stores = stores
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let store = stores.get(&process_snapshot.store).unwrap();
        assert_eq!(
            store
                .loaded
                .iter()
                .filter(|snapshot| Arc::ptr_eq(snapshot, &process_snapshot.snapshot))
                .count(),
            1
        );
    }

    #[cfg(windows)]
    #[test]
    fn process_snapshot_sharing_is_scoped_by_parent_and_owner_token() {
        let first_parent = TestDirectory::new();
        let second_parent = TestDirectory::new();
        let artifacts = TestDirectory::new();
        let dynamic = artifacts.host_dynamic_library("", "store_scope", b"scoped native code");
        let mut loaded = BTreeMap::new();
        let artifact = load_requested_artifact(&dynamic, &mut loaded).unwrap();
        let first_key = ProcessStoreKey {
            parent: fs::canonicalize(&first_parent.0).unwrap(),
            token: Some("first".to_owned()),
        };
        let other_owner_key = ProcessStoreKey {
            parent: first_key.parent.clone(),
            token: Some("second".to_owned()),
        };
        let other_parent_key = ProcessStoreKey {
            parent: fs::canonicalize(&second_parent.0).unwrap(),
            token: first_key.token.clone(),
        };
        let prepare = |key: &ProcessStoreKey| {
            let parent_lock = SnapshotParentLock::acquire(&key.parent).unwrap();
            process_snapshot(key, &artifact, &parent_lock).unwrap()
        };

        let first = prepare(&first_key);
        let other_owner = prepare(&other_owner_key);
        let other_parent = prepare(&other_parent_key);
        assert_ne!(first.path(), other_owner.path());
        assert_ne!(first.path(), other_parent.path());

        drop(first);
        drop(other_owner);
        drop(other_parent);
        release_process_store(&first_key);
        release_process_store(&other_owner_key);
        release_process_store(&other_parent_key);
    }

    #[test]
    fn execution_permissions_accept_registered_transitive_artifacts() {
        let directory = TestDirectory::new();
        let dynamic =
            directory.host_dynamic_library("", "transitive_macros", b"transitive native code");

        let prepared = prepare_with_permissions(&[], &[&dynamic], &[&dynamic]).unwrap();

        assert_eq!(prepared.proc_macro_execution_artifacts().len(), 1);
        assert_eq!(
            fs::read(prepared.proc_macro_execution_artifacts()[0].artifact()).unwrap(),
            b"transitive native code"
        );
    }

    #[test]
    fn execution_permissions_require_the_registered_host_dynamic_library_path() {
        let directory = TestDirectory::new();
        let rlib = directory.artifact("libregular.rlib", b"regular");
        let registered =
            directory.host_dynamic_library("registered", "macros", b"same native code");
        let unregistered =
            directory.host_dynamic_library("unregistered", "macros", b"same native code");
        let missing = directory.0.join(format!(
            "{}missing{}",
            std::env::consts::DLL_PREFIX,
            std::env::consts::DLL_SUFFIX
        ));

        for result in [
            prepare_with_permissions(&[("regular", &rlib)], &[], &[&rlib]),
            prepare_with_permissions(&[("macros", &registered)], &[], &[&unregistered]),
            prepare_with_permissions(&[("macros", &registered)], &[], &[&missing]),
            prepare_with_permissions(&[], &[], &[&registered]),
        ] {
            assert!(matches!(
                result,
                Err(AnalysisError::InvalidProcMacroExecutionArtifact { .. })
            ));
        }
    }

    #[test]
    fn direct_artifact_is_not_repeated_or_revalidated_as_a_dependency() {
        let directory = TestDirectory::new();
        let artifact = directory.artifact("libdirect.rlib", b"direct");

        let prepared = prepare(&[("direct", &artifact)], &[&artifact]).unwrap();

        assert_eq!(prepared.direct().len(), 1);

        let non_searchable_name = directory.artifact("lib-.rlib", b"direct");
        let prepared = prepare(&[("direct", &non_searchable_name)], &[&non_searchable_name])
            .expect("a repeated direct artifact adds no search input");
        assert_eq!(prepared.direct().len(), 1);

        let direct_only_dynamic = directory.host_dynamic_library("", "-", b"dynamic");
        let prepared = prepare(
            &[("dynamic", &direct_only_dynamic)],
            &[&direct_only_dynamic],
        )
        .expect("a repeated direct dynamic library adds no search input");
        assert_eq!(prepared.direct().len(), 1);
        assert!(matches!(
            prepare(&[], &[&direct_only_dynamic]),
            Err(AnalysisError::UnsupportedExternalCrateArtifact { .. })
        ));
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

        let empty_dynamic_name = directory.file(
            format!(
                "{}{}",
                std::env::consts::DLL_PREFIX,
                std::env::consts::DLL_SUFFIX
            ),
            b"dynamic",
        );
        assert!(matches!(
            prepare(&[("invalid", &empty_dynamic_name)], &[]),
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
        let lower_dynamic = directory.host_dynamic_library("dynamic-lower", "case", b"lower");
        let upper_dynamic = directory.host_dynamic_library("dynamic-upper", "CASE", b"upper");
        let split = prepare_with_permissions(
            &[("lower_dynamic", &lower_dynamic)],
            &[&upper_dynamic],
            &[&lower_dynamic],
        );
        if temporary_file_names_distinguish_ascii_case() {
            assert!(same.is_ok());
            assert!(different.is_ok());
            assert!(split.is_ok());
        } else {
            assert!(matches!(
                same,
                Err(AnalysisError::ConflictingExternalCrateArtifactName { .. })
            ));
            assert!(matches!(
                different,
                Err(AnalysisError::ConflictingExternalCrateArtifactName { .. })
            ));
            assert!(matches!(
                split,
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
        let parent = snapshot_parent().unwrap();
        let snapshot = SnapshotDirectory::create(&parent, ANALYZER_SNAPSHOT_PREFIX).unwrap();
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

    #[cfg(windows)]
    fn release_process_store(key: &ProcessStoreKey) {
        let stores = PROCESS_EXTERNAL_STORES.get().unwrap();
        let store = stores
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .remove(key);
        drop(store);
    }
}
