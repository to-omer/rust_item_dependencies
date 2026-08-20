//! Runtime access to the compiler artifact checked at build time.

use std::path::PathBuf;
use std::sync::OnceLock;

#[cfg(rust_item_dependencies_patched)]
use crate::digest::sha256;

#[derive(Clone, Debug)]
pub(crate) struct CompilerArtifact {
    pub sysroot: PathBuf,
    pub identity: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArtifactError {
    Mismatch,
}

pub(crate) fn compiler_artifact() -> Result<CompilerArtifact, ArtifactError> {
    static ARTIFACT: OnceLock<Result<CompilerArtifact, ArtifactError>> = OnceLock::new();
    ARTIFACT.get_or_init(validate).clone()
}

#[cfg(not(rust_item_dependencies_patched))]
fn validate() -> Result<CompilerArtifact, ArtifactError> {
    Err(ArtifactError::Mismatch)
}

#[cfg(rust_item_dependencies_patched)]
fn validate() -> Result<CompilerArtifact, ArtifactError> {
    const EXPECTED_ABI: u32 = 12;
    if rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_ABI != EXPECTED_ABI
        || rustc_driver::RUST_ITEM_DEPENDENCIES_BASE_REVISION
            != include_str!("../rustc-patches/base-revision").trim()
        || rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST
            != include_str!("../rustc-patches/queue-digest").trim()
    {
        return Err(ArtifactError::Mismatch);
    }

    let sysroot = PathBuf::from(env!("RUST_ITEM_DEPENDENCIES_BUILD_SYSROOT"));
    if !sysroot.is_dir() {
        return Err(ArtifactError::Mismatch);
    }
    let mut identity = Vec::new();
    identity.extend_from_slice(b"rust-item-dependencies-compiler-v1\0");
    identity.extend_from_slice(&EXPECTED_ABI.to_le_bytes());
    identity.extend_from_slice(rustc_driver::RUST_ITEM_DEPENDENCIES_BASE_REVISION.as_bytes());
    identity.extend_from_slice(rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST.as_bytes());
    Ok(CompilerArtifact {
        sysroot,
        identity: sha256(identity),
    })
}
