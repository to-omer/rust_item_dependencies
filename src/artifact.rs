//! Runtime access to the compiler artifact checked at build time.

use std::path::PathBuf;
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArtifactError {
    Mismatch,
}

pub(crate) fn compiler_sysroot() -> Result<PathBuf, ArtifactError> {
    static SYSROOT: OnceLock<Result<PathBuf, ArtifactError>> = OnceLock::new();
    SYSROOT.get_or_init(validate).clone()
}

#[cfg(not(rust_item_dependencies_patched))]
fn validate() -> Result<PathBuf, ArtifactError> {
    Err(ArtifactError::Mismatch)
}

#[cfg(rust_item_dependencies_patched)]
fn validate() -> Result<PathBuf, ArtifactError> {
    let expected_abi = include_str!("../rustc-patches/patch-abi")
        .trim()
        .parse::<u32>()
        .map_err(|_| ArtifactError::Mismatch)?;
    if rustc_driver::RUST_ITEM_DEPENDENCIES_PATCH_ABI != expected_abi
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
    Ok(sysroot)
}
