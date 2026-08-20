//! Deterministic SHA-256 helpers for public result identities.

use rustc_span::{SourceFileHash, SourceFileHashAlgorithm};
use std::fs::File;
use std::io;
use std::path::Path;

pub(crate) fn sha256(bytes: impl AsRef<[u8]>) -> [u8; 32] {
    let hash = SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes);
    hash.hash_bytes()
        .try_into()
        .expect("SHA-256 always produces 32 bytes")
}

pub(crate) fn sha256_file(path: &Path) -> io::Result<[u8; 32]> {
    let hash = SourceFileHash::new(SourceFileHashAlgorithm::Sha256, File::open(path)?)?;
    Ok(hash
        .hash_bytes()
        .try_into()
        .expect("SHA-256 always produces 32 bytes"))
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write;

    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(output, "{byte:02x}").expect("writing to a string cannot fail");
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashes_bytes_with_sha256() {
        assert_eq!(
            sha256(b"abc"),
            [
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
                0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
                0xf2, 0x00, 0x15, 0xad,
            ]
        );
    }
}
