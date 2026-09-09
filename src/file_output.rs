use std::fs::{self, File, Metadata};
use std::io::{self, Read, Seek, Write};
use std::path::{Path, PathBuf};

use tempfile::NamedTempFile;

#[cfg(windows)]
#[path = "file_output/windows.rs"]
mod windows;

/// The source read for one reduction, held until its verified replacement is ready.
pub(crate) struct SourceFile {
    path: PathBuf,
    file: File,
    metadata: Metadata,
    source: String,
    #[cfg(windows)]
    security: windows::Security,
}

impl SourceFile {
    pub(crate) fn read(path: &Path) -> io::Result<Self> {
        validate_file(&fs::symlink_metadata(path)?)?;
        // Opening without truncation checks write access before running the compiler.
        let mut file = File::options().read(true).write(true).open(path)?;
        let metadata = file.metadata()?;
        validate_file(&metadata)?;
        let mut source = String::new();
        file.read_to_string(&mut source)?;
        let input = Self {
            path: path.to_owned(),
            #[cfg(windows)]
            security: windows::Security::read(&file)?,
            file,
            metadata,
            source,
        };
        input.check_unchanged()?;
        Ok(input)
    }

    pub(crate) fn source(&self) -> &str {
        &self.source
    }

    pub(crate) fn replace(self, source: &str) -> io::Result<()> {
        self.check_unchanged()?;
        if source == self.source {
            return Ok(());
        }
        let mut replacement = temporary_file(&self.path)?;
        self.prepare_permissions(&replacement)?;
        replacement.as_file_mut().rewind()?;
        replacement.as_file().set_len(0)?;
        replacement.write_all(source.as_bytes())?;
        // A write can clear Unix set-ID permission bits.
        replacement
            .as_file()
            .set_permissions(self.metadata.permissions())?;
        replacement.as_file().sync_all()?;
        self.check_unchanged()?;
        // Windows persistence requires the destination's handles to be closed.
        drop(self.file);
        replacement.persist(&self.path).map_err(io::Error::from)?;
        Ok(())
    }

    fn check_unchanged(&self) -> io::Result<()> {
        let path_metadata = fs::symlink_metadata(&self.path)?;
        validate_file(&path_metadata)?;
        let mut current = File::open(&self.path)?;
        let metadata = current.metadata()?;
        if !same_metadata(&self.metadata, &metadata)?
            || !same_metadata(&self.metadata, &self.file.metadata()?)?
        {
            return Err(source_changed());
        }
        #[cfg(windows)]
        if self.security != windows::Security::read(&current)? {
            return Err(source_changed());
        }
        let mut source = String::new();
        current.read_to_string(&mut source)?;
        if source != self.source || !same_metadata(&self.metadata, &current.metadata()?)? {
            return Err(source_changed());
        }
        Ok(())
    }

    fn prepare_permissions(&self, replacement: &NamedTempFile) -> io::Result<()> {
        #[cfg(target_os = "macos")]
        // The existing destination selects fcopyfile(COPYFILE_ALL), including ACLs.
        fs::copy(&self.path, replacement.path())?;

        #[cfg(unix)]
        {
            use std::os::unix::fs::{MetadataExt, fchown};
            let metadata = replacement.as_file().metadata()?;
            if metadata.uid() != self.metadata.uid() || metadata.gid() != self.metadata.gid() {
                fchown(
                    replacement.as_file(),
                    Some(self.metadata.uid()),
                    Some(self.metadata.gid()),
                )?;
            }
        }

        #[cfg(windows)]
        if self.security != windows::Security::read(replacement.as_file())? {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "cannot preserve the input file's owner and access permissions",
            ));
        }

        replacement
            .as_file()
            .set_permissions(self.metadata.permissions())?;
        #[cfg(target_os = "linux")]
        {
            use xattr::FileExt;
            const ACL: &str = "system.posix_acl_access";
            match self.file.get_xattr(ACL)? {
                Some(acl) => replacement.as_file().set_xattr(ACL, &acl)?,
                None if replacement.as_file().get_xattr(ACL)?.is_some() => {
                    replacement.as_file().remove_xattr(ACL)?;
                }
                None => {}
            }
        }
        Ok(())
    }
}

pub(crate) fn write_new(path: &Path, source: &str) -> io::Result<()> {
    let mut builder = tempfile::Builder::new();
    builder.prefix(".rid-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o666));
    }
    let mut output = builder.tempfile_in(output_directory(path))?;
    output.write_all(source.as_bytes())?;
    output.as_file().sync_all()?;
    output.persist_noclobber(path).map_err(io::Error::from)?;
    Ok(())
}

#[cfg(test)]
#[path = "file_output/tests.rs"]
mod tests;

fn temporary_file(path: &Path) -> io::Result<NamedTempFile> {
    tempfile::Builder::new()
        .prefix(".rid-")
        .tempfile_in(output_directory(path))
}

fn output_directory(path: &Path) -> &Path {
    path.parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
}

fn source_changed() -> io::Error {
    io::Error::other("the input file changed during reduction; no result was written")
}

fn validate_file(metadata: &Metadata) -> io::Result<()> {
    if !metadata.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "in-place reduction requires a regular file, not a symbolic link",
        ));
    }
    if metadata.permissions().readonly() {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "the input file is read-only",
        ));
    }
    #[cfg(unix)]
    let links = {
        use std::os::unix::fs::MetadataExt;
        metadata.nlink()
    };
    #[cfg(windows)]
    let links = {
        use std::os::windows::fs::MetadataExt;
        if metadata.volume_serial_number().is_none() || metadata.file_index().is_none() {
            return Err(io::Error::other("cannot inspect the input file's identity"));
        }
        u64::from(
            metadata
                .number_of_links()
                .ok_or_else(|| io::Error::other("cannot inspect input hard links"))?,
        )
    };
    if links != 1 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "in-place reduction does not support hard-linked files",
        ));
    }
    Ok(())
}

fn same_metadata(original: &Metadata, current: &Metadata) -> io::Result<bool> {
    if original.len() != current.len()
        || original.modified()? != current.modified()?
        || original.permissions() != current.permissions()
    {
        return Ok(false);
    }
    #[cfg(unix)]
    let same = {
        use std::os::unix::fs::MetadataExt;
        original.dev() == current.dev()
            && original.ino() == current.ino()
            && original.nlink() == current.nlink()
            && original.uid() == current.uid()
            && original.gid() == current.gid()
            && original.ctime() == current.ctime()
            && original.ctime_nsec() == current.ctime_nsec()
    };
    #[cfg(windows)]
    let same = {
        use std::os::windows::fs::MetadataExt;
        original.volume_serial_number() == current.volume_serial_number()
            && original.file_index() == current.file_index()
            && original.number_of_links() == current.number_of_links()
            && original.creation_time() == current.creation_time()
            && original.file_attributes() == current.file_attributes()
    };
    Ok(same)
}
