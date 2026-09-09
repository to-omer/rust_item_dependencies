use super::*;

fn work() -> tempfile::TempDir {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repository = if env!("CARGO_PKG_NAME") == "cargo-rid" {
        manifest.parent().unwrap()
    } else {
        manifest
    };
    let root = repository.join("target/tests");
    fs::create_dir_all(&root).unwrap();
    tempfile::Builder::new()
        .prefix("file-output-")
        .tempdir_in(root)
        .unwrap()
}

#[test]
fn replaces_the_source_and_leaves_identical_results_untouched() {
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "fn unused() {} fn main() {}\n").unwrap();
    let original = SourceFile::read(&path).unwrap();
    original.replace("fn main() {}\n").unwrap();
    assert_eq!(fs::read_to_string(&path).unwrap(), "fn main() {}\n");
    let before = fs::metadata(&path).unwrap();
    let source = SourceFile::read(&path).unwrap();
    source.replace("fn main() {}\n").unwrap();
    assert!(same_metadata(&before, &fs::metadata(&path).unwrap()).unwrap());
    assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
}

#[test]
fn refuses_edits_and_replacement_during_reduction_even_for_a_noop() {
    for (replace, result) in [(false, "reduced"), (true, "reduced"), (false, "original")] {
        let work = work();
        let path = work.path().join("input.rs");
        fs::write(&path, "original").unwrap();
        let source = SourceFile::read(&path).unwrap();
        if replace {
            let replacement = work.path().join("replacement.rs");
            fs::write(&replacement, "original").unwrap();
            fs::rename(replacement, &path).unwrap();
        } else {
            fs::write(&path, "modified").unwrap();
        }
        assert!(
            source
                .replace(result)
                .unwrap_err()
                .to_string()
                .contains("changed")
        );
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            if replace { "original" } else { "modified" }
        );
        assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
    }
}

#[test]
fn refuses_readonly_and_hard_linked_inputs() {
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    let permissions = fs::metadata(&path).unwrap().permissions();
    let mut readonly = permissions.clone();
    readonly.set_readonly(true);
    fs::set_permissions(&path, readonly).unwrap();
    assert!(SourceFile::read(&path).is_err());
    fs::set_permissions(&path, permissions).unwrap();
    let link = work.path().join("link.rs");
    fs::hard_link(&path, &link).unwrap();
    assert!(SourceFile::read(&path).is_err());
    assert!(SourceFile::read(&link).is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), "original");
    assert_eq!(fs::read_to_string(link).unwrap(), "original");
}

#[cfg(unix)]
#[test]
fn refuses_symbolic_links_and_preserves_unix_permissions() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    let link = work.path().join("link.rs");
    symlink(&path, &link).unwrap();
    assert!(SourceFile::read(&link).is_err());
    fs::set_permissions(&path, fs::Permissions::from_mode(0o750)).unwrap();
    let before = fs::metadata(&path).unwrap();
    SourceFile::read(&path).unwrap().replace("reduced").unwrap();
    let after = fs::metadata(&path).unwrap();
    assert_eq!(
        (before.uid(), before.gid(), before.mode()),
        (after.uid(), after.gid(), after.mode())
    );
    assert!(fs::symlink_metadata(&link).unwrap().is_symlink());
    assert_eq!(fs::read_to_string(&link).unwrap(), "reduced");
}

#[cfg(unix)]
#[test]
fn new_outputs_use_normal_creation_permissions_and_updates_reject_permission_changes() {
    use std::os::unix::fs::PermissionsExt;
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    let output = work.path().join("output.rs");
    write_new(&output, "reduced").unwrap();
    assert_eq!(
        fs::metadata(&output).unwrap().permissions(),
        fs::metadata(&path).unwrap().permissions()
    );
    fs::set_permissions(&path, fs::Permissions::from_mode(0o640)).unwrap();
    let source = SourceFile::read(&path).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
    assert!(source.replace("reduced").is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), "original");
    assert_eq!(
        fs::metadata(&path).unwrap().permissions().mode() & 0o777,
        0o600
    );
}

#[test]
fn does_not_leave_temporary_outputs_when_publication_fails() {
    let work = work();
    let path = work.path().join("existing.rs");
    fs::write(&path, "original").unwrap();
    assert_eq!(
        write_new(&path, "reduced").unwrap_err().kind(),
        io::ErrorKind::AlreadyExists
    );
    assert!(write_new(work.path(), "reduced").is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), "original");
    assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
}

#[cfg(unix)]
#[test]
fn failed_write_keeps_the_original_and_cleans_up() {
    const CHILD: &str = "RID_TEST_FAIL_WRITE";
    if let Some(path) = std::env::var_os(CHILD) {
        let path = Path::new(&path);
        // Limit only this test's child process so the real file write returns EFBIG.
        unsafe {
            libc::signal(libc::SIGXFSZ, libc::SIG_IGN);
            let limit = libc::rlimit {
                rlim_cur: 64,
                rlim_max: 64,
            };
            assert_eq!(libc::setrlimit(libc::RLIMIT_FSIZE, &limit), 0);
        }
        let error = SourceFile::read(path)
            .unwrap()
            .replace(&"x".repeat(4096))
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::FileTooLarge, "{error:?}");
        assert_eq!(fs::read_to_string(path).unwrap(), "original");
        assert_eq!(fs::read_dir(path.parent().unwrap()).unwrap().count(), 1);
        return;
    }
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "file_output::tests::failed_write_keeps_the_original_and_cleans_up",
            "--nocapture",
        ])
        .env(CHILD, &path)
        .output()
        .unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    assert!(String::from_utf8_lossy(&child.stdout).contains("1 passed"));
    assert_eq!(fs::read_to_string(path).unwrap(), "original");
}

#[cfg(target_os = "linux")]
#[test]
fn preserves_access_acls_and_removes_unwanted_inherited_acls() {
    use xattr::FileExt;
    let mut acl = 2_u32.to_le_bytes().to_vec();
    // Linux's version-2 POSIX ACL: owner, named user, group, mask, other.
    for (tag, permissions, id) in [
        (1_u16, 6_u16, u32::MAX),
        (2, 4, 65534),
        (4, 0, u32::MAX),
        (16, 4, u32::MAX),
        (32, 0, u32::MAX),
    ] {
        acl.extend(tag.to_le_bytes());
        acl.extend(permissions.to_le_bytes());
        acl.extend(id.to_le_bytes());
    }
    for preserve in [true, false] {
        let work = work();
        xattr::set(work.path(), "system.posix_acl_default", &acl).unwrap();
        let path = work.path().join("input.rs");
        fs::write(&path, "original").unwrap();
        let file = File::open(&path).unwrap();
        assert!(file.get_xattr("system.posix_acl_access").unwrap().is_some());
        if !preserve {
            file.remove_xattr("system.posix_acl_access").unwrap();
        }
        let expected = file.get_xattr("system.posix_acl_access").unwrap();
        SourceFile::read(&path).unwrap().replace("reduced").unwrap();
        assert_eq!(
            File::open(&path)
                .unwrap()
                .get_xattr("system.posix_acl_access")
                .unwrap(),
            expected
        );
        assert_eq!(fs::read_to_string(&path).unwrap(), "reduced");
    }
}

#[cfg(target_os = "macos")]
#[test]
fn preserves_macos_access_acls() {
    use std::process::Command;
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    assert!(
        Command::new("/bin/chmod")
            .args(["+a", "everyone allow read"])
            .arg(&path)
            .status()
            .unwrap()
            .success()
    );
    let access = |path: &Path| {
        let output = Command::new("/bin/ls")
            .arg("-le")
            .arg(path)
            .output()
            .unwrap();
        assert!(output.status.success());
        String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .skip(1)
            .collect::<Vec<_>>()
            .join("\n")
    };
    let before = access(&path);
    assert!(before.contains("allow read"), "{before}");
    SourceFile::read(&path).unwrap().replace("reduced").unwrap();
    assert_eq!(access(&path), before);
    assert_eq!(fs::read_to_string(&path).unwrap(), "reduced");
}

#[cfg(windows)]
fn windows_sddl(path: &Path) -> String {
    let output = std::process::Command::new("powershell.exe")
        .args([
            "-NoLogo",
            "-NoProfile",
            "-NonInteractive",
            "-Command",
            "(Get-Acl -LiteralPath $env:RID_TEST_ACL_PATH -ErrorAction Stop).Sddl",
        ])
        .env("RID_TEST_ACL_PATH", path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let sddl = String::from_utf8(output.stdout).unwrap().trim().to_owned();
    assert!(!sddl.is_empty());
    sddl
}

#[cfg(windows)]
#[test]
fn preserves_windows_owner_group_and_access_permissions() {
    let work = work();
    let path = work.path().join("input 空白.rs");
    fs::write(&path, "original").unwrap();
    let before = windows_sddl(&path);
    SourceFile::read(&path).unwrap().replace("reduced").unwrap();
    assert_eq!(fs::read_to_string(&path).unwrap(), "reduced");
    assert_eq!(windows_sddl(&path), before);
    assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
}

#[cfg(windows)]
#[test]
fn refuses_unreproducible_windows_dacls_without_changing_the_original() {
    let work = work();
    let path = work.path().join("input 空白.rs");
    fs::write(&path, "original").unwrap();
    let inherited = windows_sddl(&path);
    let output = std::process::Command::new("icacls.exe")
        .arg(&path)
        .args(["/inheritancelevel:d", "/q"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let before = windows_sddl(&path);
    assert_ne!(before, inherited);
    let source = SourceFile::read(&path).unwrap();
    assert_eq!(
        source.replace("reduced").unwrap_err().kind(),
        io::ErrorKind::Unsupported
    );
    assert_eq!(fs::read_to_string(&path).unwrap(), "original");
    assert_eq!(windows_sddl(&path), before);
    assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
}

#[cfg(windows)]
#[test]
fn failed_replacement_keeps_the_original_and_cleans_up() {
    use std::os::windows::fs::OpenOptionsExt;
    let work = work();
    let path = work.path().join("input.rs");
    fs::write(&path, "original").unwrap();
    let source = SourceFile::read(&path).unwrap();
    // This handle permits reading/writing but denies deletion and replacement.
    let held = File::options()
        .read(true)
        .share_mode(3)
        .open(&path)
        .unwrap();
    assert!(source.replace("reduced").is_err());
    assert_eq!(fs::read_to_string(&path).unwrap(), "original");
    assert_eq!(fs::read_dir(work.path()).unwrap().count(), 1);
    drop(held);
}
