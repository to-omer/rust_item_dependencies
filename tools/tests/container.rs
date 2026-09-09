use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::{Command, Output};

struct Fixture {
    directory: tempfile::TempDir,
    image: String,
}

impl Fixture {
    fn new() -> Self {
        let parent = Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/container-tests");
        fs::create_dir_all(&parent).unwrap();
        Self {
            directory: tempfile::Builder::new()
                .prefix("image, 空白-")
                .tempdir_in(fs::canonicalize(parent).unwrap())
                .unwrap(),
            image: std::env::var("RUST_ITEM_DEPENDENCIES_TEST_IMAGE")
                .expect("set RUST_ITEM_DEPENDENCIES_TEST_IMAGE to the image under test"),
        }
    }

    fn write(&self, name: &str, source: &str) {
        let path = self.directory.path().join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn read(&self, name: &str) -> String {
        fs::read_to_string(self.directory.path().join(name)).unwrap()
    }

    fn execute(&self, arguments: &[&str]) -> Output {
        let generated = tempfile::Builder::new()
            .prefix("image-command-")
            .tempdir_in(self.directory.path().parent().unwrap())
            .unwrap();
        let mut command = vec![
            "/bin/sh",
            "-c",
            "\"$@\" >/tmp/rid-test-output/stdout 2>/tmp/rid-test-output/stderr || { status=$?; cat /tmp/rid-test-output/stderr >&2; exit \"$status\"; }",
            "rid-test",
        ];
        command.extend_from_slice(arguments);
        let dockerfile = format!(
            "ARG IMAGE\nFROM ${{IMAGE}} AS verify\n\
             USER root\nRUN mkdir -p /workspace /tmp/rid-test-output && chown 1000:1000 /workspace /tmp/rid-test-output\n\
             USER 1000:1000\nWORKDIR /workspace\n\
             ENV CARGO_HOME=/tmp/rid-cargo-home CARGO_TARGET_DIR=/tmp/rid-target\n\
             COPY --chown=1000:1000 . .\nRUN {}\n\
             FROM scratch\nCOPY --from=verify /tmp/rid-test-output/ /\n",
            serde_json::to_string(&command).unwrap()
        );
        fs::write(generated.path().join("Dockerfile"), dockerfile).unwrap();
        fs::write(generated.path().join("Dockerfile.dockerignore"), "").unwrap();
        let mut output = Command::new("docker")
            .current_dir(generated.path())
            .env_remove("BUILDX_BUILDER")
            .env("DOCKER_BUILDKIT", "1")
            .args([
                "build",
                "--no-cache",
                "--progress=plain",
                "--output",
                "type=local,dest=output",
                "--build-arg",
            ])
            .arg(format!("IMAGE={}", self.image))
            .args(["--file", "Dockerfile"])
            .arg(self.directory.path())
            .output()
            .unwrap();
        if output.status.success() {
            output.stdout = fs::read(generated.path().join("output/stdout")).unwrap();
            output.stderr = fs::read(generated.path().join("output/stderr")).unwrap();
        }
        output
    }

    fn compile(&self, input: &str, target: Option<&str>) -> Output {
        let mut arguments = vec![
            "/usr/local/bin/rustc",
            "--crate-name",
            "main",
            "--emit=metadata",
            input,
            "-o",
            "/tmp/input.rmeta",
        ];
        if let Some(target) = target {
            arguments.extend(["--target", target]);
        }
        self.execute(&arguments)
    }

    fn run(&self, arguments: impl IntoIterator<Item = impl AsRef<OsStr>>) -> Output {
        self.launcher().args(arguments).output().unwrap()
    }

    fn launcher(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_cargo-rid"));
        command
            .current_dir(self.directory.path())
            .env("RUST_ITEM_DEPENDENCIES_IMAGE", &self.image)
            .env("BUILDKIT_PROGRESS", "plain")
            .arg("docker");
        command
    }

    fn cargo(&self, arguments: &[&str]) -> Output {
        let mut command = vec!["/usr/local/bin/cargo"];
        command.extend_from_slice(arguments);
        self.execute(&command)
    }
}

fn success(output: Output) -> Output {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_reduces_both_targets_without_writing_to_the_installation() {
    let fixture = Fixture::new();
    fixture.write("target/host-sentinel", "host build directory");
    let source = "#[cfg(target_arch = \"x86_64\")] fn architecture() -> u32 { 64 }\n\
                  #[cfg(target_arch = \"aarch64\")] fn architecture() -> u32 { 128 }\n\
                  fn unused() { panic!() }\n\
                  fn main() { println!(\"{}\", architecture()); }\n";
    for (target, value) in [
        ("x86_64-unknown-linux-gnu", 64),
        ("aarch64-unknown-linux-gnu", 128),
    ] {
        fixture.write("input with spaces.rs", source);
        success(fixture.compile("input with spaces.rs", Some(target)));
        #[cfg(unix)]
        let before = fs::metadata(fixture.directory.path().join("input with spaces.rs")).unwrap();
        success(fixture.run(["--target", target, "input with spaces.rs"]));
        let reduced = fixture.read("input with spaces.rs");
        assert!(!reduced.contains("unused"));
        assert!(reduced.contains(&format!("{{ {value} }}")));
        assert!(!reduced.contains(&format!("{{ {} }}", 192 - value)));
        assert!(reduced.contains("fn main()"));
        success(fixture.compile("input with spaces.rs", Some(target)));
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let after =
                fs::metadata(fixture.directory.path().join("input with spaces.rs")).unwrap();
            assert_eq!(before.uid(), after.uid());
            assert_eq!(before.gid(), after.gid());
            assert_eq!(before.mode(), after.mode());
        }
        let modified = fs::metadata(fixture.directory.path().join("input with spaces.rs"))
            .unwrap()
            .modified()
            .unwrap();
        success(fixture.run(["--target", target, "input with spaces.rs"]));
        assert_eq!(fixture.read("input with spaces.rs"), reduced);
        assert_eq!(
            fs::metadata(fixture.directory.path().join("input with spaces.rs"))
                .unwrap()
                .modified()
                .unwrap(),
            modified
        );
    }
    fixture.write(".dockerignore", "target/\n");
    fixture.write("target/submitted.rs", source);
    success(fixture.run(["target/submitted.rs"]));
    let reduced = fixture.read("target/submitted.rs");
    assert!(!reduced.contains("unused"));
    success(fixture.compile("target/submitted.rs", None));
    success(fixture.run(["target/submitted.rs"]));
    assert_eq!(fixture.read("target/submitted.rs"), reduced);
    assert_eq!(fixture.read("target/host-sentinel"), "host build directory");
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_preserves_relative_docker_configuration_and_temporary_paths() {
    let fixture = Fixture::new();
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("input.rs", source);
    #[cfg(unix)]
    let temporary = fixture.directory.path().join("temporary, \"雪\"");
    #[cfg(windows)]
    let temporary = fixture.directory.path().join("temporary, 雪");
    fs::create_dir(&temporary).unwrap();
    success(
        fixture
            .launcher()
            .env("TMPDIR", &temporary)
            .env("TEMP", &temporary)
            .env("TMP", &temporary)
            .arg("input.rs")
            .output()
            .unwrap(),
    );
    assert!(!fixture.read("input.rs").contains("unused"));
    success(fixture.compile("input.rs", None));
    assert_eq!(fs::read_dir(&temporary).unwrap().count(), 0);

    fixture.write("input.rs", source);
    let info = success(
        Command::new("docker")
            .args(["info", "--format", "{{json .ClientInfo.Plugins}}"])
            .output()
            .unwrap(),
    );
    let plugins: Vec<serde_json::Value> = serde_json::from_slice(&info.stdout).unwrap();
    let buildx = plugins
        .iter()
        .find(|plugin| plugin["Name"] == "buildx")
        .expect("Docker must have a working Buildx plugin");
    let buildx = Path::new(buildx["Path"].as_str().unwrap());
    assert!(buildx.is_file(), "Buildx is missing: {}", buildx.display());
    // Changing DOCKER_CONFIG also changes the per-user plugin directory.
    let config = serde_json::json!({
        "currentContext": "rid-missing-relative-context",
        "cliPluginsExtraDirs": [buildx.parent().unwrap()],
    });
    fixture.write(
        ".docker/config.json",
        &serde_json::to_string(&config).unwrap(),
    );
    let result = fixture
        .launcher()
        .env("DOCKER_CONFIG", ".docker")
        .env_remove("DOCKER_CONTEXT")
        .env_remove("DOCKER_HOST")
        .arg("input.rs")
        .output()
        .unwrap();
    assert!(!result.status.success());
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(stderr.contains("rid-missing-relative-context"), "{stderr}");
    assert_eq!(fixture.read("input.rs"), source);
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_rebuilds_dependencies_after_host_atomic_edits() {
    let fixture = Fixture::new();
    fixture.write("Cargo.toml", "[package]\nname='dependency-edit'\nversion='0.1.0'\nedition='2024'\n[workspace]\n[dependencies]\nhelper={path='helper'}\n");
    fixture.write(
        "helper/Cargo.toml",
        "[package]\nname='helper'\nversion='0.1.0'\nedition='2024'\n",
    );
    let source = "fn left() -> u32 { 1 }\nfn right() -> u32 { 2 }\n\
                  fn main() { println!(\"{}\", helper::value!()); }\n";
    fixture.write("src/main.rs", source);
    fixture.write(
        "helper/src/lib.rs",
        "#[macro_export] macro_rules! value { () => { left() }; }\n",
    );
    // A large parent directory also exercises names outside a single directory read.
    for index in 0..3000 {
        fixture.write(&format!("helper/src/unrelated-{index}"), "");
    }
    assert_eq!(
        success(fixture.cargo(&["run", "--offline", "--quiet"])).stdout,
        b"1\n"
    );
    success(fixture.run(["--offline"]));
    let before = fixture.read("src/main.rs");
    assert!(before.contains("fn left"));
    assert!(!before.contains("fn right"));
    fixture.write("src/main.rs", source);
    fixture.write(
        "helper/src/replacement.rs",
        "#[macro_export] macro_rules! value { () => { right() }; }\n",
    );
    fs::rename(
        fixture.directory.path().join("helper/src/replacement.rs"),
        fixture.directory.path().join("helper/src/lib.rs"),
    )
    .unwrap();
    success(fixture.run(["--offline"]));
    let reduced = fixture.read("src/main.rs");
    assert!(!reduced.contains("fn left"));
    assert!(reduced.contains("fn right"));
    assert_eq!(
        success(fixture.cargo(&["run", "--offline", "--quiet"])).stdout,
        b"2\n"
    );
    success(fixture.run(["--offline"]));
    assert_eq!(fixture.read("src/main.rs"), reduced);
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_reads_host_edits_to_previously_reduced_files() {
    for separate_output in [false, true] {
        for edit in ["grow", "shrink", "same size"] {
            let fixture = Fixture::new();
            let seed_value = "a".repeat(128);
            fixture.write(
                "input.rs",
                &format!("fn unused() {{}}\nfn main() {{ println!(\"{seed_value}\"); }}\n"),
            );
            success(fixture.run(["input.rs"]));
            success(fixture.run(["input.rs"]));
            let baseline = fixture.read("input.rs");
            let (source, value) = match edit {
                "grow" => {
                    let prefix = "fn main() { println!(\"";
                    // A stale size would split this valid UTF-8 character during the read.
                    let value = format!("{}雪", " ".repeat(baseline.len() - prefix.len() - 1));
                    (format!("{prefix}{value}\"); }}\nfn unused() {{}}\n"), value)
                }
                "shrink" => (
                    "fn main() { println!(\"雪\"); }\nfn unused() {}\n".to_owned(),
                    "雪".to_owned(),
                ),
                "same size" => {
                    let value = "b".repeat(128);
                    (baseline.replace(&seed_value, &value), value)
                }
                _ => unreachable!(),
            };
            match edit {
                "grow" => assert!(source.len() > baseline.len()),
                "shrink" => assert!(source.len() < baseline.len()),
                "same size" => assert_eq!(source.len(), baseline.len()),
                _ => unreachable!(),
            }
            fixture.write("input.rs", &source);
            let output = if separate_output {
                success(fixture.run(["input.rs", "-o", "output.rs"]));
                assert_eq!(fixture.read("input.rs"), source);
                "output.rs"
            } else {
                success(fixture.run(["input.rs"]));
                "input.rs"
            };
            let reduced = fixture.read(output);
            assert!(!reduced.contains("unused"));
            assert!(reduced.contains(&format!("\"{value}\"")));
            success(fixture.compile(output, None));
            success(fixture.run([output]));
            assert_eq!(fixture.read(output), reduced);
        }
    }
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_preserves_sources_on_failure_and_supports_separate_output() {
    let fixture = Fixture::new();
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("input.rs", source);
    success(fixture.run(["input.rs", "-o", "reduced.rs"]));
    assert_eq!(fixture.read("input.rs"), source);
    assert!(!fixture.read("reduced.rs").contains("unused"));
    assert!(
        !fixture
            .run(["input.rs", "-o", "reduced.rs"])
            .status
            .success()
    );
    assert_eq!(fixture.read("input.rs"), source);

    let invalid = "fn main() { missing(); }\n";
    fixture.write("invalid.rs", invalid);
    assert!(!fixture.run(["invalid.rs"]).status.success());
    assert_eq!(fixture.read("invalid.rs"), invalid);
    assert!(
        !fixture
            .run(["--target", "wasm32-unknown-unknown", "input.rs"])
            .status
            .success()
    );
    assert_eq!(fixture.read("input.rs"), source);

    let input = fixture.directory.path().join("input.rs");
    let permissions = fs::metadata(&input).unwrap().permissions();
    let mut readonly = permissions.clone();
    readonly.set_readonly(true);
    fs::set_permissions(&input, readonly).unwrap();
    let result = fixture.run(["input.rs"]);
    let unchanged = fixture.read("input.rs");
    fs::set_permissions(&input, permissions).unwrap();
    assert!(!result.status.success());
    assert_eq!(unchanged, source);
}

#[cfg(target_os = "macos")]
#[test]
#[ignore = "runs the distribution image using Docker on a macOS host"]
fn image_preserves_macos_host_access_acls() {
    let fixture = Fixture::new();
    fixture.write("input.rs", "fn unused() {}\nfn main() {}\n");
    let path = fixture.directory.path().join("input.rs");
    success(
        Command::new("/bin/chmod")
            .args(["+a", "everyone allow read"])
            .arg(&path)
            .output()
            .unwrap(),
    );
    let access = || {
        let output = success(
            Command::new("/bin/ls")
                .arg("-le")
                .arg(&path)
                .output()
                .unwrap(),
        );
        String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .skip(1)
            .collect::<Vec<_>>()
            .join("\n")
    };
    let before = access();
    assert!(before.contains("allow read"), "{before}");
    success(fixture.run(["input.rs"]));
    assert!(!fixture.read("input.rs").contains("unused"));
    assert_eq!(access(), before);
}

#[cfg(windows)]
#[test]
#[ignore = "runs the distribution image using Docker on a Windows host"]
fn image_preserves_windows_permissions_or_refuses_unreproducible_dacls() {
    let descriptor = |path: &Path| {
        let output = success(
            Command::new("powershell.exe")
                // PowerShell 7 module paths cannot be loaded by Windows PowerShell.
                .env_remove("PSModulePath")
                .args([
                    "-NoLogo",
                    "-NoProfile",
                    "-NonInteractive",
                    "-Command",
                    "(Get-Acl -LiteralPath $env:RID_TEST_ACL_PATH -ErrorAction Stop).Sddl",
                ])
                .env("RID_TEST_ACL_PATH", path)
                .output()
                .unwrap(),
        );
        let sddl = String::from_utf8(output.stdout).unwrap().trim().to_owned();
        assert!(!sddl.is_empty());
        sddl
    };
    for explicit in [false, true] {
        let fixture = Fixture::new();
        let source = "fn unused() {}\nfn main() {}\n";
        fixture.write("input 空白.rs", source);
        let path = fixture.directory.path().join("input 空白.rs");
        let inherited = descriptor(&path);
        if explicit {
            success(
                Command::new("icacls.exe")
                    .arg(&path)
                    .args(["/inheritancelevel:d", "/q"])
                    .output()
                    .unwrap(),
            );
        }
        let before = descriptor(&path);
        if explicit {
            assert_ne!(before, inherited);
        }
        let result = fixture.run(["input 空白.rs"]);
        if explicit {
            assert!(!result.status.success());
            assert!(String::from_utf8_lossy(&result.stderr).contains("cannot preserve"));
            assert_eq!(fixture.read("input 空白.rs"), source);
        } else {
            success(result);
            let reduced = fixture.read("input 空白.rs");
            assert!(!reduced.contains("unused"));
            success(fixture.compile("input 空白.rs", None));
            success(fixture.run(["input 空白.rs"]));
            assert_eq!(fixture.read("input 空白.rs"), reduced);
        }
        assert_eq!(descriptor(&path), before);
        assert_eq!(fs::read_dir(fixture.directory.path()).unwrap().count(), 1);
    }
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_builds_cargo_dependencies_and_proc_macros_with_the_bundled_compiler() {
    let fixture = Fixture::new();
    fixture.write(
        "Cargo.toml",
        "[package]\nname='container-app'\nversion='0.1.0'\nedition='2024'\n\
         [workspace]\n\
         [features]\nselected=[]\n\
         [dependencies]\nhelper={path='helper'}\nmaker={path='maker'}\n",
    );
    fixture.write(
        "build.rs",
        "fn main() { println!(\"cargo::rustc-check-cfg=cfg(from_build)\"); println!(\"cargo::rustc-cfg=from_build\"); }\n",
    );
    fixture.write(
        "helper/Cargo.toml",
        "[package]\nname='helper'\nversion='0.1.0'\nedition='2024'\n",
    );
    fixture.write("helper/src/lib.rs", "pub fn value() -> u32 { 4 }\n");
    fixture.write(
        "maker/Cargo.toml",
        "[package]\nname='maker'\nversion='0.1.0'\nedition='2024'\n[lib]\nproc-macro=true\n",
    );
    fixture.write(
        "maker/src/lib.rs",
        "use proc_macro::TokenStream;\n#[proc_macro] pub fn number(_: TokenStream) -> TokenStream { \"3u32\".parse().unwrap() }\n",
    );
    let source = "#[cfg(not(feature = \"selected\"))] compile_error!(\"missing feature\");\n\
                  #[cfg(not(from_build))] compile_error!(\"missing build script\");\n\
                  fn unused() {}\n\
                  fn kept() -> u32 { helper::value() + maker::number!() }\n\
                  fn main() { println!(\"{}\", kept()); }\n";
    fixture.write("src/main.rs", source);
    // The runtime Cargo must not use rustup to follow the host project's toolchain file.
    fixture.write(
        "rust-toolchain.toml",
        "[toolchain]\nchannel='unavailable'\n",
    );
    let original = success(fixture.cargo(&["run", "--offline", "--features", "selected"]));
    assert_eq!(original.stdout, b"7\n");
    for target in ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"] {
        fixture.write("src/main.rs", source);
        success(fixture.run(["--offline", "--features", "selected", "--target", target]));
        let output = fixture.read("src/main.rs");
        assert!(!output.contains("unused"));
        assert!(output.contains("fn kept()"));
        assert!(output.contains("maker::number!()"));
        success(fixture.run(["--offline", "--features", "selected", "--target", target]));
        assert_eq!(fixture.read("src/main.rs"), output);
        assert!(!fixture.directory.path().join("target").exists());
    }
    let result = success(fixture.cargo(&["run", "--offline", "--features", "selected"]));
    assert_eq!(result.stdout, original.stdout);
    assert!(!fixture.directory.path().join("target").exists());
    assert!(!fixture.directory.path().join("Cargo.lock").exists());
    assert_eq!(
        fixture.read("helper/src/lib.rs"),
        "pub fn value() -> u32 { 4 }\n"
    );

    success(fixture.run([
        "--offline",
        "--features",
        "selected",
        "--target-dir",
        "custom build",
    ]));
    assert!(!fixture.directory.path().join("custom build").exists());

    let unchanged = fixture.read("src/main.rs");
    let unsupported = fixture.run([
        "--offline",
        "--features",
        "selected",
        "--target",
        "wasm32-unknown-unknown",
    ]);
    assert!(!unsupported.status.success());
    assert!(String::from_utf8_lossy(&unsupported.stderr).contains("wasm32-unknown-unknown"));
    assert_eq!(fixture.read("src/main.rs"), unchanged);
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_keeps_large_sources_and_proc_macro_output_out_of_the_result() {
    let fixture = Fixture::new();
    fixture.write(
        "Cargo.toml",
        "[package]\nname='large-source'\nversion='0.1.0'\nedition='2024'\n[workspace]\n[dependencies]\nloud={path='loud'}\n",
    );
    fixture.write(
        "loud/Cargo.toml",
        "[package]\nname='loud'\nversion='0.1.0'\nedition='2024'\n[lib]\nproc-macro=true\n",
    );
    fixture.write(
        "loud/src/lib.rs",
        "use proc_macro::TokenStream;\n#[proc_macro] pub fn number(_: TokenStream) -> TokenStream { println!(\"macro output on stdout\"); \"3u32\".parse().unwrap() }\n",
    );
    fixture.write(
        "build.rs",
        "fn main() { println!(\"build script output on stdout\"); }\n",
    );
    let comment = format!("/*{}*/\n", "日本語の大きなソース\n".repeat(16_384));
    fixture.write(
        "src/main.rs",
        &format!(
            "{comment}fn unused() {{}}\nfn main() {{ println!(\"{{}}\", loud::number!()); }}\n"
        ),
    );
    let result = success(fixture.run(["--offline"]));
    assert!(result.stdout.is_empty());
    assert!(String::from_utf8_lossy(&result.stderr).contains("macro output on stdout"));
    let reduced = fixture.read("src/main.rs");
    assert!(reduced.starts_with(&comment));
    assert!(!reduced.contains("unused"));
    assert!(reduced.contains("loud::number!()"));
    success(fixture.cargo(&["build", "--offline"]));
    success(fixture.run(["--offline"]));
    assert_eq!(fixture.read("src/main.rs"), reduced);
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_refuses_direct_updates_without_the_host_launcher() {
    let fixture = Fixture::new();
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("input.rs", source);
    // Windows-to-WSL attach streams can lose output when stdin is closed.
    let started = success(
        Command::new("docker")
            .args(["run", "--detach", "--network=none"])
            .arg(&fixture.image)
            .arg("input.rs")
            .output()
            .unwrap(),
    );
    let id = String::from_utf8(started.stdout).unwrap();
    let id = id.trim();
    let waited = Command::new("docker").args(["wait", id]).output();
    let logs = Command::new("docker").args(["logs", id]).output();
    // Collect errors and remove the container before assertions can panic.
    success(
        Command::new("docker")
            .args(["rm", "--force", id])
            .output()
            .unwrap(),
    );
    let waited = success(waited.unwrap());
    let logs = success(logs.unwrap());
    let stderr = String::from_utf8_lossy(&logs.stderr);
    let diagnostic = format!(
        "stdout:\n{}\nstderr:\n{stderr}",
        String::from_utf8_lossy(&logs.stdout)
    );
    assert_eq!(
        String::from_utf8_lossy(&waited.stdout).trim(),
        "1",
        "{diagnostic}"
    );
    assert!(stderr.contains("cargo rid docker"), "{diagnostic}");
    assert_eq!(fixture.read("input.rs"), source);
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_preserves_sources_when_buildkit_cannot_finish_the_build() {
    let fixture = Fixture::new();
    fixture.write(
        "Cargo.toml",
        "[package]\nname='build-failure'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    fixture.write(
        "build.rs",
        "fn main() { panic!(\"RID_TEST_BUILD_FAILURE\"); }\n",
    );
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("src/main.rs", source);
    let result = fixture.run(["--offline"]);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("RID_TEST_BUILD_FAILURE"));
    assert_eq!(fixture.read("src/main.rs"), source);
    assert!(!fixture.directory.path().join("Cargo.lock").exists());
    assert!(!fixture.directory.path().join("target").exists());
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_refuses_build_script_changes_to_the_copied_input() {
    let fixture = Fixture::new();
    fixture.write(
        "Cargo.toml",
        "[package]\nname='copied-edit'\nversion='0.1.0'\nedition='2024'\n[workspace]\n",
    );
    fixture.write(
        "build.rs",
        r#"fn main() {
    std::fs::write("src/main.rs", "fn main() { println!(\"changed copy\"); }\n").unwrap();
    eprintln!("RID_TEST_COPIED_INPUT_CHANGED");
}
"#,
    );
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("src/main.rs", source);
    success(fixture.cargo(&["build", "--offline"]));
    assert_eq!(fixture.read("src/main.rs"), source);
    let result = fixture.run(["--offline", "-vv"]);
    assert!(!result.status.success());
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(stderr.contains("RID_TEST_COPIED_INPUT_CHANGED"), "{stderr}");
    assert!(stderr.contains("changed"), "{stderr}");
    assert_eq!(fixture.read("src/main.rs"), source);
}

fn prepare_pending_project(fixture: &Fixture, input: &str) {
    fixture.write(
        "Cargo.toml",
        &format!(
            "[package]\nname='edit-boundary'\nversion='0.1.0'\nedition='2024'\n\
             [workspace]\n[[bin]]\nname='edit-boundary'\npath='{input}'\n"
        ),
    );
    fixture.write(
        "build.rs",
        "fn main() { eprintln!(\"RID_TEST_READY_FOR_HOST_EDIT\"); std::thread::sleep(std::time::Duration::from_secs(10)); }\n",
    );
}

#[test]
#[ignore = "runs the distribution image using Docker"]
fn image_refuses_host_edits_while_cargo_is_building() {
    let fixture = Fixture::new();
    prepare_pending_project(&fixture, "src/main.rs");
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("src/main.rs", source);
    let mut running = PendingLauncher::start(&fixture);
    running.wait_for_ready();
    assert_eq!(fixture.read("src/main.rs"), source);
    let edited = "fn main() { println!(\"host edit\"); }\n";
    fixture.write("src/main.rs", edited);
    assert!(running.child.try_wait().unwrap().is_none());
    assert!(!running.wait().success());
    assert!(running.stderr().contains("changed"), "{}", running.stderr());
    assert_eq!(fixture.read("src/main.rs"), edited);
}

#[cfg(unix)]
#[test]
#[ignore = "runs the distribution image using Docker"]
fn launcher_interrupt_preserves_source_during_buildkit_execution() {
    let fixture = Fixture::new();
    prepare_pending_project(&fixture, "src/main.rs");
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("src/main.rs", source);
    let mut running = PendingLauncher::start(&fixture);
    running.wait_for_ready();
    // A terminal sends Ctrl-C to the foreground process group, including Buildx.
    assert_eq!(
        unsafe { libc::kill(-(running.child.id() as i32), libc::SIGINT) },
        0
    );
    assert!(!running.wait().success());
    assert_eq!(fixture.read("src/main.rs"), source);
    assert!(!fixture.directory.path().join("Cargo.lock").exists());
    assert!(!fixture.directory.path().join("target").exists());
}

#[cfg(unix)]
#[test]
#[ignore = "runs the distribution image using Docker"]
fn launcher_refuses_an_input_parent_moved_outside_the_workspace() {
    use std::os::unix::fs::{MetadataExt, symlink};
    let fixture = Fixture::new();
    prepare_pending_project(&fixture, "inside/input.rs");
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("inside/input.rs", source);
    let outside = tempfile::tempdir_in(fixture.directory.path().parent().unwrap()).unwrap();
    let mut running = PendingLauncher::start(&fixture);
    running.wait_for_ready();
    let inside = fixture.directory.path().join("inside");
    let before = fs::metadata(inside.join("input.rs")).unwrap();
    let moved = outside.path().join("inside");
    fs::rename(&inside, &moved).unwrap();
    symlink(&moved, &inside).unwrap();
    let after = fs::metadata(inside.join("input.rs")).unwrap();
    assert_eq!((before.dev(), before.ino()), (after.dev(), after.ino()));
    assert_eq!(
        (before.ctime(), before.ctime_nsec()),
        (after.ctime(), after.ctime_nsec())
    );
    assert_eq!(before.modified().unwrap(), after.modified().unwrap());
    assert!(running.child.try_wait().unwrap().is_none());
    assert!(!running.wait().success());
    assert_eq!(fs::read_to_string(moved.join("input.rs")).unwrap(), source);
}

#[cfg(unix)]
#[test]
#[ignore = "runs the distribution image using Docker"]
fn launcher_allows_output_parents_inside_the_workspace_and_refuses_outside_parents() {
    use std::os::unix::fs::symlink;
    let fixture = Fixture::new();
    let source = "fn unused() {}\nfn main() {}\n";
    fixture.write("input.rs", source);
    let inside = fixture.directory.path().join("inside");
    fs::create_dir(&inside).unwrap();
    let link = fixture.directory.path().join("output");
    symlink("inside", &link).unwrap();
    success(fixture.run(["input.rs", "-o", "output/reduced.rs"]));
    let reduced = fixture.read("inside/reduced.rs");
    assert!(!reduced.contains("unused"));
    assert_eq!(fixture.read("input.rs"), source);
    success(fixture.compile("inside/reduced.rs", None));
    success(fixture.run(["inside/reduced.rs"]));
    assert_eq!(fixture.read("inside/reduced.rs"), reduced);

    let outside = tempfile::tempdir_in(fixture.directory.path().parent().unwrap()).unwrap();
    fs::remove_file(link).unwrap();
    symlink(outside.path(), fixture.directory.path().join("output")).unwrap();
    let result = fixture.run(["input.rs", "-o", "output/refused.rs"]);
    assert!(!result.status.success());
    assert_eq!(fixture.read("input.rs"), source);
    assert!(!outside.path().join("refused.rs").exists());
}

struct PendingLauncher {
    child: std::process::Child,
    stderr: tempfile::NamedTempFile,
}

impl PendingLauncher {
    fn start(fixture: &Fixture) -> Self {
        let stderr = tempfile::Builder::new()
            .prefix("launcher-")
            .tempfile_in(fixture.directory.path().parent().unwrap())
            .unwrap();
        let mut command = fixture.launcher();
        command.args(["--offline", "-vv"]);
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        Self {
            child: command
                .stdout(std::process::Stdio::null())
                .stderr(stderr.reopen().unwrap())
                .spawn()
                .unwrap(),
            stderr,
        }
    }

    fn stderr(&self) -> String {
        fs::read_to_string(self.stderr.path()).unwrap()
    }

    fn wait_for_ready(&mut self) {
        let start = std::time::Instant::now();
        loop {
            let stderr = self.stderr();
            assert!(
                self.child.try_wait().unwrap().is_none()
                    && start.elapsed() < std::time::Duration::from_secs(60),
                "launcher did not reach the boundary: {stderr}"
            );
            if stderr.contains("RID_TEST_READY_FOR_HOST_EDIT") {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    fn wait(&mut self) -> std::process::ExitStatus {
        let start = std::time::Instant::now();
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return status;
            }
            assert!(
                start.elapsed() < std::time::Duration::from_secs(60),
                "launcher did not finish: {}",
                self.stderr()
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}

impl Drop for PendingLauncher {
    fn drop(&mut self) {
        if matches!(self.child.try_wait(), Ok(None)) {
            #[cfg(unix)]
            unsafe {
                libc::kill(-(self.child.id() as i32), libc::SIGKILL);
            }
            #[cfg(windows)]
            let _ = Command::new("taskkill.exe")
                .args(["/PID", &self.child.id().to_string(), "/T", "/F"])
                .output();
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}
