#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 /path/to/rust/build/<host>/stage2" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
stage2_sysroot=$(CDPATH= cd -- "$1" && pwd -P)
rustc_source=$(CDPATH= cd -- "$stage2_sysroot/../../.." && pwd -P)
stage0_sysroot=$(CDPATH= cd -- "$stage2_sysroot/../stage0" && pwd -P)
rustfmt_root="$stage2_sysroot/../rustfmt"
observer_build="$repository_root/target/rid/compiler-observer"
observer_config="$repository_root/target/rid/compiler-observer.toml"
queue_digest=$(tr -d '\r\n' < "$repository_root/rustc-patches/queue-digest")
expected_revision=$(tr -d '\r\n' < "$repository_root/rustc-patches/patched-revision")
executable_suffix=
if [ -f "$stage2_sysroot/bin/rustc.exe" ]; then
    executable_suffix=.exe
fi
stage2_rustc="$stage2_sysroot/bin/rustc$executable_suffix"
stage0_rustc="$stage0_sysroot/bin/rustc$executable_suffix"
stage0_cargo="$stage0_sysroot/bin/cargo$executable_suffix"
cargo_fmt="$rustfmt_root/bin/cargo-fmt$executable_suffix"
rustfmt="$rustfmt_root/bin/rustfmt$executable_suffix"
llvm_config="$stage2_sysroot/../ci-llvm/bin/llvm-config$executable_suffix"

if [ "${RUSTFLAGS+x}" = x ] || [ "${CARGO_ENCODED_RUSTFLAGS+x}" = x ]; then
    echo "acceptance checks control rustc flags; unset RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS" >&2
    exit 1
fi
unset CARGOFLAGS CARGOFLAGS_BOOTSTRAP CARGOFLAGS_NOT_BOOTSTRAP

if [ ! -x "$stage0_rustc" ] \
    || [ ! -x "$stage0_cargo" ] \
    || [ ! -x "$stage2_rustc" ] \
    || [ ! -x "$rustc_source/x.py" ] \
    || [ ! -x "$cargo_fmt" ] \
    || [ ! -x "$rustfmt" ] \
    || [ ! -x "$llvm_config" ]; then
    echo "stage2 does not belong to a usable rust source checkout: $stage2_sysroot" >&2
    exit 1
fi

actual_revision=$(git -C "$rustc_source" rev-parse HEAD)
if [ "$actual_revision" != "$expected_revision" ]; then
    echo "rust source revision mismatch: expected $expected_revision, got $actual_revision" >&2
    exit 1
fi
if [ -n "$(git -C "$rustc_source" status --porcelain)" ]; then
    echo "rust source checkout must be clean" >&2
    exit 1
fi

build_target=$("$stage2_rustc" -Vv | sed -n 's/^host: //p' | tr -d '\r')
if [ -z "$build_target" ]; then
    echo "stage2 rustc did not report its host target" >&2
    exit 1
fi

native_path() {
    case "$build_target" in
        *-windows-*) cygpath -m "$1" ;;
        *) printf '%s\n' "$1" ;;
    esac
}

toml_escape() {
    sed 's/\\/\\\\/g; s/"/\\"/g'
}

echo "==> source format"
(
    cd "$rustc_source"
    "$rustc_source/x" fmt --ci=false --check --all
)
RUSTFMT="$rustfmt" \
    "$cargo_fmt" fmt \
    --manifest-path "$repository_root/Cargo.toml" --all -- --check
"$rustfmt" --edition 2024 --check "$repository_root/tools/rid.rs"
git -C "$repository_root" diff --check

echo "==> bootstrap"
(
    cd "$rustc_source"
    "$rustc_source/x" test --ci=false bootstrap
)

echo "==> stock compiler boundary"
"$repository_root/scripts/check-compiler-qualification.sh"

echo "==> patched compiler observer fixtures"
(
    cd "$rustc_source"
    RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST="$queue_digest" \
        "$rustc_source/x" test --ci=false --stage 2 \
        --keep-stage 0 --keep-stage 1 --force-rerun --all-targets \
        tests/ui-fulldeps/derive-observer.rs \
        tests/ui-fulldeps/selection-proof-trace.rs \
        tests/ui-fulldeps/macro-rule-observer.rs \
        tests/ui-fulldeps/proc-macro-load-guard.rs \
        tests/ui-fulldeps/run-compiler-twice.rs \
        tests/ui-fulldeps/external-crate-load-requirements.rs \
        tests/ui-fulldeps/associated-item-proof.rs \
        tests/ui-fulldeps/typed-mono-successors.rs \
        tests/ui-fulldeps/typeck-impl-dependencies.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-associated-struct.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-copy-coherence.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-copy-use.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-coroutine.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-drop.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-for-loop.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-source-free-origins.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-structural-pattern.rs \
        tests/ui-fulldeps/typeck-impl-dependencies-union.rs \
        tests/ui/lint/unused/unused-macro-rules-decl.rs \
        tests/ui/resolve/error-recovery-import-observer.rs
)

echo "==> patched compiler observer unit tests"
mkdir -p "$(dirname -- "$observer_config")"
{
    printf '%s\n' 'change-id = "ignore"' '' '[build]'
    printf 'rustc = "%s"\n' "$(native_path "$stage0_rustc" | toml_escape)"
    printf 'cargo = "%s"\n' "$(native_path "$stage0_cargo" | toml_escape)"
    printf 'rustfmt = "%s"\n' "$(native_path "$rustfmt" | toml_escape)"
    printf '%s\n' '' '[llvm]' 'download-ci-llvm = false' ''
    printf '[target.%s]\n' "$build_target"
    printf 'llvm-config = "%s"\n' "$(native_path "$llvm_config" | toml_escape)"
    printf '%s\n' 'llvm-has-rust-patches = true'
} > "$observer_config"
(
    cd "$rustc_source"
    RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST="$queue_digest" \
        "$rustc_source/x" test --ci=false --stage 1 \
        --config "$observer_config" \
        --build-dir "$observer_build" \
        --force-rerun --all-targets \
        compiler/rustc_expand \
        compiler/rustc_resolve \
        compiler/rustc_span
)

echo "==> owned graph, reduction, and verification"
"$repository_root/scripts/check-compiler-qualification.sh" "$stage2_sysroot"

echo "acceptance checks passed"
