#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 /path/to/rust/build/<host>/stage2" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
stage2_sysroot=$(CDPATH= cd -- "$1" && pwd)
stage2_rustc="$stage2_sysroot/bin/rustc"
if [ -f "$stage2_rustc.exe" ]; then
    stage2_rustc="$stage2_rustc.exe"
fi

expected_queue_digest=$(tr -d '\r\n' < "$repository_root/rustc-patches/queue-digest")
actual_queue_digest=$("$repository_root/scripts/patch-queue-digest.sh")
if [ "$actual_queue_digest" != "$expected_queue_digest" ]; then
    echo "patch queue digest mismatch: expected $expected_queue_digest, got $actual_queue_digest" >&2
    exit 1
fi

rustc_checkout=$(dirname -- "$(dirname -- "$(dirname -- "$stage2_sysroot")")")
expected_patched_revision=$(tr -d '\r\n' < "$repository_root/rustc-patches/patched-revision")
actual_patched_revision=$(git -C "$rustc_checkout" rev-parse HEAD)
if [ "$actual_patched_revision" != "$expected_patched_revision" ]; then
    echo "patched rustc revision mismatch: expected $expected_patched_revision, got $actual_patched_revision" >&2
    exit 1
fi
if [ -n "$(git -C "$rustc_checkout" status --porcelain)" ]; then
    echo "patched rustc checkout is not clean: $rustc_checkout" >&2
    exit 1
fi

if [ ! -x "$stage2_rustc" ]; then
    echo "stage2 rustc is not executable: $stage2_rustc" >&2
    exit 1
fi

host=$("$stage2_rustc" -Vv | sed -n 's/^host: //p' | tr -d '\r')
if [ -z "$host" ]; then
    echo "stage2 rustc did not report a host" >&2
    exit 1
fi

build_directory=$(dirname -- "$stage2_sysroot")
compiler_metadata="$build_directory/stage1/lib/rustlib/$host/lib"
if [ ! -d "$compiler_metadata" ]; then
    echo "stage1 compiler metadata is missing: $compiler_metadata" >&2
    exit 1
fi

compiler_library="$stage2_sysroot/lib"
executable_suffix=
case "$host" in
    *-windows-*)
        compiler_library="$stage2_sysroot/bin"
        executable_suffix=.exe
        ;;
esac
set --
for candidate in \
    "$compiler_metadata"/librustc_driver-*.so \
    "$compiler_metadata"/librustc_driver-*.dylib \
    "$compiler_metadata"/rustc_driver-*.dll
do
    if [ -f "$candidate" ]; then
        set -- "$@" "$candidate"
    fi
done
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one stage2 rustc_driver shared library" >&2
    exit 1
fi
rustc_driver=$1

temporary_directory=$(mktemp -d "${TMPDIR:-/tmp}/rust-item-dependencies-patch-abi.XXXXXX")
trap 'rm -rf -- "$temporary_directory"' EXIT HUP INT TERM

compile_driver_fixture() {
    source=$1
    output=$2
    case "$host" in
        *-windows-*)
            "$stage2_rustc" \
                --sysroot "$stage2_sysroot" \
                --edition=2024 \
                --extern "rustc_driver=$rustc_driver" \
                -C prefer-dynamic \
                -L "dependency=$compiler_metadata" \
                -L "native=$compiler_library" \
                "$source" \
                -o "$output"
            ;;
        *)
            "$stage2_rustc" \
                --sysroot "$stage2_sysroot" \
                --edition=2024 \
                --extern "rustc_driver=$rustc_driver" \
                -C prefer-dynamic \
                -L "dependency=$compiler_metadata" \
                -L "native=$compiler_library" \
                -C "link-arg=-Wl,-rpath,$compiler_library" \
                "$source" \
                -o "$output"
            ;;
    esac
}

compile_driver_fixture \
    "$repository_root/tests/fixtures/compiler/patch_abi.rs" \
    "$temporary_directory/patch-abi$executable_suffix"
PATH="$compiler_library${PATH:+:$PATH}" "$temporary_directory/patch-abi$executable_suffix"

compile_driver_fixture \
    "$repository_root/tests/fixtures/compiler/input_guard.rs" \
    "$temporary_directory/input-guard$executable_suffix"
PATH="$compiler_library${PATH:+:$PATH}" "$temporary_directory/input-guard$executable_suffix" \
    "$stage2_sysroot" \
    "$repository_root/tests/fixtures/compiler/environment_macro.rs" \
    2>"$temporary_directory/input-guard.stderr"
