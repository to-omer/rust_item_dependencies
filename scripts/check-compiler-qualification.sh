#!/bin/sh
set -eu

if [ "$#" -gt 1 ]; then
    echo "usage: $0 [/path/to/rust/build/<host>/stage2]" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
base_revision=$(tr -d '\r\n' < "$repository_root/rustc-patches/base-revision")
queue_digest=$(tr -d '\r\n' < "$repository_root/rustc-patches/queue-digest")

if [ "${RUSTFLAGS+x}" = x ] || [ "${CARGO_ENCODED_RUSTFLAGS+x}" = x ]; then
    echo "compiler qualification controls rustc flags; unset RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS" >&2
    exit 1
fi

sh -n \
    "$repository_root/scripts/apply-rustc-patches.sh" \
    "$repository_root/scripts/build-patched-rustc.sh" \
    "$repository_root/scripts/check-acceptance.sh" \
    "$repository_root/scripts/check-patched-rustc.sh" \
    "$repository_root/scripts/patch-queue-digest.sh"

if [ "$#" -eq 0 ]; then
    active_rustc=$(command -v rustc)
    actual_revision=$("$active_rustc" -Vv | sed -n 's/^commit-hash: //p' | tr -d '\r')
    if [ "$actual_revision" != "$base_revision" ]; then
        echo "active rustc revision mismatch: expected $base_revision, got $actual_revision" >&2
        exit 1
    fi

    RUSTC="$active_rustc" cargo test \
        --manifest-path "$repository_root/Cargo.toml" \
        --offline \
        --locked \
        -- \
        --test-threads=1
    exit 0
fi

stage2_sysroot=$(CDPATH= cd -- "$1" && pwd)
stage2_rustc="$stage2_sysroot/bin/rustc"
if [ -f "$stage2_rustc.exe" ]; then
    stage2_rustc="$stage2_rustc.exe"
fi
"$repository_root/scripts/check-patched-rustc.sh" "$stage2_sysroot"

host=$("$stage2_rustc" -Vv | sed -n 's/^host: //p' | tr -d '\r')
build_directory=$(dirname -- "$stage2_sysroot")
compiler_metadata="$build_directory/stage1/lib/rustlib/$host/lib"

native_path() {
    case "$host" in
        *-windows-*) cygpath -m "$1" ;;
        *) printf '%s\n' "$1" ;;
    esac
}

compiler_library="$stage2_sysroot/lib"
case "$host" in
    *-windows-*) compiler_library="$stage2_sysroot/bin" ;;
esac
set --
for candidate in \
    "$compiler_library"/librustc_driver-*.so \
    "$compiler_library"/librustc_driver-*.dylib \
    "$compiler_library"/rustc_driver-*.dll
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

set -- "$compiler_metadata"/librustc_ast-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_ast metadata file" >&2
    exit 1
fi
rustc_ast=$1

set -- "$compiler_metadata"/librustc_interface-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_interface metadata file" >&2
    exit 1
fi
rustc_interface=$1

set -- "$compiler_metadata"/librustc_data_structures-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_data_structures metadata file" >&2
    exit 1
fi
rustc_data_structures=$1

set -- "$compiler_metadata"/librustc_errors-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_errors metadata file" >&2
    exit 1
fi
rustc_errors=$1

set -- "$compiler_metadata"/librustc_expand-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_expand metadata file" >&2
    exit 1
fi
rustc_expand=$1

set -- "$compiler_metadata"/librustc_hir-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_hir metadata file" >&2
    exit 1
fi
rustc_hir=$1

set -- "$compiler_metadata"/librustc_feature-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_feature metadata file" >&2
    exit 1
fi
rustc_feature=$1

set -- "$compiler_metadata"/librustc_middle-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_middle metadata file" >&2
    exit 1
fi
rustc_middle=$1

set -- "$compiler_metadata"/librustc_lexer-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_lexer metadata file" >&2
    exit 1
fi
rustc_lexer=$1

set -- "$compiler_metadata"/librustc_session-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_session metadata file" >&2
    exit 1
fi
rustc_session=$1

set -- "$compiler_metadata"/librustc_serialize-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_serialize metadata file" >&2
    exit 1
fi
rustc_serialize=$1

set -- "$compiler_metadata"/librustc_span-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_span metadata file" >&2
    exit 1
fi
rustc_span=$1

set -- "$compiler_metadata"/librustc_target-*.rmeta
if [ "$#" -ne 1 ] || [ ! -f "$1" ]; then
    echo "expected exactly one rustc_target metadata file" >&2
    exit 1
fi
rustc_target=$1

stage2_rustc=$(native_path "$stage2_rustc")
rustc_driver=$(native_path "$rustc_driver")
rustc_ast=$(native_path "$rustc_ast")
rustc_interface=$(native_path "$rustc_interface")
rustc_data_structures=$(native_path "$rustc_data_structures")
rustc_errors=$(native_path "$rustc_errors")
rustc_expand=$(native_path "$rustc_expand")
rustc_hir=$(native_path "$rustc_hir")
rustc_feature=$(native_path "$rustc_feature")
rustc_middle=$(native_path "$rustc_middle")
rustc_lexer=$(native_path "$rustc_lexer")
rustc_session=$(native_path "$rustc_session")
rustc_serialize=$(native_path "$rustc_serialize")
rustc_span=$(native_path "$rustc_span")
rustc_target=$(native_path "$rustc_target")
compiler_metadata=$(native_path "$compiler_metadata")
cargo_target_directory=$(native_path "$repository_root/target/rust-item-dependencies/tests/cargo-$queue_digest")

# Cargo cannot discover rustc_private crates from the stage2 sysroot because
# their metadata is emitted under stage1. Pass every crate used directly by
# the qualification crate, without changing the compiler or copying sysroot files.
unit_separator=$(printf '\037')
encoded_rustflags="--extern${unit_separator}rustc_driver=$rustc_driver"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_ast=$rustc_ast"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_data_structures=$rustc_data_structures"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_errors=$rustc_errors"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_expand=$rustc_expand"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_feature=$rustc_feature"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_interface=$rustc_interface"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_hir=$rustc_hir"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_lexer=$rustc_lexer"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_middle=$rustc_middle"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_session=$rustc_session"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_serialize=$rustc_serialize"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_span=$rustc_span"
encoded_rustflags="${encoded_rustflags}${unit_separator}--extern${unit_separator}rustc_target=$rustc_target"
encoded_rustflags="${encoded_rustflags}${unit_separator}-L${unit_separator}dependency=$compiler_metadata"

PATH="$compiler_library${PATH:+:$PATH}" \
RUSTC="$stage2_rustc" \
CARGO_ENCODED_RUSTFLAGS="$encoded_rustflags" \
CARGO_TARGET_DIR="$cargo_target_directory" \
cargo test \
    --manifest-path "$repository_root/Cargo.toml" \
    --offline \
    --locked \
    -- \
    --test-threads=1
