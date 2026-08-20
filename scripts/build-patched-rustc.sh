#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 /path/to/patched/rust-checkout" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
rustc_checkout=$(CDPATH= cd -- "$1" && pwd)

expected_revision=$(tr -d '\r\n' < "$repository_root/rustc-patches/patched-revision")
actual_revision=$(git -C "$rustc_checkout" rev-parse HEAD)
if [ "$actual_revision" != "$expected_revision" ]; then
    echo "patched rustc revision mismatch: expected $expected_revision, got $actual_revision" >&2
    exit 1
fi
if [ -n "$(git -C "$rustc_checkout" status --porcelain)" ]; then
    echo "patched rustc checkout is not clean: $rustc_checkout" >&2
    exit 1
fi

expected_queue_digest=$(tr -d '\r\n' < "$repository_root/rustc-patches/queue-digest")
actual_queue_digest=$("$repository_root/scripts/patch-queue-digest.sh")
if [ "$actual_queue_digest" != "$expected_queue_digest" ]; then
    echo "patch queue digest mismatch: expected $expected_queue_digest, got $actual_queue_digest" >&2
    exit 1
fi

cd "$rustc_checkout"
RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST="$actual_queue_digest" \
    ./x check compiler/rustc_driver_impl compiler/rustc_builtin_macros
./x fmt --check --all
RUST_ITEM_DEPENDENCIES_PATCH_QUEUE_DIGEST="$actual_queue_digest" \
    ./x build --stage 2 compiler/rustc library
