#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 /path/to/clean/rust-checkout" >&2
    exit 2
fi

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
rustc_checkout=$1
patch_directory="$repository_root/rustc-patches"
base_revision=$(tr -d '\r\n' < "$patch_directory/base-revision")
expected_queue_digest=$(tr -d '\r\n' < "$patch_directory/queue-digest")
actual_queue_digest=$("$repository_root/scripts/patch-queue-digest.sh")

if [ "$actual_queue_digest" != "$expected_queue_digest" ]; then
    echo "patch queue digest mismatch: expected $expected_queue_digest, got $actual_queue_digest" >&2
    exit 1
fi

actual_revision=$(git -C "$rustc_checkout" rev-parse HEAD)
if [ "$actual_revision" != "$base_revision" ]; then
    echo "rustc revision mismatch: expected $base_revision, got $actual_revision" >&2
    exit 1
fi

if [ -n "$(git -C "$rustc_checkout" status --porcelain)" ]; then
    echo "rustc checkout is not clean: $rustc_checkout" >&2
    exit 1
fi

while IFS= read -r patch_name; do
    case "$patch_name" in
        ""|'#'*) continue ;;
    esac

    patch_path="$patch_directory/$patch_name"
    if [ ! -f "$patch_path" ]; then
        echo "patch listed in series does not exist: $patch_name" >&2
        exit 1
    fi
    git -C "$rustc_checkout" \
        -c user.name=rust-item-dependencies \
        -c user.email=rust-item-dependencies@invalid.example \
        am --no-gpg-sign --no-verify --committer-date-is-author-date "$patch_path"
done < "$patch_directory/series"

expected_patched_revision=$(tr -d '\r\n' < "$patch_directory/patched-revision")
actual_patched_revision=$(git -C "$rustc_checkout" rev-parse HEAD)
if [ "$actual_patched_revision" != "$expected_patched_revision" ]; then
    echo "patched rustc revision mismatch: expected $expected_patched_revision, got $actual_patched_revision" >&2
    exit 1
fi
