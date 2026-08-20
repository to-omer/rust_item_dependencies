#!/bin/sh
set -eu

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
patch_directory="$repository_root/rustc-patches"
digest_input=$(mktemp "${TMPDIR:-/tmp}/rust-item-dependencies-queue.XXXXXX")
trap 'rm -f -- "$digest_input"' EXIT HUP INT TERM

emit_file() {
    relative_path=$1
    file="$patch_directory/$relative_path"
    byte_count=$(LC_ALL=C wc -c < "$file" | tr -d ' ')
    printf 'file\000%s\000%s\000' "$relative_path" "$byte_count"
    LC_ALL=C cat "$file"
    printf '\000'
}

{
    printf 'rust-item-dependencies-patch-queue-v1\000'
    emit_file base-revision
    emit_file patch-abi
    emit_file series

    while IFS= read -r patch_name; do
        case "$patch_name" in
            ""|'#'*) continue ;;
        esac
        if [ ! -f "$patch_directory/$patch_name" ]; then
            echo "patch listed in series does not exist: $patch_name" >&2
            exit 1
        fi
        emit_file "$patch_name"
    done < "$patch_directory/series"
} > "$digest_input"

if command -v sha256sum >/dev/null 2>&1; then
    digest_output=$(sha256sum "$digest_input")
elif command -v shasum >/dev/null 2>&1; then
    digest_output=$(shasum -a 256 "$digest_input")
else
    echo "sha256sum or shasum is required" >&2
    exit 1
fi

printf '%s\n' "$digest_output" | awk '{print $1}'
