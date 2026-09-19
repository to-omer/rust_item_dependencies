#!/bin/sh
set -eu

host=$(rustc -Vv | sed -n 's/^host: //p')
stage2="/opt/rid/target/rid/rustc/build/$host/stage2"
compiler_root=/opt/rid/target/container-compiler
application_root=/opt/rid/target/container-application

printf 'fn unused() {}\nfn main() {}\n' > target/container-input.rs
target/rid/launcher/release/cargo-rid target/container-input.rs

mkdir -p "$compiler_root$(dirname "$stage2")" "$compiler_root/usr/local/bin" "$compiler_root/usr/share/doc/rust"
cp -a "$stage2" "$compiler_root$stage2"
# Bootstrap adds source links that point outside the runtime sysroot.
rm -rf "$compiler_root$stage2/lib/rustlib/src" "$compiler_root$stage2/lib/rustlib/rustc-src"
cp "$(rustup which cargo)" "$compiler_root/usr/local/bin/"
ln -s "$stage2/bin/rustc" "$compiler_root/usr/local/bin/rustc"
cp -a "$(rustc --print sysroot)/share/doc/rust/." "$compiler_root/usr/share/doc/rust/"

mkdir -p "$application_root/usr/local/bin"
cp "target/rid/cargo/$host/release/rust-item-dependencies" "$application_root/usr/local/bin/"

# Only strip linked executables and shared libraries; Rust metadata must survive.
strip --strip-unneeded --preserve-dates \
    "$compiler_root$stage2/bin/rustc" \
    "$compiler_root$stage2"/lib/librustc_driver-*.so \
    "$compiler_root$stage2"/lib/libLLVM.so.* \
    "$compiler_root/usr/local/bin/cargo" \
    "$application_root/usr/local/bin/rust-item-dependencies"

licenses="$application_root/usr/share/doc/rust-item-dependencies/licenses"
for package in /usr/local/cargo/registry/src/*/*; do
    for notice in "$package"/LICENSE* "$package"/LICENCE* "$package"/COPYRIGHT* "$package"/COPYING* "$package"/NOTICE*; do
        if [ -e "$notice" ]; then
            destination="$licenses/$(basename "$package")"
            mkdir -p "$destination"
            cp -a "$notice" "$destination/"
        fi
    done
done

# Layer digests include mtimes, even when CI rebuilds identical compiler contents.
find "$compiler_root" -exec touch --no-dereference --date=@0 {} +
