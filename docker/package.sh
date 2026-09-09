#!/bin/sh
set -eu

host=$(rustc -Vv | sed -n 's/^host: //p')
stage2="/opt/rid/target/rid/rustc/build/$host/stage2"
root=/opt/rid/target/container-root

printf 'fn unused() {}\nfn main() {}\n' > target/container-input.rs
target/rid/launcher/release/cargo-rid target/container-input.rs

mkdir -p "$root$(dirname "$stage2")" "$root/usr/local/bin" "$root/usr/share/doc/rust"
cp -a "$stage2" "$root$stage2"
# Bootstrap adds source links that point outside the runtime sysroot.
rm -rf "$root$stage2/lib/rustlib/src" "$root$stage2/lib/rustlib/rustc-src"
cp "target/rid/cargo/$host/release/rust-item-dependencies" "$root/usr/local/bin/"
cp "$(rustup which cargo)" "$root/usr/local/bin/"
ln -s "$stage2/bin/rustc" "$root/usr/local/bin/rustc"
cp -a "$(rustc --print sysroot)/share/doc/rust/." "$root/usr/share/doc/rust/"

licenses="$root/usr/share/doc/rust-item-dependencies/licenses"
for package in /usr/local/cargo/registry/src/*/*; do
    for notice in "$package"/LICENSE* "$package"/LICENCE* "$package"/COPYRIGHT* "$package"/COPYING* "$package"/NOTICE*; do
        if [ -e "$notice" ]; then
            destination="$licenses/$(basename "$package")"
            mkdir -p "$destination"
            cp -a "$notice" "$destination/"
        fi
    done
done
