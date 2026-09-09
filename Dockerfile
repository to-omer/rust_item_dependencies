FROM rust:1.89.0-trixie@sha256:57407b378b2b6e07b48a6135a20c87cc22ea6e249c0acf6cb1833ead3cf116e9 AS compiler

RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 cmake ninja-build clang lld \
    g++-x86-64-linux-gnu g++-aarch64-linux-gnu \
    && rm -rf /var/lib/apt/lists/*
RUN rustup toolchain install nightly-2026-08-10 --profile minimal --component rustc-dev --component rust-src

WORKDIR /opt/rid
COPY rust-toolchain.toml ./
COPY tools/Cargo.toml tools/Cargo.lock tools/rid.rs tools/cli.rs tools/container.rs tools/container_protocol.rs tools/
COPY src/file_output.rs src/file_output.rs
COPY src/target_libraries.rs src/target_libraries.rs
COPY rustc-patches rustc-patches
COPY docker/compiler.toml docker/compiler.toml
RUN mkdir -p target/rid/rustc \
    && cp docker/compiler.toml target/rid/rustc/config.toml \
    && cargo run --locked --release --manifest-path tools/Cargo.toml --target-dir target/rid/launcher -- rustc -Vv

FROM compiler AS application
COPY Cargo.toml Cargo.lock build.rs ./
COPY .cargo .cargo
COPY src src
COPY tests/fixtures/compiler/patch_abi.rs tests/fixtures/compiler/patch_abi.rs
COPY docker/package.sh docker/package.sh
RUN sh docker/package.sh

FROM debian:trixie-slim@sha256:d7e12182ce18b85b93007c1dedf31f2d29e01ccf3182cc4017c709b6259bc132
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates gcc g++ libc6-dev make pkg-config git zlib1g \
    && rm -rf /var/lib/apt/lists/*
COPY --from=application /opt/rid/target/container-root/ /
COPY --chmod=755 docker/cargo-rid /usr/local/bin/cargo-rid
ENV CARGO_HOME=/tmp/rid-cargo-home \
    CARGO_TARGET_DIR=/tmp/rid-target \
    RUSTC=/usr/local/bin/rustc
WORKDIR /workspace
RUN chown 1000:1000 /workspace
USER 1000:1000
ENTRYPOINT ["/usr/local/bin/cargo-rid"]
