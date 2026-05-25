# Native-only image: builds the default pure-Rust FF solver (no cvc5 / z3).
# For an image with the external backends, add their Cargo features and build
# dependencies — see docs/building.md.

# Stage 1: Builder
FROM ubuntu:24.04 AS builder

# Native build needs only a C toolchain plus m4 (for the GMP that `rug` builds
# from source) and curl to fetch rustup — no cvc5 / z3 build chains.
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates build-essential m4 \
    && rm -rf /var/lib/apt/lists/*

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /build
COPY . .

# Default build path: native solver only. The workspace default-members
# excludes the cvc5 / z3 crates, so this compiles no external backend.
RUN cargo build --release

# Stage 2: Runtime
FROM ubuntu:24.04

# The native binary links only libc / libm / libgcc_s (all in the base image);
# GMP is statically linked and there is no C++ runtime.
COPY --from=builder /build/target/release/picus /usr/local/bin/picus

ENTRYPOINT ["picus"]
