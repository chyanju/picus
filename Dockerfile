# Stage 1: Builder
FROM ubuntu:24.04 AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates build-essential cmake python3 bison git pkg-config \
    libclang-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /build
COPY . .

# Build Picus (compiles z3 + cvc5 with CoCoA from source)
RUN cargo build --release

# Stage 2: Runtime
FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
    libstdc++6 libgmp10 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/picus /usr/local/bin/picus

ENTRYPOINT ["picus"]
