# Building with cvc5 / z3

The default build is pure Rust — the in-tree `native` finite-field solver needs
no external solver and no extra system dependencies. The default commands build
native only:

```bash
cargo build --release                         # native only
cargo install --path crates/picus-cli         # native only
```

The optional cvc5 and z3 backends are compiled only on explicit opt-in via
their Cargo features. They are independent — enable either or both:

```bash
cargo build --release -p picus-cli --features cvc5
cargo build --release -p picus-cli --features z3
cargo build --release -p picus-cli --features "cvc5 z3"
```

> The `cvc5-ff` / `cvc5-ff-sys` / `z3` crates are excluded from the workspace's
> `default-members`, so no default command compiles them. They build only when
> a feature pulls them in (above), or when explicitly requested via
> `cargo build --workspace` / `-p cvc5-ff`.

## Build dependencies (cvc5 / z3 from source)

cmake, python3, python3-venv, a C++ compiler (gcc or clang), make, bison, git,
libclang-dev, pkg-config.

> The first build of either external backend compiles it from source: cvc5 and
> z3 take roughly 15–20 minutes combined. Subsequent builds are incremental.

## Using pre-installed solver libraries

To skip compiling a solver from source, point the build at an existing install:

```bash
# Use a prebuilt cvc5 (requires a cvc5 GPL build with CoCoA)
CVC5_LIB_DIR=/path/to/cvc5/lib cargo build --release -p picus-cli --features cvc5

# Use a prebuilt z3
Z3_LIBRARY_PATH_OVERRIDE=/path/to/z3/lib cargo build --release -p picus-cli --features z3
```

For `CVC5_LIB_DIR`, headers are expected at `../include/` relative to the lib
directory (or set `CVC5_INCLUDE_DIR` separately).

## Licensing

Picus source is MIT-licensed, and the default `native`-only build links no
external solver — it is MIT.

cvc5 is built with CoCoA (GPLv3) for finite-field support. A binary built
**with `--features cvc5`** is a combined work under GPLv3 when distributed. See
cvc5's [COPYING](https://github.com/cvc5/cvc5/blob/main/COPYING) for details.
