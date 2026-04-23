<div align="center">
  <img src="./docs/logo.png" width="120">
  <h1>Picus</h1>
  <p><strong>Automated detection of under-constrained signals in zero-knowledge circuits</strong></p>
  <p>
    <a href="https://doi.org/10.1145/3591283"><img src="https://img.shields.io/badge/PLDI-2023-blue" alt="PLDI 2023"></a>
    <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-green" alt="MIT License"></a>
    <a href="https://www.rust-lang.org/"><img src="https://img.shields.io/badge/rust-1.85%2B-orange" alt="Rust 1.85+"></a>
  </p>
</div>

---

Picus is a security analysis tool for detecting under-constrained signals in zero-knowledge proof circuits. Given an R1CS constraint system, it verifies that all output signals are uniquely determined by the public inputs — or produces a concrete counter-example showing two distinct valid witnesses.

The techniques underlying Picus are described in the PLDI 2023 paper *"Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs"* (see [Citation](#citation)).

> Looking for the original PLDI 2023 research artifact? See the [artifact branch](https://github.com/chyanju/Picus/tree/pldi23-research-artifact).

## Prerequisites

Both z3 and cvc5 (with finite field support) are automatically compiled from source during `cargo build`. No manual solver installation is required.

**Build dependencies:** cmake, python3, python3-venv, C++ compiler (gcc or clang), make, bison, git, libclang-dev, pkg-config.

> First build takes ~15-20 minutes (z3 + cvc5 compilation). Subsequent builds are incremental.

> **Faster builds with pre-installed solvers:** If you already have solver libraries installed, you can skip compilation:
> ```bash
> # Skip cvc5 compilation (requires cvc5 GPL build with CoCoA)
> CVC5_LIB_DIR=/path/to/cvc5/lib cargo build --release
>
> # Skip z3 compilation
> Z3_LIBRARY_PATH_OVERRIDE=/path/to/z3/lib cargo build --release
> ```
> For `CVC5_LIB_DIR`, headers should be at `../include/` relative to the lib directory (or set `CVC5_INCLUDE_DIR` separately).

> **Note on licensing:** cvc5 is compiled with CoCoA (GPLv3) for finite field support. Picus source code is MIT-licensed. The compiled binary is a combined work under GPLv3 when distributed. See cvc5's [COPYING](https://github.com/cvc5/cvc5/blob/main/COPYING) for details.

## Installation

```bash
# Option 1: Install to PATH
cargo install --path crates/picus-cli

# Option 2: Build and run locally
cargo build --release
./target/release/picus check --r1cs circuit.r1cs

# Option 3: Build and run in one step
cargo run --release -p picus-cli -- check --r1cs circuit.r1cs

# Option 4: Docker
docker build -t picus .
docker run --rm -v $(pwd):/data picus check --r1cs /data/circuit.r1cs
```

## Use as a Rust Library

Picus can also be used as a library crate in other Rust projects:

```toml
[dependencies]
picus = { git = "https://github.com/chyanju/Picus", tag = "v1.7.5" }
```

```rust
use picus::{check_circuit, Config, CheckResult};

let result = check_circuit("circuit.r1cs", Config::default()).unwrap();
match result {
    CheckResult::Safe => println!("safe"),
    CheckResult::Unsafe { witness_1, witness_2 } => {
        // witness_1/witness_2: HashMap<String, BigUint>
        for (signal, value) in &witness_1 {
            println!("{} = {}", signal, value);
        }
    }
    CheckResult::Unknown => println!("unknown"),
}
```

See `crates/picus/src/lib.rs` for the full API, including `check_r1cs_bytes()`, `check_r1cs()`, and re-exported types.

## Usage

### `picus check` — verify circuit uniqueness

```bash
picus check --r1cs circuit.r1cs                              # default: cvc5 + ff
picus check --r1cs circuit.r1cs --solver native --theory ff  # pure Rust solver (no cvc5)
picus check --r1cs circuit.r1cs --solver z3 --theory nia     # z3 with integer arithmetic
picus check --r1cs circuit.r1cs --solver none                # propagation only
picus check --r1cs circuit.r1cs --lemmas all-bim             # all lemmas except bim
picus check --r1cs circuit.r1cs --format json                # JSON output
picus check --r1cs circuit.r1cs --dump-smt /tmp/smt/         # dump SMT queries
```

| Flag | Default | Description |
|------|---------|-------------|
| `--r1cs <path>` | *required* | R1CS binary file |
| `--solver <cvc5\|z3\|native\|none>` | `cvc5` | Solver backend (`native` = pure Rust, `none` = propagation only) |
| `--theory <ff\|nia>` | `ff` | Theory: `ff` (finite field) or `nia` (integer mod) |
| `--timeout <ms>` | `5000` | Per-query solver timeout |
| `--selector <first\|counter>` | `counter` | Signal selection heuristic |
| `--lemmas <spec>` | `all` | Lemmas: `all`, `none`, `all-X,Y` (exclude), `none+X,Y` (include). Names: `linear`, `binary01`, `basis2`, `aboz`, `bim` |
| `--format <human\|json>` | `human` | Output format |
| `--dump-smt <dir>` | — | Dump SMT-LIB queries to directory |

> **Note**: `z3 + ff` is not supported (z3 has no finite field theory). Picus will reject this combination.

### `picus info` — inspect R1CS metadata

```bash
picus info --r1cs circuit.r1cs
picus info --r1cs circuit.r1cs --constraints
```

## Documentation

| | |
|---|---|
| [Usage Guide](docs/usage-guide.md) | Result interpretation, solver differences, troubleshooting, large circuit strategies |
| [Architecture](docs/architecture.md) | Crate structure, data flow, solver backends |
| [Propagation Lemmas](docs/propagation-lemmas.md) | Deduction rules and their implementation |
| [Benchmarks](docs/benchmarks.md) | Test suite from real-world ZK projects |
| [Future Work](docs/TODO.md) | Planned features and removed components |
| [Changelog](CHANGELOG.md) | Version history |

## Citation

```bibtex
@article{pailoor2023automated,
  author = {Pailoor, Shankara and Chen, Yanju and Wang, Franklyn and Rodr\'{i}guez, Clara and Van Geffen, Jacob and Morton, Jason and Chu, Michael and Gu, Brian and Feng, Yu and Dillig, Isil},
  title = {Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs},
  year = {2023},
  volume = {7},
  number = {PLDI},
  journal = {Proc. ACM Program. Lang.},
  articleno = {165},
  doi = {10.1145/3591283}
}
```

## License

[MIT](LICENSE)
