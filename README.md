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

Picus implements the **QED²** algorithm to verify that R1CS constraints in a ZK circuit uniquely determine all output signals given the public inputs. If they don't, Picus finds a concrete counter-example — two distinct valid witnesses sharing the same inputs.

> Looking for the original PLDI 2023 research artifact? See the [artifact branch](https://github.com/chyanju/Picus/tree/pldi23-research-artifact).

## Prerequisites

### cvc5 (required)

Picus requires cvc5 with finite field theory support (CoCoA). Picus has been tested with cvc5 1.3.3.

**Option A — Pre-built binaries:** Download the **GPL shared library build** (`*-shared-gpl.zip`) from the [cvc5 GitHub Releases](https://github.com/cvc5/cvc5/releases) page and install the headers and libraries to a system-searchable path (e.g., `/usr/local/`).

**Option B — Build from source:** Follow the [cvc5 installation guide](https://cvc5.github.io/docs/cvc5-1.3.2/installation/installation.html). When configuring, enable CoCoA and GPL licensing:
```bash
./configure.sh --auto-download --cocoa --gpl
```
See the [CoCoA section](https://cvc5.github.io/docs/cvc5-1.3.2/installation/installation.html#cocoa-optional-computer-algebra-library) of the guide for details. CoCoA is covered by GPLv3 — using it makes the resulting cvc5 build GPL-licensed.

> **Note:** The non-GPL builds of cvc5 do not include CoCoA and cannot solve finite field (QF_FF) problems.

z3 is bundled automatically during compilation — no separate installation needed.

## Installation

```bash
# Option 1: Install to PATH
cargo install --path crates/picus-cli

# Option 2: Build and run locally
cargo build --release
./target/release/picus check --r1cs circuit.r1cs

# Option 3: Build and run in one step
cargo run --release -p picus-cli -- check --r1cs circuit.r1cs
```

## Usage

### `picus check` — verify circuit uniqueness

```bash
picus check --r1cs circuit.r1cs                              # default: cvc5 + ff
picus check --r1cs circuit.r1cs --solver z3 --theory nia     # z3 with integer arithmetic
picus check --r1cs circuit.r1cs --solver none                # propagation only
picus check --r1cs circuit.r1cs --lemmas linear,binary01     # select specific lemmas
picus check --r1cs circuit.r1cs --dump-smt /tmp/smt/         # dump SMT queries
```

| Flag | Default | Description |
|------|---------|-------------|
| `--r1cs <path>` | *required* | R1CS binary file |
| `--solver <cvc5\|z3\|none>` | `cvc5` | Solver backend (`none` = propagation only) |
| `--theory <ff\|nia>` | `ff` | Theory: `ff` (finite field) or `nia` (integer mod) |
| `--timeout <ms>` | `5000` | Per-query solver timeout |
| `--selector <first\|counter>` | `counter` | Signal selection heuristic |
| `--lemmas <list>` | `all` | Lemmas: `all`, `none`, or comma-separated names (`linear`, `binary01`, `basis2`, `aboz`, `bim`) |
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
| [Architecture](docs/architecture.md) | Crate structure, data flow, solver backends |
| [Propagation Lemmas](docs/propagation-lemmas.md) | Deduction rules and their implementation |
| [Benchmarks](docs/benchmarks.md) | Test suite from 23 real-world projects |
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
