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

## Quick Start

```bash
# Install (requires Rust 1.85+)
cargo install --path crates/picus-cli

# Check a circuit
picus check --r1cs circuit.r1cs --solver cvc5
```

An SMT solver must be on your `PATH` — either [cvc5](https://cvc5.github.io/) (recommended, native finite-field support) or [z3](https://github.com/Z3Prover/z3) 4.10+.

## Usage

### `picus check` — verify circuit uniqueness

```bash
picus check --r1cs circuit.r1cs --solver cvc5
picus check --r1cs circuit.r1cs --nosolve              # propagation only
```

| Flag | Default | Description |
|------|---------|-------------|
| `--r1cs <path>` | *required* | R1CS binary file |
| `--solver <z3\|cvc4\|cvc5>` | `cvc5` | SMT backend |
| `--timeout <ms>` | `5000` | Per-query solver timeout |
| `--selector <first\|counter>` | `counter` | Signal selection heuristic |
| `--noprop` | off | Skip propagation lemmas |
| `--nosolve` | off | Skip solver calls |
| `--map` | off | Resolve signal names from `.sym` |
| `--precondition <path>` | — | JSON precondition file |

### `picus info` — inspect R1CS metadata

```bash
picus info --r1cs circuit.r1cs
picus info --r1cs circuit.r1cs --constraints    # print all constraints
```

## Documentation

| | |
|---|---|
| [Architecture](docs/architecture.md) | Crate structure, data flow pipeline, algorithm overview |
| [Propagation Lemmas](docs/propagation-lemmas.md) | L0–L4 deduction rules and their implementation |
| [Benchmarks](docs/benchmarks.md) | Test suite from 23 real-world projects, expected results |
| [Changelog](CHANGELOG.md) | Version history and release notes |

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
