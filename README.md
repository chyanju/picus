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

## Installation

Default builds are pure Rust: the in-tree `native` finite-field solver needs no external solver and no extra system dependencies. cvc5 / z3 are never compiled unless you opt in (see below).

```bash
# Install to PATH
cargo install --path crates/picus-cli

# Or build and run locally
cargo build --release
./target/release/picus check --r1cs circuit.r1cs

# Or via Docker
docker build -t picus .
docker run --rm -v $(pwd):/data picus check --r1cs /data/circuit.r1cs
```

> The optional **cvc5** and **z3** backends are compiled only on explicit opt-in (`--features cvc5` / `z3`) and carry extra build requirements (and, for cvc5, GPLv3 licensing) — see [docs/building.md](docs/building.md).

## Usage

```bash
picus check --r1cs circuit.r1cs                   # verify uniqueness (native + ff)
picus check --r1cs circuit.r1cs --solver none     # propagation only, no solver
picus check --r1cs circuit.r1cs --lemmas all-bim  # tune propagation lemmas
picus check --r1cs circuit.r1cs --format json     # machine-readable output
picus check --r1cs circuit.r1cs --config my.toml  # load settings from a config file

picus info --r1cs circuit.r1cs --constraints      # inspect R1CS metadata
```

**Configuration.** No config is required — every setting has a built-in default. To customise, copy [`picus.default.toml`](picus.default.toml) (it documents every key), edit it, and pass it with `--config <file>`; or drop a `./picus.toml` in the working directory and it is picked up automatically. Sources layer, with later winning: built-in defaults < config file < individual CLI flags. Full flag and configuration reference: [docs/usage.md](docs/usage.md).

## Use as a Rust Library

```toml
[dependencies]
# Tracks the main branch (the stable branch); default features = native
# solver only, no external build chain.
picus = { git = "https://github.com/chyanju/Picus", branch = "main" }

# To also build the cvc5 / z3 backends:
# picus = { git = "https://github.com/chyanju/Picus", branch = "main", features = ["cvc5"] }
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

See `crates/picus/src/lib.rs` for the full API, including `check_r1cs_bytes()`, `check_r1cs()`, `PicusConfig::from_file()`, and re-exported types.

## Documentation

| | |
|---|---|
| [Usage](docs/usage.md) | CLI flags, configuration, result interpretation, solver differences, troubleshooting |
| [Building cvc5 / z3](docs/building.md) | Optional external backends: build requirements and licensing |
| [Architecture](docs/architecture.md) | Crate structure, data flow, solver backends |
| [Propagation Lemmas](docs/lemmas.md) | Deduction rules and their implementation |
| [Changelog](CHANGELOG.md) | Version history |

## Citation

To cite the **software** itself, use the **"Cite this repository"** button in the GitHub sidebar — it is generated from [`CITATION.cff`](CITATION.cff) and provides ready-made APA and BibTeX entries pinned to a released version.

To cite the **research** behind Picus, use the PLDI 2023 paper:

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
