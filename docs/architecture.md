# Architecture

Picus is organized as a Cargo workspace with seven crates. Data flows top-to-bottom through the pipeline; each layer depends only on the one below it.

```
┌─────────────┐
│  picus-cli  │   CLI entry point (clap subcommands)
└──────┬──────┘
       │
┌──────▼──────┐
│    picus    │   Public library API (facade crate)
└──────┬──────┘
       │
┌──────▼──────┐
│picus-analysis│  DPVL algorithm, propagation lemmas, selectors
└──────┬──────┘
       │
┌──────▼──────┐
│  picus-smt  │   Solver backends (z3/cvc5 Rust APIs), query IR
└──────┬──────┘
       │
┌──────▼──────┐
│  picus-r1cs │   Binary R1CS parser, AST types
└─────────────┘

┌──────────────┐   ┌────────────┐
│  cvc5-ff-sys │   │  cvc5-ff   │   Local fork of cvc5 Rust bindings
│  (C FFI)     │◄──│  (safe API)│   Auto-compiles cvc5 with CoCoA from source
└──────────────┘   └────────────┘
```

## Crates

### `picus-r1cs`

Foundation layer. No external Picus dependencies.

- **`grammar.rs`** — AST type definitions (`RCmd`, `RExpr`) used by the propagation pipeline, plus variable extraction utilities (linear vs. nonlinear classification).
- **`parser.rs`** — Reads the [iden3 R1CS binary format](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md): magic number, header, constraints (sparse A·B=C triples), wire-to-label section.

### `picus-smt`

Solver interaction layer with three sub-components:

- **`query.rs`** — Defines `UniquenessQuery`, a solver-agnostic intermediate representation (IR). The `build_query()` function converts R1CS binary constraints directly into IR form (linear and nonlinear terms), bypassing the AST pipeline.
- **`backends/`** — Three solver backend implementations, each implementing the `SolverBackend` trait:
  - **`z3_nia.rs`** — z3 Rust API, QF_NIA (integer arithmetic with `mod p`)
  - **`cvc5_ff.rs`** — cvc5 Rust API, QF_FF (native finite field, recommended)
  - **`cvc5_nia.rs`** — cvc5 Rust API, QF_NIA
- **`r1cs_parser.rs`** — R1CS binary → RCmds AST conversion (used by propagation lemmas only, not by solver backends).
- **`optimizer.rs`** — AST-to-AST optimization passes for the propagation pipeline:
  - **AB0:** A·B=0 → A=0 ∨ B=0 (z3 only; disabled for cvc5 due to a known solver bug with `or` in QF_FF)
  - **Normalize:** strip `*1`, `+0`, replace `x0` with `1`
  - **SubP:** substitute field-prime-related constants (`p-1` → `ps1`, etc.)

### `picus-analysis`

Core verification algorithms.

- **`dpvl.rs`** — The DPVL (Decide & Propagate Verification Loop). Uses a `DpvlContext` struct to hold all state. The main loop is non-recursive:
  1. Propagate: run enabled lemmas to fixed point
  2. Check: are all target (output) signals known?
  3. Select: pick an unknown signal via heuristic
  4. Solve: build `UniquenessQuery` IR, call solver backend
  5. Repeat
- **`propagation/`** — Five propagation lemmas. See [Propagation Lemmas](./propagation-lemmas.md).
- **`selector.rs`** — Signal selection heuristics: `first` (trivial) and `counter` (frequency-weighted with negative feedback on timeouts).

### `picus`

Public library API (facade crate). Re-exports key types from the internal crates and provides high-level functions:

- **`check_circuit(path, config)`** — Read an R1CS file and run the full analysis pipeline.
- **`check_r1cs_bytes(data, config)`** — Analyze from raw bytes.
- **`check_r1cs(r1cs, config)`** — Analyze a pre-parsed `R1csFile`.
- **`Config`** — Analysis configuration with sensible defaults (cvc5 + QF_FF + all lemmas).
- **`CheckResult`** — Structured result: `Safe`, `Unsafe { witness_1, witness_2 }`, or `Unknown`.
- **`PicusError`** — Error type covering parse, solver, config, and I/O errors.

This is the entry point for programmatic use from other Rust projects.

### `picus-cli`

Thin entry point with two subcommands:

- **`picus check`** — Runs DPVL on an R1CS file and prints `safe`, `unsafe` (with counter-example), or `unknown`.
- **`picus info`** — Prints R1CS metadata and optionally all constraints in human-readable form.

## Data Flow

```
Circom source (.circom)
  │  circom --r1cs --sym --O0
  ▼
R1CS binary (.r1cs)
  │
  ├──► picus-r1cs::parser ──► R1csFile struct
  │                              │
  │                    ┌─────────┴──────────┐
  │                    │                    │
  │              [Propagation]        [Solving]
  │                    │                    │
  │        r1cs_parser + optimizer    query::build_query
  │              ▼                         ▼
  │         RCmds (AST)           UniquenessQuery (IR)
  │              │                         │
  │         5 lemmas              SolverBackend::solve()
  │         (fixed-point)          ├── Z3NiaBackend
  │              │                 ├── Cvc5FfBackend
  │              ▼                 └── Cvc5NiaBackend
  │         known_set                      │
  │              └────────┬────────────────┘
  │                       ▼
  └──────────────► DpvlResult { Safe | Unsafe(model) | Unknown }
```

The propagation and solving paths operate on different representations:
- **Propagation** uses the RCmds AST (with AB0/normalize/SubP optimizations) because the lemmas need pattern matching on expression structure.
- **Solving** uses the `UniquenessQuery` IR (built directly from R1CS binary) because the solver backends need type-safe term construction via their respective Rust APIs.
