# Architecture

Picus is organized as a Cargo workspace with eight crates. Data flows top-to-bottom through the pipeline; each layer depends only on the one below it.

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

┌──────────────┐
│ picus-solver │   Pure-Rust QF_FF solver (in-tree GB engine, no C++ deps)
└──────────────┘
```

## Crates

### `picus-r1cs`

Foundation layer. No external Picus dependencies.

- **`grammar.rs`** — AST type definitions (`RCmd`, `RExpr`) used by the propagation pipeline, plus variable extraction utilities (linear vs. nonlinear classification).
- **`parser.rs`** — Reads the [iden3 R1CS binary format](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md): magic number, header, constraints (sparse A·B=C triples), wire-to-label section.

### `picus-smt`

Solver interaction layer:

- **`query.rs`** — Defines `UniquenessQuery`, a solver-agnostic intermediate representation (IR). The `build_query()` function converts R1CS binary constraints directly into IR form (linear and nonlinear terms), bypassing the AST pipeline.
- **`backends/`** — Four solver backend implementations, each implementing the `SolverBackend` trait:
  - **`z3_nia.rs`** — z3 Rust API, QF_NIA (integer arithmetic with `mod p`)
  - **`cvc5_ff.rs`** — cvc5 Rust API, QF_FF (native finite field)
  - **`cvc5_nia.rs`** — cvc5 Rust API, QF_NIA
  - **`native_ff.rs`** — pure-Rust QF_FF via `picus-solver`
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
- **`Config`** — Analysis configuration. Defaults: `solver = Cvc5`, `theory = Ff`, `timeout_ms = 5000`, `lemmas = all`, `selector = Counter`.
- **`CheckResult`** — Structured result: `Safe`, `Unsafe { witness_1, witness_2 }`, or `Unknown`.
- **`PicusError`** — Error type covering parse, solver, config, and I/O errors.

This is the entry point for programmatic use from other Rust projects.

### `picus-cli`

Thin entry point with two subcommands:

- **`picus check`** — Runs DPVL on an R1CS file and prints `safe`, `unsafe` (with counter-example), or `unknown`.
- **`picus info`** — Prints R1CS metadata and optionally all constraints in human-readable form.

### `picus-solver`

Pure-Rust finite field (QF_FF) solver. In-tree Buchberger engine
(`src/ff/`) over GMP-backed `FieldElem` (`rug::Integer`); no external
GB library dependency.

- **`core.rs`** — High-level API (`solve_split_gb`, `solve_single_gb`, `SolverMode`, `SolveOutcome`).
- **`split_gb/`** — Split GB algorithm with inter-basis propagation. `split_gb_cancel_traced` carries per-polynomial original-input dependency sets through the fixpoint so the whole-ring detection can report a precise UNSAT core.
- **`gb.rs`** — Single GB solver (DegRevLex → Lex) with cooperative timeout.
- **`ideal.rs`** — Ideal operations (GB computation, membership, reduce, zero-dim check, minimal polynomial).
- **`tracer.rs`** — UNSAT core tracing via `BuchbergerObserver` hooks. Builds a dependency DAG to identify the input subset responsible for unsatisfiability.
- **`encoder.rs`** — `ConstraintSystem` → polynomial encoding. Runs `rewriter::rewrite_system` then `auto_extract_bitsums` before `encode_impl`; the latter routes bitsum-defining polynomials into `bitsum_polys` (basis 0 only).
- **`rewriter.rs`** — Flat term-list canonicalization (`normalize_term_list`, `rewrite_system`): sort vars within each term, sort terms by vars, merge like terms mod prime, drop zero-coefficient terms, drop `0 = 0` equalities. Equivalent of cvc5 `theory_ff_rewriter`.
- **`boolean.rs`** — `Formula` AST over `Eq`/`Neq` literals plus `And`/`Or`/`Not`/`True`/`False`. `nnf` + `to_dnf` produce a DNF; `BooleanQuery::from_formula` runs `rewrite_disjunctive_bit` then NNF/DNF; `solve_boolean_query` dispatches each disjunct to `solve_encoded_with_cancel`. `rewrite_disjunctive_bit` is the equivalent of cvc5 `preprocessing/passes/ff_disjunctive_bit.cpp` (`(or (= x 0) (= x 1))` → `x*x = x`).
- **`model.rs`** — Model construction via iterative ideal augmentation (univariate roots, minimal polynomial, round-robin).
- **`bitprop.rs`** — Bit propagation (constant + equal bitsum) across split bases.
- **`parse.rs`** — Pattern detection (`bit_constraint`, `linear_monomial`, `bit_sums`).
- **`incremental.rs`** — Push/pop API for incremental solving.
- **`incremental_context.rs`** — `IncrementalSolverContext`: split-GB cache keyed on the constraint side; resumable mid-build state.
- **`roots.rs`** — Univariate root finding (Cantor-Zassenhaus, in-tree implementation in `ff/univariate.rs`).
- **`timeout.rs`** — `CancelToken` (atomic cancellation threaded through Buchberger).
- **`smt2.rs`** — QF_FF SMT-LIB v2 parser. `parse(&str) -> Result<ConstraintSystem, ParseError>` handles the conjunctive subset (`=`, `not =`); `parse_boolean(&str) -> Result<BooleanQuery, ParseError>` additionally accepts `and`, `or`, `not`, `=>`, and assertion-level `ite`.
- **`bin/run_smt2.rs`** — Standalone CLI: reads a QF_FF SMT2 file, solves it, prints verdict (and optional timing).

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
  │              ▼                 ├── Cvc5NiaBackend
  │         known_set              └── NativeFfBackend (picus-solver)
  │              └────────┬────────────────┘
  │                       ▼
  └──────────────► DpvlResult { Safe | Unsafe(model) | Unknown }
```

The propagation and solving paths operate on different representations:
- **Propagation** uses the RCmds AST (with AB0/normalize/SubP optimizations) because the lemmas need pattern matching on expression structure.
- **Solving** uses the `UniquenessQuery` IR (built directly from R1CS binary) because the solver backends need type-safe term construction via their respective Rust APIs.
