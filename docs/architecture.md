# Architecture

Picus is organized as a Cargo workspace with four crates. Data flows top-to-bottom through the pipeline; each layer depends only on the one below it.

```
┌─────────────┐
│  picus-cli  │   CLI entry point (clap subcommands)
└──────┬──────┘
       │
┌──────▼──────┐
│picus-analysis│  DPVL algorithm, propagation lemmas, selectors
└──────┬──────┘
       │
┌──────▼──────┐
│  picus-smt  │   R1CS→AST conversion, SMT-LIB generation, solver invocation
└──────┬──────┘
       │
┌──────▼──────┐
│  picus-r1cs │   Binary R1CS parser, AST types, .sym parser, preconditions
└─────────────┘
```

## Crates

### `picus-r1cs`

Foundation layer. No external Picus dependencies.

- **`grammar.rs`** — AST type definitions (`RCmd`, `RExpr`) used throughout the pipeline, plus variable extraction utilities (linear vs. nonlinear classification).
- **`parser.rs`** — Reads the [iden3 R1CS binary format](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md): magic number, header section (field size, wire/constraint counts), constraint section (sparse A·B=C triples), wire-to-label section.
- **`sym.rs`** — Parses Circom `.sym` CSV files to map signal indices to qualified names and scope information.
- **`precondition.rs`** — Reads JSON precondition files that seed the known-set or inject extra constraints.

### `picus-smt`

Translates R1CS constraints into SMT-LIB queries and manages solver interaction.

- **`r1cs_parser.rs`** — Converts binary R1CS constraints into the AST in standard form (A·B = C) and then into expanded form (cross-product of terms). Two variants: z3/cvc4 (QF_NIA with `mod p`) and cvc5 (QF_FF finite field).
- **`optimizer.rs`** — Three AST-to-AST transformation passes:
  - **Phase 0 (ab0):** A·B=0 → A=0 ∨ B=0 (z3/cvc4 only; disabled for cvc5 due to a solver bug with `or` in QF_FF)
  - **Normalize (simple):** strip `*1`, `+0`, replace `x0` with `1`
  - **Phase 1 (subp):** substitute field-prime-related constants (`p`, `p-1`, ..., `p-5`)
- **`interpreter.rs`** — Serializes AST to SMT-LIB2 strings. Three backends: z3 (`rem` for mod, integer arithmetic), cvc4 (`mod`), cvc5 (`ff.add`/`ff.mul`, `#f<v>m<p>` literals).
- **`solver.rs`** — Writes SMT-LIB to a temp file, spawns the solver as a subprocess with timeout, reads stdout/stderr in separate threads (avoids pipe deadlock), parses `sat`/`unsat`/`unknown` results and extracts models. Set `PICUS_DUMP_SMT=<path>` to save the last SMT query for debugging.

### `picus-analysis`

Core verification algorithms.

- **`dpvl.rs`** — The DPVL (Decide & Propagate Verification Loop). Uses a `DpvlContext` struct to hold all state:
  1. Parse original + alternative (two-copy) constraint systems
  2. Run optimization pipeline on both copies; pre-serialize SMT prefix
  3. Loop (non-recursive): propagate → check → select → solve → repeat
- **`propagation/`** — Six lemmas that cheaply deduce signal uniqueness without the solver. Lemmas handle both numeric (`Int`) and named (`Var("ps1")`) constants from the SubP optimizer. See [Propagation Lemmas](./propagation-lemmas.md).
- **`selector.rs`** — Signal selection heuristics: `first` (trivial) and `counter` (frequency-weighted with negative feedback on timeouts).
- **`constraint_graph.rs`** — Builds an undirected graph (via `petgraph`) where nodes are signals and edges connect signals that share a constraint. Used for scoped counterexample generation.
- **`cex.rs`** — Counterexample generation (stub for scope-by-scope compositional solving).

### `picus-cli`

Thin entry point. Two subcommands:

- **`picus check`** — Runs DPVL on an R1CS file and prints `safe`, `unsafe` (with counter-example), or `unknown`.
- **`picus info`** — Prints R1CS metadata and optionally all constraints in human-readable form.

## Data Flow

```
Circom source (.circom)
  │  circom --r1cs --sym --O0
  ▼
R1CS binary (.r1cs) + Symbol map (.sym)
  │  picus-r1cs::parser::read_r1cs_file
  ▼
R1csFile { header, constraints, w2l, inputs, outputs }
  │  picus-smt::r1cs_parser::parse_r1cs  (× 2: original + alt)
  ▼
RCmds (AST in standard form: A·B = C)
  │  optimize_p0 → expand → normalize → optimize_p1
  ▼
RCmds (optimized, expanded AST)
  │  picus-analysis::dpvl::run_dpvl
  │    ├── propagate (L0–L4 lemmas, fixed-point)
  │    ├── select (counter heuristic)
  │    └── solve (two-copy query → SMT solver)
  ▼
DpvlResult { Safe | Unsafe(model) | Unknown }
```
