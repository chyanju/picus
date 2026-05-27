# Architecture

Picus is organized as a Cargo workspace. Each layer depends only on
the one below it.

```
          ┌─────────────┐
          │  picus-cli  │   CLI entry point (clap subcommands)
          └──────┬──────┘
          ┌──────▼──────┐
          │    picus    │   Public library API (facade crate)
          └──────┬──────┘
        ┌────────┴────────┐
┌───────▼──────┐   ┌──────▼──────┐
│picus-analysis│   │  picus-smt  │   PolyIR + R1CS lowering + solver backends
│ DPVL, lemmas │   └──────┬──────┘
└───────┬──────┘          │
        │          ┌──────▼──────┐
        │          │ picus-solver│   QF_FF GB / CDCL(T) engine
        │          └──────┬──────┘
        └────────┬────────┘
          ┌───────▼──────┐   ┌─────────────┐
          │  picus-core  │   │  picus-r1cs │   Binary R1CS parser
          │ GF(p) algebra│   └─────────────┘
          │ poly·config· │
          │ cancel·prof  │
          └──────────────┘

┌──────────────┐   ┌────────────┐
│  cvc5-ff-sys │   │  cvc5-ff   │   Local fork of cvc5 Rust bindings.
│  (C FFI)     │◄──│  (safe API)│   Auto-compiles cvc5 with CoCoA from source
└──────────────┘   └────────────┘
```

`picus-core` holds the shared GF(p) algebra (`Poly` / `FfPolyRing`, field,
dense/sparse polynomials and reduction), the runtime config, the cancellation
token, and the profiler. `picus-solver` builds the GB / CDCL(T) engine on it;
`picus-smt` depends on both (`PolyIR` is built on `picus_core::poly::Poly`, and
the `native_ff` backend drives `picus-solver`). `picus-analysis` depends on
`picus-core` (its lemmas pattern-match against `Poly`) and `picus-smt`, not on
the solver engine.

## Crates

### `picus-r1cs`

Binary-file parser. No internal Picus dependencies.

- **`grammar.rs`** — `R1csFile`, `HeaderSection`, `ConstraintSection`,
  `Constraint`, `ConstraintBlock`, `W2lSection`. Header carries the
  field prime; constraints store sparse `(wire_id, factor)` pairs for
  the A / B / C sides.
- **`parser.rs`** — Reads the
  [iden3 R1CS binary format](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md):
  magic, header, constraint blocks, wire-to-label section. Factors
  are reduced modulo the prime carried by the header (no hard-coded
  curve).
- **`lib.rs`** — `bn128_prime()` constant and `field_reduce(x, &p)`
  convenience helper. `parse_var_index("x5")` / `"y3"` for callers
  that need to sort a witness map by wire index.

### `picus-core`

Shared substrate every other crate builds on: the GF(p) algebra plus the
runtime config, cancellation token, and profiler. No internal Picus
dependencies.

- **`config.rs`** — `RuntimeConfig`, the engine-layer knobs (`gb_strategy`,
  `use_f4`, `dnf_cap`, `dnf_enabled`, `cdclt_iter_cap`, `gb_stats_enabled`,
  `gb_trace_enabled`, `profile_enabled`, `cache_enabled`,
  `aboz_emit_disjunctions`, `poly_repr`), plus `ReprKind` and `GbStrategy`.
  Thread-local storage with `ConfigGuard` for RAII overrides; the
  `picus::check_r1cs` driver installs the resolved engine config per call.
  `EngineOverlay` is the all-optional partial used for config layering.
- **`poly.rs`** — `FfPolyRing` (multivariate polynomial ring over
  `PrimeField`), `Poly` / `Mono` aliases, `PolyRingFacade` (`terms`,
  `exponent_at`, `appearing_indeterminates`, owned-`Poly` `add` / `sub` /
  `mul`). `Poly` is the runtime dense/sparse `ff::Polynomial` enum, selected by
  `ReprKind` (`PolyRing::repr`).
- **`ff/`** — GF(p) algebra: `field` (`PrimeField` / `FieldElem`, dispatching
  between a `u64`/`u128` small-prime backend and a `rug::Integer` GMP backend
  by `bits(prime)`), `monomial`, `polynomial` (`DensePoly` + the dense/sparse
  `Polynomial` enum + `PolyRing`), `sparse_monomial` / `sparse_polynomial` /
  `sparse_geobucket`, `repr` (the `MonomialRepr` / `PolyRepr` interface),
  `divmask`, `geobucket`. The Gröbner-basis and root-finding engines that
  consume these live in `picus-solver`.
- **`timeout.rs`** — `CancelToken` (atomic cancellation threaded through the
  engine). `CancelToken::either(a, b)` fires when either source fires.
- **`profile.rs`** — Per-site wall-clock profiler (`ScopedTimer`,
  `dump_to_stderr`) plus the `SPLIT_DFS` / `SPLIT_GB` / `NATIVE_FF` counters.

### `picus-solver`

The QF_FF solving engine built on `picus-core`. Modules are grouped into
`gb/` (Gröbner-basis computation, ideals, models, root finding,
homogenisation, tracing), `frontend/` (encoding and IO: `encoder`, `parse`,
`rewriter`, `bitprop`, `bench_fixtures`), `sat/` + `cdclt/` (the SAT and
CDCL(T) layers), `ff/` (the GB / root-finding engine over the `picus-core`
algebra), `smt2/`, and `split_gb/`, with `core.rs`, `boolean.rs`, and
`incremental_context.rs` at the root.
- **`ideal.rs`** — `Ideal` + `compute_gb_with_order`
  (`_traced`, `_incremental`) + `interreduce_basis`. Every public
  GB entry point routes through `compute_gb_dispatch`, which reads
  `config::with(|c| c.gb_strategy)` and forwards to the configured
  `GbAlgorithm` impl. The trait signature is:

  ```rust
  pub trait GbAlgorithm {
      fn name(&self) -> &'static str;
      fn compute(&self, pr, gens, cancel, order)
          -> Result<Vec<Poly>, EngineError>;
      fn supports_tracing(&self) -> bool { false }
      fn compute_traced(&self, pr, gens, cancel, order, tracer)
          -> Result<Vec<Poly>, EngineError> { /* default panics */ }
  }
  ```

  Built-in impls: `BuchbergerDirect` (always; supports tracing) and
  `BuchbergerByHomog` (only meaningful for DegRevLex; tracing not
  supported, so dispatch falls back to `BuchbergerDirect` for
  traced requests). `last_dispatched_algorithm()` exposes the most
  recent algorithm name selected on the current thread — used by
  tests to confirm strategy dispatch actually fires.

  `compute_gb_buchberger(_traced)` is the raw entry point that
  bypasses dispatch; algorithm implementations call it directly to
  avoid recursive dispatch (e.g. `BuchbergerByHomog` lowers its
  inner DegRevLex computation through this entry).
- **`core.rs`** — `solve_split_gb`, `solve_single_gb`, `SolveOutcome`.
  The top-level QF_FF solving entry point used by the `native_ff` backend.
- **`split_gb/`** — Split GB algorithm with inter-basis propagation
  (OKTB23). `split_gb_cancel_traced` carries per-polynomial
  dependency sets through the fixpoint so whole-ring detection
  reports a sound (conservative over-approximation) UNSAT core.
- **`gb.rs`** — Single GB solver (DegRevLex → Lex) with cooperative
  timeout.
- **`gb_homog.rs`** + **`homog_ring.rs`** — Homogenisation extension
  ring + GB-by-homogenisation driver. Used by
  `BuchbergerByHomog::compute`.
- **`tracer.rs`** — UNSAT core tracing via `BuchbergerObserver`
  hooks. Builds a dependency DAG to identify the input subset
  responsible for unsatisfiability.
- **`encoder.rs`** — `ConstraintSystem` → polynomial encoding. Runs
  `rewriter::rewrite_system` then `auto_extract_bitsums` before
  `encode_impl`; bitsum-defining polynomials route into
  `bitsum_polys` (basis 0 only).
- **`rewriter.rs`** — Flat term-list canonicalisation: sort vars
  within each term, sort terms by vars, merge like terms mod prime,
  drop zero-coefficient terms, drop `0 = 0` equalities. Mirrors
  cvc5's `theory_ff_rewriter`.
- **`boolean.rs`** — `Formula` AST over `Eq` / `Neq` literals plus
  `And` / `Or` / `Not` / `True` / `False`. `nnf` + `to_dnf` produce a
  DNF; `BooleanQuery::from_formula` runs `rewrite_disjunctive_bit`
  then NNF/DNF. `solve_boolean_query` dispatches to
  `cdclt::solve_formula`; `RuntimeConfig::dnf_enabled` selects
  `solve_boolean_query_dnf`, which routes each DNF disjunct through
  `solve_encoded_with_cancel`. `rewrite_disjunctive_bit` matches
  cvc5's `preprocessing/passes/ff_disjunctive_bit.cpp`
  (`(or (= x 0) (= x 1))` → `x*x = x`).
- **`sat/`** — In-tree CDCL Boolean SAT solver. `lit` (Var / Lit /
  LBool), `clause` (Clause / ClauseArena), `solver` (Solver).
  Watched-literal unit propagation, 1-UIP conflict analysis with
  VSIDS variable activity, phase saving, Luby restart, max-heap
  variable order; theory integration via `add_theory_lemma_with_trail`
  (sorts by descending level, backtracks to the conflict's second-highest
  level, enqueues the asserting literal, returns the post-backtrack trail
  length) and `enqueue_theory`
  (theory-propagated literal with a learnt reason clause
  `(lit ∨ ¬r_i …)`).
- **`cdclt/`** — CDCL(T) orchestration. `atoms` (canonical FF atom
  interning with sign-flip canonicalisation so `(= a b)` and
  `(= b a)` share one SAT var, plus at-most-one mutex clauses
  across single-variable equalities), `cnf` (Tseitin transformation),
  `theory` (plug-in trait), `ff_theory` (concrete plug-in: full-
  effort GB via `solve_encoded_with_cancel`; two-tier theory
  propagation — Tier 1 evaluates atoms under pinned variables, Tier
  2 reduces multi-variable trail atoms to `a·v + c = 0` and
  propagates against registered single-var equalities, with Fermat-
  based modular inverse), `orchestrator` (`solve_formula` interleaves
  SAT propagation, theory notification, theory propagation, full-
  effort theory check, and theory-conflict learning). Layered after
  cvc5's `theory_ff.{h,cpp}` + `sub_theory.{h,cpp}`.
- **`model.rs`** — Model construction via iterative ideal
  augmentation (univariate roots, minimal polynomial, round-robin).
- **`bitprop.rs`** — Bit propagation (constant + equal bitsum)
  across split bases.
- **`parse.rs`** — Pattern detection
  (`bit_constraint`, `linear_monomial`, `bit_sums`).
- **`incremental.rs`** + **`incremental_context.rs`** — Push/pop API
  + `IncrementalSolverContext` (split-GB cache keyed on the
  constraint side; resumable mid-build state).
- **`gb/roots.rs`** — Univariate root finding (Cantor-Zassenhaus, see
  `ff/univariate.rs`).
- **`smt2/`** — QF_FF SMT-LIB v2 parser
  (`smt2/{mod, tokenizer, session, tests}.rs`).
  `parse(&str) -> Result<ConstraintSystem, ParseError>` handles the
  conjunctive subset (`=`, `not =`);
  `parse_boolean(&str) -> Result<BooleanQuery, ParseError>` accepts
  `and`, `or`, `not`, `=>`, and assertion-level `ite`. `SmtSession`
  drives the full SMT-LIB v2 incremental loop.
- **`bench_fixtures.rs`** — SMT-LIB QF_FF source builders for the
  bench corpus (`conjunction`, `single_or`, `disj_bit`,
  `and_of_ors_{sat,unsat}`, `implies_chain_unsat`, `bit_sum`,
  `random_3cnf`, `or_of_ands`). `corpus()` returns the full
  `(family, label, source)` list shared by `cdclt_bench` and
  `cvc5_compare`.
- **`bin/run_smt2.rs`** — Standalone CLI: reads a QF_FF SMT2 file,
  solves it, prints verdict (and optional timing).
- **`bin/cvc5_compare.rs`** — Standalone CLI: runs every
  `bench_fixtures::corpus` entry through `cdclt::solve_formula` and
  through an external cvc5 process (`--ff-solver split`); prints a
  side-by-side wall-time table. Flags: `--cvc5 <path>`,
  `--timeout-ms <N>`, `--iters <K>`.
- **`ff/`** — Gröbner-basis / root-finding engine over the `picus-core`
  algebra: `buchberger/` (Buchberger with the GM-criterion incremental path
  and S-pair criteria), `f4/` (matrix layer, workspace, symbolic
  preprocessing), `sparse_gb` (Buchberger on the sparse representation with the
  same product / M / B criteria, sugar selection, and incremental seeding),
  `hilbert`, `spair`, `univariate` (Cantor-Zassenhaus), and `repr_oracle`
  (cross-checks the sparse GB against the dense engine).

### `picus-smt`

R1CS-to-PolyIR lowering and solver-backend trait.

- **`poly_ir.rs`** — `PolyIR` bundles a polynomial ring over GF(p)
  with the constraint system extracted from a uniqueness query: a
  flat `Vec<Poly>` of equality constraints, an optional disjunction
  list, R1CS-specific metadata (`input_indices`, `known_signals`,
  `target_signal`), and the four general-purpose GB-query fields
  (`disequalities`, `assignments`, `bitsums`, `add_field_polys`)
  that let the encoder lower a `PolyIR` to an `EncodedSystem`
  without a separate `ConstraintSystem` intermediate.

  `PolyIR::to_indexed_constraint_system` and `PolyIR::encode` give
  callers a one-call path to the encoder; the `native_ff` backend's
  stateless path goes through `ir.encode()` directly.

  Variable layout: for an R1CS with `n_wires` wires, the ring carries
  `2 * n_wires` variables. Variable index `i` (for `i < n_wires`) is
  the original copy `x_i`; index `n_wires + i` is the alt copy
  `y_i`. Input wires share their value across copies — the lowering
  emits `x_i` (not `y_i`) for input-wire alt-copy references, so no
  explicit `x_i - y_i = 0` equality is needed for inputs. Wire 0
  folds straight into a constant during lowering (so `c * x_0`
  never appears as a distinct linear monomial); `x_0 = 1` is
  surfaced as one explicit equality.

  `r1cs_to_poly_ir(r1cs, &known, target) -> Result<PolyIR, LowerError>`
  performs the lowering in a single pass over the R1CS constraint
  blocks: each `A * B = C` becomes one polynomial equality
  `(expand(A))(expand(B)) - expand(C) = 0`. The prime comes from
  `r1cs.header.prime_number` (no hard-coded curve). An out-of-bounds
  wire id in any constraint block surfaces as
  `LowerError::WireOutOfBounds` rather than a silent skip.

  `PolyIR::add_known_wire(w)` appends `x_w - y_w = 0` so the next
  backend call sees newly-verified wires as constraints;
  `PolyIR::set_target(w)` selects the disequality target.
  `PolyIR::var_to_wire(idx)` maps a ring variable index back to its
  underlying wire (both `x_i` and `y_i` indices return wire `i`).
  `PolyIR::poly_terms(poly)` yields each monomial as
  `(coeff, Vec<String>)` (one name per degree); the sibling
  `PolyIR::poly_terms_idx(poly)` yields `(coeff, Vec<(var_idx, exp)>)`
  for callers that don't need names.
- **`backends/`** — Solver-backend implementations, each consuming
  `&PolyIR`:
  - **`z3_nia.rs`** — z3 Rust API, QF_NIA (integer arithmetic with
    `rem p`). Gated by the `z3` Cargo feature.
  - **`cvc5_ff.rs`** — cvc5 Rust API, QF_FF (native finite field).
    Gated by the `cvc5` Cargo feature.
  - **`cvc5_nia.rs`** — cvc5 Rust API, QF_NIA (`mod p`). Gated by
    the `cvc5` Cargo feature.
  - **`native_ff.rs`** — Pure-Rust QF_FF via `picus-solver`. Always
    available. The encoder's `add_field_polys` flag is enabled for
    primes ≤ 1000 (essential for sound GB reasoning over small
    primes; prohibitive for cryptographic primes). The
    `IncrementalSolverContext` cache is enabled by default;
    `RuntimeConfig::cache_enabled = false` (`--no-cache` on the
    CLI, or `cache_enabled = false` in config) opts out.
  - `mod.rs` defines the `SolverBackend` trait
    (`solve(&PolyIR, timeout_ms, &CancelToken)` + `dump_smt(&PolyIR)`),
    the `SolverResult { Unsat, Sat(model), Unknown(UnknownReason) }`
    return type with `UnknownReason { Timeout, IncompleteTheory,
    BackendError(String) }`, the shared `poly_to_smtlib_nia` /
    `poly_to_smtlib_ff` text emitters, and the
    `SolverBackendDescriptor { name, theory, factory }` inventory
    registry that `create_backend_by_name` walks at dispatch time.
- **`lib.rs`** — `SolverKind` / `Theory` enums,
  `validate_combination`, `create_backend`. Dispatch goes through
  the inventory of `SolverBackendDescriptor`s: built-in `SolverKind`
  variants are ergonomic aliases that match the descriptor's `name`
  field. A new backend registers via an `inventory::submit!` block and
  is then reachable through `create_backend_by_name`; selection by name
  (`--solver`, config) additionally needs a matching `SolverKind`
  variant, since `SolverKind::from_str` resolves the built-in names.
  `SUBP_CONSTANT_NAMES` lists the
  named field constants that the `picus` witness post-processor
  filters out of solver-produced models.

#### Cargo features

`picus-smt` exposes three features, propagated through `picus` and
`picus-cli`:

| Feature | Effect |
|---|---|
| `native` (default) | In-tree pure-Rust FF solver; no external build chain |
| `cvc5` (opt-in) | Enable `cvc5_ff` and `cvc5_nia` backends; build cvc5 from source via `cvc5-ff-sys` |
| `z3` (opt-in) | Enable `z3_nia` backend; build z3 from source via the vendored `z3-sys` |

The default build is `native` only. `cvc5` / `z3` are opt-in
(`--features cvc5` / `z3`) and pull their vendored build chains; the workspace
`default-members` also excludes the cvc5 / z3 crates, so no default command
compiles them.

### `picus-analysis`

DPVL algorithm + propagation lemma plugins.

- **`dpvl.rs`** — The DPVL outer loop. Lowers `R1csFile` → `PolyIR`
  once, instantiates the lemma plugins selected by `LemmaSet`, and
  iterates:
  1. Propagation: each registered `PropagationLemma` runs once
     per outer iteration; `ctx.learned` polynomials are folded
     into `ir.equalities` between iterations.
  2. Verification check: if every target wire is in `known`, return
     `Safe`.
  3. Solver dispatch: the selector picks an unknown wire, the
     backend tries `solve(&ir, timeout_ms)` after
     `ir.set_target(sid)`. UNSAT ⇒ verified (append to known,
     `ir.add_known_wire(sid)`); SAT on a target ⇒ `Unsafe(model)`.

  `LemmaSet` is a `HashSet<String>` of enabled names; the CLI
  `--lemmas all` / `all-X` / `none+X` syntax resolves names against
  the live `inventory` registry.
- **`propagation/`** — Five propagation lemmas plus the plugin
  infrastructure. See [Propagation Lemmas](./lemmas.md).
- **`selector.rs`** — `SelectorKind` (`First` / `Counter`) +
  `SelectorState`. The counter strategy consumes a
  `wire_connectivity_score(&PolyIR)` map built once by the DPVL
  driver: wires that participate in more constraints score higher.

### `picus`

Public library facade.

- **`check_circuit(path, config)`** — Read an R1CS file and run the
  full analysis pipeline.
- **`check_r1cs_bytes(data, config)`** — Analyse from raw bytes.
- **`check_r1cs(r1cs, config)`** — Analyse a pre-parsed `R1csFile`.
- **`PicusConfig { analysis, engine }`** (aliased `Config`) — the resolved
  configuration. `analysis` (`AnalysisConfig`: `solver = Native`,
  `theory = Ff`, `timeout_ms = 5000`, `lemmas = all`, `selector = Counter`,
  `dump_smt = None`) plus `engine` (`EngineConfig` = `RuntimeConfig`:
  `gb_strategy = Direct`, `poly_repr = Sparse`, `cache_enabled = true`,
  `aboz_emit_disjunctions = true`, the caps at `100_000` / `1_000_000`, and
  the remaining toggles off). `default()` is zero-I/O.
- **`resolve_config(path, cli_overlay)`** — layers, in increasing
  precedence, built-in defaults < config file (`--config`, else
  `./picus.toml`) < CLI overlay, into one `PicusConfig`.
  `PicusConfig::from_file` is a library shortcut.
- **`CheckResult`** — `Safe`, `Unsafe { witness_1, witness_2 }`,
  or `Unknown`.
- **`dump_profile(tag)`** / **`dump_gb_stats()`** — facade for the
  `picus_core::profile` dump helpers, used by `picus-cli`.

### `picus-cli`

Thin CLI entry point:

- **`picus check`** — Runs DPVL on an R1CS file and prints `safe`,
  `unsafe` (with counter-example), or `unknown`. `--config <FILE>` loads a
  TOML config (else `./picus.toml` when present); the flags (`--solver`,
  `--timeout`, `--profile wall`, `--gb-by-homog`, `--poly-repr`, `--use-f4`,
  `--dnf`, `--gb-stats`, `--gb-trace`, `--no-cache`, `--no-aboz-disj`, …)
  form the highest-precedence overlay over the file and the built-in
  defaults (`picus::resolve_config`). Depends only on `picus`; does not
  import `picus_solver::*`.
- **`picus info`** — Prints R1CS metadata and optionally all
  constraints in human-readable form.

## Data Flow

```
Circom source (.circom)
  │  circom --r1cs --sym --O0
  ▼
R1CS binary (.r1cs)
  │  picus-r1cs::parser
  ▼
R1csFile struct
  │  picus-smt::poly_ir::r1cs_to_poly_ir
  ▼
PolyIR  (polynomial ring + Vec<Poly> equalities)
  │
  ├──► propagation lemmas (inventory registry, read-only IR + mutable ctx)
  │       │  ctx.known / ctx.unknown / ctx.ranges / ctx.learned
  │       ▼
  │     known_set grows; ctx.learned folded into ir.equalities
  │       │
  └──► SolverBackend::solve(&PolyIR, timeout, &CancelToken)
          ├── Z3NiaBackend       (QF_NIA, rem p)      [`z3` feature]
          ├── Cvc5FfBackend      (QF_FF, native FF)   [`cvc5` feature]
          ├── Cvc5NiaBackend     (QF_NIA, mod p)      [`cvc5` feature]
          └── NativeFfBackend    (in-tree GB engine via picus-solver)
                  │
                  ▼
        DpvlResult { Safe | Unsafe(model) | Unknown }
```

Propagation and solving consume the same `PolyIR`. Lemmas
pattern-match on polynomial structure via `appearing_indeterminates`
and `poly_terms` / `poly_terms_idx`; SMT backends translate each
`Poly` into their solver-native term tree via `poly_to_smtlib_ff` /
`poly_to_smtlib_nia`, and the `native_ff` backend lowers each `Poly`
into `picus_solver::frontend::encoder::ConstraintSystem` for the in-tree GB
engine.
