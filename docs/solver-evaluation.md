# picus-solver

A pure-Rust QF_FF (quantifier-free finite field) solver. Used as the
`--solver native --theory ff` backend in Picus.

## 1. Scope

`picus-solver` operates at the polynomial constraint level. Input is a
`ConstraintSystem` over `GF(p)`; output is `Sat { model }`, `Unsat`, or
`Unknown`.

The following are **not** in scope and must be handled by a caller:

- Boolean connectives (`or`, `not`, `=>`, `ite`)
- Uninterpreted functions
- Theory combination

## 2. Module layout

```
src/
├── core.rs                # Top-level API: solve_split_gb, solve_single_gb, SolveOutcome
├── encoder.rs             # ConstraintSystem → Polynomial encoding
├── split_gb.rs            # Split-GB algorithm: model search + DFS branching
├── gb.rs                  # Single-GB solver (DegRevLex → Lex)
├── ideal.rs               # Ideal: GB computation, membership, reduce, zero-dim check
├── model.rs               # Model construction (univariate roots, minpoly, round-robin)
├── bitprop.rs             # Bit propagation (constant + equal bitsum)
├── parse.rs               # Pattern detection (bit_constraint, linear_monomial, bit_sums)
├── roots.rs               # Univariate root finding (Cantor-Zassenhaus driver)
├── incremental.rs         # Push/pop fact-stack API
├── incremental_context.rs # Cross-call constraint-system + GB cache
├── tracer.rs              # UNSAT core via Buchberger observer
├── timeout.rs             # CancelToken (atomic cancellation)
├── homog.rs, gb_homog.rs  # Homogenize → GB → dehomogenize pipeline (optional)
├── poly.rs, field.rs      # Helper types
└── ff/                    # In-tree Groebner basis engine
    ├── field.rs           # GF(p) arithmetic (rug/GMP), thread-local FieldElem pool
    ├── monomial.rs        # Packed-exponent monomials, divisibility, orderings
    ├── divmask.rs         # 128-bit divisibility mask
    ├── polynomial.rs      # Sparse polynomial, reduce_by_refs_geobucket
    ├── geobucket.rs       # Geometric-bucket accumulator
    ├── buchberger.rs      # BuchbergerState, IncrementalGB
    ├── spair.rs           # S-pair representation
    ├── f4.rs              # Opt-in F4-lite (degree-batched matrix reduction)
    └── univariate.rs      # Univariate polynomial arithmetic, Cantor-Zassenhaus
```

## 3. Public API

| Entry point | Signature | Purpose |
|-------------|-----------|---------|
| `core::solve_split_gb` | `(cs, opts, cancel) -> SolveOutcome` | Split-GB driver with model search |
| `core::solve_single_gb` | `(cs, opts, cancel) -> SolveOutcome` | Single-GB (DegRevLex → Lex → findZero) |
| `core::solve_encoded_with_cancel` | `(encoded, cs, opts, cancel) -> SolveOutcome` | Reuse a pre-encoded constraint system |
| `incremental_context::IncrementalSolverContext` | — | State cache keyed by constraint-side digest |
| `encoder::encode` | `(cs) -> EncodedSystem` | `ConstraintSystem` → polynomial form |
| `ideal::Ideal::compute_gb` | `(generators, ring, cancel) -> Ideal` | Reduced Groebner basis |
| `ideal::Ideal::extend_with_cancel` | `(extra_gens, cancel) -> Ideal` | Add generators and re-run Buchberger |

`SolveOutcome` is three-valued:

- `Sat { model }` — concrete satisfying assignment
- `Unsat` — proven infeasible
- `Unknown` — search bounded out (cancel token fired, or branching budget
  exhausted). Callers may retry with a larger budget.

## 4. Configuration

Compile-time: the `ff` engine has no Cargo features that change behavior.

Runtime environment variables:

| Variable | Default | Effect |
|----------|---------|--------|
| `PICUS_NO_INCREMENTAL_CACHE` | unset | Disables `IncrementalSolverContext` |
| `PICUS_USE_F4` | unset | Routes `BuchbergerState::run` to F4-lite |
| `PICUS_GB_STATS` | unset | Prints per-phase reducer timers + driver counters |
| `PICUS_GB_TRACE` | unset | Per-iteration trace |

## 5. Algorithmic notes

### Groebner basis engine

- Coefficients: `rug::Integer` (GMP `mpz_t`) with a thread-local pool that
  recycles buffers across operations.
- Monomials: packed exponent vector; divisibility filter via 128-bit
  `DivMask`.
- Reduction: geometric-bucket accumulator (`geobucket.rs`) for the cascade
  of polynomial additions during division.
- S-pair criteria: Gebauer-Möller M-criterion at generation time, companion
  B-criterion at basis-add time.
- Pair selection: sugar order.
- Divisor lookup: linear scan below the bucket-index threshold (256
  divisors); hash-bucketed index keyed on `DivMask` bits above it.

### Split-GB

`split_gb.rs` partitions the input by bitprop-detectable structure (bit
variables, linear monomials, bitsums) into separate bases that share
propagation results across iterations. Each iteration:

1. Compute / extend the GB of each partition.
2. Run bit-propagation; propagate new equalities back into the partitions.
3. Memoize `contains`-results across iterations (key: `(content_hash(p),
   basis_idx)`).
4. Repeat until quiescent or until a fixpoint cap is reached.

Search inside a partition uses DFS branching with:

- Phase saving (the last popped value is reordered to the front of the
  next branch's root list for the same variable).
- A nogood cache (infeasible partial assignments; supersets are
  short-circuited).
- A linear-only quick UNSAT pre-check that reduces the candidate against
  the linear basis directly (Buchberger ≡ Gauss-Jordan in this case).
- Iterative (explicit-stack) recursion to avoid stack overflow on deep
  search trees.

### Incremental Buchberger

`Ideal::extend_with_cancel` adds new generators to an already-reduced GB
and re-runs Buchberger from the extended state. The result equals a full
recomputation on the union of generators.

`IncrementalGB` (in `ff/buchberger.rs`) exposes `run_only` and
`set_cancel_token` so that a cancelled Buchberger run can be resumed across
calls with a fresh cancel budget.

### Incremental solver context

`IncrementalSolverContext` caches the encoded constraint side and computed
split-GB across `solve_encoded` calls within a backend session. The cache
key is a digest of the constraint side excluding per-query disequalities.

- Lazy: the cache is only built after two consecutive same-digest calls.
- On hit: the per-query Rabinowitsch disequality polynomial is encoded in
  the cached ring and added via `extend_with_cancel`.
- On mid-build cancellation: partial state is preserved and resumed by a
  subsequent matching-digest call.

### F4-lite (opt-in)

`ff/f4.rs` implements sugar-batched S-pair processing:

1. Collect all S-pairs of the current minimum sugar degree.
2. Symbolic preprocessing: BFS closure under reducibility, adding `(m /
   lt(b)) · b` reducer rows for every monomial divisible by some active
   basis LT.
3. Sparse matrix construction with a monomial-DESC column index.
4. Sparse row-echelon over GF(p); reducer rows pivoted first.
5. Extract new generators from S-poly residues whose LT column is not a
   reducer LT.

Falls back to direct geobucket reduction for batches of size 1. Disabled
by default; enable with `PICUS_USE_F4=1`.

### UNSAT core tracing

`tracer.rs` wires `BuchbergerObserver` callbacks (`on_initial_basis`,
`on_new_poly`, `on_inter_reduce`) into the in-tree engine and builds a
polynomial dependency DAG. From the DAG it extracts the subset of input
indices responsible for producing the trivial element.

- Single-GB mode: dependency-DAG core. Conservative on initial
  inter-reduction (each survivor is marked as depending on all inputs).
  Reduction-step-level dependency tracking is not implemented.
- Split-GB mode: trivial (all-input) core only.

## 6. Test layout

| Test file | Count | Source |
|-----------|-------|--------|
| `lib.rs` unit tests | 48 | Internals (field, poly, ideal, parse, bitprop, split_gb, core, incremental, timeout, stats, tracer, roots) |
| `tests/cvc5_regression.rs` | 9 | Direct ports of cvc5 `regress0/ff/*.smt2` |
| `tests/cvc5_extended.rs` | 14 | Additional cvc5 regression ports |
| `tests/cvc5_unit_uni_roots.rs` | 5 | Univariate root tests |
| `tests/cvc5_unit_multi_roots.rs` | 15 | Multi-root model search tests |
| `tests/cvc5_unit_split_gb.rs` | 4 | Split-GB property tests (randomized) |
| `tests/cvc5_unit_parse.rs` | 11 | Pattern detection tests |
| `tests/integration.rs` | 6 | End-to-end |
| `tests/timeout.rs` | 7 | Cooperative timeout |

Every cross-checked test produces the same SAT/UNSAT verdict as cvc5. For
SAT outcomes the returned model is verified against the input constraints.

## 7. Running benchmarks

```bash
# Unit + integration tests
cargo test -p picus-solver --release

# Criterion benchmarks
cargo bench -p picus-solver --bench solver_bench

# cvc5 side-by-side comparison (requires cvc5 with --cocoa --gpl)
cd crates/picus-solver/benches
./benchmark_cvc5.sh 50
```

## 8. Known limitations

- **UNSAT core (split-GB)**: trivial (all-input) only.
- **`Or` constraints in `NativeFfBackend`**: encoded as conjunctions
  (unsound for disjunction).
- **Performance on dense-ideal circuits**: classical Buchberger over GMP
  is the bottleneck. F4/F5 with Macaulay-matrix reduction and
  Montgomery-form arithmetic for BN128 would address this but are not in
  the current engine.
