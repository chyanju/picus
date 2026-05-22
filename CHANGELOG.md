# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

## [1.7.29] - 2026-05-22

Documentation-only release: comment and module-doc audit across the
picus-solver crate. No behavioural or performance changes.

### Changed

- `picus-solver::ff::buchberger::BasisElement::lt_divmask`: removed
  the stale `#[allow(dead_code)] // reserved for future
  Gebauer-Möller chain criterion` attribute and comment. The field
  is read at `run_f4` (line ~1042) when constructing `F4BasisRef`;
  F4 symbolic preprocessing uses it as a constant-time prefilter.
  Replaced with a doc comment describing the current use.
- `picus-solver::sat::solver` module doc rewritten. The prior text
  ("Skeleton at this point: only declares the public types …; the
  actual CDCL loop is added in the next phase") predated the full
  CDCL implementation now present in the file. New doc describes
  BCP / 1-UIP analysis / VSIDS / Luby restarts / backjumping and
  the theory-lemma entry points.
- `picus-solver::gb_homog` module doc: attribution updated from
  "feanor's sugar-degree-driven S-pair selector" to
  "`ff::buchberger`" (the in-tree Buchberger this code has used
  since the feanor dependency was removed).
- `picus-solver::homog::HomogRing::new` doc: replaced the
  feanor-`Zn`-based soundness argument with one stated in terms of
  the current `PrimeField` dispatch.
- `picus-solver::roots` module doc tightened; "Both steps are now
  handled inside …" rewritten as a direct delegation note.
- Narrative phrasing scrubbed from comments in `bitprop.rs`,
  `ideal.rs`, `incremental_context.rs`, `poly.rs`,
  `ff/f4.rs`, `ff/field.rs`, `ff/univariate.rs`, and one
  `tests/cvc5_unit_split_gb.rs` test header. Replacements describe
  current behaviour without referencing prior implementations,
  development history, or speculative future work.

### Removed

- `picus-solver::ff::f4::sparse_sub_scaled` (the non-consuming
  `#[cfg(test)]` wrapper). No callers in tests or production; the
  hot path uses `sparse_sub_scaled_consume_a` directly. Removing
  the function also clears the only `dead_code` warning under
  `cargo build --tests --release`.

### Tests

- 339 lib tests + 1 ignored pass under both `PICUS_USE_F4=0` and
  `PICUS_USE_F4=1`. 77 integration tests + 6 cdclt_regression tests
  pass under `PICUS_USE_F4=1`. `cargo build --tests --release` is
  warning-free.

### Performance

- `cvc5_compare` 38-fixture corpus (cvc5 1.3.1 `--ff-solver split`,
  5 iters each): geomean cvc5/picus = 11.25× (within run-to-run
  variance of the 12.03× reported at v1.7.28). All 38 verdicts
  match cvc5.
- `picus check --solver native --theory ff` on the 68-circuit
  circomlib-cff5ab6 corpus (60s wall-clock cap, 5000 ms per-query
  timeout, `PICUS_USE_F4=1`): total 580.05 s vs the v1.7.27
  baseline 579.29 s (+0.13%, noise). All 69 verdicts identical to
  the prior baseline.

## [1.7.28] - 2026-05-22

### Added

- `picus-solver::ff::field::PrimeField` and `FieldElem` gain an
  internal `u64` + `u128` backend selected automatically by
  [`PrimeField::new`] when `bits(prime) <= 64`. Primes larger than
  64 bits (e.g. BN128 at 254 bits) continue through the existing
  `rug::Integer` (GMP) backend; the dispatch is per-ring and
  transparent to callers.
- u64 backend arithmetic: `add` / `sub` / `mul` (via u128
  intermediate) / `neg` / `inv` (extended-Euclidean in i128) /
  `pow` (repeated squaring on u64). No heap allocations, no
  thread-local pool traffic.
- `ff::field::tests::small_matches_gmp_axioms`: per-prime cross-
  check between the two backends on the same fixed prime. Verifies
  every operation produces `to_biguint`-equal results.
- `ff::field::tests::small_prime_dispatch_is_picked`: asserts the
  constructor routes a 64-bit prime to the u64 backend and BN128 to
  the GMP backend.

### Changed

- `picus-solver::ff::field::FieldElem` is now a struct wrapping a
  private `ElemRepr` enum (`Gmp(rug::Integer)` / `Small(u64)`). All
  existing methods on `PrimeField` dispatch through the enum.
  Drop / Clone / Hash / PartialEq are variant-aware.
- `picus-solver::ff::field::PrimeField` is now a struct wrapping a
  private `FieldKind` enum (`Gmp { prime, result_bits, product_bits }`
  / `Small { prime: u64 }`).
- `picus-solver::ff::field::FieldElem::as_integer` (previously
  `pub` returning `&rug::Integer`) removed; the only external
  caller (`ff::univariate::find_roots`) now uses `as_biguint()` for
  the root-set sort.
- `picus-solver::ff::field::PrimeField::prime_integer` (previously
  `pub(crate)` returning `&rug::Integer`) removed; no callers.

### Tests

- 339 lib tests pass under both `PICUS_USE_F4=0` and
  `PICUS_USE_F4=1` (was 337; +2 for the new cross-check tests).
  77 integration tests + 6 cdclt_regression tests pass under
  `PICUS_USE_F4=1`.

### Performance

- Median absolute timings on the small-prime micro-benchmarks
  (`bench_f4_vs_per_pair_large`, F_7919) before vs after this
  release:

  | workload | v1.7.27 pp_us | v1.7.28 pp_us | speedup |
  |---|---|---|---|
  | cyclic-4 | ~89–155 | 47–53 | ~2–3× |
  | cyclic-5 | ~3789–4231 | 1893–2127 | ~2× |
  | cyclic-6 | ~94595–103036 | 32625–34356 | ~3× |
  | dense-10/20/30 | ~52–137 | 32–82 | ~1.5–1.6× |

  Non-cyclic (`bench_f4_non_cyclic_workloads`):

  | workload | v1.7.27 pp_us | v1.7.28 pp_us | speedup |
  |---|---|---|---|
  | katsura-3 | ~208 | 124 | ~1.7× |
  | katsura-4 | ~1529 | 746 | ~2× |

- `cvc5_compare` geomean (38-fixture corpus, 5 iters each, cvc5
  1.3.1 `--ff-solver split`): cvc5/picus ratio improved from
  9.50× / 9.68× (v1.7.27) to **12.03×**. `bit_sum_n=8_t=99_unsat`
  (previously the only fixture where picus lost to cvc5): picus
  77.3 ms → 36.4 ms; cvc5/picus 0.16× → 0.30×.
- BN128 (`bench_is_zero_bn128`) total time 181 µs, unchanged
  relative to v1.7.27. The 3 match arms per field op are absorbed
  by GMP's per-op cost (~100–200 ns).

## [1.7.27] - 2026-05-22

### Added

- `picus-solver::ff::hilbert` module. Sparse `Z[t]` polynomial type
  `HilbertNum` (saturating arithmetic on `i64` coefficients) and
  `hilbert_numerator(&[Monomial]) -> HilbertNum` implementing the
  Bigatti–Caboara–Robbiano recursion
  `N(I) = N(I + (p)) + t^deg(p) · N(I : p)`. Pivot selected as the
  most-occurring variable's smallest nonzero exponent. 16 unit tests
  cover empty / unit / single / coprime / non-coprime / redundant-
  generator cases plus textbook targets `(x^2, x*y) → 1 - 2t^2 + t^3`,
  `m^2 → 1 - 3t^2 + 2t^3`, `(x*y, y*z) → 1 - 2t^2 + t^3`.
- `picus-solver::ff::buchberger::GbEngineStats` fields `f4_batches`,
  `f4_pair_total`, `f4_fallback_pairs`. Counters were previously
  local to `BuchbergerState::run_f4` and only emitted via stderr
  under `PICUS_GB_STATS=1`; moving them onto the struct lets unit
  tests assert routing decisions directly.
- `picus-solver::ff::buchberger::IncrementalGB::engine_stats() ->
  &GbEngineStats` accessor.
- Per-batch scratch buffers on `F4Workspace`: `handled_scratch`,
  `worklist_scratch`, `reducer_lts_scratch`,
  `reducer_basis_idx_scratch`, `all_monomials_scratch`,
  `monomial_sorted_scratch`, `monomial_to_col_scratch`,
  `col_to_monomial_scratch`, `reducer_cols_scratch`.
  `symbolic_preprocess` and `process_batch_with_workspace` `mem::take`
  each into a local at entry and assign it back at end-of-call;
  allocator capacity persists across consecutive batches in the same
  Buchberger run.
- `picus-solver::ff::f4::sparse_sub_scaled_consume_a`. Consume-`a`
  axpy that moves the row's `FieldElem` coefficients into the merge
  instead of cloning them. `sparse_echelon` holds a single
  `SparseRow` scratch buffer and `mem::swap`s it into / out of
  `rows[i]` per axpy.
- `picus-solver::ff::buchberger::F4_HILBERT_CHECK_MAX_BATCH = 16`
  and `F4_REDUNDANCY_LIMIT = 4.0` constants (added then removed
  same release — see "Removed").
- Four new `ff::f4::tests` cases:
  `f4_size_fallback_fires_on_small_batches` (Katsura-3 forces
  `f4_fallback_pairs > 0`), `f4_matrix_path_fires_on_cyclic_5`
  (asserts `f4_batches > 0`), `f4_large_batch_homog_5vars_deg2`
  (8-generator degree-2 ideal, asserts `f4_pair_total >= 12`),
  `f4_large_batch_cyclic_6` (`#[ignore]`, release-only, asserts
  avg batch ≥ 20 and ≥ 90% pair share through the F4 path).
- `tests/bench_perf.rs::bench_f4_non_cyclic_workloads`. Katsura-3,
  Katsura-4, and a hand-crafted diffuse 4-variable ideal. Validates
  the `F4_MIN_BATCH` threshold generalises beyond cyclic-N.
- F4 unit tests `f4_workspace_idempotent_on_repeated_batch` and
  `f4_workspace_invalidates_on_basis_deactivation` covering the
  reducer cache lifecycle.

### Changed

- `picus-solver::ff::buchberger::F4_MIN_BATCH`: `4` → `12`. The
  prior value targeted cyclic-N's small batches; on Katsura-4
  (3 batches avg 8.3) and the diffuse-4vars ideal F4 ran 2.37× /
  3.53× slower than per-pair because the matrix-build + reducer-row
  construction overhead exceeded the amortisation gain on medium
  batches. At `12` both cases recover to within 1.02× / 1.15× of
  per-pair; cyclic-6 retreats from ~1.06× to ~1.13× (acceptable
  trade).
- `picus-solver::ff::f4::symbolic_preprocess` consumes its
  `spolys: Vec<Polynomial>` argument (was `&[Polynomial]`); the
  vector becomes the prefix of `all_polys` without a per-batch
  clone.
- `picus-solver::ff::f4::symbolic_preprocess` destructures
  `&mut F4Workspace` so the reducer cache and the scratch buffers
  hold independent `&mut` references concurrently.
- `picus-solver::ff::buchberger::BuchbergerState::run_f4` writes F4
  counters into `self.stats` and emits per-run deltas in
  `[picus-gb-stats F4]` (was per-`run_f4` locals).
- `picus-solver::ff::hilbert::HilbertNum::{add_assign, sub_assign,
  mul}` saturate on overflow (`i64::saturating_*`) so adversarial
  inputs that would otherwise wrap return a saturated coefficient.
- Module doc on `picus-solver::ff::f4` updated to reflect the new
  bench ratios and the reverted Hilbert gating.

### Removed

- `picus-solver::ff::hilbert::batch_density_score`. Added then
  reverted in the same release: the Gebauer–Möller M-criterion
  inside `gm_insert` collapses every same-LCM pair against an
  existing one before it reaches the F4 batch, so the gating signal
  (`sum |HN coefficients|` over the LCM ideal) is `Ω(batch.len())`
  on every input that survives GM and never crosses the threshold.
  Confirmed empirically with a 6-variable redundant-LCM ideal that
  initially has 15 same-LCM pairs but only 11 survive GM-insert.
  The `hilbert_numerator` module is retained as a reusable building
  block; the `run_f4` integration and the `F4_HILBERT_CHECK_MAX_BATCH`
  / `F4_REDUNDANCY_LIMIT` constants are gone.

### Tests

- 337 lib tests pass under both `PICUS_USE_F4=0` and
  `PICUS_USE_F4=1`; 1 `#[ignore]` (`f4_large_batch_cyclic_6`,
  release-only). 77 integration tests + 6 cdclt_regression tests
  pass under F4=1. `f4_vs_per_pair_random_cross_check` (12
  deterministic seeds) still fuzzes F4 against per-pair LT-set
  agreement.

### Performance

- `bench_f4_vs_per_pair_large` and `bench_f4_non_cyclic_workloads`
  F4 / per-pair ratios at `F4_MIN_BATCH = 12`:

  | workload | ratio |
  |---|---|
  | cyclic-4 | 0.82–0.92× |
  | cyclic-5 | 0.91–1.12× |
  | cyclic-6 | 1.06–1.20× |
  | dense-10/20/30 | 0.96–1.02× |
  | katsura-3 | 0.77–0.88× |
  | katsura-4 | 0.92–1.02× |
  | diffuse-4vars | 0.92–1.15× |

- End-to-end `picus check --solver native --theory ff` on the 68
  circomlib-cff5ab6 circuits (PLDI 2023 corpus), 60s wall-clock cap
  per circuit, 5000 ms per-query timeout: F4=0 total 579.25 s,
  F4=1 total 579.29 s — 0.01% wall delta, 69/69 verdicts identical.
  Per-circuit deltas above 15%: BinSub −53%, EscalarProduct −27%,
  Bits2Num −25%, MiMC7 −25%, AliasCheck −16% (all F4=1 faster);
  XOR +240% on an 8 µs baseline (noise). Total time is dominated
  by 9 circuits hitting the 60s wall-clock cap in both modes
  (~540 s of 579 s). On the cvc5_compare corpus picus is ~9.5×
  faster than cvc5 1.3.1 (`--ff-solver split`) in geomean both
  with and without F4 enabled.

## [1.7.26] - 2026-05-21

### Added

- `picus-solver::ff::f4::F4Output { poly, from_pairs, from_reducers }`.
  Replaces the prior `Vec<Polynomial>` return type of
  `process_batch`. Each output carries the indices (into the
  `batch[]` argument) of every S-pair whose row contributed during
  matrix echelon, and the basis indices of every reducer row that
  participated. `BuchbergerState::run_f4` threads these into the
  observer protocol so the `GbTracer` UNSAT-core path stays sound
  when F4 is enabled.
- `picus-solver::ff::f4::RowProv` private type: per-row provenance
  carried through `sparse_echelon`. Pair-parent and reducer-parent
  contributions are unioned on each row-vs-pivot axpy, so a row's
  final provenance is the complete set of contributing inputs.
- `lt_divmask: DivMask` field on `F4BasisRef`. Symbolic
  preprocessing applies the constant-time
  `DivMask::divides_consistent_with` filter before the O(n_vars)
  `Monomial::divides` check, eliminating the slow path on basis
  elements that cannot possibly divide the query monomial.
- `tests/bench_perf.rs::bench_f4_vs_per_pair_large`. Workload set
  sized to expose F4's amortisation benefit: cyclic-N (N=4,5) plus
  dense degree-2 ideals with 10/20/30 generators. Reports F4 vs
  per-pair median timings.
- Six new `ff::f4::tests` cases: `f4_prov_single_pair_no_reducers`,
  `f4_prov_reducer_basis_index_recorded`,
  `f4_prov_multibatch_unions_pair_indices`,
  `f4_incremental_push_pop_roundtrip`,
  `f4_incremental_pop_clears_trivial_state`,
  `f4_vs_per_pair_random_cross_check` (12 deterministic seeds).

### Changed

- `picus-solver::ff::f4::process_batch` return type is now
  `Vec<F4Output>` (was `Vec<Polynomial>`).
  `picus-solver::ff::f4::symbolic_preprocess` return tuple gains a
  fourth element listing the basis index each reducer row was built
  from, parallel to the existing `reducer_lts` array.
- `picus-solver::ff::f4::sparse_echelon` borrows pivot rows in
  place via `split_at_mut(i)` rather than cloning them per axpy.
  Provenance is unioned with the same in-place borrow, removing a
  `BTreeSet::clone()` per pivot use.
- `picus-solver::ff::f4::process_batch`'s monomial → column index
  uses a `HashSet`-collect + `sort_unstable_by` + `HashMap` lookup
  in place of the prior `BTreeMap` insertion + reverse iteration.
- `picus-solver::ff::f4::poly_to_sparse_row` no longer performs a
  trailing `sort_by_key`: terms are stored in monomial-DESC order
  and column 0 is the largest monomial, so iterating terms in
  source order already produces a column-ascending sparse row. A
  debug-mode `debug_assert!` checks the invariant.
- `picus-solver::ff::buchberger::run_f4` populates `lt_divmask` on
  every `F4BasisRef` from the precomputed
  `BasisElement::lt_divmask` and consumes each `F4Output`'s
  provenance to drive `observer.on_pair_reducers` + `on_new_poly`
  with the full dependency set.

### Tests

- 470 tests pass under both `PICUS_USE_F4=0` and `PICUS_USE_F4=1`
  (was 467 at 1.7.25 — the 3 regression-guard tests
  `cvc5_ff_is_zero_unsound_sat`,
  `core::tests::ff_is_zero_unsound_full_unsat_core_is_sound`, and
  `core::tests::bit_prop_derived_eq_unsat_core_is_sound` failed
  under `PICUS_USE_F4=1` before this release).

### Performance

- `bench_f4_vs_per_pair_large` median ratios F4 / per-pair after
  this release: cyclic-4 ≈ 1.10–1.17×, cyclic-5 ≈ 1.07–1.14×,
  dense-10 ≈ 1.08–1.21×, dense-20 ≈ 1.04–1.09×, dense-30 ≈
  1.01–1.04×. The `split_at_mut`-based pivot borrowing was the
  largest single contributor (cyclic-5 dropped from ≈ 1.30× to
  ≈ 1.10×).
- Default GB engine remains the per-pair geobucket path
  (`use_f4_default()` returns `true` iff `PICUS_USE_F4=1` is set in
  the environment). F4-lite ties dense-30 but does not beat
  per-pair outright on any tested workload.

## [1.7.25] - 2026-05-21

### Added

- `picus-solver::smt2::SmtSession`. Persistent SMT-LIB v2 session
  evaluator. Commands accepted: `set-logic`, `set-info`,
  `set-option` (including `:tlimit-per <ms>` for per-`check-sat`
  cancellation budget), `define-sort`, `declare-fun` /
  `declare-const`, `define-fun`, `assert` with
  `(! term :named NAME [other attrs])` annotations, `push n` /
  `pop n`, `check-sat`, `get-model`, `get-value`,
  `get-unsat-core`, `echo`, `reset`, `reset-assertions`, `exit`.
  `eval_script(src)` returns one [`SessionOutput`] per non-silent
  command in source order; `(exit)` truncates the response stream.
- `picus-solver::smt2::SessionOutput`. Tagged union over
  `Silent` / `CheckSat(SessionVerdict)` / `Model(String)` /
  `Values(Vec<(String, String)>)` / `UnsatCore(Vec<String>)` /
  `Echo(String)`. `to_smtlib()` renders each variant in the SMT-LIB
  v2 response shape: `sat`/`unsat`/`unknown`, the multi-line
  `(...)` model block, the `(get-value …)` pair list, the
  `(get-unsat-core)` name list, and the echo string.
- `picus-solver::smt2::SessionVerdict::{Sat, Unsat, Unknown}` and
  `SmtSession::{last_verdict, last_model, decision_level}`
  introspection accessors.
- `:named` annotation plumbing: `assert_names: Vec<Option<String>>`
  runs parallel to the `formulas` vector, is truncated by
  `(pop n)`, and feeds the `(get-unsat-core)` response. When
  `(check-sat)` returns UNSAT, every `:named` assert in scope at
  that moment is reported as the core (SMT-LIB §4.2.2 allows any
  sufficient subset; minimality is not produced).
- Per-check timeout via `(set-option :tlimit-per <ms>)`: each
  `(check-sat)` constructs a fresh
  [`crate::timeout::CancelToken::with_timeout(Duration::from_millis(ms))`].
  `:tlimit-per 0` disables the timeout.
- `crates/picus-solver/tests/run_smt2_smoke.rs`. Six binary
  integration tests that spawn the compiled `run_smt2` binary on
  a tempfile and assert the stdout response shape for
  `check-sat`, `get-model`, `get-value`, `push`/`pop`,
  `:named` + `get-unsat-core`, and `(exit)` truncation.
- 30 `smt2::tests::session_*` unit tests covering SAT / UNSAT
  verdicts, `(get-model)` printing for FF and Bool variables,
  `(get-value (…))` formatting (including the
  skip-undeclared-name rule), `(get-unsat-core)` for SAT / UNSAT /
  no-check / mixed named-and-unnamed asserts, `(push n)` and
  `(pop n)` arity handling (including past-root pops),
  declaration / macro / `__ite_N` skolem / side-constraint
  restore on `pop`, deterministic Bool-var bit-constraint
  emission ordering, `(reset)` vs `(reset-assertions)` semantics,
  `(exit)` truncation, `set-option :tlimit-per` overwrite and
  non-numeric tolerance, and `to_smtlib()` formatting for every
  output variant.
- 6 `cdclt_regression::cdclt_sat_model_*` integration tests
  asserting that `solve_formula` returns a model containing the
  declared FF variable, the declared Bool variable (both asserted
  polarities), free Bool variables, mixed Bool + FF systems, and
  the FF variables touched by a term-level `(ite c x y)` skolem.

### Changed

- `picus-solver::bin::run_smt2` rewritten on top of `SmtSession`.
  Single-run mode emits one SMT-LIB response per non-silent
  command in source order. Timed mode (`iters >= 2`) emits a CSV
  line where the verdict column is the `|`-separated sequence of
  every `(check-sat)` outcome captured from the first evaluation.
- `picus-solver::cdclt::orchestrator::cdclt_loop`: the
  SAT branch no longer routes through a `build_full_model` helper.
  `theory.collect_model()` already covers every named variable
  because Bool vars live in the polynomial namespace as FF
  elements; the SAT branch returns
  `theory.collect_model().unwrap_or_default()`.

### Fixed

- `SmtSession::check_sat` iterated `&self.vars` (HashMap) to emit
  Bool-var bit constraints `b*b = b`. HashMap iteration order is
  not stable; this leaked into the atom-interning order. Now
  iterates `&self.var_order` (declaration order).
- `SmtSession::eval_get_value` fabricated a zero-valued response
  for names not declared in the session
  (`(get-value (undeclared)) → ((undeclared #f0mP))`). Undeclared
  names are now skipped instead of being given a false value.
- `SmtSession::eval_script` continued evaluating commands after
  `(exit)`. `(exit)` now truncates the response stream and leaves
  later commands unprocessed.
- `(reset-assertions)` collapsed into `(reset)` — both wiped
  declarations, macros, the logic, and options. Per SMT-LIB v2
  §4.2.1 the former preserves declarations, macros, the prime,
  and options; only the assertion stack and the push trail are
  now cleared.

### Removed

- `picus-solver::cdclt::orchestrator::build_full_model`. The
  function returned `HashMap::new()` and the indirection added
  no value over calling `theory.collect_model()` directly.

## [1.7.24] - 2026-05-21

### Added

- `picus-solver::smt2` accepts `(declare-fun b () Bool)` and treats
  bare Bool atoms as SAT-only literals. A Bool variable
  auto-emits a bit-constraint equality `b * b = b` so its FF
  encoding stays consistent with its Boolean value.
- `picus-solver::smt2` Boolean-context handling for `=` and
  `distinct`. When the first operand is detected as Bool (via
  `is_bool_expr`), `=` lowers to an n-ary iff (`(¬a ∨ b) ∧ (¬b ∨ a)`
  chain) and `distinct` lowers to xor (2-ary) or constant `False`
  (3+-ary, vacuously unsatisfiable for Bool).
- `picus-solver::smt2` term-level `(ite c t e)` inside FF
  expressions: introduces a fresh FF variable `__ite_N` and two
  conditional equality constraints `c ⇒ __ite_N = t` and
  `¬c ⇒ __ite_N = e`. Handles arbitrarily nested ite via
  `build_poly_with_ctx`.
- `picus-solver::smt2` `(define-fun name ((p1 T1) ...) ret body)`
  parsed into a `MacroDef` and expanded alpha-renamed at each use
  site, both in FF term position (`build_poly_with_ctx`) and
  assertion position (`assert_to_formula`).
- `picus-solver::smt2` n-ary `(xor a b c ...)` lowers to a
  left-associative binary xor chain `(a ⊕ b) ⊕ c ⊕ ...` where
  each binary step is `(a ∧ ¬b) ∨ (¬a ∧ b)`.
- `picus-solver::smt2` recognises negative FF constants
  `ff-N` and `#f-NmP` as `(p - N) mod p`, and `ff.bitsum` as a
  weighted sum `a_0 + 2·a_1 + 4·a_2 + …`.
- `BuchbergerObserver::on_pair_reducers(reducer_indices)`. Mirror
  of the existing `on_initial_reducers` for the S-pair processing
  paths in `BuchbergerState::run` and
  `BuchbergerState::process_pair_geobucket`. Reports the
  active-basis indices whose `use_count > 0` after
  `reduce_by_refs_counted`, so observers can fold the reducers'
  deps into the new entry alongside the two pair parents.
- `picus-solver::tracer::GbTracer::pending_pair_reducers` field
  and matching `on_pair_reducers` impl. Cached reducer set is
  consumed (and cleared) by the next `on_new_poly` event so the
  new entry's deps include every reducer's transitive deps.
  `GbTracer::restore` also clears this cache.
- `picus-solver::sat::Solver::add_theory_lemma_with_trail(lits) ->
  Option<usize>`. Like `add_theory_lemma`, but returns the trail
  length immediately after the internal backtrack and before
  `learn_clause` enqueues the asserting literal. Callers thread
  this through their `notified` pointer so the asserting literal
  reaches the theory on the next notify pass.
- 4 ports of cvc5 `regress0/ff` to `cdclt_regression`:
  `cvc5_simple_unsat` (Bool/FF bridging via term-level ite),
  `cvc5_xor_unsound_missing_sat` (xor compilation with missing
  bit constraint), `cvc5_ff_xor_unsound_sat` (xor compilation
  overflowing GF(5)), and `cvc5_ff_xor_sound_unsat` (asserting-
  literal notify regression guard).

### Changed

- `picus-solver::cdclt::orchestrator::cdclt_loop` threads
  `trail_pre_lemma` (the trail length captured before
  `learn_clause` enqueues the asserting literal) through every
  conflict path — `sat::propagate` conflict, theory propagation
  conflict, and `post_check(Full)` theory conflict — and clamps
  `notified = notified.min(trail_pre_lemma).min(sat.trail_len())`.
  Without this, the post-backtrack notify loop skipped the
  asserting literal, leaving the theory's fact list out of sync
  with the SAT trail.
- `picus-solver::cdclt::orchestrator::TheoryStep::Conflict` now
  wraps `usize` (the `trail_pre_lemma` returned by
  `add_theory_lemma_with_trail`); `apply_theory_conflict` returns
  `Option<usize>`.
- `BuchbergerState::run` (line 756) and
  `BuchbergerState::process_pair_geobucket` (line 905) collect
  `pair_reducers` from `active_idxs` filtered by `use_counts > 0`
  and fire `observer.on_pair_reducers(&pair_reducers)`
  immediately before the existing `observer.on_new_poly` call.
- `picus-solver::split_gb::fixpoint::fixpoint_loop` attributes
  each derived bit equality from `BitProp::get_bit_equalities`
  conservatively to the union of every current basis element's
  deps (was: empty set), preventing under-approximated UNSAT
  cores when bit equalities participate in trivial-element
  derivation.
- `picus-solver::cdclt::ff_theory::FfTheory::check_full_with_mapping`
  maps `core_indices` from `solve_encoded_with_cancel`'s
  `SolveOutcome::Unsat` back to atom variables via the
  `equality_atoms ++ disequality_atoms` encoded-input order. With
  `on_pair_reducers` and the `bit_eqs` deps fix in place, the
  traced GB core is now sound to use directly.

### Tests

- 359 tests pass across the workspace (278 lib + 81 integration).
  `cdclt_regression` rises to 71, `cvc5_extended` to 14.
  - 4 new `cdclt_regression` cases (see Added).
  - 1 new `tracer::tests::test_tracer_pair_reducers_fold_into_new_poly_deps`
    asserting that reducer deps are folded into the new entry's
    deps and that `pending_pair_reducers` clears after each
    `on_new_poly`.
  - 3 new `core::tests` cases: `ff_is_zero_unsound_subset_is_sat`
    (3-poly SAT subset), `ff_is_zero_unsound_full_unsat_core_is_sound`
    (UNSAT-core must name the asserting literal), and two
    bit-prop derived-core tests
    (`bit_prop_derived_unsat_core_includes_bit_constraints`,
    `bit_prop_derived_eq_unsat_core_is_sound`).

### Fixed

- `picus-solver::cdclt::orchestrator::cdclt_loop` lost the
  asserting literal from theory lemmas on every conflict path.
  After backtrack + `learn_clause`, the `notified` pointer was
  clamped to `sat.trail_len()` which now sat one position past
  the asserting literal; the theory was never told about that
  literal's polarity. Manifested as `cvc5_ff_xor_sound_unsat`
  reporting SAT instead of UNSAT.
- `picus-solver::split_gb::split_gb_cancel_traced` returned UNSAT
  cores that named a strict subset which was itself SAT.
  Root cause: `GbTracer::on_new_poly` folded only the two pair
  parents' deps, dropping any reducer-basis deps consumed during
  `reduce_by_refs_counted`. Manifested as `cvc5_ff_is_zero_unsound_sat`
  reporting UNSAT instead of SAT after the asserting-literal fix
  exposed more facts to the theory.
- `picus-solver::split_gb::fixpoint::fixpoint_loop` propagated
  bit equalities with empty dependency sets; bit-equality-derived
  trivial elements could trace back to a core that excluded the
  bit constraints or the bitsum.

## [1.7.23] - 2026-05-21

### Added

- `picus-solver::sat::Solver::enqueue_theory(lit, reason_facts)`.
  Enqueues a theory-propagated literal with a learnt reason clause
  `(lit ∨ ¬r_i …)`. The clause is added to the arena and watched
  on `lit` and the highest-level reason negation so backtrack-aware
  unit propagation re-fires correctly. Rejects empty `reason_facts`
  (a length-1 unit clause cannot be watched) and already-assigned
  `lit`.
- `picus-solver::cdclt::atoms::AtomTable::n_atom_slots()` and
  `AtomTable::atoms_for_var(var_name) -> &[(BigUint, Var)]`. The
  latter exposes the existing `single_var_eq` index so theory
  propagation can look up single-variable-equals-constant atoms by
  FF variable name.
- `picus-solver::cdclt::ff_theory::FfTheory` theory propagation
  implementation in two tiers:
  - **Tier 1**: for each atom not on the trail whose canonical
    polynomial reduces to a constant under the pinned variables,
    derive its truth value (zero ⇒ True, non-zero ⇒ False). Reason
    = pinning sources for the variables used by the atom.
  - **Tier 2**: for each positive multi-variable atom `A` on the
    trail, substitute pinned variables into `A`'s polynomial. If
    the result reduces to `a·v + c = 0` with a single unpinned
    linear variable `v` and a non-zero coefficient `a`, solve
    `v = −c · a⁻¹ mod p` via Fermat. For each registered
    single-variable-equals-constant atom `(= v c')` not on the
    trail, propagate True (when `c' == derived_value`) or False
    (otherwise). Reason = `[A] + pinning sources for the other
    variables in A`.
  - `FfTheory::pending_reasons: HashMap<Var, Vec<(Var, bool)>>`
    caches reasons across `propagate()` / `explain()` and is
    cleared on `propagate()` entry and `pop()`. `explain()` returns
    only cached reasons; an empty result from a cache miss is
    treated as a contract violation and rejected by
    `enqueue_theory`.
- `picus-solver::cdclt::orchestrator::run_theory_propagation`. New
  step between the trail-notify loop and `post_check(Full)`. Each
  `theory.propagate()` result either no-ops (SAT agrees),
  `enqueue_theory`s into SAT (SAT had it Undef), or emits a theory
  lemma via `add_theory_lemma` (SAT disagrees).

### Changed

- `picus-solver::cdclt::ff_theory::FfTheory` gains a
  `pending_reasons` field and rewrites `propagate()` / `explain()`
  around the two-tier propagation above. `pinned_vars` now returns
  `HashMap<String, (BigUint, Var)>` so reason construction can
  attribute each pinning to its source atom.
- `picus-solver::cdclt::orchestrator::cdclt_loop` invokes
  `run_theory_propagation` after the notify loop on each main-loop
  iteration; `TheoryStep::Progressed` re-enters the loop,
  `Conflict` syncs and continues, `RootUnsat` terminates,
  `Idle` falls through to `post_check`.

### Tests

- 379 lib + integration tests (358 in the library / 50 in
  `cdclt_regression`; up from 342 at 1.7.22).
  - 14 new `cdclt::ff_theory` tests: tier-1 negative-fact / aux-var
    filters, degree-2 atoms, equivalent-canonical-form idempotence,
    constant-only atoms, tier-2 linear residue derivation, tier-2
    skip on multi-unpinned / degree-2-unpinned, tier-2 explain
    reason coverage, tier-2 non-unit pinned-factor coefficient.
  - 4 new `sat::solver` tests: `enqueue_theory` assign + reason
    pointer + multi-level reason sort + post-backtrack re-fire,
    rejection of empty reason and already-assigned literals.
  - 9 new `cdclt_regression` cross-validation tests: linear
    residue, chain, three-branch SAT/UNSAT, negated-equality
    pinning, degree-2 SAT/UNSAT, tier-2 linear / chain / non-unit
    coefficient / multi-unpinned, 20-instance random linear sweep.

### Fixed

- `picus-solver::cdclt::ff_theory::compute_tier1` skips atoms with
  no variables. Without the guard, such atoms would produce an
  empty-reason propagation that fed a length-1 reason clause
  through `enqueue_theory` (unwatchable by the two-literal scheme,
  stranding the literal Undef after backtrack).
- `picus-solver::sat::Solver::enqueue_theory` refuses empty
  `reason_facts` instead of silently constructing an unwatched
  unit reason clause.
- `picus-solver::cdclt::ff_theory::FfTheory::explain` returns only
  cached reasons; the previous legacy fallback could attribute
  Tier 2 derivations to single-var-eq pinning facts alone, missing
  the multi-variable source atom.

### Notes

- Two-tier theory propagation reaches verdicts that previously
  needed a full `post_check(Full)` GB call. The tier 1.5
  limitation noted in 1.7.22 (skip when any variable is unpinned)
  is replaced by tier 2, which solves the single-unpinned linear
  case directly.

## [1.7.22] - 2026-05-21

### Added

- `picus-solver::sat::Solver` decision heuristic and restart machinery.
  - VSIDS variable-activity score (`var_activity`, `var_inc`, `var_decay`),
    bumped during 1-UIP resolution for every variable encountered
    (the 1-UIP and intermediate resolved vars included, not only
    `learnt[1..]`), with `1e100` rescale.
  - Phase saving (`saved_phase`): the last polarity assigned to a
    variable is reused on its next decision; survives backtrack.
  - MiniSAT-style max-heap (`order_heap`, `heap_pos`) on
    `var_activity`. `pick_decision` is now O(log n) extract-max with
    skip-already-assigned; `bump_var_activity` percolates up in place;
    `backtrack_to` re-inserts each unassigned variable.
  - Luby restart (`luby(i)`, `should_restart`, `perform_restart`,
    `n_conflicts`). Restart base 100; sequence
    `1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, …`. Backtrack to
    root, advance the Luby index, set the next threshold to
    `n_conflicts + base × luby_idx`.
- `picus-solver::cdclt::atoms::AtomKey::as_single_var_eq(&BigUint)`.
  Detects atoms canonically of the form `a·x + c = 0` for any non-zero
  coefficient `a`; computes `a⁻¹` via Fermat (`a^(p-2) mod p`) and
  returns `(var_name, −c·a⁻¹ mod p)`.
- `AtomTable::single_var_eq: HashMap<String, Vec<(BigUint, Var)>>`.
  `intern_eq` emits a pairwise at-most-one mutex clause
  `(¬new ∨ ¬other)` for each existing entry with a different value.
- `ENV_TEST_LOCK: Mutex<()>` (`#[cfg(test)]`) in `picus-solver` root.
  Serializes the `PICUS_DNF_CAP` / `PICUS_CDCLT_ITER_CAP` tests so
  the suite can run with the default parallel test threads.

### Changed

- `picus-solver::cdclt::orchestrator::cdclt_loop` checks
  `should_restart` after each learnt clause; on restart, calls
  `sync_theory_after_backtrack` and clamps `notified` to the new
  trail length.
- `picus-solver::sat::Solver::pick_decision` signature changed from
  `&self` to `&mut self` (heap pop is destructive).
- `picus-solver::sat::Solver::analyze` signature changed from
  `&self` to `&mut self` (VSIDS bump + conflict count update).

### Fixed

- `AtomKey::from_eq` reduces `rhs` coefficients mod `prime` before
  negation. Previously, passing an un-reduced coefficient (e.g. `10`
  for GF(7)) caused a `BigUint` subtract-underflow panic.
- `cdclt::orchestrator::apply_theory_conflict`'s `LBool::Undef`
  branch is now `unreachable!` with a diagnostic instead of silently
  returning `false`; the previous behavior reported the formula as
  UNSAT when the theory/SAT push/pop discipline diverged.

### Tests

- 342 lib + integration tests (235 in the library, 107 across
  integration suites; up from 317 at 1.7.21).
  - 28 in `sat::solver` (+ `luby_first_15_values`,
    `phase_saving_remembers_after_backtrack`,
    `vsids_prefers_higher_activity_variable`,
    `vsids_bumps_intermediate_resolved_variables`,
    `restart_preserves_root_level_units`,
    `perform_restart_resets_decision_level`).
  - 13 in `cdclt::atoms` (+ pairwise mutex emission, lhs/rhs swap
    canonicalization, three-constant pairwise count, Fermat
    non-unit coefficient detection, semantically-equivalent scaled
    atoms).
  - `cross_validate_random_3cnf_sweep` (8 seeds × 4 sizes = 32
    instances) and `cross_validate_random_implies_chain_sweep` (32
    instances) added to `cdclt_regression`; both run CDCL(T) and
    DNF and assert agreement (skipping when the DNF size cap fires).
- `restart_preserves_root_level_units` calls `perform_restart()`
  directly rather than relying on `solve()` to accumulate enough
  conflicts on a small input.
- `cross_validate_mutex_pin_unsat` uses non-bit constants (5, 6, 7)
  so `rewrite_disjunctive_bit` does not collapse the disjunctions,
  exercising the mutex code path.

### Notes

- Suite re-validated single-threaded (`--test-threads=1`) and with
  the default parallel threads; both report 342 passed, 0 failed.

## [1.7.21] - 2026-05-20

### Added

- `picus-solver::sat` module. CDCL SAT engine: `lit` (`Var`, `Lit`,
  `LBool`), `clause` (`Clause`, `ClauseArena`, `ClauseRef`), `solver`
  (`Solver`). Public API: `new_var`, `add_clause`, `decide`,
  `propagate`, `analyze`, `backtrack_to`, `learn_clause`,
  `add_theory_lemma`, `solve`. Two-literal watching for propagation;
  1-UIP conflict analysis; decision heuristic = lowest-index Undef
  variable, positive polarity.
- `picus-solver::cdclt` module. Submodules:
  - `atoms::AtomTable`: canonical FF equality atom interning.
    `AtomKey::from_eq` normalizes `lhs − rhs` mod prime via
    `rewriter::normalize_term_list`, then flips signs when the
    leading coefficient exceeds `p/2`. `new_aux` allocates Tseitin
    auxiliary SAT variables.
  - `cnf::tseitin`: `Formula` → CNF + top-level literal. Folds
    `True`/`False` constants; emits `t ↔ ⋀lᵢ` / `t ↔ ⋁lᵢ` clauses
    for non-leaf nodes.
  - `theory::Theory` trait: `notify_fact`, `pre_check`,
    `post_check`, `propagate`, `explain`, `push`, `pop`,
    `collect_model`. Matches the cvc5 `theory_ff` interface shape.
  - `ff_theory::FfTheory`: level-indexed fact trail; on
    `post_check(Full)` builds a `ConstraintSystem` from the trail,
    calls `core::solve_encoded_with_cancel`, maps `original_polys`
    indices in the returned UNSAT core back to atom variables.
  - `orchestrator::solve_formula(prime, &Formula, &CancelToken) ->
    SolveOutcome`. Loop: SAT propagate → if conflict, analyze and
    backtrack; → if full assignment, run `post_check(Full)`; → on
    theory UNSAT, build a SAT clause from negated core literals and
    feed via `Solver::add_theory_lemma` (sorted by descending level,
    backtrack to the second-highest level, enqueue the asserting
    literal).
- `boolean::solve_boolean_query_dnf`: DNF-enumeration entry; selected
  when `PICUS_BOOLEAN=dnf` is in the environment.
- `crates/picus-solver/tests/cdclt_regression.rs`: integration tests
  that run both `solve_formula` and `solve_boolean_query_dnf` on the
  same `BooleanQuery` and assert the verdicts agree and match the
  expected value. Inputs: hand-written Boolean shapes, parameter
  sweeps for each `bench_fixtures` family, and the cvc5
  `regress0/ff` ports compatible with the picus-solver SMT-LIB
  parser (`negneg`, `univar_conjunction_sat`,
  `univar_conjunction_unsat`, `elim_disjunctive_bit_constraints`,
  `issue10937`).
- `crates/picus-solver/benches/cdclt_bench.rs`: Criterion bench
  pairing `cdclt::solve_formula` and
  `boolean::solve_boolean_query_dnf` on every fixture in
  `bench_fixtures::corpus`.
- `crates/picus-solver/benches/smt2_bench.rs`: Criterion bench embeds
  `benches/smt2/*.smt2` via `include_str!` and times
  `parse_boolean` and `solve_formula` separately on each.
- `picus-solver::bench_fixtures` module. Programmatic SMT-LIB v2
  QF_FF source builders for the bench corpus: `conjunction`,
  `single_or`, `disj_bit`, `and_of_ors_sat`, `and_of_ors_unsat`,
  `implies_chain_unsat`, `bit_sum`, `random_3cnf`, `or_of_ands`.
  Used by `cdclt_bench.rs` and the `cvc5_compare` binary.
- `crates/picus-solver/src/bin/cvc5_compare.rs`. Binary that runs
  the `bench_fixtures::corpus()` workloads through both
  picus-solver's `cdclt::solve_formula` and an external cvc5
  binary (`--ff-solver split`), prints median wall-times and
  ratios. Flags: `--cvc5 <path>`, `--timeout-ms <N>`, `--iters <K>`.

### Changed

- `boolean::BooleanQuery` carries `formula: Formula` and a
  `OnceLock`-backed lazy DNF. Use `BooleanQuery::dnf()` to materialize.
- `boolean::solve_boolean_query` dispatches to
  `cdclt::solve_formula`; `PICUS_BOOLEAN=dnf` selects
  `solve_boolean_query_dnf`.

### Removed

- `crates/picus-solver/benches/benchmark_native.sh`.
- `crates/picus-solver/benches/benchmark_cvc5.sh`.
- `crates/picus-solver/benches/smt2/simple.smt2` and
  `crates/picus-solver/benches/smt2/bigff_is_zero_sound.smt2`
  (require Boolean-typed declarations, term-level `ite`, or Boolean
  iff; not in the SMT-LIB subset accepted by `smt2::parse_boolean`).

### Fixed

- `Solver::add_theory_lemma`: when every literal in the supplied
  conflict clause sits at the same decision level, the assertion
  level is computed as `max_level - 1` instead of `max_level`.
  Otherwise `backtrack_to` is a no-op, `learn_clause`'s asserting
  literal stays False (not Undef), and the orchestrator spins in
  the SAT-propagate / theory-check loop without progress.
- `boolean::BooleanQuery::from_formula` no longer materializes the
  DNF expansion eagerly. The `dnf` field is replaced by a
  `OnceLock`-backed `dnf()` method. DNF size grows as `O(3^k)` for
  k-clause CNF inputs and the eager expansion was consuming
  multi-GB heap on random 3-CNF workloads even when the only
  consumer (CDCL(T)) does not require DNF.

### Tests

- 317 lib + integration tests (231 at 1.7.20):
  - 29 in `sat`.
  - 16 in `cdclt::atoms` and `cdclt::cnf`.
  - 5 in `cdclt::ff_theory`.
  - 6 in `cdclt::orchestrator`.
  - 4 cross-validation tests in `boolean::tests`.
  - 31 in `cdclt_regression` (matrix sweeps + explicit shapes +
    cvc5 `regress0/ff` ports).

### Notes

- `core::solve_encoded_with_cancel` is reachable from both the
  existing R1CS path and the new `cdclt::solve_formula` entry; its
  signature, semantics, and `SolveOutcome` shape are unchanged.
- Full PLDI/circomlib-cff5ab6 suite (68 circuits) re-run at 5 s
  per-query, 30 s wall: 0 verdict differences, identical 50/7/9/2
  safe/unsafe/walltimeout/unknown counts. Median per-circuit wall
  +1.0 ms (+3.3%), mean +3.5 ms (+2.2%).
- Criterion `--save-baseline v1.7.20` then `--baseline v1.7.20` on
  `solver_bench`: all 10 measurement groups report `p > 0.05`,
  `|Δ%| ≤ 8`.

## [1.7.20] - 2026-05-20

### Added

- `picus-solver` module `rewriter`. `normalize_term_list(&mut Vec<PolyTerm>, &BigUint)`
  sorts variables inside each term, sorts terms by variable list, merges
  like terms (sum of coefficients mod `prime`), drops zero-coefficient
  terms. `rewrite_system(&mut ConstraintSystem)` applies it to every
  equality and drops equalities whose normalized term list is empty.
  Mirrors cvc5 `theory_ff_rewriter` (pre/post-rewrites for FfAdd, FfMult,
  FfNeg, FfEq) at the flat-term-list granularity picus-solver works in.
- `picus-solver` module `boolean`. `Formula` AST over `Literal`
  (`Eq`/`Neq` over `PolyTerm` lists) plus `And`/`Or`/`Not`/`True`/`False`.
  `Formula::nnf` and `Formula::to_dnf` produce a `Vec<Vec<Literal>>`
  disjunctive normal form. `BooleanQuery::from_formula` runs the
  `rewrite_disjunctive_bit` preprocessing pass then `nnf` + `to_dnf`;
  `to_disjunct_systems` returns one `ConstraintSystem` per DNF disjunct,
  each routed through `rewriter::rewrite_system`. `solve_boolean_query`
  dispatches to `solve_encoded_with_cancel` per disjunct and returns
  `Sat` on the first SAT, `Unsat` if every disjunct is UNSAT, `Unknown`
  if any disjunct returned `Unknown`.
- `picus-solver::boolean::rewrite_disjunctive_bit`. Walks a `Formula`
  and rewrites every `Or` whose two children match `(= x 0)` and
  `(= x 1)` (in either order, same variable) to the literal
  `Eq([1·x·x], [1·x])`. Equivalent of cvc5
  `preprocessing/passes/ff_disjunctive_bit.cpp`.
- `picus-solver::smt2::parse_boolean(&str) -> Result<BooleanQuery, ParseError>`.
  Top-level parser accepting `and`, `or`, `not`, `=>`, and
  assertion-level `ite` in addition to the existing equality / `not eq`
  subset that `parse` handles.
- `picus-solver::split_gb::split_gb_cancel_traced` and
  `picus-solver::split_gb::TracedSplitGb`. Variant of `split_gb_cancel`
  that takes per-input original-poly dependency sets and, when any
  partition becomes the whole ring during fixpoint, returns the precise
  subset of original input indices that derived the trivial element.
  Uses `Ideal::extend_with_cancel_traced` (which feeds a `GbTracer`)
  per partition; cross-partition propagations carry the source poly's
  current orig-deps forward.

### Changed

- `encoder::encode`, `encoder::encode_constraint_side`, and
  `encoder::encode_no_auto_bitsum` now run `rewriter::rewrite_system`
  on a cloned `ConstraintSystem` before `auto_extract_bitsums` and
  `encode_impl`. `smt2::parse` runs the same rewrite on its result
  before returning.
- `core::solve_split_gb_cancel` now calls `split_gb_cancel_traced` with
  initial deps (bitsum polys have empty deps; each original poly
  contributes its index). When a partition is whole-ring, the returned
  `SolveOutcome::Unsat(core)` uses the precise traced core in place of
  the prior `(0..original_polys.len()).collect()` placeholder.

### Tests

- 231 lib + integration tests pass (was 212 at 1.7.19):
  - +8 in `rewriter::tests` (term-list merge, coefficient reduction,
    variable canonicalization, zero-coefficient drop, system-level
    triviality drop).
  - +6 in `boolean::tests` (NNF distribution, DNF combinatorics,
    True/False propagation, disjunctive-bit pattern rewrite and
    non-match, three end-to-end smt2 → `solve_boolean_query` cases).
  - +2 in `boolean::tests` for the disjunctive-bit pass (positive and
    negative pattern match).
  - +1 `core::tests::test_split_gb_traced_unsat_core_non_trivial`:
    three-input UNSAT where only two inputs cause the conflict; the
    returned core has `len() < 3`.

### Notes

- The PLDI/circomlib-cff5ab6 suite (68 circuits) at 5 s per-query was
  re-run against the alignment-only changes; verdict matches the
  baseline on every circuit. The 10 timeout circuits (Edwards-curve /
  Pedersen / scalar-mul family) still time out — consistent with cvc5
  timing out on the same circuits under the same budget.

## [1.7.19] - 2026-05-20

### Added

- `Polynomial::reduce_by_refs_counted` and
  `Polynomial::reduce_by_refs_counted_cancel`. Variants of
  `reduce_by_refs` and `reduce_by_refs_cancel` that take a
  `use_counts: &mut [u64]` slice aligned with `divisors`. Each
  iteration of the geobucket reduce loop increments
  `use_counts[chosen]` by one when a divisor is selected.
- `BasisElement::use_count: u64`. Cumulative reducer-usage count
  per active basis element; incremented by writeback after each
  `reduce_by_refs_counted*` call.
- `USE_COUNT_SORT_THRESHOLD = 32` in
  `ff::buchberger::mod`. Below this active-basis size the
  `active_idxs` list is left in basis-insertion order; at or above
  it the list is sorted by `use_count` descending before being
  passed to `reduce_by_refs_counted_cancel`. The inner stable LT-
  degree sort in `reduce_by_refs_geobucket` preserves the
  `use_count` order across equal LT-degree ties.

### Changed

- `BuchbergerState::add_generators`, `BuchbergerState::run` (main
  loop), and `BuchbergerState::process_pair_geobucket` now build
  `active_idxs` directly (instead of iterating
  `self.basis.iter().filter(active)` for `active_refs` and
  separately calling `active_indices`), sort it conditionally by
  `use_count`, allocate a `use_counts: Vec<u64>` aligned with the
  sorted list, call the counted reduce variant, and write the
  counts back into `BasisElement::use_count` via
  `saturating_add`.

### Removed

- `docs/solver-evaluation.md`.
- `docs/benchmarks.md`. The `Benchmarks` row in `README.md`'s
  documentation table is dropped.

### Correctness

212 lib + integration tests pass.

## [1.7.18] - 2026-05-20

### Fixed

- `core::solve_split_gb_cancel` now calls `populate_bitprop` on
  `bitsum_polys` in addition to `original_polys`. Before this change,
  bitsum-defining polynomials moved to `bitsum_polys` by
  `auto_extract_bitsums` (1.7.17) were invisible to
  `populate_bitprop`'s pattern-matching pass, so `BitProp::bitsums`
  remained empty and the split-GB DFS enumerated `2^K` bit
  assignments instead of propagating bit values from the linear
  basis. End-to-end on synthetic bitdecomp (`stress_v2/bitdecomp_kN.smt2`,
  BN128): K=14 drops from 5800 ms to ~7 ms; K=16 from 27000 ms to
  ~8 ms; K=20 and K=24 from > 30 s timeout to ~9 ms and ~11 ms
  respectively. The same pattern resolves rangecheck (double-bitsum)
  workloads where cvc5 times out.

### Changed

- `BuchbergerState::generate_pairs_against` drops coprime S-pairs at
  generation time instead of routing them through `gm_insert` and
  filtering them via `new_pairs.retain(|p| !p.is_coprime)` afterwards.
  Coprime pairs are eliminated by the product criterion regardless;
  removing the `gm_insert` call removes its O(N) per-pair scan, taking
  pair-generation cost on sparse-support workloads from O(N²) to O(N).
  The same-LCM swap rule no longer fires (a coprime new pair no
  longer replaces an existing non-coprime pair with identical LCM);
  any such non-coprime pair stays in the queue and reduces normally.
  End-to-end on `Pedersen@pedersen_old` (BN128, 100 constraints,
  basis_size_max=167, 13861 generated pairs all coprime):
  `extend_with_cancel` drops from 428 ms to 135 ms.
- `BuchbergerState::run` periodic in-loop tail-reduction now also
  runs for non-homogeneous input, gated to every 128 useful S-pair
  reductions (homogeneous input remains at every 32).

### Correctness

212 lib + integration tests pass. 3 `#[ignore]` perf tests unchanged.

## [1.7.17] - 2026-05-20

### Added

- `encoder::auto_extract_bitsums(&ConstraintSystem) -> ConstraintSystem`.
  Scans each equality for the longest chain
  `c·b_0 + 2·c·b_1 + ... + 2^k·c·b_k` where each `b_i` is in the
  bit-constrained set (collected from `bitsums` plus matched
  `b·(b − 1) = 0` equalities). Rewrites the equality to replace the
  chain with `c · __bitsum_N` and appends the bit list to `bitsums`.
  Base coefficients tried in ascending symmetric-residue order
  (`min(c, p − c)`). Minimum chain length:
  `MIN_AUTO_BITSUM_LEN = 2`.
- `encoder::encode_no_auto_bitsum`. `encode` entry point that skips
  `auto_extract_bitsums`.
- `smt2` module. `pub fn parse(&str) -> Result<ConstraintSystem,
  ParseError>` covering: `(set-logic QF_FF)`,
  `(define-sort F () (_ FiniteField N))`, `(declare-fun x () F)` /
  `(declare-const x F)` / inline `(declare-fun x () (_ FiniteField
  N))`, `(assert (= a b))`, `(assert (not (= a b)))`, `ff.add`,
  `ff.mul`, `ff.neg`, `(as ffN F)`, constants `ffN` and `#fNmP`,
  decimal literals. Boolean operators (`and`, `or`, `=>`, `ite`)
  inside `(assert ...)` return `ParseError::BooleanInAssert`.
- `run_smt2` binary (`src/bin/run_smt2.rs`). One-argument form
  prints one of `sat` / `unsat` / `unknown`. With an iteration
  count `N ≥ 2`, also prints
  `file,verdict,iters,encode_us,gb_med_us,gb_min_us,gb_max_us,total_med_us`.
- `bench_bitdecomp_auto_extract_speedup` `#[ignore]` test in
  `tests/bench_perf.rs`. K-bit decomposition systems over BN128
  for K ∈ {6, 8, 10, 12}; asserts verdict agreement between
  `encode` and `encode_no_auto_bitsum`.

### Changed

- `encoder::encode` and `encoder::encode_constraint_side` invoke
  `auto_extract_bitsums` on the input before encoding.
- `encode_impl` deduplicates auxiliary variable names via a
  `HashSet`.
- `ConstraintSystem` derives `Clone` and `Debug`.

### Fixed

- `benches/solver_bench.rs`: `FfField::new(&BigUint)` →
  `FfField::new(BigUint)`.

### Correctness

141 lib tests pass. 71 integration tests pass.

## [1.7.16] - 2026-05-20

Refactor and documentation release. No behavioural changes; the
201-test algorithmic suite plus an R1CS smoke against a curated
17-circuit `circomlib-cff5ab6` subset pass throughout.

### Added

- `crates/picus/tests/r1cs_smoke.rs` — integration test that runs
  `picus::check_circuit` with `SolverKind::Native` + `Theory::Ff`
  against a curated 17-circuit subset of `circomlib-cff5ab6` (10
  safe + 7 unsafe) and compares verdicts to `docs/benchmarks.md`.
  Auto-skips with a hint if the `benchmarks/circom/` submodule is
  not initialised or the circuits are not yet compiled, so a clean
  checkout still passes `cargo test`.
- `encoder::encode_constraint_side` — encodes equalities,
  assignments, bitsum definitions, and (optionally) field polynomials
  while reserving `__w_diseq_i` witness-variable slots without
  emitting the per-disequality Rabinowitsch polynomial. Used by
  `IncrementalSolverContext` to build a cache keyed on the constraint
  side and add per-query Rabinowitsch polynomials lazily.
- `R1csBackend` descriptor in `picus-smt::r1cs_parser`. Captures
  per-solver R1CS-encoding parameters (logic, sort, range checks,
  `mod p` wrapping) so the shared `parse_r1cs_impl` /
  `expand_cmd_impl` bodies can dispatch on a small config struct.

### Changed

- `ff/buchberger.rs` split into `ff/buchberger/{mod.rs,
  spair_criteria.rs, incremental.rs}`. `mod.rs` retains the core
  `BuchbergerState` + main `run` loop and public entry points;
  `spair_criteria.rs` holds `gm_insert` / `b_criterion_kill` /
  `merge_sorted_descending`; `incremental.rs` holds `IncrementalGB`
  + `Checkpoint`. `BasisElement` and the fields / methods of
  `BuchbergerState` accessed by the sibling submodules are exposed at
  `pub(super)`.
- `split_gb.rs` split into `split_gb/{mod.rs, fixpoint.rs, search.rs,
  branching.rs}`. `mod.rs` retains the shared types (`SplitGb`,
  `PartialPoint`, `ZeroExtendResult`, `SplitFindZeroOutcome`), the
  `split_find_zero{,_cancel}` orchestrator, and the
  `admit` / `total_degree` / `num_terms` helpers; `fixpoint.rs`
  hosts `split_gb` / `split_gb_cancel` / `split_gb_extend_cancel`,
  with the two cancel-aware drivers sharing a single private
  `run_fixpoint` body (eliminating ~190 lines of near-duplicate
  bit-prop fixpoint logic); `search.rs` hosts
  `split_zero_extend{,_cancel}`; `branching.rs` hosts `apply_rule`
  / `apply_rule_multi` / `univariate_coeffs`.
- `picus-smt::r1cs_parser` consolidated. Backend-specific
  `parse_r1cs_z3` / `parse_r1cs_cvc5` and `expand_cmd_z3` /
  `expand_cmd_cvc5` (each ~70 lines of near-identical code) collapse
  into shared `parse_r1cs_impl` and `expand_cmd_impl` bodies driven
  by an `R1csBackend` config. Net ~80 LOC reduction.
- `picus-smt::optimizer::subp_optimize_z3` and `subp_optimize_cvc5`
  share a single `subp_optimize_impl` body parameterised by the SMT
  sort name and the substitution map. Z3 keeps `p` as a named
  constant; cvc5 keeps `p → "zero"` as an extra substitution.
- `Ideal::new` (in `picus-solver::ideal`) now delegates to
  `Ideal::new_with_cancel(..., &CancelToken::none())`. The two entry
  points previously produced subtly different bases (the
  cancel-aware variant ran an extra `interreduce_basis` pass on top
  of Buchberger's own internal finalisation).
- `picus-solver`: non-cancel variants of `solve_split_gb`,
  `solve_encoded`, `solve_encoded_with_mode`, and
  `IncrementalSolver::check` now delegate to their `_cancel`
  counterparts with a no-op `CancelToken::none()`, removing ~75 lines
  of duplicated solve logic.
- `IncrementalSolverContext::rebuild_base` (in
  `picus-solver::incremental_context`) uses
  `encode_constraint_side(cs)` directly instead of fabricating a
  placeholder `("x0", "x0")` disequality, calling `encode`, and
  `.pop()`-ing the Rabinowitsch polynomial off the result. The
  placeholder hack was fragile under `add_field_polys = true` (which
  appends field polynomials *after* the Rabinowitsch term) and is
  gone.
- `picus-solver::field::FfField` is now a type alias for
  `PrimeField` (was a wrapper struct that re-exported every method
  on `PrimeField` as a one-line delegate). Callsites use
  `FfField::new(p.clone())` (was `FfField::new(&p)`) and
  `pr.field.prime()` (was `pr.field.prime` field access).
- `split_gb`'s `total_degree` and `num_terms` helpers no longer take
  a `_ring: &PolyRingType` parameter — it was unused.
- All in-source comments and `docs/` content rewritten to drop
  development-process narrative (plan-phase tags, KPI discussion,
  version-by-version storytelling, source-line references into
  external libraries, circuit-name anecdotes). Doc comments now
  describe interfaces, invariants, and algorithms without referring
  to internal development plans or external source-line citations.
- `CHANGELOG.md` rewritten with the same convention applied to every
  prior version entry.

### Removed

- `picus-solver::ff::buchberger::Ideal` and its impl — internal
  duplicate of the higher-level `picus-solver::ideal::Ideal`. The
  `min_poly_cancel` Gaussian-elimination body lifted up into the
  public Ideal; `poly_coefficient_at` exposed at `pub(crate)`. Two
  redundant tests (`gb_simple_two_gen`, `min_poly_simple`) removed —
  the same scenarios are already covered by tests on the public
  `Ideal` in `ideal.rs::tests`.
- `picus-smt::optimizer::ab0_optimize_cvc5` and its helpers
  (`ab0_opt_cmd_cvc5`, `match_ab0_cvc5`, `is_zero_rhs_cvc5`) — 56
  lines that had been marked `#[allow(dead_code)]` since v1.1.2.
  `ab0_optimize_z3` retains the rewrite pattern; if the cvc5 QF_FF
  `or` bug (1.2.0–1.3.3) is fixed in a future cvc5 release, the
  cvc5 entry point can be re-derived from the Z3 implementation
  (drop the `(mod _ p)` wrappers).
- Unused `const_poly` test helper in `ff/f4.rs`.

### Documentation

- `docs/solver-evaluation.md` rewritten as a technical reference
  (module layout, public API, algorithmic notes, configuration,
  tests, known limitations) — version timelines and per-release
  prose removed.
- `docs/TODO.md` trimmed to factual entries.

## [1.7.15] - 2026-05-01

### Added

- Thread-local `FieldElem` allocation pool (`ff/field.rs`). `FieldElem`
  implements `Drop` to recycle its `rug::Integer` buffer back into a
  thread-local stack (size 4096). `field.add` / `sub` / `mul` / `neg`
  draw from the pool. `add_owned` / `sub_owned` consume both operands
  and recycle the right-hand side. Reentrancy guarded by an
  `IN_POOL_DROP` cell.
- GMP in-place arithmetic on the geobucket cascade path.
  `Geobucket::pop_leading_term`'s cross-bucket coefficient sum uses
  `field.add_assign`. `Polynomial::merge_owned` uses `add_owned` /
  `sub_owned`.
- 128-bit `DivMask` (`ff/divmask.rs`), replacing the previous 32-bit
  mask. Per-variable threshold count adapts via `DIVMASK_BITS / n_vars`,
  covering > 32 variables on wide circuits.
- Sorted divisor bucket with early-break in `reduce_by_refs_geobucket`.
  Divisors within a bucket are sorted by leading-term total degree
  ascending; the scan breaks on the first divisor whose LT degree
  exceeds the current LT's. Gated to ≥ 256 divisors.
- `IncrementalGB` resume primitives (`ff/buchberger.rs`): `run_only`,
  `set_cancel_token`, `is_quiescent`, `open_queue_len`. Lets a cancelled
  Buchberger run resume across calls with a fresh cancel budget.
- `IncrementalSolverContext` partial-build fallback
  (`incremental_context.rs`). When a fresh cache rebuild is cancelled
  mid-build, encoded artifacts plus per-partition `IncrementalGB`
  in-flight state are preserved as `partial_build`; the next solve
  call with the matching digest resumes via `continue_partial`. Counters
  `cache_partial_resumes` and `cache_partial_completions` surfaced via
  `PICUS_GB_STATS=1`.
- F4-lite scaffolding (`ff/f4.rs`, opt-in via `PICUS_USE_F4=1`).
  Sugar-batched S-pair processing: symbolic preprocessing (BFS closure
  under reducibility), sparse matrix construction with monomial-DESC
  column index, sparse row-echelon over GF(p) with reducer rows
  pivoted first. Falls back to direct geobucket for batches of size 1.
  Disabled by default.

### Correctness

132 unit tests pass. 110-circuit correctness gate produces 0 verdict
mismatches with `PICUS_USE_F4=0` (default) and `PICUS_USE_F4=1`.

## [1.7.14] - 2026-04-28

### Added

- `IncrementalSolverContext` solver-state cache. Caches the encoded
  constraint side and computed split-GB across `solve_encoded` calls
  within a `NativeFfBackend` session. On a cache hit, the per-query
  Rabinowitsch disequality polynomial is encoded in the cached ring
  and added via `Ideal::extend_with_cancel`. Lazy build (only after
  two consecutive same-digest calls). Disable via
  `PICUS_NO_INCREMENTAL_CACHE=1`.
- Hash-bucketed divisor index in `reduce_by_refs_geobucket`. Groups
  divisors by `DivMask` bits; the lookup loop iterates only buckets
  whose mask is a submask of the current LT's mask. Gated to ≥ 64
  divisors.
- AST-level integer-literal folding in `+` and `*`. The IR optimizer's
  `simple_opt_expr_z3` consolidates `Int(a) + Int(b) → Int(a+b)` and
  `Int(a) * Int(b) → Int(a*b)` with canonical position (constants at
  the end of `+`, at the start of `*`).
- HOMOG-gated periodic in-loop tail-reduce. When all initial generators
  are homogeneous (every term shares the same total degree),
  `BuchbergerState::run` invokes `tail_reduce_active` every 32 useful
  S-pair reductions. Off for non-homogeneous inputs.
- `BitPropState` (`bitprop.rs`): owned snapshot of `BitProp`'s `bits`
  and `bitsums` sets, with `to_state` / `from_state` accessors. Used
  by the cache to persist BitProp contents across solve calls.
- `NativeFfBackendCounters` surfaced via `PICUS_GB_STATS=1`. Counters:
  `solve_calls`, `encode_time_ns`, `solve_inner_time_ns`,
  `encoded_polys_max`, `distinct_cs_digests`,
  `repeated_cs_digest_streak`, `cache_hits`,
  `cache_rebuild_time_ns`, `cache_query_diff_time_ns`.

### Correctness

127 unit tests pass. 110-circuit correctness gate produces 0 verdict
mismatches.

## [1.7.13] - 2026-04-28

### Added

- Memoized cross-basis containment in the split-GB propagation loop.
  `Polynomial::content_hash()` produces a u64 fingerprint from
  exponents, per-term degrees, and a leading-coefficient hash. Each
  `split_gb_cancel` / `split_gb_extend_cancel` invocation maintains a
  `HashSet<(u64, basis_idx)>` recording polynomials known to be
  members of each basis. The set is pre-populated each fixpoint
  iteration with self-membership facts and updated with positive
  results as the loop runs. Soundness rests on ideal-membership
  monotonicity during a single fixpoint call.
- Move-based polynomial merge for owned operands
  (`Polynomial::merge_owned`, `field.add_owned` / `sub_owned` /
  `neg_owned`). Consumes both inputs' coefficient `Vec`s and recycles
  their `FieldElem` (and underlying `mpz_t`) allocations into the
  output.
- Borrowed leading-term info in `reduce_by_refs_geobucket`. The
  per-divisor `(exps, deg, coeff, divmask)` tuple now borrows the
  exponent slice from the divisor's own storage rather than cloning
  it into a per-call `Vec<u16>`.
- Degree-sorted divisor scan with early-break (gated to large
  divisor sets). Iterates an auxiliary index sorted by leading-term
  total degree ascending and breaks on the first divisor whose LT
  degree exceeds the current LT's.
- `PICUS_GB_STATS=1` and `PICUS_GB_TRACE=1` instrumentation surfaces.
  Stats extend the existing telemetry with split-GB driver counters
  and per-phase reducer timers (`div_lt_setup`, `pop_lt`,
  `div_lookup`, `sub_scaled`, `finalize`, plus a `sub_scaled_tail`
  setup / `add_poly` split). Trace emits one line per fixpoint
  iteration with basis sizes and propagation counts.

### Correctness

127 unit tests pass. 110-circuit correctness gate produces 0 verdict
mismatches.

## [1.7.12] - 2026-04-28

### Added

- GMP backend via the `rug` crate. `PrimeField` and the in-tree
  polynomial pipeline use `rug::Integer` instead of `num_bigint::BigUint`.
  `PrimeField` caches `result_bits` (`prime_bits + 1`) and
  `product_bits` (`2 * prime_bits + 1`) at construction; `add` / `sub`
  / `mul` allocate the result with `Integer::with_capacity(...)`.
- Pair-free seed path in `compute_gb_incremental_with_order`. The
  seeding pass pushes seed elements directly with non-strict
  deactivation and applies the divmask, skipping pair generation.
- No-op skip in `Ideal::extend_with_cancel`. When every new generator
  reduces to zero against the existing reduced GB, the GB engine and
  the subsequent `interreduce_basis` call are both skipped.
- Linear-only quick UNSAT check optimization in `split_gb.rs`. The
  per-DFS-branch linear-only UNSAT pre-check now uses a direct
  `reduce_with_cancel` plus non-zero-constant check on `basis[0]`,
  replacing the prior clone + incremental Buchberger + `is_whole_ring()`
  chain.
- Cancel-token propagation through reduction hot paths:
  `Polynomial::reduce_by_refs_cancel` (cancel-checked inside the
  geobucket `pop_leading_term` loop, every 64 iterations),
  `Ideal::reduce_with_cancel`, `Ideal::contains_with_cancel`,
  `buchberger::interreduce_with_cancel`,
  `BitProp::get_bit_equalities_with_cancel`. On cancel the reducer
  returns a partial remainder (already-emitted terms plus the
  unprocessed bucket contents) — sound but not necessarily a normal
  form.
- `PICUS_GB_STATS=1` telemetry in `buchberger.rs` (`GbEngineStats`):
  pairs generated, pairs killed by coprime / GM / B criteria,
  reductions total / useful / useless, interreduces run.
- 5 bit-pattern detection tests in `parse.rs` covering negated,
  nested, sum-form, and rejection cases.
- 5 encoder equivalence tests in `encoder.rs`.
- Geobucket scratch buffers (`scratch_exps`, `scratch_coeffs`,
  `scratch_degs`) for reusing `sub_scaled_tail` working buffers.

### Changed

- Geobucket bucket constants: `BASE_CAPACITY = 128`, `RATIO = 4`,
  `MAX_BUCKETS = 20` (were `4` / `_` / `16`).
- Sugar formula at S-pair generation: `sugar = pair.sugar` with a
  `debug_assert!(lt.total_degree() <= pair.sugar)` invariant (was
  `sugar = pair.sugar.max(lt.total_degree())`).

### Correctness

127 unit tests pass. 0 compiler warnings. 110-circuit correctness
gate produces 0 verdict mismatches.

## [1.7.11] - 2026-04-28

### Added

- Buchberger B-criterion at basis-add time. When a new basis element
  is added, every pending S-pair `(i, j)` is killed if all of
  `new_lt | lcm(LT_i, LT_j)`, `lcm(LT_j, new_lt) ≠ lcm`, and
  `lcm(LT_i, new_lt) ≠ lcm` hold.

### Changed

- Skip inactive basis elements during S-pair generation (was: include).
- Final interreduce reduced from a fixed-point loop to a single pass.
- Removed the periodic in-loop tail-reduce throttle (`INTERREDUCE_EVERY
  = 32`).

### Correctness

178 unit tests pass (5 new B-criterion + 5 GM-insert + 9 geobucket +
existing). 0 compiler warnings. 110-circuit correctness gate produces
0 verdict mismatches.

## [1.7.10] - 2026-04-28

### Added

- Geobucket data structure (`ff/geobucket.rs`) for polynomial
  accumulation. Multi-bucket with geometric capacity growth
  (`BASE_CAPACITY = 4`, `RATIO = 4`, `MAX_BUCKETS = 16` at this
  release); per-bucket head cursors give O(1) leading-term pop;
  cross-bucket coefficient cancellation is resolved at pop time.
- Geobucket-based reduction in `Polynomial::reduce_by_refs`. Each
  reduction step is O(D · log(N/D)). The prior fused-merge
  implementation is retained as `reduce_by_refs_naive` for
  cross-validation.
- Gebauer-Möller M-criterion at S-pair generation time. New pairs are
  pruned within `generate_pairs_against` whenever an existing pair's
  lcm divides the new pair's lcm (with the equal-lcm
  coprime-replacement rule).
- Coprime-pair participation in M-criterion walks before being
  filtered out of the open queue. `SPair` gains an `is_coprime`
  field.

### Changed

- S-pair queue is now a sorted `Vec<SPair>` (descending by `(sugar,
  lcm_deg, age)`, pop from back) instead of a `BinaryHeap<Reverse<SPair>>`.

### Correctness

178 unit tests pass (9 geobucket + 5 `gm_insert` + 2 cross-validating
reduction implementations + existing). 110-circuit correctness gate
produces 0 verdict mismatches.

## [1.7.9] - 2026-04-27

### Fixed

- Soundness: `FindZeroOutcome::Unsat` now maps to `SolveOutcome::Unsat`
  (was: `Unknown`).
- Soundness: `u16` exponent overflow in monomial multiplication uses
  `checked_add` and panics on overflow (was: silent wrap). Affects
  `Monomial::mul` and `mul_assign`.
- Soundness: `from_i64(i64::MIN)` uses `unsigned_abs()` to avoid
  signed-overflow panic on `.abs()`.
- Robustness: `split_gb_cancel` and `split_gb_extend_cancel` fixpoint
  loops have a 1000-iteration cap.
- Robustness: `IncrementalGB::interreduce` safety cap uses the
  post-filter basis length.
- Robustness: `incremental.rs` encode failures log and return
  `Unknown` instead of panicking.
- Debug assertion on `row_dep` bounds in Buchberger matrix row
  operations.

### Changed

- Hot-loop monomial allocation eliminated in `reduce_by_refs` via
  `DivMask::compute_from_slice` on raw exponent data.
- `total_degree()` is O(1) — cached in `Polynomial` and maintained
  through arithmetic operations.
- `poly_coefficient_at` uses binary search on sorted terms.
- `from_raw_sorted` avoids re-sorting already-sorted term vectors.
- `add` / `sub` share `merge_sorted` with a `negate_other` flag.
- `BuchbergerState::active_poly_refs()` returns `&[&Polynomial]`.
- Removed dead code: `chain_criterion_skip` body (kept as
  `#[allow(dead_code)]`), `bitsum_bits`, `GbRingCache`, unused
  `clone_poly` wrappers.
- `TermsIter` uses safe lifetime-correct references (was: unsafe
  pointer cast).
- `TermRef::coefficient()` returns `&'a FieldElem`.

### Verified

167 lib tests pass. 0 compiler warnings.

## [1.7.8] - 2026-04-27

### Added

- In-tree finite-field GB engine (`picus-solver/src/ff/`). Modules:
  `ff::field` (`FieldElem` over `BigUint`), `ff::polynomial`
  (`Polynomial` with packed monomial vectors and divisibility masks),
  `ff::monomial` (`MonomialOrder` enum), `ff::buchberger`
  (`BuchbergerState`, `IncrementalGB`), `ff::univariate` (single-
  variable factoring for root extraction). Inner reduction loop uses
  `reduce_by_refs(&[&Polynomial])`.
- `tail_reduce_active` in `IncrementalGB` every 32 basis adds
  (`INTERREDUCE_EVERY = 32`). Mutates polynomial bodies only, never
  `lt`/`active`/`sugar`/indices.

### Fixed

- Soundness in `ff::buchberger::chain_criterion_skip`. The simplified
  "any-`k` divides lcm → skip" form was unsound under non-strict
  deactivation: substitute pairs `(i,k)` and `(j,k)` were not
  guaranteed to have been generated and discharged. Trivially-UNSAT
  systems silently produced incomplete GBs. Fix:
  1. `generate_pairs_against` no longer skips inactive basis elements
     when adding a new generator.
  2. `state.run` no longer calls `chain_criterion_skip`.
  `chain_criterion_skip` is retained as `#[allow(dead_code)]`.
- `bn128_invariants` integration tests now pass.

### Changed

- `feanor-math` dependency removed from `Cargo.toml` and `Cargo.lock`.
  The previous `gb_stats.rs` wrapper around feanor's observer was
  deleted; `gb.rs` is now a two-phase (DegRevLex → Lex) wrapper over
  `ideal::compute_gb_with_order{,_traced}`.
- CLI: removed `--profile gb` (the observer it surfaced was feanor-
  specific). `--profile wall` is unchanged.
- Removed release-profile debug overrides from `picus/Cargo.toml`.
- Removed unused `#![feature(allocator_api)]` from
  `picus-solver/src/lib.rs`.

### Verified

96 lib tests + 71 integration tests pass. Cargo.lock contains 0
references to `feanor`. 110-circuit correctness gate produces 0
verdict mismatches.

### Removed

- `examples/probe_*.rs` and `tests/probe.rs` ad-hoc reproducers.

## [1.7.7]

### Changed

- Buchberger algorithm overhaul in the upstream-fork polynomial ring:
  removed density-triggered restart heuristic; moved inter-reduction
  to once at loop termination; basis deactivation uses non-strict
  divisibility; pairs against deactivated elements are kept in the
  queue; S-pair processing is one-at-a-time.
- `GbRingCache`: the polynomial ring (with its multiplication table)
  is built once per solve and reused across incremental GB calls.
- Removed round-robin branching cap (was: 256 values for large primes).
- Removed dead `extend_with_cancel`; only `extend_with_cancel_cached`
  remains.
- `map_in_batch` / `map_out_batch`: polynomial ring homomorphisms
  created once per batch.

### Verified

130 picus-solver tests pass.

## [1.7.6] - 2026-04-24

### Added

- In-place Buchberger restart in the upstream-fork polynomial ring.
  After a round of pair processing, basis / sugar / active / open
  structures are cleared and rebuilt in place via `update_basis`; the
  reducer cache is preserved across restarts.
- Hilbert numerator engine in the upstream-fork polynomial ring
  (`src/algorithms/hilbert/`). Modules for `EMonom` exponent-vector
  representation, `TermList` working state, recursive splitter via
  coprimality and connected-component decomposition, leaf evaluators,
  and univariate helpers (multiplication by `1 - t^k`, synthetic
  division by `1 - t`). 38 internal tests. Not wired into the
  Buchberger loop.
- Pair-profile diagnostic
  (`buchberger_pair_profile.rs`). Test-only helper recording S-pair
  lifecycle events.
- GB statistics module (`gb_stats.rs`). Counters for Buchberger
  top-level invocations, S-pair reductions, sugar tightening, and
  batch-zero rate. Enabled via `--profile gb`.
- Homogenisation plumbing (`gb_homog.rs`, `homog.rs`). Feature-gated
  and opt-in; no callers in the default path.
- Profile module (`profile.rs`). Per-stage timing wrapper.

### Changed

- `gb_stats` label: `restarts (calls-1)` renamed to
  `extra_top_level_calls`.

### Verified

132 lib + bin + integration tests pass (6 ignored). 110-circuit
correctness gate produces 0 verdict mismatches.

## [1.7.5] - 2026-04-23

### Added

- Yan-style geobucket reduction in the upstream-fork polynomial ring.
  Buchberger reduction accumulates intermediate sums in a logarithmic
  bucket structure, deferring monomial-merge work until the bucket is
  materialised.
- BigInt scratch pool with `Global` allocator specialisation. A
  thread-local pool reuses `BigInt` allocations across the inner FMA
  loop of `bigint_mul_assign`.

### Fixed

- `bigint_fma` allocator contract. The `scratch_alloc` parameter was
  silently ignored in the `Global` fast path. Split into `bigint_fma`
  (honours the caller's allocator) and `pub(crate) bigint_fma_global`
  (used by the scratch pool).

### Changed

- Removed ~440 lines of dead code in the upstream-fork polynomial
  ring (`reduction_accum.rs`, `bigint_mul_pooled`, unused accessors).
- Deduplicated `mult_table_bounds` and `max_supported_deg` between
  `poly.rs` and `ideal.rs`.
- Demoted high-volume `split_zero_extend` logs from `debug` to `trace`.

### Verified

398 lib + integration tests in the upstream fork; 48 picus-solver
lib + 7 integration tests. 110-circuit correctness gate produces 0
verdict mismatches.

## [1.7.4] - 2026-04-22

### Added

- Gebauer-Möller pair management in the upstream-fork polynomial ring:
  B_k criterion (retroactive pair elimination when a new polynomial's
  LT divides an existing pair's LCM) and M criterion (dominated-pair
  removal among new pairs).
- `DivMask` divisibility pre-filter. `find_reducer` does a bitwise
  `(mask_reducer & ~mask_target) != 0` check before the O(n_vars)
  exponent comparison.
- Multi-basis branching in the split-GB model search. `apply_rule`
  now checks all split-GB bases for univariate polynomials and
  zero-dimensional structure (was: linear basis only).
- Squarefree root preprocessing. `find_roots` computes
  `gcd(f, x^q - x mod f)` before factoring.
- Fast paths in root finding: direct extraction for linear polynomials
  and zero roots before invoking the full factoring routine.
- Lazy branching. Round-robin candidate generation uses a counter-
  based iterator instead of pre-allocating all candidates.

### Fixed

- UNSAT-pop-brancher bug in `model.rs`. The UNSAT handler popped the
  parent's brancher when a child branch was UNSAT; only the ideal is
  popped on UNSAT.
- Timeout vs UNSAT distinction in split-GB search. Added
  `ZeroExtendResult::Cancelled` to distinguish timeout from genuine
  UNSAT in `split_zero_extend_cancel`.
- Quick UNSAT pre-check at search branch nodes. Evaluates polynomials
  under the partial assignment to detect trivially UNSAT branches in
  O(n).
- Linear-first UNSAT check at branch nodes. Tests the linear basis
  alone (Gaussian elimination) before recomputing the nonlinear basis.

## [1.7.3] - 2026-04-22

### Fixed

- Degree-overflow crash in the native solver. `FfPolyRing::new` and
  `compute_gb_with_order` use lower `max_supported_deg` thresholds:
  32 for ≤ 20 vars, 16 for ≤ 50, 8 for ≤ 200, 4 otherwise.
- `NativeFfBackend` panic safety. `encode()` and
  `solve_encoded_with_cancel()` are wrapped in `catch_unwind` with
  panic-hook suppression; returns `Unknown` on panic.
- Encoder variable-count guard. `encode()` returns an error for
  systems with more than 5000 variables.
- `picus-cli` build errors: missing `bitsums` field in `NativeFfBackend`'s
  `ConstraintSystem` initialiser; missing `SolverKind::Native` arms in
  `optimizer.rs` and `r1cs_parser.rs`; unused `HashMap` import in
  `native_ff.rs`.

## [1.7.2] - 2026-04-21

### Added

- UNSAT core tracing (`ffTraceGb`) in single-GB mode. Uses
  `BuchbergerObserver` hooks in the polynomial-ring engine to build
  a polynomial dependency DAG during Groebner basis computation. The
  `tracer` module extracts a (possibly non-trivial) subset of input
  indices.
- `tracer.rs` module. `GbTracer` struct implementing the observer
  trait. Tracks transitive input dependencies for each derived basis
  element via `BTreeSet`-based dependency propagation.
- `GbResultTraced` enum in `gb.rs`. Returns the UNSAT core directly
  on trivial (UNSAT) results.

### Changed

- `solve_single_gb` automatically traces polynomial derivations and
  returns a precise UNSAT core (was: trivial all-inputs core).
- `compute_gb_with_order` refactored. Extracted `max_supported_deg`
  helper; added `compute_gb_with_order_traced` sharing the same ring
  setup.

### Fixed

- `GbTracer::deps_of` bounds safety. Returns `Option` instead of
  panicking on out-of-range indices.

## [1.7.1] - 2026-04-21

### Added

- Native finite-field solver crate (`picus-solver`). Pure-Rust
  replacement for cvc5's QF_FF theory solver.
  - Split-GB solver with bit propagation (matches cvc5's `--ff-solver
    split` mode).
  - Single-GB solver (DegRevLex → Lex → findZero; matches cvc5's
    `--ff-solver gb` mode).
  - Pattern detection (`bit_constraint`, `linear_monomial`,
    `bit_sums`) wired into the solver pipeline.
  - Cooperative timeout via `CancelToken`.
  - Incremental push/pop API.
- `--solver native` CLI option.
- Criterion benchmark suite. `cargo bench -p picus-solver` runs
  encode, end-to-end, and root-finding benchmarks.
- `benches/benchmark_cvc5.sh` for comparing native vs cvc5 on
  matching `.smt2` inputs.
- `SolverStats` module tracking GB run counts, timing, and branching
  strategy usage.
- `docs/solver-evaluation.md`.

### Fixed

- `admit` predicate swap. The split-GB admission criteria for basis 0
  (linear) and basis 1 (nonlinear) were swapped, weakening cross-basis
  propagation.
- Degree-overflow safety. Engine panics from exceeding
  `max_supported_deg` are caught via `catch_unwind`; the solver returns
  the original generators unreduced (instead of an empty basis, which
  would be misinterpreted as SAT).
- `NativeFfBackend` uses the split-GB pipeline
  (`core::solve_encoded_with_cancel`) instead of plain Buchberger.

### Changed

- Polynomial normalisation. Encoded polynomials are divided by their
  leading coefficient.
- Polynomial-ring multiplication table tuned. `MultivariatePolyRingImpl`
  uses `new_with_mult_table((2, 2))`.

## [1.7.0] - 2026-04-19

### Changed

- Benchmarks externalised. The `benchmarks/` directory is now a
  [git submodule](https://github.com/chyanju/picus-benchmarks)
  (`picus-benchmarks`). Benchmark circuits are under
  `benchmarks/circom/` with a `compile.sh` helper.
- Library API: `Config::dump_smt` documented and exposed.

### Fixed

- z3 timeout truncation. `timeout_ms` (u64) was truncated to u32 when
  passed to z3; uses saturating cast.
- `create_backend` panic on invalid combination replaced with a proper
  error return.
- README build dependencies: added `git`, `libclang-dev`,
  `pkg-config`.
- Hardcoded z3 AST path documented with an explanatory comment.

## [1.6.0] - 2026-04-19

### Added

- `picus` library crate. Public API: `check_circuit()`,
  `check_r1cs_bytes()`, `check_r1cs()` with structured `CheckResult`
  (using `BigUint` values, not strings). Re-exports `SolverKind`,
  `Theory`, `LemmaSet`, `BigUint`, `R1csFile`.
- `Config::dump_smt` field. SMT query dumping supported through the
  library API.

### Changed

- `picus-cli` depends solely on the `picus` facade crate. The
  `dump_smt` code path no longer bypasses the public API.

### Fixed

- Removed duplicated `split_model` logic between `picus` and
  `picus-cli`.
- `log::warn` added for silently-dropped constraints in solver
  backends.
- `cvc5-ff-sys` doc comment referencing `cvc5` corrected to `cvc5-ff`.
- Architecture documentation updated to include the `picus` facade
  crate.

## [1.5.1] - 2026-04-19

### Changed

- `--lemmas` syntax. Added `all-X,Y` (exclude) and `none+X,Y` (include)
  formats. Bare comma-separated lists remain supported as a shorthand
  for `none+...`.

### Fixed

- Removed stale `.sym parser` reference from `docs/architecture.md`.
- Removed orphaned doc comments in `binary01.rs` and `basis2.rs`.

## [1.5.0] - 2026-04-19

### Added

- Multi-stage `Dockerfile` (Ubuntu 24.04). `docker build -t picus .`
  produces a self-contained image with all solvers pre-compiled.
- `--format` flag. `human` (default) produces styled terminal output
  with colour; `json` outputs machine-readable JSON to stdout.
  Supported by `check` and `info`.
- Coloured terminal output via `owo-colors` + `anstream`. Colours
  enabled in terminals, stripped when piped.
- Structured human output. Circuit info, analysis config, and results
  are displayed in separated sections with aligned labels.

## [1.4.0] - 2026-04-19

### Fixed

- R1CS parser bounds check. Wire IDs exceeding `n_wires` in malformed
  R1CS files are caught gracefully.
- Timestamp safety. SMT dump timestamp uses `unwrap_or_default()`.
- cvc5-ff doc examples: import paths corrected from `cvc5::` /
  `cvc5_sys::` to `cvc5_ff::` / `cvc5_ff_sys::`.
- Removed duplicate `SolverFeedback::Sat` call on non-target SAT
  results. `SolverFeedback` simplified to `Verified` and `Skip`.

### Changed

- `resolve_named_constant` extracted to `propagation/mod.rs` (was
  duplicated in `binary01.rs` and `basis2.rs`).
- `constraint_to_smtlib_nia` extracted to `backends/mod.rs` (was
  duplicated in `z3_nia.rs` and `cvc5_nia.rs`).
- `RExpr::Mod` display now shows the modulus (`(expr mod p)`).

### Removed

- `sym.rs` and `csv` dependency. The `.sym` symbol map parser had no
  callers.
- Unused `range_vec` parameter from ABOZ and BIM lemma signatures.
- `SolverFeedback::Sat` variant.

## [1.3.0] - 2026-04-19

### Changed

- Zero-config cvc5 compilation. cvc5 (with CoCoA / finite-field
  support) is compiled from source during `cargo build`. The
  `cvc5-ff-sys` and `cvc5-ff` local crates handle source download,
  configuration (`--cocoa --gpl --auto-download`), and static linking.
- CLI: `--solver none` replaces `--nosolve`. Runs propagation only.
- CLI: `--lemmas` replaces `--noprop`. Accepts comma-separated lemma
  names (`linear`, `binary01`, `basis2`, `aboz`, `bim`) or
  `all` / `none`. Default: `all`.
- `run_dpvl` returns `Result`. No longer calls `process::exit`.

### Fixed

- Stable Rust compilation. Replaced nightly-only `is_multiple_of()`
  with `% 8 != 0`.
- cvc5 NIA `dump_smt` missing constraint serialisation.
- Replaced bare `.unwrap()` with `.expect()` in z3 model extraction
  and BigInt conversion.

### Removed

- CVC4 support (final cleanup; was already non-functional since
  v1.2.0).
- `--map` and `--precondition` CLI flags. Removed `precondition.rs`
  and the `serde` / `serde_json` dependencies.
- BabyJubJub lemma stub (`baby.rs`), constraint graph
  (`constraint_graph.rs`), CEX stub (`cex.rs`), and the `petgraph`
  dependency. See `docs/TODO.md`.
- Short lemma aliases (`l0`–`l4`).

### Added

- `docs/TODO.md`.

## [1.2.0] - 2026-04-18

### Changed

- Native solver API integration. Replaced subprocess-based solver
  invocation with direct Rust API calls to z3 and cvc5. Solvers are
  linked as libraries.
- CLI: `--solver <cvc5|z3>` and `--theory <ff|nia>` replace the prior
  single `--solver` flag. Default: `--solver cvc5 --theory ff`.
- CLI: `--dump-smt <dir>` replaces `--smt`. Dumps each solver query
  as an SMT-LIB file for debugging.
- Solver-agnostic IR. Introduced `UniquenessQuery` decoupling
  constraint encoding from solver-specific APIs.
- Three solver backends: `Z3NiaBackend` (QF_NIA), `Cvc5FfBackend`
  (QF_FF), `Cvc5NiaBackend` (QF_NIA). Each implements
  `SolverBackend` with `solve()` and `dump_smt()`.

### Removed

- CVC4 support.
- Subprocess solver invocation. `interpreter.rs` and `solver.rs`
  removed.

### Added

- `picus_smt::backends` module with `SolverBackend` trait.
- `picus_smt::query` module with `UniquenessQuery` IR and
  `build_query()`.
- `picus_smt::create_backend()` factory.
- `picus_smt::validate_combination()` for checking solver + theory
  compatibility.
- z3 solver bundled via the `vendored` feature.
- cvc5 links against a system-installed `libcvc5.so` (GPL build with
  CoCoA required).

### Prerequisites

- cvc5 GPL shared library must be installed system-wide (see README).
- z3 is bundled during `cargo build`.

## [1.1.2] - 2026-04-18

### Fixed

- cvc5 QF_FF correctness: disabled AB0 optimisation
  (`A * B = 0 → A = 0 ∨ B = 0`) for the cvc5 backend. cvc5 1.2.0–1.3.3
  has a bug where `or` disjunctions in QF_FF can produce spurious SAT
  results with inconsistent models.
- Propagation on parameterised circuits. Binary01 and Basis2 lemmas
  handle named constants (`ps1`, `ps2`, …) introduced by the SubP
  optimiser.
- Basis2 power-of-2 check for large bit widths.
  `is_power_of_2_sequence` failed when `2^k > p/2` because
  `min(c, p-c)` broke the ascending sequence. Now checks each
  coefficient or its field negation directly against powers of 2.
- Wire 0 constraint preservation. The simple optimiser replaced
  `Var("x0")` with `Int(1)` everywhere, turning the `x0 = 1`
  assertion into a tautology. An explicit `x0 = 1` assertion is now
  added for both witness copies.

### Verified

112 PLDI 2023 paper benchmarks pass (cvc5 1.3.3 GPL, QF_FF, weak
uniqueness). 13 baseline circuits pass (z3 4.13.4, QF_NIA, weak +
strong).

### Changed

- Removed the `--weak` / `--strong` distinction. Picus always checks
  uniqueness of output signals (weak uniqueness per the QED² paper).

## [1.1.1] - 2026-04-17

### Fixed

- Stack overflow on large circuits. DPVL iteration loop converted
  from recursion to iteration.
- Parser panic on malformed input. Replaced `.unwrap()` with `?` in
  the R1CS binary parser.
- Solver subprocess cleanup. Reads stdout / stderr in separate
  threads to prevent pipe deadlock, with hard-timeout kill as a
  safety net.
- Duplicate `p` / `ps1` / … declarations in SMT queries.

### Changed

- `bn128_prime()` is a `LazyLock<BigUint>`.
- Propagation lemmas mutate `&mut HashSet` in place (was: clone on
  every call).
- SMT prefix (definitions + constraints) pre-serialised once; solver
  calls only append the per-query block.
- `DpvlContext` struct introduced (was: 12-parameter functions).
- `RCmds.vs` renamed to `RCmds.commands`.
- `SolverKind` and `SelectorKind` implement `FromStr`.
- Shared utilities (`parse_var_index`, `RExpr::is_zero`,
  `RExpr::strip_mod`) extracted to common locations.
- Variable extraction unified into `collect_vars(mode)`.

### Added

- `RangeValue::is_empty()` for detecting over-constrained signals.
- `#[must_use]` annotations on pure functions.
- `picus info` subcommand for inspecting R1CS file metadata.

## [1.1.0] - 2026-04-17

### Added

- Complete Rust rewrite (previously Racket / Rosette).
- Four-crate workspace: `picus-r1cs`, `picus-smt`, `picus-analysis`,
  `picus-cli`.
- CLI with `check` and `info` subcommands.
- Three solver backends: z3 (QF_NIA), cvc4 (QF_NIA), cvc5 (QF_FF).
- Five propagation lemmas: Linear, Binary01, Basis2, ABOZ, BIM.
- Counter and first signal selection strategies.
- R1CS binary parser, `.sym` symbol map parser, JSON precondition
  parser.
- Three SMT optimisation passes: AB0, normalise, SubP.

### Removed

- Racket / Rosette source.
- Docker build infrastructure (re-added in v1.5.0).
- Research artifact batch scripts.
