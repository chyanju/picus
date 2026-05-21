# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

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
