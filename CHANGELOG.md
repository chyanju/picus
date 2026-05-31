# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/). Entries are telegraphic: one line per change — what changed plus the key term/API — with no narrative, mechanism explanations, or "no verdict change" boilerplate.

## [1.8.21] - 2026-05-30
- `radical_membership` (default off): monolithic-GB whole-ring Safe filter — decides `x_a − x_b ∈ √I` (Rabinovich) on the combined query system instead of reducing against the non-GB partition union; sub-budget bounded, one-sided over GF(p).

## [1.8.20] - 2026-05-30
- `membership_fastpath` (default on): reduce a uniqueness query's `x_a − x_b` against the cached split-GB constraint basis; a zero remainder proves membership and returns Safe without the Rabinowitsch extend (exact radical membership for primes ≤ 1000, else one-sided Safe filter). PLDI A/B −2.9% total, identical verdicts.
- `dynamic_order` (default on): size-adaptive term order — alt-copy elimination order for rings ≥ `encoder::DYNAMIC_ORDER_MIN_VARS`, DegRevLex below. PLDI A/B −3.1% total, identical verdicts.
- `signature_criterion` (default off): GVW signature Gröbner engine (Schreyer signatures, signature-safe reduction, syzygy / rewrite / singular criteria) replacing the per-pair run on rings ≥ `buchberger::GVW_MIN_VARS`. 300-seed differential oracle ≡ per-pair reduced GB; benchmark-neutral.
- `matrix_elim_order` (default off): matrix-defined monomial orderings (`ff::matrix_order::MatrixOrder`, interned index) + alt-copy elimination order for the split-GB.
- `zech_log_small_fp` (default off): Zech discrete-log multiply / inverse / power tables for prime fields ≤ `ff::field::ZECH_LOG_MAX_PRIME` (2²⁰); result-identical, opt-in for inverse-heavy small-prime arithmetic.
- Nonzero-constant generator short-circuits to UNSAT before partition building and the split-GB fixpoint (cvc5 `postRewriteFfEq` analogue); exact one-element core.

## [1.8.19] - 2026-05-29
- Soundness: `gb::model::compute_candidates` Case 2.5 routes zero-dimensional ideals through `fglm_to_lex_cancel` + triangular DFS before the round-robin fallback; an exhausted DFS yields the new `Brancher::ProvedUnsat`. `fglm_to_lex_cancel` adds cancel-token plumbing to the BFS staircase walk. `picus_core::profile::IDEAL` counters track `is_zero_dim` / `quotient_dimension` calls under `gb_stats`.
- Perf: `--f4-hilbert-select` and `--f4-sparse-reducer-cache` flip default on (inert when `--use-f4` is off). PLDI corpus differential under `--use-f4`: −1.3% total wall-clock, 0 verdict regressions, EdDSAPoseidonVerifier −55% (3349 → 1500 ms), EdDSAMiMCVerifier −21%, EdDSAVerifier −24%, EdDSAMiMCSpongeVerifier −4%, no fixture-level regression > 200 ms. Cyclic-{4,5,6} flat within noise; katsura-{4,5} flat to marginal improvement.
- New: `cdclt::multi_prime::FfTheoryRouter` orchestrator wire under `--cdclt-multi-prime-router` (single-slot for single-prime input; aux-var filter in `notify_fact`). SMT-LIB multi-prime acceptance via `smt2::parse_boolean_multi` (per-prime subset rebuild) + `cdclt::orchestrator::solve_formula_multi` (per-prime `tseitin` against a shared SAT solver, `FfTheoryRouter` dispatch).
- New: `cdclt::ff_theory_incremental::IncrementalFfTheoryState` orchestrator wire under `--cdclt-incremental-theory`. Model extraction bridge re-wraps live `IncrementalGB::basis()` on a user-namespaced facade ring and delegates to `gb::model::find_zero_cancel`; BN254 single-pinned-eq inputs now extract Sat with the user binding instead of returning Unknown. `pinned_vars_for` / `eval_key_under_pinned` / `compute_tier1_for` / `compute_tier2_for` lifted from `FfTheory` as `pub(crate)` free functions so the incremental theory reuses the propagation substrate verbatim. `LARGE-PRIME GAP` comment block + field-poly invariant `debug_assert!` (slot-claimed ⇒ basis non-empty under `add_field_polys`) guard the large-prime slot-claim hazard class.
- New: `cdclt::ee_filtered::EeFilteredTheory<T>` generic wrapper under `--cdclt-equality-engine`. `EqualityEngine::polarity_witness` + `prior_witness(rep)` + `rep_of(var)`; `EeFilteredTheory.pending_contradiction` snapshots per push level so a polarity conflict at notify time surfaces a precise 2-literal `{atom, witness}` core at `post_check`. EE corpus differential: −0.38% total, 0 verdict regressions, EdDSAMiMCVerifier −21% clean win, EdDSAMiMCSpongeVerifier +1.7% borderline → kept default off.
- New: `HilbertNum::add_generators_incremental(existing_gens, new_gens)` BCR colon recursion `N(I ∪ {g}) = N(I) − t^deg(g) · N(I:g)`. `BuchbergerState::select_sugar_hilbert` caches `N(I)` once per selection and consults the incremental update per candidate, lifting `HILBERT_SELECT_BASIS_CAP` from 50 to 250.
- New: `F4Workspace.reducer_cache` switches to `HashMap<MonoKey, usize>`; per-entry memory drops from O(n_terms × n_vars) to one `usize`, rematerialising the reducer via `basis[bi].poly.mul_term(m / LT(basis[bi]), 1)` at hit time.
- `linear_elim` default-off retained after PLDI corpus differential: +3.3% total, 0 verdict regressions, 7 fixtures ≥ 200 ms regression (BinSum / BinSub 80×, EdDSA family 1.3–1.6×, Pedersen +2.9 s), zero clean wins. Docstring on `RuntimeConfig::linear_elim` records the measurement.
- `IncrementalFfTheoryState::engine_stats` surfaces the wrapped `IncrementalGB`'s `GbProfileCounters` for amortisation regression tests (`audit_inc_deep_dfs_amortizes_gb` asserts `reductions_useful < 8N` over N push/notify/post_check cycles).

## [1.8.18] - 2026-05-29
- Perf: `--frobenius-cache` and `--branching-incremental-gb` (both default on); thread-local `x^p mod poly` memo keyed on `(prime, coeffs)`, and per-DFS branch GB extension via `compute_gb_incremental_with_order`. Same-binary A/B over PLDI: ON beats OFF by −3.2 s wall-clock, 0 verdict regression (Pedersen@pedersen −2.18 s, EdDSAMiMCSpongeVerifier −604 ms, EdDSAPoseidonVerifier −113 ms, BabyDbl −93 ms).
- New cdclt submodules: `ff_theory_incremental::IncrementalFfTheoryState` (cross-decision `IncrementalGB`, Rabinowitsch disequalities, `x^p − x` injection on prime ≤ 1000), `multi_prime::FfTheoryRouter` (per-prime atom partitioning over `check_full_with_atoms` with UNSAT-core union), `equality_engine::EqualityEngine` (union-find atom dedup keyed on canonical polynomial bytes).
- Soundness (`IncrementalFfTheoryState`): `push` snapshots `name_to_slot` / `next_slot` / `diseq_counter` / `degraded` per level (was: slot table leaked past `pop` ⇒ reused slot skipped `x^p − x` re-injection ⇒ GF(5) `x^2 = 2` flipped UNSAT to Sat); `notify_fact` computes polys before mutating the trail and flips a sticky `degraded` (`post_check` ⇒ Unknown) on unregistered atom or slot-budget exhaustion. Regressions: `bug_inc_pop_restores_slot_claims_gf5`, `bug_inc_notify_fact_slot_budget_exhausted_returns_unknown`, `bug_inc_notify_fact_unknown_atom_returns_unknown`.
- Soundness (`FfTheoryRouter`): `degraded` + `degraded_levels` lockstep stack (debug-asserted) replaces silent drop on unregistered `notify_fact`. Regressions: `bug_router_unregistered_fact_degrades_to_unknown_not_sat`, `bug_router_pop_restores_degraded_flag`.
- Soundness (`EqualityEngine`): `register_atom` returns `RegisterOutcome::{Ok, Contradiction}` and reports the union of two opposite-polarity singleton classes (was: silent merge lost the conflict). Regressions: `bug_register_atom_surfaces_orphan_polarity_conflict`, `bug_register_atom_merges_opposite_polarity_classes_reports_contradiction`.

## [1.8.17] - 2026-05-29
- Soundness: `sat::Solver::solve` drains root-level propagation after `perform_restart` and returns `Unsat` on a root conflict (was: post-restart root unit left unpropagated, root conflict analyzed at level 1 ⇒ wrong `Sat` under aggressive restart). Regression `audit_solve_sound_under_aggressive_restart`.
- Workspace lib unit-test coverage 83.02% → 91.92%: picus-analysis 5.60% → 90.40%, picus-smt 2.01% → 85.94%, picus-r1cs 74.63% → 98.16%, picus-core 83.58% → 87.20%, picus-solver 87.90% → 97.59%. 1874 lib tests total.
- Test layout: large sibling files split by prefix; `smt2/tests.rs` → `tests.rs` + `tests_session.rs` + `tests_property.rs`; `split_gb/tests.rs` → `tests.rs` + `tests_prop.rs` + `tests_hard.rs`; `frontend/encoder_tests.rs` → `encoder_tests.rs` + `encoder_tests_spec.rs`.
- Sibling test files added for previously-untested algorithmic modules in `picus-analysis` (propagation/aboz/bim/basis2/binary01/linear/range/lemma + dpvl + selector), `picus-smt` (poly_ir, native_ff, native_lower), `picus-r1cs` (parser, grammar), and `picus-core` (dense_reduce, sparse_geobucket, sparse_monomial).

## [1.8.16] - 2026-05-28
- Test layout: unit tests move to sibling files (`mod.rs`→`tests.rs`, leaf→`<name>_tests.rs`); no inline `mod tests {}` blocks remain in `src/`.
- Integration tests renamed by scenario; `cdclt_regression` split into `cdclt_vs_dnf_parity` + `cdclt_scenarios`; `cvc5_*` corpus/unit files renamed.
- 3 semantically-unit `tests/*.rs` (parse, uni-roots, split-gb) reverse-migrated to `src/` siblings.
- Regression tests gain `audit_`/`bug_` fn-name prefixes for `cargo test <prefix>` filtering.

## [1.8.15] - 2026-05-28
- Profiling refactor: instrumentation moves to a `metric::` DSL (`incr!`/`add!`/`max!`/`timer!`/`timer_local!`/`gate!`/`stopwatch!`/`clock!`/`def!`/`bump!`/`scope!`/`trace!`/`next!` + `#[metric]` proc-macro in the new `picus-metric-macros` crate) replacing the hand-cached `if gb_stats_enabled() { ... }` / bare `Instant::now()` / `ScopedTimer::new` pattern across solver, `native_ff` backend, and `dense_reduce` / `geobucket` hot paths; `metric::gate!` caches the flag once for per-monomial timers.
- Buchberger engine telemetry strictly separated from logic: new always-on logic field `BuchbergerState::useful_reductions` drives the interreduce schedule; `GbEngineStats` renamed to `GbProfileCounters`, field `stats` renamed to `profile`, all writes routed through gb-stats-gated `metric::scope!`; `engine_stats()` returns the pure-telemetry bundle (`&GbProfileCounters`).
- `compute_gb_dispatch` gets `#[metric]`; `compute_gb_with_order`'s `log::trace!` drops the hand-timed `Instant` substring — timing through the metric channel, log channel keeps the operator diagnostic.
- Maintainability: removed seven unused `observe_*_max` methods (superseded by `metric::max!` lowering to the free `observe_max`), the unused `metric::flush!` macro, and the unused `log` dep in `picus-core`; ~200 added unit/integration tests pushing modules past 85% coverage (`incremental_context`, `split_gb/{search,fixpoint,branching}`, `gb/ideal/engine`, `buchberger/{mod,incremental}`, `smt2/{session,tokenizer,parser}`, `brancher`, `spair`, `criteria`, `sparse_gb`, `f4_matrix`, `constraint_system`, `bitsum_extract`, `cdclt`, `gb_incremental`, `gb_model::verify_model`, `gb_mod` public API); `scripts/coverage.sh` for reproducible per-crate coverage.

## [1.8.14] - 2026-05-28
- Soundness: `linsolve::eliminate_linear` passes through on an empty linear GB without cancellation (engine error); SMT-LIB parsers (`parse`/`parse_boolean`/`SmtSession`) infer the session prime from `#fNmP` literal moduli and reject `ff.*` without an inferable prime (was: defaulted to 2); `parse_ff_const` validates the literal's `P` matches.
- `sat::Solver::analyze`/`::propagate` route 1-UIP trail exhaustion and watched-literal enqueue-of-non-Undef through `give_up`→Unknown in release (was `debug_assert!`-only).
- Doc: `sparse_gb::groebner_basis(_incremental)` cancel return is a sub-ideal; `digest_constraint_side` ~2⁻¹²⁸ is benign-collision only (`DefaultHasher` fixed key).

## [1.8.13] - 2026-05-27
- Soundness backstops: cached SAT verdicts now re-verify the model against `bitsum_polys` (the non-cached `core::solve_split_gb_cancel` path already did); `verify_model` returns `false` on a model missing an appearing variable (was defaulted to zero, which could vacuously pass a narrow check).
- `R1csFile::constraint_to_string` returns a placeholder on an out-of-range id (was index panic); F4 S-poly extraction debug-asserts on the unreachable "leads on a reducer column" branch (silent skip would drop a generator and weaken the ideal); `cvc5_compare` arg parser reports a usage error on a trailing flag with no value (was index panic).
- Maintainability: single-sourced the split-GB propagation iteration cap (`max_fixpoint_iters`), the SMT-LIB `declare-fun`/`declare-const` scan (`classify_declare`), and the CDCL(T) UNSAT-core back-mapping (`map_core_to_atoms`); removed unused `GbTracer` API (`checkpoint`/`restore`/`next_input_idx`/`unsat_core_for_trivial`/`deps_of`); documented the `SolverKind` dispatch-vs-selection checklist.

## [1.8.12] - 2026-05-27
- `DensePoly::from_raw_sorted` drops the total-degree-monotonicity debug assert (invalid under Lex) — fixes a debug/test-build panic on the Lex model-extraction reduction path.
- SMT-LIB term builders (`build_poly`/`build_poly_with_ctx`) reject a zero-argument `-` instead of indexing out of bounds (was a `run_smt2` process abort).
- Maintainability: `encode_impl` derives the bitsum aux index from `bitsum_aux_index` (was a debug-only cross-check); single-sourced `propagation::mod_inverse`, the split-GB partition layout (`build_partitions`), and the GB `resolve_strategy`; removed dead guards (`bim` bound, `binary01` subsumed disjunct, `_GbBaseRing`); fixed all picus-core rustdoc intra-doc links.

## [1.8.11] - 2026-05-27
- `set_target` asserts a non-input uniqueness target in release builds (was debug-only); split-GB SAT models are re-verified against the bitsum polynomials in addition to the original generators.
- Sparse Gröbner-basis path (the default representation) wraps the engine in `catch_unwind`, degrading a panic to an empty basis → `Unknown` via `finish_gb` (was a process abort); matches the dense path.
- `linalg` echelon `expect`s that a nonzero leading coefficient is invertible (was a silently unnormalized pivot row); `min_poly_cancel` uses the cancel-aware reduction.
- Single-sourced the bitsum aux-variable index (`bitsum_aux_index`), the geobucket reducer thresholds (`ReducerIndex`), and the split-GB self-membership memo seeding (`seed_self_membership`); added dense incremental-vs-from-scratch GB, encoder `n_diseq > 0` bitsum, and lowering copy-symmetry tests.

## [1.8.10] - 2026-05-27
- SMT-LIB parser caps S-expression nesting and `define-fun` expansion depth (stack overflow → malformed-input error); `ff.mul` exponent overflow returns a parse error instead of panicking.
- R1CS parser accepts a non-multiple-of-8 `field_size` (1-byte small primes, e.g. GF(7)).
- `PolyIR::set_target` debug-asserts a non-input target; `Counter` selector tie-breaks by wire index; cvc5/z3 backends error instead of dropping a target disequality on a missing copy variable.
- Maintainability: removed the `IrPolyRing` facade and a dead `FieldElem` drop guard; single-sourced the `(_ FiniteField N)` sort detection and disequality-witness naming; `serde_json` to workspace deps; by-homog reduced-GB differential test.

## [1.8.9] - 2026-05-27
- Soundness (false UNSAT, small primes): bit propagation gates the bitsum bit-pinning on `2^len <= p` (shared `bitsum_fits`) in both phases, so a modular collision (GF(7): `0b111 ≡ 0b000`) no longer prunes a satisfying assignment; +2 GF(7) regression tests.
- R1CS section-table parser computes section ends with `checked_add` (rejects a near-`usize::MAX` size instead of wrapping past the bounds check).
- Split-GB `Ideal` routes through `compute_gb_with_order`, so `poly_repr` (sparse default) and the `finish_gb` cancel/error/backup contract apply to the split-GB solve.
- `--gb-strategy` flag (`--gb-by-homog` kept as a hidden alias).
- Single-sourced the split-GB propagation decision, univariate-coefficient extractor, round-robin brancher, and bitsum chain-length cap; `BitProp::get_bit_equalities` takes `&self`; four engine files split into re-exported submodules; added a config-overlay drift guard and an F4-vs-per-pair reduced-GB differential test.

## [1.8.8] - 2026-05-26
- R1CS parser bounds the header wire/IO counts before allocating (`HeaderImplausible`; iden3 invariants `1 + n_pub_out + n_pub_in + n_prv_in <= n_wires`, `n_wires <= w2l.labels.len()`).
- `IncrementalGB::pop` restores the basis polynomial bodies, not only the active flags.
- Incremental-solver cache key is a 128-bit digest (was 64-bit), so a constraint-side collision can't yield an unsound UNSAT.
- SMT-LIB front end rejects an `=`/`distinct` chain mixing Bool and FF sorts; the tokenizer errors instead of indexing out of bounds on a truncated stream.
- BIM lemma accumulates repeated-wire coefficients (mod p) instead of keeping only the last.
- Witness output filters internal aux variables (`__w_diseq_*`, `__bitsum_*`).
- Removed dead code (`Solver::add_theory_lemma`, `Theory::level`); single-sourced the geobucket cascade constants, Fermat inverse, GB-entry error/cancel fallback, and disequality witness naming.

## [1.8.7] - 2026-05-26
- Soundness (false UNSAT): `BitProp::is_bit` is a pure query — it no longer caches a per-basis `x^2 - x ∈ I` proof into the persistent global bit set (never rolled back on split-GB backtrack), which let a sibling branch derive a spurious bitsum-overflow contradiction; +GF(7) regression test.
- Dense geobucket reduction re-attaches the in-flight leading term before draining on cancellation (matches the indexed/sparse paths); was dropped.
- SMT-LIB rewriter and naive reduction oracle accumulate exponents with `checked_add` (`u16` discipline).
- cvc5 backend refuses a query carrying `assignments`/`bitsums` it does not lower (`Unknown(IncompleteTheory)`), matching the NIA backends.
- Incremental solver falls back to a stateless solve when a cached ring cannot resolve a disequality variable.
- Documented the copy-symmetry lowering invariant at the emission site and on each wire-keyed lemma; `split_model` echoes shared inputs into the second witness.

## [1.8.6] - 2026-05-26
- Traced incremental GB (`compute_gb_incremental_with_order_traced`) returns an empty basis on a genuine engine error (not the unreduced generators), matching its non-traced sibling, so a non-GB can't be consumed as a GB.
- aboz zero-product lemma emits each alt-copy disjunction over the variable in that copy's constraint (`x_w` for an input wire), not the unconstrained `y_w`.
- R1CS parser rejects a field modulus ≤ 1 (`InvalidPrime`).
- SMT-LIB term builder accumulates exponents with `checked_add` (`u16` discipline).
- `Solver::learn_clause` enforces its non-empty precondition in release builds.

## [1.8.5] - 2026-05-26
- CDCL(T) maps a theory UNSAT core to trail atoms via per-polynomial provenance (`EncodedSystem::poly_provenance`), not an assumed positional layout; an unattributable index falls back to the full trail core.
- `compute_gb_*` distinguishes cancellation from a genuine engine error: an error yields an empty basis (not the unreduced generators), so a non-GB can't be consumed as a GB.
- `fglm_to_lex` verifies the staircase size against the Hilbert quotient dimension in release builds, returning `None` (→ direct Lex) on mismatch.
- `interreduce` de-duplicates equal-leading-monomial elements (dense and sparse).
- Sparse Buchberger reduction is cancel-aware (`reduce_by_refs_cancel`).
- `CancelToken` evaluates timeouts / `either` lazily in `is_cancelled()` instead of spawning a watcher thread per token.
- `native_ff` installs its panic-silencing hook once per process.
- `enqueue_theory` rejects a stale theory reason in release builds.
- `r1cs_to_poly_ir` validates `target_signal` against the wire count (`WireOutOfBounds`).
- QF_NIA backends (`cvc5_nia`, `z3_nia`) return `Unknown(IncompleteTheory)` for disjunctions/assignments/bitsums they do not lower.

## [1.8.4] - 2026-05-25
- Unified the Gebauer–Möller M/B-criteria and S-pair queue merge into a representation-agnostic `ff::spair_criteria` module (shared by the dense and sparse Buchberger engines).
- `ff::buchberger` factors out `build_spoly` / `deactivate_superseded` (shared across per-pair, F4, seeding).
- CDCL(T) main loop is generic over the `Theory` trait; removed the unused `Effort` / `pre_check` scaffolding.
- `PolyIR` depends only on `picus-core`: its native-engine lowering moves to the native backend.
- `FfPolyRing` reads field / variable count / names from the shared ring context.
- `run_dpvl` returns a typed `DpvlError`; `PicusError` gains a `Dpvl` variant.
- Removed the unused `SolverMode` enum and `solve_encoded_with_mode`.

## [1.8.3] - 2026-05-25
- Split-GB UNSAT core is a sound conservative over-approximation (union of a partition's original inputs), closing an under-approximation hazard; consumed only by the CDCL(T) path, so verdicts are unchanged.
- Univariate root-finding returns `(roots, complete)`; the brancher and model search treat an incomplete Cantor–Zassenhaus split as inconclusive (→ round-robin → `unknown`), never as infeasibility.
- CDCL(T): a theory core mapping to no trail atom falls back to the full trail; an unassigned theory-core literal yields `unknown` instead of a panic.
- `--selector first` selects the smallest unknown signal index (deterministic).
- Renamed the engine error `SolverError` → `EngineError`; `new_with_repr` sets the representation explicitly; added Goldilocks (`u64` arm above 2^63) and F4-vs-per-pair differential tests and a config drift guard.

## [1.8.2] - 2026-05-25
- `ff::hilbert::quotient_dimension` + `Ideal::quotient_dimension`: `dim_k(R/I)` from the basis leading terms via the graded Hilbert function; cross-checks the FGLM staircase.
- Geobucket reducer reads each divisor's leading coefficient lazily (only the selected divisor).
- Incremental GB extends run the per-pair engine; F4 (`use_f4`) is used only for from-scratch GB.
- New config keys / CLI flags (default off): `split_triangular` (`--split-triangular`, triangular model construction on the split-GB path) and `reducer_index_cache` (`--reducer-index-cache`, cache the divisor index across reductions with an unchanged basis).

## [1.8.1] - 2026-05-25
- Removed the `PICUS_*` runtime environment overrides (`PICUS_USE_F4`, `PICUS_POLY_REPR`, `PICUS_BOOLEAN`, `PICUS_DNF_CAP`, `PICUS_CDCLT_ITER_CAP`, `PICUS_GB_STATS`, `PICUS_GB_TRACE`, `PICUS_PROFILE`, `PICUS_NO_INCREMENTAL_CACHE`, `PICUS_NO_ABOZ_DISJ`). Every engine knob is now set through the config file (`--config` / `./picus.toml`) or a CLI flag only; config resolves as built-in defaults < file < CLI. Build-time locators (`CVC5_LIB_DIR`, …) are unaffected.

## [1.8.0] - 2026-05-25
- Default solver is `native` (was `cvc5`): a bare `picus check` / `Config::default()` works without opt-in features. `cvc5` / `z3` need their features and an explicit `--solver`.
- Workspace `default-members` excludes `cvc5-ff` / `cvc5-ff-sys` / `z3`; default commands compile only the native solver.
- Layered configuration (defaults < config file < `PICUS_*` env < CLI flags); `--config <FILE>`, auto-loaded `./picus.toml`, documented `picus.default.toml`.
- Public `Config` is `PicusConfig { analysis, engine }`; `EngineOverlay` / `DpvlOverlay` carry the partial layers (serde + TOML).
- `poly_repr` and the `aboz` disjunction toggle become config keys / CLI flags (`--poly-repr`, `--no-aboz-disj`); `--gb-stats` added.
- Docker image is native-only; docs reorganised (slimmer README, `docs/usage.md`, `docs/building.md`; removed `docs/TODO.md`).

## [1.7.35] - 2026-05-25
- New `picus-core` crate holding the shared GF(p) algebra (`ff` field / monomial / dense+sparse polynomials / reduction, the `poly` ring facade), runtime `config`, `timeout::CancelToken`, and `profile`, extracted from `picus-solver`. `picus-solver` keeps the Gröbner / CDCL(T) engine and depends on `picus-core`; `picus-analysis` depends on `picus-core` instead of `picus-solver`.
- `picus-solver` modules grouped into `gb/` (ideal, GB drivers, model, brancher, tracer, roots, homogenisation) and `frontend/` (encoder, parse, rewriter, bitprop, bench_fixtures); large inline test modules externalised to sibling `tests.rs` files.
- `GbStrategy` moved from `ideal` to `config`; removed the `field.rs` alias shim (`FfField` / `FfEl` → `PrimeField` / `FieldElem`).
- `GbStrategy::ByHomog` is honoured on the sparse representation (sparse homogenise → GB → dehomogenise pipeline); `last_dispatched_algorithm` records on both representations.
- `#[inline]` on the hot cross-crate algebra methods (field, monomial, polynomial term accessors) so they inline into the engine without link-time optimisation.
- `docs/architecture.md` updated for the new crate and module layout.

## [1.7.34] - 2026-05-24
- Sparse Gröbner engine (`ff::sparse_gb`) brought to parity with the dense engine's pair management: product (coprime) + Gebauer-Möller M + Buchberger B criteria, sugar-degree pair selection, and cooperative cancellation (the sparse path now honours `--timeout`).
- `ff::sparse_geobucket`: geobucket reduction (Yan 1998) for `SparsePolynomial`, replacing the naive accumulator's O(n) leading-term removal and per-step re-merge.
- Incremental seeding on the sparse path (`sparse_gb::groebner_basis_incremental`): `ideal::compute_gb_incremental_with_order` extends a trusted reduced GB with cross / intra-new S-pairs instead of recomputing the union.
- `SparseMonomial::divmask`: presence-based 128-bit divisibility prefilter (hashes every variable, vs the dense first-128-variables scheme) used in the criteria and geobucket divisor selection.

## [1.7.33] - 2026-05-24
- Runtime dense/sparse polynomial representation (`config::ReprKind`, `PICUS_POLY_REPR`, default `sparse`): `Polynomial` is a `Dense(DensePoly)` / `Sparse(SparsePolynomial)` enum; sparse stores only nonzero `(var, exp)` pairs (O(nnz) per term), keeping the IR and native solve resident-sparse on wide rings where the dense per-term exponent vector is O(n_vars). Arm fixed per ring by `PolyRing::repr`.
- Sparse Gröbner engine `ff::sparse_gb` (Buchberger + inter-reduction) and `SparsePolynomial` reduction; `ideal.rs` GB entry points route through it under the sparse representation, dense path unchanged.
- `ff::repr_oracle` differential tests: sparse monomial/polynomial ops and reduced Gröbner bases checked against the dense implementation; suite green under both representations.
- Propagation lemmas (`binary01`/`linear`/`bim`/`aboz`) read terms via the nonzero `(var, exp)` accessor instead of a per-term `0..n_vars` scan.

## [1.7.32] - 2026-05-23
- Single index-keyed `ConstraintSystem` + `ConstraintSystemBuilder`; `PolyIR::to_constraint_system`/`encode` lower to it; `compact_used_vars` drops unreferenced variables.
- `basis2` recognises circomlib `CompConstant` + AliasCheck and relaxes the `2^n > p` gate so bit decompositions propagate.
- Learned disjunctions route through both backends (native `BooleanQuery`, cvc5 `(or …)`); `aboz` emits the zero-product disjunction.
- `sat::Solver` resolves non-asserting theory conflicts via 1-UIP; `analyze` returns `Option` instead of panicking. Removed the dpvl `x_target ≠ y_target` re-check before `Unsafe`.
- Vendored cvc5 `1.3.1` → `1.3.4` (finite-field split-solver soundness fix).

## [1.7.31] - 2026-05-22
- Pluggable SMT backends via an `inventory` registry (`create_backend_by_name`); `SolverResult::Unknown(reason)`.
- Cancellation: `CancelToken::either`, `solve` takes a token, mid-solve cancel in `native_ff`.
- Soundness gates: `aboz` (`excludes_zero`), `basis2`/`auto_extract_bitsums` (`2^n ≤ p`), `native_ff` small-prime field polys.
- Hardened R1CS parser (`Truncated`/`HeaderImplausible`, bounds-checked slices/capacities); `r1cs_to_poly_ir` returns `Result`.
- All `RuntimeConfig` fields exposed via `picus::Config` + CLI flags; Cargo features `cvc5`/`z3`/`native`. All public GB entry points route through `compute_gb_dispatch`.

## [1.7.30] - 2026-05-22
- `PolyIR` solver-agnostic IR over GF(p); `r1cs_to_poly_ir` one-pass lowering.
- Plugin propagation lemmas (`PropagationLemma` + `inventory`); thread-local `RuntimeConfig`.
- `GbAlgorithm` trait (`BuchbergerDirect`/`BuchbergerByHomog`); `SolverBackend` consumes `&PolyIR`.
- Lowering uses the parsed header prime instead of hard-coded BN128.
- Removed legacy `query`/`optimizer`/`r1cs_parser` and the `picus-r1cs::grammar` AST.

## [1.7.29] - 2026-05-22
- `sat::solver` and module docs rewritten; removed the unused `ff::f4::sparse_sub_scaled`.

## [1.7.28] - 2026-05-22
- `PrimeField`/`FieldElem` gain a `u64`/`u128` backend for primes ≤ 64 bits (larger stay on GMP).

## [1.7.27] - 2026-05-22
- `ff::hilbert` module (`hilbert_numerator`, Bigatti–Caboara–Robbiano); F4 engine stats + scratch-buffer reuse; `F4_MIN_BATCH` 4 → 12.

## [1.7.26] - 2026-05-21
- `F4Output` carries per-row provenance, keeping the F4 UNSAT-core path sound; `DivMask` prefilter on `F4BasisRef`.

## [1.7.25] - 2026-05-21
- `smt2::SmtSession` — persistent SMT-LIB v2 session (push/pop, get-unsat-core, `:tlimit-per`).
- Fixed declaration-order Bool constraints, undeclared `get-value`, and `(reset-assertions)` vs `(reset)`.

## [1.7.24] - 2026-05-21
- `smt2` Bool atoms, `(ite …)`, `(define-fun …)`, `(xor …)`, negative FF constants, `ff.bitsum`.
- Fixed CDCL(T) losing the asserting literal on conflict paths and an unsound split-GB UNSAT core.

## [1.7.23] - 2026-05-21
- `FfTheory` two-tier theory propagation with cached reasons; `orchestrator::run_theory_propagation`.

## [1.7.22] - 2026-05-21
- `sat::Solver` VSIDS, phase saving, max-heap decisions, Luby restarts.
- Fixed `AtomKey::from_eq` mod-reduction underflow and an `Undef`-branch spurious UNSAT.

## [1.7.21] - 2026-05-20
- `sat` (CDCL) and `cdclt` (CDCL(T)) modules — equality-atom interning, Tseitin CNF, `FfTheory`, `solve_formula`.

## [1.7.20] - 2026-05-20
- `rewriter` (cvc5-style FF normalisation) and `boolean` (`Formula`, NNF/DNF, `solve_boolean_query`) modules; traced split-GB UNSAT core.

## [1.7.19] - 2026-05-20
- Per-divisor `use_count` reorders the active basis; removed stale `docs/`.

## [1.7.18] - 2026-05-20
- Fixed split-GB bitprop leaving `bitsums` empty (range-check timeouts); coprime S-pair drop at generation.

## [1.7.17] - 2026-05-20
- `auto_extract_bitsums` folds bit-decomposition chains; `smt2::parse` over a QF_FF subset; `run_smt2` binary.

## [1.7.16] - 2026-05-20
- 17-circuit circomlib verdict integration test; `encode_constraint_side` with cached lazy Rabinowitsch.

## [1.7.15] - 2026-05-01
- Thread-local `FieldElem` pool; 128-bit `DivMask`; `IncrementalGB` resume primitives; F4-lite scaffolding.

## [1.7.14] - 2026-04-28
- `IncrementalSolverContext` solver-state cache; hash-bucketed divisor index (≥ 64 divisors).

## [1.7.13] - 2026-04-28
- Memoized cross-basis containment (`content_hash`); move-based polynomial merge.

## [1.7.12] - 2026-04-28
- GMP backend via `rug`; cancel-token propagation through reduction hot paths.

## [1.7.11] - 2026-04-28
- Buchberger B-criterion at basis-add; skip inactive basis elements during S-pair generation.

## [1.7.10] - 2026-04-28
- Geobucket reduction (`ff/geobucket.rs`); Gebauer-Möller M-criterion.

## [1.7.9] - 2026-04-27
- Soundness: `Unsat` mapping, `u16` exponent overflow `checked_add`, `from_i64(i64::MIN)`; split-GB iteration cap.

## [1.7.8] - 2026-04-27
- In-tree finite-field GB engine (`picus-solver/src/ff/`); `feanor-math` dependency removed.

## [1.7.7]
- Buchberger overhaul (inter-reduce once at termination, one-at-a-time S-pairs); ring built once per solve.

## [1.7.6] - 2026-04-24
- In-place Buchberger restart; Hilbert numerator engine; GB statistics/profile modules.

## [1.7.5] - 2026-04-23
- Yan-style geobucket reduction; BigInt scratch pool.

## [1.7.4] - 2026-04-22
- Gebauer-Möller pair management; `DivMask` prefilter; multi-basis branching in split-GB search.

## [1.7.3] - 2026-04-22
- Degree-overflow crash fix; `NativeFfBackend` `catch_unwind` → `Unknown`; >5000-variable reject.

## [1.7.2] - 2026-04-21
- UNSAT-core tracing (`GbTracer`); `solve_single_gb` returns a precise core.

## [1.7.1] - 2026-04-21
- Native finite-field solver crate (`picus-solver`), a pure-Rust QF_FF replacement; `--solver native`.

## [1.7.0] - 2026-04-19
- Benchmarks moved to a submodule; z3 `timeout_ms` saturating-cast fix.

## [1.6.0] - 2026-04-19
- `picus` library crate (`check_circuit`/`check_r1cs_bytes`/`check_r1cs`); `picus-cli` depends on the facade.

## [1.5.1] - 2026-04-19
- `--lemmas` gains `all-X,Y` / `none+X,Y` syntax.

## [1.5.0] - 2026-04-19
- Multi-stage Dockerfile; `--format human|json`; coloured output.

## [1.4.0] - 2026-04-19
- R1CS wire-ID bounds check; removed `sym.rs` and the `csv` dependency.

## [1.3.0] - 2026-04-19
- Zero-config cvc5 compilation from source; `--solver none`/`--lemmas` replace `--nosolve`/`--noprop`; dropped CVC4.

## [1.2.0] - 2026-04-18
- Native solver API integration (direct z3/cvc5 calls, was subprocess); `--solver` + `--theory` flags.

## [1.1.2] - 2026-04-18
- cvc5 QF_FF: disabled the AB0 optimisation (spurious SAT in cvc5 1.2.0–1.3.3); Basis2 large-bit-width fix.

## [1.1.1] - 2026-04-17
- Stack-overflow fix (DPVL recursion → iteration); parser panic fix; `picus info` subcommand.

## [1.1.0] - 2026-04-17
- Complete Rust rewrite (from Racket/Rosette); four-crate workspace; z3/cvc4/cvc5 backends; five propagation lemmas.
