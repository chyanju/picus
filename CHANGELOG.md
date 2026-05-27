# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

## [1.8.10] - 2026-05-27
- SMT-LIB parser caps S-expression nesting and `define-fun` expansion depth (stack overflow → malformed-input error); `ff.mul` exponent overflow returns a parse error instead of panicking.
- R1CS parser accepts a non-multiple-of-8 `field_size` (1-byte small primes, e.g. GF(7)).
- `PolyIR::set_target` debug-asserts a non-input target; `Counter` selector tie-breaks by wire index; cvc5/z3 backends error instead of dropping a target disequality on a missing copy variable.
- Maintainability: removed the `IrPolyRing` facade and a dead `FieldElem` drop guard; single-sourced the `(_ FiniteField N)` sort detection and disequality-witness naming; `serde_json` to workspace deps; by-homog reduced-GB differential test.

## [1.8.9] - 2026-05-27
- Fixes a finite-field solver soundness bug (a false UNSAT — a falsely "safe" verdict) on small primes, plus an R1CS parser robustness fix and a representation-routing fix; the rest is maintainability. The 61-circuit circomlib corpus (BN254) is unaffected (identical verdicts, dense and sparse); the soundness fix changes a verdict only on a small-prime input that triggered the bug. The CLI gains `--gb-strategy` (with `--gb-by-homog` kept as a hidden alias); no other CLI or public-API change.
  - **Soundness (false UNSAT, small primes).** Bit propagation pinned a bitsum's bits from its value modulo `p` — when the bitsum reduced to a constant (Phase 1) or two bitsums were equal modulo `p` (Phase 2) — but `A ≡ B (mod p)` implies the integer (bitwise) equality only when the bitsum range fits in `p` (`2^len <= p`). The Phase 2 guard used `len <= prime.bits()` (= `floor(log2 p) + 1`, one bit too loose) and Phase 1 had no such guard, so on a small prime a modular collision (`GF(7)`: `7 ≡ 0`, so `0b111` and `0b000` are equal mod 7) was forced bit-equal and pruned a satisfying assignment. Both phases now gate on `2^len <= p` through a shared `bitsum_fits` helper, which also single-sources the encoder's bitsum chain-length cap. Inert on cryptographic primes (a bitsum that long never arises); two `GF(7)` regression tests are added.
  - **Robustness.** The R1CS section-table parser computes each section's end with `checked_add`, so a section size near `usize::MAX` is rejected instead of wrapping past the bounds check into an out-of-range slice (a crash on untrusted input).
  - The split-GB `Ideal` constructor routes through `compute_gb_with_order`, so the configured polynomial representation (`poly_repr`, sparse by default) drives the split-GB solve — that path previously always ran the dense engine regardless of the setting — and the shared `finish_gb` cancel/error/backup contract now applies there too. Verdict- and performance-neutral on the corpus; the dense and sparse reduced Gröbner bases are cross-checked equal by `repr_oracle`.
  - Maintainability (no behavior change). Duplicated logic is single-sourced: the split-GB propagation decision (admit / memo / contains / pre-record), the univariate-coefficient extractor, the round-robin brancher construction, and the bitsum chain-length cap. `BitProp::get_bit_equalities` takes `&self`, so its no-cache contract (the basis of the 1.8.7 false-UNSAT fix) is type-enforced. The four largest engine files are split into re-exported submodules — the GB engine front-door out of `ideal.rs`, the `ConstraintSystem` family and bitsum extractor out of `encoder.rs`, the dense reduction engine out of `polynomial.rs`, and the circomlib comparator recognizer out of `basis2.rs` — leaving public paths unchanged. Added: a `DpvlConfig` overlay drift-guard test and an F4-vs-per-pair full-reduced-GB differential test. Documentation: the `repr` / `Theory` extensibility notes now state the actual dispatch mechanism (the `Polynomial` enum, not the trait) and the single-theory model channel.

## [1.8.8] - 2026-05-26
- Robustness and maintainability hardening. No change to any verdict on valid input (identical over the 61-circuit corpus, dense and sparse), the public API, or the CLI.
  - The R1CS parser bounds the header wire/IO counts (`n_wires`, `n_pub_out`, `n_pub_in`, `n_prv_in`) before allocating: a header claiming counts the payload cannot describe (e.g. `n_pub_in = u32::MAX`) is rejected as `R1csParseError::HeaderImplausible` rather than driving a multi-gigabyte allocation on untrusted input. The bounds are the iden3 invariants `1 + n_pub_out + n_pub_in + n_prv_in <= n_wires` and `n_wires <= w2l.labels.len()`.
  - `IncrementalGB::pop` restores the basis polynomial bodies, not only the active flags. `tail_reduce_active` can rewrite a pre-push element's body with contributions from post-push (higher-generation) reducers that need not lie in the pre-push ideal, so a flags-only pop left the popped-level basis no longer a basis of that ideal. Reachable only through the engine-level push/pop, which currently has no production caller (backtracking elsewhere re-encodes from a fact stack); the push/pop regression test now compares bodies, not just basis length.
  - The incremental-solver cache key is a 128-bit digest (two domain-separated hashes) rather than 64-bit. A cache hit is trusted to reuse a prior split-GB, and an UNSAT result from a hit is returned without a model re-check, so a two-distinct-constraint-side collision would be an unsound UNSAT; 128 bits makes that negligible.
  - The QF_FF SMT-LIB front end rejects an `=` / `distinct` chain whose operands mix Bool and FF sorts (the chain was previously classified by its first operand alone), and the tokenizer reports a malformed-input error instead of indexing out of bounds on a truncated token stream.
  - The BIM propagation lemma accumulates repeated-wire coefficients (mod p) when building its matrix instead of keeping only the last.
  - Witness output filters the encoder's internal auxiliary variables (`__w_diseq_*`, `__bitsum_*`), which are not circuit signals.
  - Maintainability: dead code removed (`Solver::add_theory_lemma`, `Theory::level`, an unreachable DPVL branch); duplicated logic single-sourced (the geobucket cascade constants, the Fermat modular inverse, the GB-entry error/cancel fallback, the disequality witness-variable naming); the backend-inventory extensibility docs and the `ff`/`gb` module-boundary docs corrected.

## [1.8.7] - 2026-05-26
- Fixes a finite-field solver soundness bug (a false UNSAT — a falsely "safe" verdict) plus robustness and maintainability hardening. The 61-circuit circomlib corpus is unaffected (identical verdicts, dense and sparse); the soundness fix changes the verdict only on an input that triggered the bug. No change to the public API or the CLI.
  - **Soundness (false UNSAT).** `BitProp::is_bit` no longer caches a per-basis `x^2 - x ∈ I` proof into the persistent global bit set. That set is threaded across the split-GB DFS and is never rolled back on backtrack, so a variable proven a bit on one branch (e.g. pinned to 0/1) was then treated as a bit on sibling branches. Combined with a bitsum registered purely from a `c, 2c, 4c, …` coefficient run — over variables that need not be bit-constrained — this let `get_bit_equalities` derive a spurious bitsum-overflow contradiction and prune satisfiable assignments. `is_bit` is now a pure query that re-derives the per-basis proof on each call; the global set holds only user-asserted bits. A reproduction (a satisfiable `GF(7)` quadratic whose linear part matches the coefficient run) is added as a regression test.
  - The dense geobucket reduction re-attaches the in-flight leading term before draining on cancellation, so an interrupted reduction's partial remainder stays in the input's coset (matching the indexed and sparse cancel paths); the term was previously dropped.
  - Monomial-exponent accumulation in the SMT-LIB term rewriter and the naive reduction oracle uses `checked_add`, matching the engine's `u16` discipline: a degree overflow panics (caught at the backend boundary → `Unknown`) instead of wrapping to a wrong exponent.
  - The QF_FF cvc5 backend refuses a query carrying `assignments` / `bitsums` it does not lower (`Unknown(IncompleteTheory)`), matching the NIA backends, instead of silently solving a weakened query.
  - The incremental solver falls back to a fresh stateless solve when a cached ring cannot resolve a query's disequality variable, rather than returning `Unknown`.
  - Documentation and structure: the copy-symmetry lowering invariant the wire-keyed propagation lemmas depend on is documented at the emission site and on each lemma; the linear lemma's empty-dependency (unconditional) promotion is documented as intended for single-variable forced wires; the CDCL(T) post-lemma resync is factored into one helper; the `learn_clause` watch-order comment is corrected; `split_model` echoes shared input values into the second witness so it is a complete assignment.

## [1.8.6] - 2026-05-26
- Soundness and robustness hardening. No change to any verdict (identical over the 61-circuit corpus, dense and sparse), the public API, or the CLI.
  - The traced incremental Gröbner-basis path (`compute_gb_incremental_with_order_traced`) returns an empty basis on a genuine engine error (a caught panic or non-cancel `Err`) rather than the unreduced concatenated generators, matching its non-traced sibling; only cancellation returns the generators unchanged. An empty basis reads as `is_whole_ring() == false`, so the split-GB fixpoint keeps searching instead of risking a non-GB being consumed as a GB by `is_zero_dim` / `min_poly` / FGLM.
  - The aboz zero-product lemma emits each alt-copy disjunction over the variable that actually appears in that copy's constraint. An input wire reuses `x_w` in both copies, so its alt-copy clause now uses `x_w` — entailed by the `x_s · y_o = 0` equality already in the IR — rather than the unconstrained `y_w`; previously the emitted clause was sound only because `y_w` for an input was a free variable.
  - The R1CS parser rejects a field modulus ≤ 1 (`R1csParseError::InvalidPrime`). A malformed header (e.g. `field_size = 0`, decoding to a zero prime) previously reached `PrimeField::new`'s assertion during lowering and aborted the process before the backend's panic guard.
  - The SMT-LIB term builder accumulates monomial exponents with `checked_add`, matching the engine's `u16` exponent discipline: a degree overflow now panics (caught at the backend boundary → `Unknown`) instead of wrapping silently to a wrong exponent and mistranslating the polynomial.
  - `Solver::learn_clause` enforces its non-empty-clause precondition in release builds (was `debug_assert`), so a violated invariant fails loudly (caught → `Unknown`) rather than indexing out of bounds.
  - Internal invariant checks and documentation accuracy: the theory trail is asserted to advance by at most one decision level per propagation sync; the range-lattice producer copy-awareness requirement is documented; the small-field `from_biguint` reduction asserts its always-valid `u64` fit; stale comments (the backends' Cargo-feature description, the lazy `CancelToken` tests) and a redundant `is_univariate` branch are corrected.

## [1.8.5] - 2026-05-26
- Soundness and robustness hardening. No change to any verdict (identical over the 61-circuit corpus, dense and sparse), the public API, or the CLI.
  - CDCL(T) maps a theory UNSAT core back to trail atoms through per-polynomial provenance (`EncodedSystem::poly_provenance`) instead of an assumed positional layout, which the interleaved zero-assignment / Rabinowitsch / field polynomials and dropped zero polynomials could misalign. Equality entries are trusted only when the pre-encode rewrite dropped no equality; disequality (Rabinowitsch) entries always align; encoder-internal polynomials contribute no atom. An unattributable index falls back to the full trail core.
  - `compute_gb_*` distinguishes cancellation from a genuine engine error: a real error (e.g. a caught degree-overflow panic) now yields an empty basis rather than the unreduced input generators, so `is_zero_dim` / `min_poly` / FGLM cannot consume a non-GB as a GB (a former false-UNSAT hazard). Cancellation still returns the generators unchanged for the caller's `is_cancelled` check.
  - `fglm_to_lex` verifies the staircase size against the Hilbert quotient dimension in release builds (was debug-only) and returns `None` on mismatch, so the caller falls back to a direct Buchberger Lex computation instead of a possibly-not-in-ideal lex basis.
  - `interreduce` de-duplicates elements with equal leading monomials (keeping the lowest index), not only strict-divisibility duplicates; dehomogenisation can produce equal leading monomials, and the previous code could leave a non-minimal basis. Applies to both the dense and sparse engines.
  - The sparse Buchberger reduction is cancel-aware (`reduce_by_refs_cancel`, threaded into the sparse geobucket reducer), so a single large reduction can be interrupted as on the dense path.
  - `CancelToken` evaluates timeouts and `either` combination lazily in `is_cancelled()` (an optional deadline plus a source list) instead of spawning a background timer / watcher thread per token, so creating one token per solve no longer accumulates detached threads.
  - `native_ff` installs its panic-silencing hook once per process behind a thread-local guard rather than swapping the global hook on every solve.
  - `enqueue_theory` rejects a stale theory reason (a negated reason literal not currently False) in release builds, not only under `debug_assert`, avoiding a malformed justification clause.
  - `r1cs_to_poly_ir` validates `target_signal` against the wire count and returns `LowerError::WireOutOfBounds` rather than building a query over a non-existent ring variable.
  - The QF_NIA backends (`cvc5_nia`, `z3_nia`) return `Unknown(IncompleteTheory)` when the query carries disjunctions / assignments / bitsums they do not lower, instead of silently solving a weakened query.
  - Documentation/comment accuracy: the split-GB UNSAT core is documented as a sound conservative over-approximation (was "precise"); the `u16` monomial-exponent overflow contract and the Gebauer–Möller F-criterion behaviour of `gm_insert` are stated; stale comments in the encoder and incremental context are corrected.

## [1.8.4] - 2026-05-25
- Internal refactors only — no change to any verdict, the public API, or the CLI. Maintainability/structure cleanups toward the planned cvc5/CoCoA engine alignment:
  - The Gebauer–Möller M-criterion, B-criterion, and S-pair queue merge are unified into one representation-agnostic `ff::spair_criteria` module (generic over a `CriterionPair` / `LeadingTerms` trait pair); the dense and sparse Buchberger engines share it instead of hand-mirrored copies.
  - `ff::buchberger` factors S-polynomial construction and non-strict deactivation into `build_spoly` / `deactivate_superseded`, shared across the per-pair, F4, and seeding paths.
  - The CDCL(T) main loop is generic over the `Theory` trait; the unused `Effort` / `pre_check` scaffolding is removed.
  - `PolyIR` no longer depends on `picus-solver`: its native-engine lowering (`to_constraint_system` / `to_boolean_query` / `encode` / `pre_eliminate_linear`) moves to the native backend, leaving the IR dependent only on `picus-core`.
  - `FfPolyRing` reads field / variable count / names from the shared ring context instead of storing duplicates.
  - `run_dpvl` returns a typed `DpvlError` (was `String`); `PicusError` gains a `Dpvl` variant.
  - Removed the unused `SolverMode` enum and `solve_encoded_with_mode` entry points; the `solver_bench` criterion target builds again and `cargo build --all-targets` is warning-clean.

## [1.8.3] - 2026-05-25
- Split-GB UNSAT core is now a sound conservative over-approximation: every element of a partition, and any extracted core, is attributed the union of the original inputs that fed that partition. This closes an under-approximation hazard where Buchberger deactivation (active-vs-push index skew) or a zero-reducing batched generator could yield a too-small core. Only the CDCL(T) conflict path consumes the core; the default conjunctive path discards it, so verdicts are unchanged.
- Univariate root-finding distinguishes completeness: `find_roots_checked` returns `(roots, complete)`, with `complete = false` when Cantor–Zassenhaus leaves an unsplit product of linear factors. The split-GB brancher and model search treat an incomplete result as inconclusive (fall through to round-robin → `unknown`) instead of as proof of infeasibility, so a dropped root can never produce a wrong `unsafe`/UNSAT.
- CDCL(T) hardening: a theory UNSAT core that maps to no trail atom falls back to the full trail (a sound, coarser conflict) instead of returning `unknown`; an unassigned theory-core literal yields `unknown` rather than an `unreachable!` panic.
- `--selector first` selects the smallest unknown signal index (deterministic across runs) rather than an arbitrary hash-set iteration order.
- Internal: the Gröbner-engine error type is renamed `SolverError` → `EngineError` (the backend-facing `picus_smt::backends::SolverError` is unchanged); `PolyRing::new_with_repr` / `FfPolyRing::new_with_repr` set the polynomial representation explicitly instead of through the thread-local config. Added differential tests for the `u64` field arm above 2^63 (Goldilocks) and for F4 vs per-pair Gröbner bases over BN254, plus a config drift guard asserting `apply_overlay` consumes every overlay field.

## [1.8.2] - 2026-05-25
- `ff::hilbert::quotient_dimension` + `Ideal::quotient_dimension`: `dim_k(R/I)` (the standard-monomial count, i.e. the solution count with multiplicity) read from a finished basis' leading terms via the graded Hilbert function. Cross-checks the FGLM staircase size in `fglm_to_lex` (debug assertion).
- Geobucket reducer reads each divisor's leading coefficient lazily — only for the divisor actually selected — instead of cloning it for every divisor on every reduce call (a heap `FieldElem` clone over large primes).
- Incremental Gröbner-basis extends always run the per-pair engine; F4 (`use_f4`) is used only for from-scratch GB, where its degree-batched matrix amortises.
- New config keys / CLI flags, both default off: `split_triangular` (`--split-triangular on|off`) — triangular model construction (univariate roots + back-substitution) for a zero-dimensional combined system on the split-GB path, in place of the brancher DFS; `reducer_index_cache` (`--reducer-index-cache on|off`) — cache the reducer's DivMask/degree divisor index across reductions with an unchanged active basis.

## [1.8.1] - 2026-05-25
- Removed the `PICUS_*` runtime environment overrides (`PICUS_USE_F4`, `PICUS_POLY_REPR`, `PICUS_BOOLEAN`, `PICUS_DNF_CAP`, `PICUS_CDCLT_ITER_CAP`, `PICUS_GB_STATS`, `PICUS_GB_TRACE`, `PICUS_PROFILE`, `PICUS_NO_INCREMENTAL_CACHE`, `PICUS_NO_ABOZ_DISJ`). Every engine knob is now set through the config file (`--config` / `./picus.toml`) or a CLI flag only; config resolves as built-in defaults < file < CLI. Build-time locators (`CVC5_LIB_DIR`, …) are unaffected.

## [1.8.0] - 2026-05-25
- Default solver is now `native` (was `cvc5`), matching the default `native`-only build — a bare `picus check` / `Config::default()` now works without opt-in Cargo features. `cvc5` / `z3` need their features and an explicit `--solver`.
- Workspace `default-members` excludes the `cvc5-ff` / `cvc5-ff-sys` / `z3` crates: the default commands (`cargo build`, `cargo test`, `cargo install --path crates/picus-cli`) compile only the native solver. cvc5 / z3 build solely on opt-in (`--features cvc5` / `z3`, or an explicit `cargo build --workspace`).
- Layered configuration: built-in defaults < config file < `PICUS_*` environment < CLI flags, each layer overriding only the keys it sets. `picus check` gains `--config <FILE>` (TOML); `./picus.toml` in the working directory is auto-loaded when present. A commented [`picus.default.toml`](picus.default.toml) documents every knob at its default value, with a test asserting it matches the compiled defaults.
- Config types unified: the public `Config` is now `PicusConfig { analysis, engine }` — `analysis` (solver/theory/lemmas/selector/timeout/dump) and `engine` (the native-FF knobs). Each knob is declared once; `picus::Config` stays as an alias. `EngineOverlay` / `DpvlOverlay` carry the partial (all-optional) config layers, parsed via serde + TOML.
- `poly_repr` and the `aboz` zero-product disjunction toggle — previously settable only through `PICUS_*` — are now first-class config keys and CLI flags (`--poly-repr`, `--no-aboz-disj`); `--gb-stats` added.
- Docker image is native-only (drops the cvc5 / z3 build chain), matching the default build.
- Documentation reorganised: a slimmer README, the full flag / configuration reference in `docs/usage.md`, and cvc5 / z3 build instructions + licensing in `docs/building.md`; removed `docs/TODO.md`.

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
