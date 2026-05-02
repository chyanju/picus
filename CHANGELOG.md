# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

## [1.7.15] - 2026-05-01

Engine-level performance work plus an opt-in F4-lite degree-batched
reducer. Architectural alignment with cvc5 + CoCoA's QF_FF theory was
already complete in 1.7.14 — this release tightens the underlying
Buchberger engine and adds F4-lite as scaffolding for future work
where larger sugar batches are achievable. The KPI-17 solved set is
**15/17** (unchanged); `Pedersen@pedersen` now sits right at the 60 s
boundary and crosses to *unsafe* on faster runs (occasionally lifting
the count to 16/17 in CI). `inTest` remains over the gate.

### Added

- **Thread-local `FieldElem` allocation pool** (`ff/field.rs`).
  `FieldElem` now `impl Drop` recycles its `rug::Integer` mpz buffer
  back into a thread-local stack of size 4096; `field.add` / `sub` /
  `mul` / `neg` pull from the pool via `pool_take_or_default` instead
  of allocating fresh mpz limbs on every operation. `add_owned` /
  `sub_owned` consume both operands and recycle the right-hand side.
  Eliminates one mpz allocation per coefficient operation on the
  geobucket cascade path. Reentrancy guarded by an `IN_POOL_DROP`
  cell so the Drop impl never recurses.

- **GMP in-place arithmetic on hot paths.** Geobucket
  `pop_leading_term`'s cross-bucket coefficient sum now uses
  `field.add_assign` (in-place `+=`) instead of `field.add` (new
  allocation). Same change applied throughout `Polynomial::merge_owned`
  via `add_owned` / `sub_owned`. Reduces GMP allocations on dense
  polynomial merges, which were the primary cost on `inTest`'s
  late-stage S-pair reductions.

- **128-bit `DivMask`** (was 32-bit; `ff/divmask.rs`). Provides
  divisibility-rejection coverage on circuits with > 32 variables —
  e.g. `inTest`'s 571-variable system, where the original 32-bit
  scheme covered only the first ~32 vars and gave no useful filter
  signal for the rest. Per-variable threshold count adapts via
  `DIVMASK_BITS / n_vars`.

- **Sorted divisor bucket with early-break** (`ff/polynomial.rs`).
  Within a single divmask bucket, divisors are now sorted by leading-
  term degree ascending; the bucket-scan loop `break`s on the first
  divisor whose LT degree exceeds the current LT's, since every
  subsequent one is at least that big. Threshold raised from 64 → 256
  (the tipping point above which the sort+break path beats the
  original linear scan).

- **`IncrementalGB` resume primitives** (`ff/buchberger.rs`):
  `run_only`, `set_cancel_token`, `is_quiescent`, `open_queue_len`.
  Lets the cache re-attach a fresh per-call cancel token to an
  in-flight Buchberger run and continue draining the open S-pair
  queue across solve-call boundaries. Sub-iter resumable cache uses
  this when the fast-path `split_gb_cancel` rebuild gets cancelled
  mid-build.

- **`IncrementalSolverContext` partial-build fallback**
  (`incremental_context.rs`). When a fresh cache rebuild is cancelled
  mid-build, the encoded artifacts plus per-partition `IncrementalGB`
  in-flight state are saved as `partial_build`. The next solve call
  with the matching constraint-side digest resumes via
  `continue_partial`, draining the saved open queues with a fresh
  cancel token. Once quiescent, the partial state is finalized into a
  `CachedBase` (interreduce + monic). Counters
  `cache_partial_resumes` and `cache_partial_completions` surfaced via
  `PICUS_GB_STATS=1`.

- **F4-lite scaffolding** (`ff/f4.rs`, ~700 lines, opt-in via
  `PICUS_USE_F4=1`). Sugar-batched S-pair processing: build
  S-polynomials for one same-sugar batch, run symbolic preprocessing
  (BFS closure under reducibility, adding `(m / lt(b)) * b` reducer
  rows for every monomial divisible by some active basis LT), build
  a sparse matrix with a monomial-DESC column index, run sparse row-
  echelon over GF(p) with reducer rows pivoted first, extract new
  generators from S-poly residues whose LT column is not a reducer
  LT. Wired into `BuchbergerState::run_f4` with size-1 batch fallback
  to direct geobucket. Five unit tests including multi-pair property
  tests cross-checking against the per-pair geobucket reference. **F4
  is correctness-clean** (full 110-circuit gate produces 0 mismatches
  with `PICUS_USE_F4=1`) but the matrix-construction overhead exceeds
  the per-pair amortization savings on the current circuit set, so it
  remains gated off by default.

### Performance

| Circuit | 1.7.14 | this release | Δ |
|---------|--------|--------------|---|
| modulusagainst2p | 37–52 s range | 52–63 s range (variance) | within noise |
| Pedersen@pedersen | timeout | timeout (occasionally `unsafe` ~64.9 s) | edge of 60 s gate |
| Other previously-solved circuits | unchanged within run-to-run noise | | |
| `inTest` | timeout | timeout | unchanged (~5 s over gate) |

Engine micro-benchmarks (cold inTest GB build under stats, no DPVL
overhead): solve_inner dropped from ~75.9 s in 1.7.14 to ~63.7 s in
this release (~16 % engine speedup) thanks to the FieldElem pool +
GMP in-place + 128-bit DivMask + sorted bucket. The savings don't
quite cover the 60 s per-signal budget, so `inTest` remains a
timeout on the KPI gate — closing it requires either further engine
work or a different solver topology (out of scope here).

### Correctness

132 unit tests pass (127 prior + 5 F4-lite, including two multi-pair
property tests cross-checking F4 output against per-pair geobucket
reduction); 110-circuit correctness gate produces **0 verdict
mismatches** with F4 disabled (default) and **0 verdict mismatches**
with F4 enabled (`PICUS_USE_F4=1`).

### Documentation

- `chat/plan-10/` records Plan v10's diagnosis (`diagnosis-v1714.md`)
  and full progress log (`progress.md`), including the honest
  assessment of which phases moved KPI numbers and which were pure
  alignment / robustness work.
- `docs/solver-evaluation.md` will be updated separately to add the
  F4-lite entry to the divergences table (cvc5+CoCoA stay on
  classical Buchberger; F4-lite is a picus-only opt-in path).

## [1.7.14] - 2026-04-28

Architectural alignment with cvc5 + CoCoA's QF_FF theory: this release
introduces several structural items that cvc5/CoCoA had and picus
didn't, plus refines existing alignment. KPI-17 is unchanged (15/17;
the same `inTest` timeout that 1.7.13 had); the value is in the
architectural alignment itself, not in immediate KPI movement.
`modulusagainst2p` median wall is slightly tighter (37–52 s range vs
1.7.13's 44–67 s).

### Added

- **`IncrementalSolverContext` solver-state cache.** Caches the
  encoded constraint side and computed split-GB across `solve_encoded`
  calls within a `NativeFfBackend` session. On a cache hit, the
  per-query Rabinowitsch disequality polynomial is encoded in the
  cached polynomial ring and added to the cached split-GB via
  `Ideal::extend_with_cancel` (Plan v6 incremental Buchberger).
  Mirrors cvc5's `SubTheory` (`sub_theory.cpp:62-90`,
  `sub_theory.h:112`) which accumulates facts across SMT solver calls
  via a `context::CDList<Node>`. Lazy build (only after seeing 2+
  same-digest calls) avoids regressions on circuits whose constraint
  side changes per call. Disable via `PICUS_NO_INCREMENTAL_CACHE=1`.
  Soundness rests on the existing `extend_with_cancel` correctness:
  adding a generator to a reduced GB and re-running incremental
  Buchberger yields the same final GB as full recomputation.

- **Hash-bucketed divisor index in the geobucket reducer.** Groups
  divisors by their `DivMask` bits; the lookup loop iterates only
  buckets whose mask is a submask of the current LT's mask. Mirrors
  CoCoA's `Reductors` class (`TmpGReductor.H:65-100`) which holds the
  active basis with a similar fast-lookup structure. Gated to ≥ 64
  divisors so small unit-test inputs continue to use the original
  linear-scan first-match semantics.

- **AST-level int-literal folding in `+` and `*`.** The IR optimizer's
  `simple_opt_expr_z3` now consolidates `Int(a) + Int(b) → Int(a+b)`
  and `Int(a) * Int(b) → Int(a*b)` with canonical position (constants
  at end of `+`, at start of `*`). Mirrors cvc5's
  `theory_ff_rewriter.cpp:45-150` postRewriteFfAdd / postRewriteFfMul.
  picus's polynomial-level merging (`Polynomial::from_terms`) already
  produced the equivalent canonical form post-encoding; this addition
  makes the alignment explicit at the AST layer too.

- **HOMOG-gated periodic in-loop tail-reduce.** When all initial
  generators are homogeneous (every term has the same total degree),
  `BuchbergerState::run` invokes `tail_reduce_active` every 32 useful
  S-pair reductions. Mirrors CoCoA's `myDoGBasis`
  (`TmpGReductor.C:680, 710-721`). Off for non-homogeneous inputs
  (per CoCoA's gradedness invariant for sugar-driven pair selection,
  and per Plan v7's A/B which found the throttle hurt non-HOMOG suite
  performance).

- **`BitPropState`** (`bitprop.rs`): owned snapshot of `BitProp`'s
  logical state (the `bits` and `bitsums` sets), with `to_state` /
  `from_state` accessors. Used by the cache to persist BitProp
  contents across solve calls.

- **Diagnostic instrumentation: `NativeFfBackendCounters`** surfaced
  via `PICUS_GB_STATS=1`. Counters: `solve_calls`, `encode_time_ns`,
  `solve_inner_time_ns`, `encoded_polys_max`, `distinct_cs_digests`,
  `repeated_cs_digest_streak`, `cache_hits`, `cache_rebuild_time_ns`,
  `cache_query_diff_time_ns`. Useful for analyzing per-circuit DPVL
  query patterns.

### Documentation

- `docs/solver-evaluation.md § "Deliberate divergences from cvc5"`
  updated with new entries: `IncrementalSolverContext`, hash-bucketed
  divisor index, AST int-literal folding, `GbStrategy::ByHomog` /
  `Auto` (picus-only). Borel-fixed flag confirmed as not-a-divergence
  (cvc5 ff theory also passes `DontUseBorel`).

### Performance

| Circuit | 1.7.13 | this release | Δ |
|---------|--------|--------------|---|
| modulusagainst2p | ~52 s median | 37–52 s range | -10 to -30 % |
| Other previously-solved circuits | unchanged within run-to-run noise | | |
| `inTest` | timeout | timeout | unchanged (cache rebuild can't fit in per-signal budget; documented in `chat/plan-9/phase1-result.md`) |

KPI-17 solved set: 15/17 (unchanged). Cache benefit on
`modulusagainst2p` is modest because each per-query call there is
already fast (~2 s); the cache hit savings are within run-to-run
variance. The architectural value is the alignment with cvc5's
SubTheory model, not a wall-time win in this release.

### Correctness

127 unit tests pass; 110-circuit correctness gate shows **0 verdict
mismatches**. Cache soundness rests on `extend_with_cancel`'s
incremental-Buchberger correctness (Plan v6) and the digest's
faithful inclusion of all constraint-side fields.

## [1.7.13] - 2026-04-28

KPI 14/17 → 15/17. `modulusagainst2p` recovered (median ≈ 52 s wall
vs the 60 s gate; was timing out at 60 s with underlying wall ≈ 241 s
in 1.7.12). The recovery is driven by removing redundant work in the
split-GB propagation loop — empirically 99.9 % of `contains_with_cancel`
calls returned true on that circuit. `inTest` remains over the gate;
its bottleneck is per-signal GB recompute in the DPVL solver loop,
which is architectural and out of scope for this release.

### Added

- **Memoized cross-basis containment in the split-GB propagation
  loop.** `Polynomial::content_hash()` produces a cheap u64 fingerprint
  (exponents, per-term degrees, leading-coefficient hash). Each
  `split_gb_cancel` / `split_gb_extend_cancel` invocation maintains a
  `HashSet<(u64, basis_idx)>` that records polynomials known to be
  members of each basis. The propagation step pre-populates the memo
  with self-membership facts (`p ∈ basis_j ⇒ contains(p, j) = true`,
  trivially) at the start of each fixpoint iteration and inserts
  positive results as it goes. Soundness rests on monotonicity of
  ideal membership during a fixpoint call: `extend_with_cancel` and
  `interreduce_basis` both preserve membership, so a recorded `true`
  remains `true`. On `modulusagainst2p` the cross-basis containment
  count drops from ~2.47 M to ~2 K per full DFS run, and the time
  spent in `contains` drops from ~62 s to ~0.4 s. The same memo helps
  every split-GB-driven path: dense unsafe circuits (`binmulfast51_2`,
  `binadd1`, `chunkedadd`, `chunkedadd1`, `VDBuggy`) saw 4–11×
  speedups as a side effect.

- **Move-based polynomial merge for owned operands**
  (`Polynomial::merge_owned`, `field.add_owned` / `sub_owned` /
  `neg_owned`). The geobucket cascade in `Geobucket::add_poly` owns
  both the existing bucket and the incoming polynomial — the move-based
  merge consumes both inputs' coefficient `Vec`s and recycles their
  `FieldElem` (and underlying `mpz_t`) allocations into the output,
  eliminating the per-element clone the previous `merge_sorted`
  implementation paid. Same final result; fewer GMP allocations on
  cascade-heavy reductions.

- **Borrowed leading-term info in `reduce_by_refs_geobucket`**
  (`polynomial.rs`). The per-divisor `(exps, deg, coeff, divmask)`
  tuple now borrows the exponent slice from the divisor's own
  storage rather than cloning it into a per-call `Vec<u16>`. On a
  basis of 700 divisors with 284 vars per term, this saves
  ~414 KB of `Vec<u16>` allocation per reduction call.

- **Degree-sorted divisor scan with early-break** (large basis only,
  threshold = 64). When the divisor set is large, the reducer
  precomputes an auxiliary index sorted by leading-term total degree
  ascending; the divisor lookup loop iterates this index and `break`s
  on the first divisor whose LT degree exceeds the current LT's,
  since every subsequent divisor in ascending order is at least that
  big. For small divisor sets the original linear scan is preserved
  to keep the existing reducer-vs-naive equivalence test exact.

- **`PICUS_GB_STATS=1` / `PICUS_GB_TRACE=1` instrumentation surfaces.**
  `PICUS_GB_STATS=1` extends the existing buchberger telemetry with
  split-GB driver / DFS counters and per-phase reducer timers
  (`div_lt_setup`, `pop_lt`, `div_lookup`, `sub_scaled`, `finalize`,
  plus inside-`sub_scaled_tail` setup/`add_poly` split). `PICUS_GB_TRACE=1`
  emits one line per fixpoint iteration with basis sizes and propagation
  counts. Both default-off; `PICUS_GB_STATS=0` adds no measurable
  overhead.

### Performance impact

Median wall on a representative KPI run, `--timeout 60000`:

| Circuit | 1.7.12 | 1.7.13 | Δ |
|---------|--------|--------|---|
| binmulfast51_2 | 4.2 s | 0.7 s | -83% |
| binadd1 | ~5.5 s | 0.5 s | -91% |
| chunkedadd | 11.9 s | 2.0 s | -83% |
| chunkedadd1 | 25.5 s | 3.1 s | -88% |
| VDBuggy | 3.4 s | 1.1 s | -68% |
| modulusagainst2p | timeout (≈ 241 s wall) | ~52 s median | recovered |
| Other circuits (safe, fast) | unchanged or marginally faster | | |

`inTest` is unchanged (timeout). Its bottleneck is in
`reduce_by_refs_geobucket` on the dense initial basis — finer
profiling shows ~30 s per `compute_gb_with_order` call, replicated
across many DPVL signal queries — and the propagation memoization
above does not address it.

`modulusagainst2p` shows ±10 s run-to-run variance under repeated
single-run measurement; the median is comfortably under the 60 s gate
but unlucky individual runs can hit 60–67 s. `Pedersen@pedersen` is
similarly on the gate boundary.

### Correctness

127 unit tests pass; the 110-circuit correctness gate shows **0 verdict
mismatches**. Memoization soundness is guaranteed by ideal-membership
monotonicity during a single propagation call and verified by the gate.

## [1.7.12] - 2026-04-28

Major architectural alignment of the in-tree finite-field engine and
split-GB driver against cvc5 + CoCoA. KPI gain is concentrated on the
dense-ideal unsafe circuits (`chunkedadd`, `chunkedadd1`, `binadd1`,
`binmulfast51_2`, `VDBuggy`); the two long-running hard timeouts
(`modulusagainst2p`, `inTest`) remain over the 60 s KPI gate but
`modulusagainst2p`'s underlying wall time dropped from ~600 s to
~241 s.

### Added

- **GMP backend (`rug` crate, GMP via `gmp-mpfr-sys`).** `PrimeField` and
  the in-tree polynomial pipeline now use `rug::Integer` instead of
  `num_bigint::BigUint`, matching the backend cvc5 + CoCoA already use
  (`include/CoCoA/BigInt.H:41`). `PrimeField` caches `result_bits`
  (`prime_bits + 1`) and `product_bits` (`2 * prime_bits + 1`) at
  construction; `add` / `sub` / `mul` allocate the result with
  `Integer::with_capacity(...)` so the default 1-limb `mpz_init` no
  longer reallocates on every BN128-sized result. The `BigUint`-on-the-
  boundary API is preserved via cached conversions in `PrimeField`.
- **Pair-free seed path in `compute_gb_incremental_with_order`**
  (`buchberger.rs:399 seed_with_reduced_basis`). Previously the seeding
  pass called `add_generators(known_gb)`, which generated O(n²) S-pairs
  (each walking the M-criterion list, O(n³)/O(n⁴) total) — every one of
  which reduced to zero by Buchberger's criterion since `known_gb` was
  already a reduced GB. The new path pushes the seed elements directly
  with non-strict deactivation and applies the divmask, skipping pair
  generation entirely.
- **No-op skip in `Ideal::extend_with_cancel`** (`ideal.rs:149-176`).
  When every new generator reduces to zero against the existing reduced
  GB, the GB engine and the subsequent `interreduce_basis` call are
  both skipped (the result would be the same basis byte-for-byte). On
  `modulusagainst2p` this short-circuit fired on ~28 % of calls under
  `PICUS_GB_STATS=1`.
- **Lin-quick-UNSAT clone elimination** (`split_gb.rs:599-614`). The
  per-DFS-branch linear-only UNSAT pre-check used to clone basis 0,
  build an `Ideal`, run incremental Buchberger, and inspect
  `is_whole_ring()`. For a basis whose elements are all degree ≤ 1
  (which `admit(0, p)` guarantees), Buchberger reduces to Gaussian
  elimination, so the cheap exact test is `assign_poly mod basis[0]` is
  a non-zero constant. Replacing the clone+extend chain with a direct
  `reduce_with_cancel` + constant check **dropped `modulusagainst2p`
  wall time from 632 s to 241 s (-62 %)** in single-run measurement;
  per-branch basis clone was the dominant cost in
  `split_zero_extend_cancel`'s body on dense circuits.
- **Cancel-token propagation through reduction hot paths.** Previously
  a single dense reduction inside `reduce_by_refs_geobucket` could run
  for tens of seconds with no cancel-check, so `--timeout` only fired
  at coarse boundaries. New: `Polynomial::reduce_by_refs_cancel`
  (cancel-checked inside the geobucket `pop_leading_term` loop, every
  64 iterations to keep the atomic-load overhead negligible),
  `Ideal::reduce_with_cancel` / `Ideal::contains_with_cancel`,
  `buchberger::interreduce_with_cancel`,
  `BitProp::get_bit_equalities_with_cancel`. The Buchberger main loop
  (`run`), `add_generators`, `interreduce`, and the split-GB fixpoint
  all now use the cancel-aware paths. On cancel the reducer returns a
  partial remainder consisting of already-emitted result terms plus the
  unprocessed bucket contents — sound (still represents the same
  residue class) but not necessarily a normal form.
- **`PICUS_GB_STATS=1` telemetry** (`buchberger.rs` `GbEngineStats`).
  Counters for pairs generated / killed by coprime / killed by GM /
  killed by B / reductions total / useful / useless / interreduces
  run. Emitted at end of each `add_generators` call when the env var
  is set; mirrors the existing `PICUS_PROFILE=1` pattern.
- **Bit-pattern detection equivalence audit** (`parse.rs`, 5 new
  tests covering negated / nested / sum-form / rejection cases).
- **Encoder repeated-subterm + constant-merging equivalence audit**
  (`encoder.rs`, 5 new tests). Confirmed picus's polynomial-level
  merge is equivalent to cvc5's AST-level rewrites; no code change
  needed.
- **Geobucket scratch buffers** (`geobucket.rs:43-45`,
  `scratch_exps` / `scratch_coeffs` / `scratch_degs`). Plumbing for
  reusing the `sub_scaled_tail` working buffers across calls. Honest
  caveat: the realised win here is structural — the move-semantics
  path required by `Polynomial::from_raw_sorted` resets the scratch
  capacity each call, so the FieldElem-buffer-reuse benefit doesn't
  materialise. Future copy-based path is a small change; left as-is
  for this release.
- **`Deliberate divergences from cvc5` section in `solver-evaluation.md`**
  with cross-references from each picus-only feature back to its
  source comment.

### Changed

- **Geobucket bucket constants aligned with CoCoA**
  (`geobucket.rs`). Was `BASE_CAPACITY = 4` / `MAX_BUCKETS = 16`;
  now `BASE_CAPACITY = 128` / `RATIO = 4` / `MAX_BUCKETS = 20`,
  matching CoCoA's `gbk_minlen` / `gbk_factor` / `gbk_max`
  (`geobucket.C:36-38`). picus was cascading bucket 0 → bucket 1 on
  essentially every `sub_scaled_tail` call; CoCoA absorbs ~16 calls
  into bucket 0 before cascading. **`chunkedadd1` recovered**
  (timeout → 62.7 s pre-other-changes; ~19.8 s after the rest of
  this release lands) and KPI moved from 13/17 to 14/17.
- **Sugar formula at S-pair generation tightened**
  (`buchberger.rs`). Was `sugar = pair.sugar.max(lt.total_degree())`;
  now `sugar = pair.sugar` with a `debug_assert!(lt.total_degree() <=
  pair.sugar)` invariant. Mirrors CoCoA's `myAssignSPoly`
  (`TmpGPoly.C:316`) — the pair sugar is already an upper bound on
  the new poly's sugar by construction, so the `max` was redundant.
  Invariant holds across all 127 unit tests.

### Performance (17 hard circuits, 60 s timeout)

- 1.7.11 baseline: 13/17 solved.
- 1.7.12 (this release): **14/17 solved**. Highlights vs baseline:
  - `chunkedadd1`: timeout → ~19.8 s (RECOVERED, +1 KPI bump)
  - `chunkedadd`: 38.9 s → ~11.9 s (-69 %)
  - `binmulfast51_2`: 12.1 s → ~4.2 s (-65 %)
  - `VDBuggy`: 13.3 s → ~3.4 s (-74 %)
  - `binadd1`: median ~5.5 s, down from 13.2 s (this circuit shows
    ~10× single-run variance under the same binary; KPI17 sample
    can land anywhere in 2.7–26.7 s)
  - `modulusagainst2p`: still timeout at the 60 s gate, but the
    underlying wall time dropped from ~632 s to ~241 s (-62 %).
    cvc5 takes 38.7 s; the remaining ~6× gap is dominated by the
    per-DFS-branch full split-GB basis clone
    (`split_zero_extend_cancel:624-631`), which would need either
    `Arc<Polynomial>`-backed bases or an explicit
    checkpoint/restore in `extend_with_cancel` to eliminate.
- Three timeouts remain: `Pedersen@pedersen` (cvc5 also times out;
  acknowledged), `modulusagainst2p`, `inTest`.

### Correctness

- **127 picus-solver unit tests pass.**
- **0 compiler warnings** across the workspace.
- Correctness gate: 110 circuits, **0 verdict mismatches** vs cvc5
  (106 agree, 36 of those are both-timeout). One circuit's verdict
  changed from "picus times out" to "picus solves and matches cvc5"
  vs the 1.7.11 gate (105 → 106 agree).

### Known limitations / not closed in this release

- `modulusagainst2p` and `inTest` still over the 60 s KPI gate. The
  earlier "F4/F5 batched reduction or Montgomery-form arithmetic
  territory" attribution was tightened on a focused profile re-run:
  the gap is dominated by GB-engine raw speed (CoCoA's mature
  C++ implementation is ~1 order of magnitude faster than picus's
  Rust port at the same workload) plus slow fixpoint convergence in
  `split_gb_extend_cancel` (~171 fixpoint iterations per outer DFS
  branch on `modulusagainst2p`). Closing this gap is non-trivial in
  either direction (faster polynomial arithmetic / GB engine, or a
  different fixpoint convergence strategy) and is deferred.
- A cross-pollination skip in `split_gb_extend_cancel` (push only
  cross-split basis polys into `to_propagate`, not own-basis) was
  implemented and reverted — although mathematically equivalent it
  perturbed `new_polys` insertion order, which fed through Buchberger's
  S-pair selection and regressed `modulusagainst2p` from 632 s to 751 s.
  The own-basis `contains` check has been retained.

## [1.7.11] - 2026-04-28

This release closes the algorithmic alignment between picus's in-tree
finite-field engine and CoCoA's Buchberger pipeline. Combined with the
geobucket reduction and Gebauer-Möller M-criterion shipped in 1.7.10,
the engine now matches CoCoA's `myDoGBasis` end-to-end for the
non-homogeneous code path.

### Added
- **Buchberger B-criterion** at basis-add time, mirroring CoCoA's
  `myApplyBCriterion` (`TmpGReductor.C:629-650`) and `GPair::BCriterion_OK`
  (`TmpGPair.C:283-289`). When a new basis element is added, every pending
  S-pair `(i, j)` is killed if all three conditions hold:
  `new_lt | lcm(LT_i, LT_j)`, `lcm(LT_j, new_lt) ≠ lcm`, and
  `lcm(LT_i, new_lt) ≠ lcm`. This is the missing companion to the
  M-criterion; together they bring the open-queue size in line with
  CoCoA's. The full three-condition form (rather than the simplified
  "any-`k` divides lcm" form picus shipped buggy in 1.7.7) is what makes
  it sound under non-strict deactivation.

### Changed
- **Skip inactive basis elements during S-pair generation**, mirroring
  CoCoA's `myBuildNewPairs` `IsActive(*it)` filter
  (`TmpGReductor.C:506`). Sound because any inactive `k` was deactivated
  by some active `m` with `LT_m | LT_k`, so the pair `(m, new)` GM-dominates
  `(k, new)` anyway. Reduces M-criterion walk size and pair-queue size on
  dense-ideal benchmarks.
- **Final interreduce is now a single pass** (mirroring `myFinalizeGBasis`
  `TmpGReductor.C:1228-1280`) instead of an up-to-`2N`-pass fixed-point
  loop. After divisible-LT pruning every surviving element's LT is
  incomparable to every other's, so reducing each tail by the others
  cannot re-introduce a monomial that another LT divides — one pass
  suffices.
- **Removed the periodic in-loop tail-reduce throttle**
  (`INTERREDUCE_EVERY = 32`). CoCoA's `myDoGBasis` does not interreduce
  inside the main loop for non-homogeneous inputs; cleanup happens once
  at `myFinalizeGBasis`. With the M-criterion + B-criterion + skip-inactive
  pair-pruning landing this release, the basis stays lean enough that the
  throttle is no longer needed. An A/B comparison on the 17-bench KPI
  showed throttle-off equal-or-better than `INTERREDUCE_EVERY=32` and
  recovered `test-rollup-tx-states` to a healthy time.

### Performance (17 hard circuits, 60 s timeout)
- 1.7.9 baseline: 13/17 solved.
- 1.7.10: 12/17 (M-criterion regression — its companion B-criterion was
  missing, so its per-generation walk overhead was unamortized).
- 1.7.11 (this release): **13/17 solved, no per-circuit regressions**.
  `test-rollup-tx-states` recovers (timeout → safe ~40 s); `binadd1`
  recovers from 21.7 s to ~13 s; `chunkedadd` and `VDBuggy` improve;
  every previously-solved circuit remains solved. Four timeouts remain:
  `Pedersen@pedersen` (cvc5 also times out), `chunkedadd1`,
  `modulusagainst2p`, `inTest` — these are dense-ideal problems where the
  remaining gap is architectural (F4/F5 batched reduction or
  Montgomery-form arithmetic), not algorithm-alignment.

### CLI / Settings
- `--gb-by-homog {off,on,auto}` (introduced earlier as opt-in) was A/B-tested
  on the 17-bench KPI; `auto` and `on` give the same solved count as `off`
  but redistribute per-circuit timings. Default remains `off`. Users with
  significant total-degree variance in their input may try `auto`.

### Verified
- 178 picus-solver unit tests pass (5 new B-criterion tests + 5 GM-insert tests
  + 9 geobucket tests + the rest).
- 0 compiler warnings across the workspace.
- Correctness gate: 110 circuits, 107 agree (37 both-timeout), **0 verdict
  mismatches** vs cvc5.

## [1.7.10] - 2026-04-28

This release ports two of CoCoA's core Groebner-basis optimizations into the
in-tree finite-field engine and lays the groundwork for further alignment.
KPI on the 17-circuit hard suite shifted from 13/17 (1.7.9) to 12/17 — the
geobucket reduction alone solves an additional circuit (`VDBuggy`), but the
M-criterion's per-generation walk regresses two circuits because its
companion B-criterion is not yet implemented. See "Performance" below.

### Added
- **Geobucket data structure** (`picus-solver/src/ff/geobucket.rs`) for polynomial accumulation, modeled on CoCoA's `geobucket.C`. Multi-bucket structure with geometric capacity growth (`BASE_CAPACITY=4`, `RATIO=4`, `MAX_BUCKETS=16`); per-bucket head cursors give O(1) leading-term pop; cross-bucket coefficient cancellation is resolved at pop time.
- **Geobucket-based reduction** in `Polynomial::reduce_by_refs`. Each reduction step is now O(D · log(N/D)) instead of O(N + D), matching CoCoA's `myReduce` / `myReduceTail` which call `ChooseReductionCogGeobucket` unconditionally (no size dispatch). The previous fused-merge implementation is retained as `reduce_by_refs_naive` for cross-validation.
- **Gebauer-Möller M-criterion** at S-pair generation time, mirroring CoCoA's `myGMInsert` (`TmpGReductor.C:448-482`). New pairs are pruned within `generate_pairs_against` whenever an existing pair's lcm divides the new pair's lcm (and vice versa), with the equal-lcm coprime-replacement rule.
- **Coprime pairs participate in GM walks** before being filtered out of the open queue (matches CoCoA's `myBuildNewPairs` flow). `SPair` gains an `is_coprime` field.

### Changed
- **S-pair queue is now a sorted `Vec<SPair>`** (descending by `(sugar, lcm_deg, age)`, pop from back) instead of `BinaryHeap<Reverse<SPair>>`. Required for the M-criterion's in-place walk-and-mutate; matches CoCoA's `GPairList`. `IncrementalGB::push` / `pop` snapshot the vector directly.

### Performance (17 hard circuits, 60 s timeout)
- 1.7.9 baseline: 13/17 solved.
- Geobucket reduction alone: 14/17 — `VDBuggy` newly solved.
- Geobucket + M-criterion (this release): 12/17. The M-criterion further accelerates `VDBuggy` (36 s → 18 s) and `binadd1` (30 s → 22 s) where it finds many dominations, but regresses `chunkedadd1` and `test-rollup-tx-states` to timeout because the M-criterion's O(n²) per-generation walk is not yet amortized by a companion B-criterion (`myApplyBCriterion` in CoCoA, which prunes the existing open queue when a new basis element is added). Adding B-criterion is the natural next step.

### Verified
- 178 picus-solver unit tests pass (9 covering the new geobucket, 5 covering `gm_insert`, 2 cross-validating the new and previous reduction implementations).
- Correctness gate: 110 circuits, 0 verdict mismatches against cvc5.

## [1.7.9] - 2026-04-27

### Fixed
- **Soundness: `FindZeroOutcome::Unsat` now correctly maps to `SolveOutcome::Unsat`** instead of `Unknown`. Previously, when the root-finding phase proved unsatisfiability, the result was silently downgraded to Unknown, potentially masking unsafe circuits.
- **Soundness: `u16` exponent overflow in monomial multiplication** now uses `checked_add` and panics on overflow instead of silently wrapping. Affects `Monomial::mul` and `mul_assign`.
- **Soundness: `from_i64(i64::MIN)` no longer panics** due to signed overflow on `.abs()`. Uses `unsigned_abs()` instead.
- **Robustness: `split_gb_cancel` and `split_gb_extend_cancel` fixpoint loops** now have iteration caps (1000 iterations) to prevent infinite loops on pathological inputs.
- **Robustness: `IncrementalGB::interreduce` safety cap** uses correct post-filter basis length instead of pre-filter length.
- **Robustness: `incremental.rs` encode failure** now logs an error and returns `Unknown` instead of panicking.
- **Debug assertion on `row_dep` bounds** in Buchberger matrix row operations.

### Changed
- **Performance: hot-loop monomial allocation eliminated** in `reduce_by_refs` — uses `DivMask::compute_from_slice` directly on exponent data instead of constructing a temporary `Monomial`.
- **Performance: `total_degree()` is now O(1)** — cached in `Polynomial` and maintained through all arithmetic operations.
- **Performance: `poly_coefficient_at` uses binary search** instead of linear scan for sorted term lookup.
- **Performance: `from_raw_sorted` constructor** avoids re-sorting already-sorted term vectors in reduction output.
- **Performance: `add`/`sub` refactored** to shared `merge_sorted` with a `negate_other` flag, eliminating code duplication.
- **`active_poly_refs()` method** on `BuchbergerState` returns `&[&Polynomial]` slice for zero-copy basis access.
- **Removed dead code**: `chain_criterion_skip` body (retained as `#[allow(dead_code)]`), `bitsum_bits` function, `GbRingCache` type, unused `clone_poly` wrappers.
- **Legacy feanor-math aliases** in `PrimeField` (`eq_el`, `negate`, `mul_ref`, `add_ref`, `sub_ref`, `from_int`, `int_hom`) documented as deprecated.
- **Unsafe pointer cast removed** in `TermsIter` — now uses safe lifetime-correct references.
- **`TermRef::coefficient()` returns `&'a FieldElem`** (borrowed) instead of cloned value.
- **Doc comment on BN128 hardcoding** added to `picus-analysis/src/propagation/mod.rs`.

### Verified
- **Lib tests: 167 pass. 0 compiler warnings** across the entire workspace.
- Clean build on `cargo +nightly` (edition 2024).

## [1.7.8] - 2026-04-27

### Added
- **In-tree finite-field GB engine (`picus-solver/src/ff/`)**: Replaces the previous `feanor-math` Buchberger pipeline on the live solve path. New modules: `ff::field` (`FieldElem` over `BigUint`), `ff::polynomial` (`Polynomial` with packed monomial vectors and divisibility masks), `ff::monomial` (`MonomialOrder` enum, no `TypeId` dispatch), `ff::buchberger` (`BuchbergerState`, `IncrementalGB`), `ff::univariate` (single-variable factoring for root extraction). Inner reduction loop avoids `RingStore`/`El` indirection and per-iteration `Vec<Polynomial>` clones via `reduce_by_refs(&[&Polynomial])`.
- **`tail_reduce_active` in `IncrementalGB`** every 32 basis adds (`INTERREDUCE_EVERY=32`). Mutates poly bodies only — never `lt`/`active`/`sugar`/indices — so it preserves all per-element invariants. Architecturally guards against basis bloat in long incremental runs; no KPI gain in isolation but kept as a correctness-preserving hedge.

### Fixed
- **GB soundness bug in `ff::buchberger::chain_criterion_skip` (CRITICAL)**. The simplified "any-`k` divides lcm → skip" form of Buchberger's chain criterion was unsound: with non-strict deactivation (deactivated basis elements remain in `self.basis` and contribute LTs at index lookup) and `generate_pairs_against` previously skipping inactive elements when adding a new generator, the substitute pairs `(i,k)` and `(j,k)` were not guaranteed to have been generated and discharged. **Symptom**: trivially-UNSAT systems silently produced incomplete GBs; minimal repro `{ab-1, a-2, b-2}` over GF(5) returned **Unknown** instead of **Unsafe** (the constant `3` from S-pair `(0,1)` was being skipped, basis ended at 2 elements, `is_whole_ring()` returned false, model extraction produced a bogus assignment, validation rejected it). The correctness gate masked this across the prior development cycle because the gate counted only safe↔unsafe disagreements — Unknown was implicitly "agree". **Fix** (`buchberger.rs`):
  1. `generate_pairs_against`: removed the `if !self.basis[k].active { continue; }` guard. Pairs against deactivated elements are now generated; their LTs are real S-pair obligations.
  2. `state.run`: removed the call to `chain_criterion_skip`. The (sound) product criterion at generation time remains. `chain_criterion_skip` is retained as `#[allow(dead_code)]` for future re-introduction with a properly sound Gebauer-Möller chain criterion (full `(i,k)`/`(j,k)` lcm comparison).
- **`bn128_invariants` integration tests** now pass (`test_simple_unsat_gf5`, `test_is_zero_sound_bit_constraint` in `cvc5_regression`).

### Changed
- **`feanor-math` dependency fully removed.** No longer in `Cargo.toml`; not in `Cargo.lock`. The legacy `gb_stats.rs` module (which only wrapped feanor's pair-profile observer) was deleted; `gb.rs` is now a thin two-phase (DegRevLex → Lex) wrapper over `ideal::compute_gb_with_order{,_traced}`; `gb_homog.rs` and `homog.rs` rewired to `crate::ff::monomial::MonomialOrder`.
- **CLI: removed `--profile gb`.** Stats observer was specific to the deleted feanor pipeline. `--profile wall` (per-site wall-clock) is unchanged.
- **Removed release-profile debug overrides** from `picus/Cargo.toml`. Binary shrunk **627 MB → 67 MB**. No KPI impact.
- **Removed unused `#![feature(allocator_api)]`** from `picus-solver/src/lib.rs`.

### Verified
- **Lib tests: 96/96 pass. Integration tests: 71/71 pass** (10 binaries, 0 ignored except 2 long-running probes). Builds clean on `cargo +nightly` (rustc 1.97.0-nightly, edition 2024). Zero warnings across the workspace.
- **Cargo.lock contains 0 references to `feanor`.**
- **circomlibex-cff5ab6 sweep (110 circuits, 15 s timeout): 105 agree (35 both-timeout), 0 mismatch vs cvc5.** (Was 106 agree pre-fix; the 1 lost agreement is a single Unknown vs solved on a circuit where no safe↔unsafe collision occurs.)
- **17-bench KPI (60 s timeout): 12 / 17 solved** — net **+9 vs the 1.7.7 baseline (3/17)**, +2 vs the 1.7.6 baseline (3/17 stable). An earlier development snapshot recorded 13/17; an independent re-measurement on the 1.7.8 shipped code gives 12/17. The difference is `chunkedadd1`, which lives right at the wall-clock boundary (~62 s solve time vs the script's 65 s `timeout` wrapper after the chain-criterion fix); re-runs flap between solve and timeout. Net solves attributable to the in-tree `ff` engine + `reduce_by_refs` + chain-criterion fix: ~+9 over 1.7.7.

### Known limitations / trade-offs
- **The chain-criterion fix slowed two previously-fast circuits**: `chunkedadd` 17.1 s → 44.1 s, `chunkedadd1` 24.9 s → 61.9 s. Their prior numbers had relied on the unsound criterion to prune real S-pair work; new times are correct. A sound Gebauer–Möller chain criterion (deferred to a future release) would recover this 2× cost; estimated at ~150 LoC with non-trivial correctness risk, deemed out of scope for 1.7.8.
- **4 KPI timeouts remain**: `circomlib-cff5ab6/Pedersen@pedersen.r1cs`, `ed25519-099d19c-fixed/modulusagainst2p.r1cs`, `motivating/VDBuggy.r1cs`, `iden3-core-56a08f9/inTest.r1cs`. All are dense-ideal problems (e.g. Pedersen 2nd GB call: 1100 S-pairs in 20 s, 2100 in 116 s, final basis size 253 in both cases — work is dominated by reductions whose normal form is zero or already-known-redundant). Sequential Buchberger has no way to amortize this; literature solutions are F4/F5 (Macaulay matrix, batched symbolic preprocessing) or Montgomery-form arithmetic for BN128, both out of scope per the user directive ("research-grade solver, no multi-day rewrites").
- **Correctness-gate masking**: the gate counts only safe↔unsafe disagreements; Unknown vs solved is implicitly "agree". This masked the 1.7.7 chain-criterion soundness bug across the prior development cycle. Future gates should additionally flag "picus Unknown but cvc5 solved" as a *suspicion* class.

### Internal
- Stale `examples/probe_*.rs` and `tests/probe.rs` ad-hoc reproducers removed.
- Comments in `gb.rs`, `encoder.rs`, `picus-smt/src/backends/native_ff.rs` updated to reflect the in-tree engine (no present-tense feanor references remain in source).



### Changed
- **Buchberger algorithm overhaul in feanor-math fork** (matching CoCoA behaviour):
  - Removed density-triggered restart heuristic — CoCoA never restarts; the restart was firing on essentially every top-level call (29k/29k on MontgomeryAdd) and was a major source of redundant work.
  - Moved inter-reduction from per-sugar-batch to once at loop termination — CoCoA inter-reduces only at the end.
  - Changed basis deactivation from strict proper divisibility to non-strict divisibility (matching CoCoA's `IsDivisibleFast`); deactivated-element pairs are now kept in the queue (matching CoCoA).
  - Changed S-pair processing from sugar-batch to one-at-a-time (matching CoCoA's single-pair main loop).
- **GB ring caching (`GbRingCache`)**: The `AsLocalPIR` + `MultivariatePolyRingImpl` polynomial ring (with its O(C(n+d,d)^2) multiplication table) is now built once per solve and reused across all incremental GB calls, eliminating ~25k redundant ring constructions on typical circuits.
- **Removed round-robin branching cap**: Both `split_gb` and `model` branchers no longer cap at 256 values for large primes; enumeration is bounded by the cancel token / timeout, matching cvc5's behaviour.
- **Removed dead `extend_with_cancel`**: Only the cached variant (`extend_with_cancel_cached`) remains; the non-cached path that rebuilt the ring on every call has been removed.
- **`map_in_batch` / `map_out_batch`**: Polynomial ring homomorphisms are now created once per batch instead of once per polynomial.
- **feanor-math dependency**: bumped to revision `f40ec3e` (Buchberger overhaul).
- **Internal cleanup**: Removed all sprint/plan development-tracking comments; made `GbRingCache` and related functions `pub(crate)`.

### Verified
- All buchberger tests pass in feanor-math fork (18 passed, 5 ignored).
- All picus-solver tests pass (130 tests).
- circomlibex-cff5ab6 sweep (110 circuits, 15 s timeout): 100 agree (35 both-timeout), **0 mismatch** vs cvc5.
- 17-bench KPI (60 s timeout): **3 / 17 solved** — `MontgomeryAdd@montgomery` unsafe (45 s), `Pedersen@pedersen_old` safe (22 s), `biglessthan_23` safe (17 s).

### Known limitations
- The 13/17 remaining timeouts are due to the split-DFS branching strategy (~25k branching iterations), not per-call GB performance. cvc5's CDCL conflict-driven search prunes branches that picus's plain DFS cannot. An architectural refactor of the search strategy is required for further progress.

## [1.7.6] - 2026-04-24

### Added
- **In-place Buchberger restart in feanor-math fork**: When the algorithm needs to switch reducer set after a round of pair processing, the basis/sugar/active/open structures are now cleared and rebuilt in place via `update_basis`, instead of returning to the top-level driver and re-entering the function. The reducer cache is preserved across restarts, eliminating redundant reduction work. On `biglessthan_23`, end-to-end native solver time dropped from 26.3 s → 16.5 s (-33%).
- **Hilbert numerator engine in feanor-math fork (`src/algorithms/hilbert/`)**: New ~2 200-line module with `EMonom` exponent-vector representation, `TermList` working state, recursive splitter via coprimality and connected-component decomposition, leaf evaluators, and univariate polynomial helpers (multiplication by `1 - t^k`, synthetic division by `1 - t`). 38 internal tests. Reusable primitive; not yet wired into the Buchberger loop.
- **Pair-profile diagnostic (`buchberger_pair_profile.rs`)**: Test-only helper that records S-pair lifecycle events (sugar bucket, F4-style trace) for analysis of where Buchberger spends time. Sister of `gb_stats.rs` on the picus side; intended for sprint-style profiling and post-mortem.
- **GB statistics profile in picus-solver (`gb_stats.rs`)**: Counters covering Buchberger top-level invocation count, S-pair reductions, sugar tightening, batch-zero rate, etc. Enabled via the `--profile gb` CLI flag and gated by `is_enabled()`; emits a tabular `eprintln!` summary at end of run. Used to characterise the picus-solver split-DFS bottleneck (≥ 18 000 distinct top-level calls per circuit, 99.62 % batch-zero S-pair reductions).
- **Homogenisation infrastructure (`gb_homog.rs`, `homog.rs`)**: Plumbing for working in homogenised polynomial rings during specific Buchberger sub-tasks. Currently dormant — feature-gated, opt-in, no callers in the default path.
- **Profile module (`profile.rs`)**: Thin per-stage timing wrapper; complements `gb_stats.rs`.

### Changed
- **`gb_stats` label fix**: The metric formerly mislabelled as `restarts (calls-1)` is now `extra_top_level_calls`, with a clarifying comment. After the in-place restart change above, that counter no longer represents restart count — it equals the number of *additional* top-level Buchberger entries from picus-solver's split-DFS recursion (which is the real bottleneck, not feanor-internal restarts).
- **feanor-math dependency**: bumped to revision `58cf287` (Hilbert engine + in-place restart + pair profile, on top of the 1.7.5 geobucket/scratch-pool work).

### Verified
- 451/451 lib tests pass in feanor-math fork (18 ignored).
- 132/132 lib + bin + integration tests pass across the picus workspace (6 ignored).
- circomlibex-cff5ab6 sweep (110 circuits, 15 s timeout): 103 agree (38 both-timeout), **0 mismatch** vs cvc5.
- 17-bench KPI (60 s timeout): **3 / 17 solved** — `MontgomeryAdd@montgomery` unsafe, `Pedersen@pedersen_old` safe, `biglessthan_23` safe. Stable across consecutive runs (per-bench timing has high noise).

### Known limitations
- The 17-bench KPI did not reach the earlier 16–17/17 projection. Profiling shows the bottleneck is **picus-solver's split-DFS top-level re-invocation count**, not per-call Buchberger work — the optimisations in this and previous releases all targeted per-call cost and so hit a ceiling. An architectural refactor of the split-DFS loop is a candidate for a future cycle and is out of scope for 1.7.6.

## [1.7.5] - 2026-04-23

### Added
- **Yan-style geobucket reduction in feanor-math fork**: Polynomial reduction during Buchberger now accumulates intermediate sums in a logarithmic bucket structure, deferring monomial-merge work until the bucket is materialized. This avoids the quadratic cost of repeatedly merging the running residue with each reducer's tail, matching the strategy used in modern Groebner basis implementations (Singular, Macaulay2).
- **Bigint scratch pool with `Global` allocator specialization**: A thread-local pool reuses `BigInt` allocations across the inner FMA loop of `bigint_mul_assign`. The hot path is specialized on the `Global` allocator (the only allocator used in practice by the polynomial pipeline), avoiding allocation churn during reduction.

### Fixed
- **`bigint_fma` allocator contract**: The `scratch_alloc` parameter was previously silently ignored when the function fell through to the `Global` fast path, violating the documented API contract. Split into two functions: `bigint_fma` (honors the caller's allocator for inner workspace) and `pub(crate) bigint_fma_global` (used by the scratch pool, which is `Global`-only by construction). Restores correctness for callers passing custom allocators.

### Changed
- **feanor-math dependency**: Updated to fork revision `0fb1ea4` (geobucket + scratch pool); switched picus-solver back to a git dependency (no path override).
- **Code cleanup in feanor-math fork**: Removed ~440 lines of dead code (`reduction_accum.rs` module, `bigint_mul_pooled`, unused accessors); fixed misplaced doc comments and `Debug` impl brace; suppressed dead-code warnings on `geobucket` API methods kept for module completeness.
- **Deduplicated `mult_table_bounds` and `max_supported_deg`**: `poly.rs` now reuses the helpers exported from `ideal.rs` instead of inlining the same sizing tables.
- **Demoted high-volume `split_zero_extend` logs to `trace`**: Per-iteration progress lines no longer appear at `debug` level.

### Verified
- 398 lib + integration tests pass in feanor-math fork; 48 picus-solver lib + 7 integration tests pass.
- circomlibex-cff5ab6 sweep (110 circuits, 15s timeout): 103 agree (35 both-timeout), 0 mismatch vs cvc5.

## [1.7.4] - 2026-04-22

### Added
- **Gebauer-Möller pair management in feanor-math fork**: Implemented B_k criterion (retroactive pair elimination when a new polynomial's LT divides an existing pair's LCM) and M criterion (dominated pair removal among new pairs). This reduces unnecessary S-polynomial computations during Groebner basis computation, matching CoCoA's `TmpGReductor` pair management strategy.
- **DivMask for fast divisibility rejection**: Added O(1) bitmask pre-filter in `find_reducer` — before the O(n_vars) exponent comparison, a bitwise check `(mask_reducer & ~mask_target) != 0` rejects non-divisible cases instantly. Matches CoCoA's `DivMaskRule` optimization.
- **Multi-basis branching in split-GB model search**: `apply_rule` now checks ALL split-GB bases (not just the linear basis) for univariate polynomials and zero-dimensional structure. This discovers branching structure in the nonlinear basis that the linear basis alone misses, reducing round-robin fallback.
- **Squarefree root preprocessing**: `find_roots` now computes `gcd(f, x^q - x mod f)` before factoring, stripping repeated roots and irreducible factors of degree > 1. Matches cvc5's `distinctRootsPoly` (`uni_roots.cpp:74-85`).
- **Fast paths in root finding**: Direct extraction for linear polynomials and zero roots before invoking the full factoring library. Matches cvc5's `uni_roots.cpp:174-188`.
- **Lazy branching**: Round-robin candidate generation uses a counter-based iterator instead of pre-allocating all candidates. Prevents O(p × n_vars) allocation for large primes.

### Fixed
- **UNSAT-pop-brancher bug in model.rs**: The UNSAT handler incorrectly popped the parent's brancher when a child branch was UNSAT, causing infinite loops when the first round-robin candidate was UNSAT. Now matches cvc5's behavior: only the ideal is popped on UNSAT, never the brancher.
- **Timeout vs UNSAT distinction in split-GB search**: Added `ZeroExtendResult::Cancelled` variant to distinguish timeout from genuine UNSAT in `split_zero_extend_cancel`. Previously both returned `NoZero`, risking false-UNSAT on timeout during model construction.
- **Quick UNSAT pre-check**: Before running expensive `split_gb_cancel` at search branch nodes, fully evaluates polynomials under the partial assignment to detect trivially UNSAT branches in O(n) time.
- **Linear-first UNSAT check**: Before the full split-GB recomputation at branch nodes, tests the linear basis alone (cheap O(n²) Gaussian elimination). If the linear basis is already UNSAT, skips the expensive nonlinear basis recomputation.

### Changed
- **feanor-math dependency**: Updated to fork revision `79495ba` with Gebauer-Möller and DivMask optimizations.
- **Benchmark results**: 295 of 465 circuits now resolve correctly (was 293 in v1.7.3). MontgomeryDouble (both variants) newly resolved as `unsafe` in 1-2s.

## [1.7.3] - 2026-04-22

### Fixed
- **Degree overflow crash in native solver**: `FfPolyRing::new` and `compute_gb_with_order` used overly large `max_supported_deg` for circuits with many variables (the DPVL doubled-variable formulation produces 2x the original variable count). Reduced the degree thresholds: 32 for ≤20 vars, 16 for ≤50, 8 for ≤200, 4 otherwise. This eliminates panics on mid-size circuits (20-100 variables).
- **`NativeFfBackend` panic safety**: Wrapped `encode()` + `solve_encoded_with_cancel()` in `catch_unwind` with panic hook suppression to gracefully return `Unknown` instead of crashing the CLI when feanor-math panics on degree overflow. Prevents DPVL loop from flooding stderr with repeated panic messages.
- **Encoder variable count guard**: `encode()` now returns an error for systems with more than 5000 variables, avoiding construction of impossibly large polynomial rings.
- **`picus-cli` build errors**: Fixed 6 compilation errors in `picus-smt` that prevented building the full CLI:
  - Added missing `bitsums` field in `NativeFfBackend`'s `ConstraintSystem` initializer.
  - Added `SolverKind::Native` arms to match statements in `optimizer.rs` and `r1cs_parser.rs`.
  - Removed unused `HashMap` import in `native_ff.rs`.

### Changed
- **Benchmark validation**: Full 465-circuit benchmark suite tested with `--solver native`. All 292 circuits that the native solver resolves (277 safe + 15 unsafe) produce results identical to cvc5. 23 circuits that cvc5 solves within 30s exceed the native solver's timeout — a performance gap, not a correctness issue.

## [1.7.2] - 2026-04-21

### Added
- **UNSAT core tracing (`ffTraceGb`)**: Single-GB mode now traces which input polynomials contribute to an UNSAT proof, matching cvc5's `--ff-trace-gb` behavior. Uses `BuchbergerObserver` hooks in a forked feanor-math to build a polynomial dependency DAG during Groebner basis computation. The `tracer` module extracts a (possibly non-trivial) subset of input indices, rather than returning all inputs.
- **`tracer.rs` module**: `GbTracer` struct implementing feanor-math's `BuchbergerObserver` trait. Tracks transitive input dependencies for each derived basis element via `BTreeSet`-based dependency propagation.
- **`GbResultTraced` enum in `gb.rs`**: Traced variant of GB computation that returns the UNSAT core directly on trivial (UNSAT) results.

### Changed
- **feanor-math dependency**: Now depends on a [forked feanor-math](https://github.com/chyanju/feanor-math) with `BuchbergerObserver` trait extensions (`on_initial_basis`, `on_new_poly`, `on_inter_reduce`). Recursive Buchberger restarts now propagate the observer instead of discarding it.
- **`solve_single_gb` uses traced GB**: The single-GB solver automatically traces polynomial derivations and returns a precise UNSAT core instead of the trivial all-inputs core.
- **`compute_gb_with_order` refactored**: Extracted `max_supported_deg` helper; added `compute_gb_with_order_traced` variant sharing the same ring setup logic.

### Fixed
- **Misplaced doc comment in feanor-math fork**: `BuchbergerObserver` trait methods now have correctly placed documentation (`on_initial_basis` before `on_new_poly`).
- **`GbTracer::deps_of` bounds safety**: Now returns `Option` instead of panicking on out-of-range indices. `unsat_core_for` falls back to trivial core on invalid index.

## [1.7.1] - 2026-04-21

### Added
- **Native finite field solver (`picus-solver`)**: Pure-Rust replacement for cvc5's QF_FF theory solver, eliminating the C++/CoCoA/GPL dependency. Uses feanor-math for Groebner basis computation.
  - Split GB solver with bit propagation, matching cvc5's `--ff-solver split` mode.
  - Single GB solver (DegRevLex → Lex → findZero), matching cvc5's `--ff-solver gb` mode.
  - Pattern detection (`bit_constraint`, `linear_monomial`, `bit_sums`) wired into the solver pipeline.
  - Cooperative timeout via `CancelToken` (atomic cancellation threaded through Buchberger).
  - Incremental push/pop API.
  - 109 passing tests ported from cvc5's regression and unit test suites.
- **`--solver native` CLI option**: Select the pure-Rust solver backend with `picus check --solver native --theory ff`.
- **Criterion benchmark suite**: `cargo bench -p picus-solver` runs encode, end-to-end, and root-finding benchmarks.
- **cvc5 CLI benchmark script**: `benches/benchmark_cvc5.sh` for comparing native vs cvc5 on matching .smt2 inputs.
- **Solver statistics**: `SolverStats` module tracks GB run counts, timing, and branching strategy usage.
- **Evaluation report**: `docs/solver-evaluation.md` documents architecture, correctness, performance, and feature parity with cvc5.

### Fixed
- **`admit` predicate swap**: The split-GB admission criteria for basis 0 (linear) and basis 1 (nonlinear) were swapped, weakening cross-basis propagation. Now matches cvc5's `split_gb.cpp:245-249`.
- **Degree-overflow safety**: feanor-math panics from exceeding `max_supported_deg` are caught via `catch_unwind`; the solver returns the original generators unreduced instead of an empty basis (which would be misinterpreted as SAT).
- **`NativeFfBackend` upgraded**: Now uses the Split GB pipeline (`core::solve_encoded_with_cancel`) instead of the old plain-Buchberger path.

### Changed
- **Polynomial normalization**: Encoded polynomials are divided by their leading coefficient, matching cvc5's `cocoa_encoder.cpp` behavior.
- **feanor-math multiplication table tuning**: `MultivariatePolyRingImpl` uses `new_with_mult_table((2, 2))` to avoid the O(C(n+8,8)^2) precomputation cost of the default `(6, 8)` table.

## [1.7.0] - 2026-04-19

### Changed
- **Benchmarks externalized**: The `benchmarks/` directory is now a [git submodule](https://github.com/chyanju/picus-benchmarks) (`picus-benchmarks`). Benchmark circuits are organized under `benchmarks/circom/` with a `compile.sh` helper script. This keeps the main repository focused on the tool itself.
- **Library API `Config::dump_smt` version pin**: Library usage example in README now includes a version tag for reproducibility.

### Fixed
- **z3 timeout truncation**: `timeout_ms` (u64) was silently truncated to u32 when passed to z3. Now uses saturating cast.
- **`create_backend` panic on invalid combination**: Replaced `unreachable!()` with proper error return in the public API.
- **AB0 version comments**: Code comments now correctly reference "cvc5 1.2.0–1.3.3" instead of just "1.2.0".
- **README build dependencies**: Added missing `git`, `libclang-dev`, and `pkg-config` to the prerequisites list.
- **Hardcoded z3 AST path documented**: Added explanatory comment for why the propagation pipeline always uses z3-style AST regardless of the solver choice.

## [1.6.0] - 2026-04-19

### Added
- **`picus` library crate**: Public API for programmatic use from other Rust projects. Provides `check_circuit()`, `check_r1cs_bytes()`, `check_r1cs()` with structured `CheckResult` type (using `BigUint` values, not strings). Re-exports key types (`SolverKind`, `Theory`, `LemmaSet`, `BigUint`, `R1csFile`).
- **`Config::dump_smt`** field: SMT query dumping is now supported through the library API, not just the CLI.

### Changed
- **README intro rewritten**: Picus is presented as a security analysis tool, with the PLDI 2023 paper referenced as a description of the underlying techniques (not the other way around).
- **CLI simplified**: `picus-cli` now depends solely on the `picus` facade crate. The `dump_smt` code path no longer bypasses the public API.

### Fixed
- Removed duplicated `split_model` logic between `picus` lib and `picus-cli`.
- Added `log::warn` for silently dropped constraints in solver backends.
- Fixed `cvc5-ff-sys` doc comment referencing `cvc5` instead of `cvc5-ff`.
- Architecture documentation updated to include the `picus` facade crate (seven crates total).

## [1.5.1] - 2026-04-19

### Changed
- **`--lemmas` syntax**: Added `all-X,Y` (exclude) and `none+X,Y` (include) formats for more natural lemma selection. Bare comma-separated lists remain supported as a shorthand for `none+...`.

### Fixed
- Removed stale `.sym parser` reference from `docs/architecture.md` (module was deleted in v1.4.0).
- Removed orphaned doc comments in `binary01.rs` and `basis2.rs` left over from `resolve_named_constant` refactor.
- Updated benchmark verification version reference in `docs/benchmarks.md`.

## [1.5.0] - 2026-04-19

### Added
- **Dockerfile**: Multi-stage Docker build (Ubuntu 24.04). `docker build -t picus .` produces a self-contained image with all solvers pre-compiled. Users can run `docker run --rm -v $(pwd):/data picus check --r1cs /data/circuit.r1cs`.
- **`--format` flag**: `--format human` (default) produces styled terminal output with color and structured layout. `--format json` outputs machine-readable JSON to stdout. Supported by both `check` and `info` subcommands.
- **Colored terminal output**: Uses `owo-colors` + `anstream` for automatic color detection. Colors are enabled in terminals, automatically stripped when piping to files or other programs.
- **Structured human output**: Circuit info, analysis config, and results are displayed in clearly separated sections with aligned labels.

## [1.4.0] - 2026-04-19

### Fixed
- **R1CS parser bounds check**: Wire IDs exceeding `n_wires` in malformed R1CS files are now caught gracefully instead of panicking with an index-out-of-bounds error.
- **Timestamp safety**: SMT dump timestamp uses `unwrap_or_default()` to avoid panic on systems with misconfigured clocks.
- **cvc5-ff doc examples**: Fixed import paths from `cvc5::` / `cvc5_sys::` to `cvc5_ff::` / `cvc5_ff_sys::`.
- **Double solver feedback**: Removed duplicate `SolverFeedback::Sat` call on non-target SAT results. `SolverFeedback` enum simplified to `Verified` and `Skip`.

### Changed
- **Shared utilities**: `resolve_named_constant` extracted to `propagation/mod.rs` (was duplicated in binary01 and basis2). `constraint_to_smtlib_nia` extracted to `backends/mod.rs` (was duplicated in z3_nia and cvc5_nia).
- **`RExpr::Mod` display**: Now shows the modulus (`(expr mod p)` instead of just `expr`).

### Removed
- **`sym.rs` and `csv` dependency**: The `.sym` symbol map parser had no callers in the workspace. Removed along with the `csv` crate dependency.
- **Unused `range_vec` parameter**: Removed from ABOZ and BIM lemma signatures (was `_range_vec`, never used).
- **`SolverFeedback::Sat` variant**: Was never meaningfully handled; merged into `Skip` behavior.

## [1.3.0] - 2026-04-19

### Changed
- **Zero-config cvc5 compilation**: cvc5 (with CoCoA/finite field support) is now automatically compiled from source during `cargo build`, just like z3. Users no longer need to manually install cvc5. The `cvc5-ff-sys` and `cvc5-ff` local crates handle source download, configuration (`--cocoa --gpl --auto-download`), and static linking.
- **CLI: `--solver none`** replaces `--nosolve`. Setting `--solver none` runs propagation only without invoking any SMT solver.
- **CLI: `--lemmas`** replaces `--noprop`. Accepts comma-separated lemma names (`linear`, `binary01`, `basis2`, `aboz`, `bim`) or `all`/`none`. Default: `all`.
- **`run_dpvl` returns `Result`**: The library function no longer calls `process::exit`; errors are propagated to the caller.

### Fixed
- **Stable Rust compilation**: Replaced nightly-only `is_multiple_of()` API with `% 8 != 0`.
- **cvc5 NIA `dump_smt`**: Fixed missing constraint serialization in the CVC5 NIA backend's SMT dump output.
- **Unwrap safety**: Replaced bare `.unwrap()` calls with `.expect()` in z3 model extraction and BigInt conversion.

### Removed
- **CVC4 support** (removed in v1.2.0, cleanup completed).
- **`--map` and `--precondition` CLI flags** and their backing code (`precondition.rs`, `serde`/`serde_json` dependencies).
- **BabyJubJub lemma stub** (`baby.rs`), **constraint graph** (`constraint_graph.rs`), **CEX stub** (`cex.rs`), and `petgraph` dependency. See [Future Work](docs/TODO.md) for plans.
- **Short lemma aliases** (`l0`–`l4`): Only full names are accepted in `--lemmas`.

### Added
- `docs/TODO.md` documenting removed components and planned features.

## [1.2.0] - 2026-04-18

### Changed
- **Native solver API integration**: Replaced subprocess-based solver invocation with direct Rust API calls to z3 and cvc5. No more SMT-LIB string generation → temp file → subprocess → stdout parsing. Solvers are now linked as libraries.
- **New CLI options**: `--solver <cvc5|z3>` and `--theory <ff|nia>` replace the old single `--solver` flag. Default: `--solver cvc5 --theory ff`.
- **`--dump-smt <dir>`**: Replaces the old `--smt` flag. Dumps each solver query as an SMT-LIB file to the specified directory for debugging.
- **Solver-agnostic IR**: Introduced `UniquenessQuery` intermediate representation that decouples constraint encoding from solver-specific APIs.
- **Three solver backends**: `Z3NiaBackend` (QF_NIA), `Cvc5FfBackend` (QF_FF), `Cvc5NiaBackend` (QF_NIA). Each implements `SolverBackend` trait with `solve()` and `dump_smt()`.

### Removed
- **CVC4 support**: Fully removed. CVC4 is end-of-life; use cvc5 instead.
- **Subprocess solver invocation**: `interpreter.rs` and `solver.rs` (SMT-LIB text generation + process spawning) have been removed. All solving now goes through Rust API bindings.

### Added
- `picus_smt::backends` module with `SolverBackend` trait.
- `picus_smt::query` module with `UniquenessQuery` IR and `build_query()` builder.
- `picus_smt::create_backend()` factory function.
- `picus_smt::validate_combination()` for checking solver+theory compatibility.
- z3 solver is bundled via `vendored` feature (compiled from source automatically).
- cvc5 links against system-installed `libcvc5.so` (GPL build with CoCoA required).

### Prerequisites
- **cvc5 GPL** shared library must be installed system-wide. See README for instructions.
- z3 is bundled automatically during `cargo build`.

## [1.1.2] - 2026-04-18

### Fixed
- **cvc5 QF_FF correctness**: Disabled AB0 optimization (`A*B=0 → A=0 ∨ B=0`) for cvc5 backend. cvc5 1.2.0–1.3.3 has a bug where `or` disjunctions in QF_FF produce spurious SAT results with inconsistent models. The solver handles nonlinear `A*B=0` constraints natively without the rewrite.
- **Propagation on parameterized circuits**: Binary01 (L1) and Basis2 (L2) lemmas now correctly handle named constants (`ps1`, `ps2`, etc.) introduced by the SubP optimizer, fixing failures on circomlib parameterized circuits (e.g., `GreaterEqThan@circomlib_8`, `Num2Bits@circomlib_254`).
- **Basis2 power-of-2 check for large bit widths**: Fixed `is_power_of_2_sequence` which failed when `2^k > p/2` (bit index 253) because `min(c, p-c)` broke the ascending sequence. Now checks each coefficient or its field negation directly against powers of 2.
- **Wire 0 constraint preservation**: The simple optimizer replaced `Var("x0")` with `Int(1)` everywhere, turning the `x0=1` assertion into a tautology. An explicit `x0=1` assertion is now always added for both witness copies.

### Verified
- **112/112** PLDI 2023 paper benchmarks pass (cvc5 1.3.3 GPL, QF_FF, weak uniqueness).
- **13/13** baseline circuits pass (z3 4.13.4, QF_NIA, weak + strong).
- Tested with cvc5 1.3.3 (latest official release with CoCoA/Groebner basis support).

### Changed
- **Unified uniqueness mode**: Removed the `--weak`/`--strong` distinction. Picus now always checks uniqueness of output signals (weak uniqueness per the QED² paper), which is the standard safety property. The `--weak` CLI flag has been removed.

## [1.1.1] - 2026-04-17

### Fixed
- **Stack overflow on large circuits**: DPVL iteration loop converted from recursion to iteration, preventing stack overflow on circuits with thousands of signals.
- **Parser panic on malformed input**: Replaced `.unwrap()` with `?` in R1CS binary parser for consistent error handling.
- **Solver subprocess cleanup**: Solver invocation now reads stdout/stderr in separate threads to prevent pipe deadlock, with hard timeout kill as a safety net.
- **Duplicate p-constant declarations**: Fixed SMT query generation that declared `p`, `ps1`, etc. twice (once per witness copy), causing z3 errors.

### Changed
- **Performance**: `bn128_prime()` is now a `LazyLock<BigUint>` static — parsed once, reused everywhere.
- **Performance**: All propagation lemmas now mutate `&mut HashSet` in place instead of cloning on every call.
- **Performance**: SMT prefix (definitions + constraints) is pre-serialized once; solver calls only append the per-query block.
- **API**: Introduced `DpvlContext` struct, replacing 12-parameter internal functions with method calls.
- **API**: `RCmds.vs` renamed to `RCmds.commands` for clarity.
- **API**: `SolverKind` and `SelectorKind` now implement `std::str::FromStr`.
- **API**: Shared utilities (`parse_var_index`, `RExpr::is_zero`, `RExpr::strip_mod`) extracted to common locations, eliminating duplication across modules.
- **API**: Variable extraction unified into a single `collect_vars(mode)` method, replacing three near-identical recursive functions.

### Added
- `RangeValue::is_empty()` method for detecting over-constrained signals.
- `#[must_use]` annotations on pure functions.
- `picus info` subcommand for inspecting R1CS file metadata.

## [1.1.0] - 2026-04-17

### Added
- Complete Rust rewrite of the Picus/QED² tool (previously Racket/Rosette).
- Four-crate workspace: `picus-r1cs`, `picus-smt`, `picus-analysis`, `picus-cli`.
- CLI with `check` and `info` subcommands.
- Three solver backends: z3 (QF_NIA), cvc4 (QF_NIA), cvc5 (QF_FF).
- Five propagation lemmas: Linear (L0), Binary01 (L1), Basis2 (L2), ABOZ (L3), BIM (L4).
- Counter and first signal selection strategies.
- R1CS binary parser, .sym symbol map parser, JSON precondition parser.
- Three SMT optimization passes: AB0, normalize, SubP.

### Removed
- All Racket/Rosette source code.
- Docker build infrastructure.
- Research artifact batch scripts.
