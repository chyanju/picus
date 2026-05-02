# picus-solver Evaluation Report

This document evaluates `picus-solver`, the pure-Rust finite field (QF_FF) solver that replaces cvc5's Split GB / CoCoA backend in Picus.

## 1. Architecture Overview

`picus-solver` is a from-scratch Rust reimplementation of cvc5's finite field theory solver. It faithfully replicates cvc5's Split Groebner Basis algorithm, including:

| Component | cvc5 (C++ / CoCoA) | picus-solver (Rust, in-tree) |
|-----------|--------------------|------------------------------|
| Polynomial ring | CoCoA `SparsePolyRing` | `ff::polynomial::Polynomial` (`BigUint` coeffs, packed exponents, divisibility masks) |
| Groebner basis | CoCoA `GBasis` | `ff::buchberger::{BuchbergerState, IncrementalGB}` |
| Split GB | `theory/ff/split_gb.cpp` | `split_gb.rs` |
| Model search | `theory/ff/multi_roots.cpp` (`findZero`, `splitFindZero`) | `split_gb.rs` (`split_find_zero`, `split_zero_extend`) |
| Univariate roots | `theory/ff/uni_roots.cpp` (CoCoA factor) | `roots.rs` (Cantor-Zassenhaus, in-tree `ff::univariate`) |
| Bit propagation | `theory/ff/bitprop.cpp` | `bitprop.rs` |
| Pattern detection | `theory/ff/parse.cpp` | `parse.rs` |
| UNSAT core | `theory/ff/core.cpp` (trivial mode) | `core.rs` (trivial mode) |
| Incremental | CDContext push/pop | `incremental.rs` (fact-stack + height markers) |
| Encoding | SMT Node → CoCoA polynomial | `encoder.rs` (ConstraintSystem → polynomial) |

### Key differences from cvc5

- **No Boolean layer**: cvc5's FF solver sits below a SAT/DPLL(T) engine that handles `or`, `ite`, `=>`, `not`, and uninterpreted functions. `picus-solver` operates purely at the polynomial constraint level. This means ~25 of cvc5's 42 `regress0/ff/` tests (which require Boolean reasoning) are not applicable.
- **No CoCoA dependency**: All Groebner basis computation uses an in-tree pure-Rust engine (`src/ff/`). No C++ libraries, no GPL dependency, no external GB crate.
- **Cooperative timeout**: Implemented as an atomic cancellation token, plumbed through the Buchberger inner loop and the recursive model search.

## 2. Correctness

### Test coverage

| Test file | Tests | Source |
|-----------|-------|--------|
| `lib.rs` unit tests | 48 | Solver internals (field, poly, ideal, parse, bitprop, split_gb, core, incremental, timeout, stats, tracer, roots) |
| `cvc5_regression.rs` | 9 | Direct ports of `regress0/ff/*.smt2` |
| `cvc5_extended.rs` | 14 | Extended ports of additional cvc5 regression tests |
| `cvc5_unit_uni_roots.rs` | 5 | Ports of `theory_ff_uni_roots_black.cpp` |
| `cvc5_unit_multi_roots.rs` | 15 | Ports of `theory_ff_multi_roots_black.cpp` |
| `cvc5_unit_split_gb.rs` | 4 | Ports of `theory_ff_split_gb_black.cpp` (randomized) |
| `cvc5_unit_parse.rs` | 11 | Ports of `theory_ff_parse_white.cpp` |
| `integration.rs` | 6 | End-to-end integration tests |
| `timeout.rs` | 7 | Cooperative timeout integration tests |
| **Total** | **119** | (+ 4 ignored perf/probe tests) |

### A/B correctness guarantee

Every portable cvc5 test produces the same SAT/UNSAT outcome in `picus-solver`. For SAT outcomes, the returned model is verified to satisfy all input constraints.

### Coverage gaps

The following cvc5 features are **not implemented** (they live in cvc5's Boolean/SAT layer, above the FF theory solver):

- Boolean connectives (`or`, `not`, `=>`, `ite`)
- Uninterpreted functions (`with_uf*` tests)
- Disjunctive bit constraint elimination
- Resource manager / `tlimit_per`

Non-trivial UNSAT core tracing (`ffTraceGb`) is implemented for single-GB mode. Split-GB mode returns trivial (all-input) cores. See `docs/TODO.md` for remaining limitations.

These are architectural boundaries, not bugs. A full SMT solver built on top of `picus-solver` would handle these at the SAT/DPLL(T) level.

## 3. Performance

### Native solver benchmarks (Criterion)

| Benchmark | Encode | End-to-end |
|-----------|--------|------------|
| `issue10937_gf7` (11 vars, UNSAT) | 168 µs | 678 µs |
| `bigff_is_zero_bn128` (4 vars, BN128 prime, UNSAT) | 2.46 ms | 3.39 ms |
| `field_poly_gf7` (8 vars, field polys, UNSAT) | 175 µs | 3.09 ms |
| `random_6var_gf11` (6 vars, SAT) | 173 µs | 4.34 ms |

| Root finding | Time |
|-------------|------|
| `degree4_gf7` | 103 µs |
| `degree2_curve25519` (2^255-19) | 8.33 ms |

### cvc5 CLI benchmarks (same problems)

| Benchmark | cvc5 avg (µs) | cvc5 min (µs) |
|-----------|---------------|----------------|
| `issue10937` (UNSAT) | 8,603 | 7,687 |
| `bigff_is_zero_sound` (UNSAT) | 10,653 | 9,193 |
| `field_poly` (UNSAT) | 8,699 | 7,421 |
| `simple` (UNSAT) | 9,903 | 8,697 |
| `univar_conjunction_sat` (SAT) | 8,937 | 8,042 |
| `univar_conjunction_unsat` (UNSAT) | 8,823 | 7,754 |

### Comparison

> **Important caveat**: cvc5 CLI times include process startup, SMT-LIB parsing, type checking, Boolean abstraction, and result printing. The native solver times are pure computation (no I/O, no parsing). A fair comparison would measure cvc5's internal FF theory solver time only, which is not easily accessible from the CLI. The numbers below are therefore **upper bounds** on the cvc5 overhead and **lower bounds** on the speedup.

| Problem | picus-solver | cvc5 CLI | Ratio |
|---------|-------------|----------|-------|
| `issue10937` | 678 µs | 8,603 µs | ~12.7x faster |
| `bigff_is_zero` | 3,390 µs | 10,653 µs | ~3.1x faster |
| `field_poly` | 3,090 µs | 8,699 µs | ~2.8x faster |

### Performance note: in-tree GB engine

Earlier picus releases used `feanor-math`'s `MultivariatePolyRingImpl`, whose `new` defaulted to a multiplication table size of `(6, 8)` and precomputed `O(C(n+8,8)^2)` monomial products — this caused multi-second startup per ring construction with 11+ variables, and `buchberger_simple` re-created the ring on every call. As of v1.7.9, picus-solver uses a from-scratch in-tree engine (`src/ff/`) over `BigUint` with packed monomial vectors and divisibility masks; ring construction is O(n_vars) and there is no precomputed monomial table at all. The hot reduction loop avoids `RingStore`/`El` indirection and per-iteration `Vec<Polynomial>` clones via `reduce_by_refs(&[&Polynomial])`.

Subsequent releases brought the engine into close algorithmic alignment with CoCoA's `myDoGBasis` for the non-homogeneous code path:

- **v1.7.10** added the geobucket data structure (`src/ff/geobucket.rs`, mirroring CoCoA `geobucket.C`) and rewired `reduce_by_refs` to use it — each reduction step is now O(D · log(N/D)) instead of O(N + D), matching CoCoA's `ChooseReductionCogGeobucket` strategy. The same release added the Gebauer-Möller M-criterion at S-pair generation time (`myGMInsert`).
- **v1.7.11** added the companion B-criterion (`myApplyBCriterion`) at basis-add time, switched pair generation to skip inactive basis elements (matching CoCoA's `IsActive` filter), reduced final interreduce from a fixed-point loop to a single pass (`myFinalizeGBasis`-style), and removed the prior in-loop tail-reduce throttle (CoCoA does no in-loop interreduction for non-homogeneous inputs).
- **v1.7.12** swapped the `BigUint` arithmetic backend for GMP via the `rug` crate, matching CoCoA's `mpz_t`-based `BigInt` (`include/CoCoA/BigInt.H:41`); aligned the geobucket bucket constants with CoCoA's (`gbk_minlen=128`, `gbk_factor=4`, `gbk_max=20` from `geobucket.C:36-38`) which dramatically reduced cascade frequency; tightened the sugar update at S-poly construction to mirror CoCoA's `myAssignSPoly` (`TmpGPoly.C:316`); installed a pair-free seed path in `compute_gb_incremental_with_order` (the previous `add_generators(known_gb)` was generating O(n²) S-pairs that all reduced to zero by Buchberger's criterion); added a no-op skip in `Ideal::extend_with_cancel` (pre-reduce new generators against the existing reduced GB and short-circuit when every input reduces to zero); replaced the per-DFS-branch basis clone in the linear-only quick UNSAT pre-check with a direct `assign_poly mod basis[0]` reduction (sound because for a linear basis Buchberger ≡ Gauss-Jordan); and threaded the cancel token through every reduction hot path (`reduce_by_refs_cancel`, `Ideal::reduce_with_cancel` / `contains_with_cancel`, `interreduce_with_cancel`, `BitProp::get_bit_equalities_with_cancel`) so `--timeout` is now honored within a single dense reduction instead of only at coarse-grained boundaries.
- **v1.7.13** introduced cross-iteration memoization in the split-GB propagation loop (`split_gb_cancel` / `split_gb_extend_cancel`): a `HashSet<(content_hash(p), basis_idx)>` records polynomials known to be members of each basis, pre-populated each iteration with self-membership facts and updated with positive results as the loop runs. Sound by ideal-membership monotonicity during a fixpoint call. On `modulusagainst2p`, 99.9 % of the pre-memo `contains_with_cancel` calls returned true; the memo eliminates these as direct redundant work, dropping `contains` time from ~62 s to ~0.4 s and recovering the circuit under the 60 s KPI gate. The same release added a move-based polynomial merge (`Polynomial::merge_owned` plus `field.add_owned` / `sub_owned` / `neg_owned`) that recycles `mpz_t` allocations through the geobucket cascade rather than cloning, borrowed leading-term info in `reduce_by_refs_geobucket` (saves the per-divisor `Vec<u16>` clone), a degree-sorted divisor scan with early-break gated to large divisor sets (≥ 64), and `PICUS_GB_STATS=1` / `PICUS_GB_TRACE=1` instrumentation surfaces (split-GB driver counters, per-phase reducer timers, per-iteration trace).
- **v1.7.15** is engine-tightening rather than alignment: at this point picus and cvc5+CoCoA are structurally aligned on every QF_FF theory entry-point, so this release tunes the underlying Buchberger engine. It adds (1) a thread-local `FieldElem` allocation pool with auto-recycling Drop impl that eliminates one mpz allocation per coefficient operation on the geobucket cascade path; (2) GMP in-place arithmetic (`add_assign` / `sub_assign` / `add_owned` / `sub_owned`) on the cross-bucket coefficient-sum and merge-owned paths; (3) a 128-bit `DivMask` (was 32-bit) so divisibility-rejection covers all variables on circuits with > 32 vars (e.g. `inTest`'s 571 vars, where the original 32-bit scheme gave no useful filter signal beyond the first ~32); (4) a sorted divisor bucket with early-break gated to ≥ 256 divisors (was ≥ 64). It also lands sub-iter resumable cache primitives in `IncrementalGB` (`run_only`, `set_cancel_token`, `is_quiescent`) and an `IncrementalSolverContext::partial_build` fallback that resumes a cancelled cache rebuild across solve-call boundaries when the per-call budget is too small to complete the build in one shot. Cumulatively the engine is ~16 % faster on `inTest`'s cold GB build (75.9 s → 63.7 s under PICUS_GB_STATS), still over the 60 s gate.

  An opt-in **F4-lite** scaffold (`ff/f4.rs`, `PICUS_USE_F4=1`) was added in this release: sugar-batched S-pair processing with symbolic preprocessing (BFS closure under reducibility) and sparse row-echelon over GF(p). This is **not** an alignment item — cvc5+CoCoA's solver uses classical Buchberger (CoCoA `GReductor`); F4 is **out of scope for cvc5+CoCoA** and is included here as a picus-specific direction for future work where larger sugar batches make the matrix amortization win materialize. F4-lite is correctness-validated end-to-end (5 unit tests including multi-pair property tests cross-checking against the per-pair geobucket reference; full 110-circuit gate produces 0 mismatches with the flag enabled) but currently slower than the geobucket path on the present circuit set, so it stays gated off by default.

- **v1.7.14** brought four further structural alignments. (1) An `IncrementalSolverContext` solver-state cache held inside `NativeFfBackend` mirrors cvc5's `SubTheory` fact-accumulation pattern (`sub_theory.cpp:62-90`, `sub_theory.h:112`'s `context::CDList<Node> d_facts`): the encoded constraint side and computed split-GB are cached across `solve_encoded` calls within a session; on a hit the per-query Rabinowitsch disequality polynomial is encoded in the cached ring and added via `Ideal::extend_with_cancel`. The cache is lazy-built (only after seeing 2+ same-digest calls) so circuits with all-distinct constraint sides pay no overhead; `PICUS_NO_INCREMENTAL_CACHE=1` disables it for diagnostics. (2) A hash-bucketed divisor index in `reduce_by_refs_geobucket` groups divisors by their `DivMask` bits and iterates only buckets whose mask is a submask of the current LT's, mirroring CoCoA's `Reductors` (`TmpGReductor.H:65-100`) fast-lookup structure; gated to ≥ 64 divisors. (3) AST-level int-literal folding in `simple_opt_expr_z3` for `+` and `*` (sum / product of `Int` children, with canonical position) explicitly mirrors cvc5's `theory_ff_rewriter.cpp:45-150` postRewriteFfAdd / postRewriteFfMul, even though picus's polynomial-level merging already produced the equivalent canonical form post-encoding. (4) A HOMOG-gated periodic in-loop tail-reduce in `BuchbergerState::run` (every 32 useful S-pair reductions on homogeneous input), mirroring CoCoA `myDoGBasis`'s `TmpGReductor.C:680, 710-721` HOMOG path; off for non-homogeneous input per CoCoA's gradedness invariant for sugar-driven pair selection.

### Deliberate divergences from cvc5

Several picus features go beyond cvc5's QF_FF theory solver. They were added across earlier releases after analysis and KPI validation; they are kept (not removed) and documented here so a side-by-side reader of the two codebases can distinguish "deliberate improvement" from "missed alignment."

| Feature | Where in picus | cvc5 / CoCoA equivalent | Rationale |
|---------|---------------|------------------------|-----------|
| **`apply_rule_multi` checks all bases** for univariate / zero-dim structure | `picus-solver/src/split_gb.rs::apply_rule_multi` | cvc5 `multi_roots.cpp:164-196` only checks basis 0 | Finds branching opportunities in the nonlinear basis after bit-propagation that cvc5's narrower scan misses; sound (the structure detected is mathematically valid in either basis). |
| **Phase saving (CDCL-lite)** — last-popped value remembered, reordered to front of next `Brancher::Roots` for the same variable on backtrack | `split_gb.rs` (`saved_phase` field) | none | Short-circuits search in highly symmetric spaces (bit constraints) — common in zk-circuit input. |
| **Nogood cache + subsumption pruning** — infeasible partial assignments retained and supersets pre-rejected before recomputing GB | `split_gb.rs` (`nogoods` field) | none | Avoids redundant GB recomputation on provably-infeasible branches; sound by partial-assignment monotonicity. |
| **Linear-only quick UNSAT pre-check** — before the full split-GB extension, test if the candidate makes the linear basis whole-ring | `split_gb.rs` (lines 515-543) | none | ~10× faster rejection of linearly-infeasible branches; sound (whole-ring is whole-ring regardless of which sub-basis proves it). |
| **Incremental Buchberger** (`extend_with_cancel`, `split_gb_extend_cancel`) — reuse the previously-computed reduced GB across DFS branches | `picus-solver/src/ideal.rs::extend_with_cancel`, `split_gb.rs::split_gb_extend_cancel` | cvc5 recomputes full GB per branch | Sound: extending an existing GB by additional generators and re-running Buchberger yields the same final GB as full recomputation. Significant speedup on deep search trees. |
| **Three-valued result** (`SolveOutcome::{Sat, Unsat, Unknown}`, `ZeroExtendResult::NoZero { exhaustive: bool }`) — distinguish "search bounded out" from "no model exists" | `picus-solver/src/core.rs`, `split_gb.rs`, `model.rs` | cvc5 conflates them via empty-vector return | More-honest reporting; allows downstream callers to retry with relaxed bounds rather than treating bounded-no-model as definitive UNSAT. |
| **Fixpoint iteration cap** (`(k * 64).max(256)`) on the bit-propagation fixpoint | `split_gb.rs` (lines 91-92) | none (cvc5 relies on caller timeout) | Safety bound against pathological propagation loops. |
| **Iteration-based recursion** in `split_zero_extend_cancel` (explicit stack instead of recursive call) | `split_gb.rs` | cvc5 `splitZeroExtend` is recursive (`split_gb.cpp:156-264`) | Stack-overflow robustness on deep DFS trees common in large circuits. |
| **`IncrementalSolverContext` solver-state cache** (Plan v9): caches the encoded constraint side + computed split-GB across `solve_encoded` calls within a `NativeFfBackend` session; lazy-build (only after seeing 2+ same-digest calls) avoids regressions on circuits with all-distinct constraint sets. Disable via `PICUS_NO_INCREMENTAL_CACHE=1`. | `picus-solver/src/incremental_context.rs` | cvc5's `SubTheory` (`sub_theory.cpp:62-90`, `sub_theory.h:112`) accumulates facts in a `context::CDList<Node>` across SMT solver calls. picus's cache is the equivalent state-amortization for picus's per-signal DPVL queries. | Sound: per-query Rabinowitsch poly is added to the cached split-GB via `split_gb_extend_cancel` (Plan v6 incremental Buchberger), equivalent to recomputing GB on the union. |
| **Hash-bucketed divisor index** in `reduce_by_refs_geobucket` (Plan v9): groups divisors by `DivMask` bits; lookup iterates only buckets whose mask is a submask of the LT's mask. Gated to `≥ 64` divisors. | `picus-solver/src/ff/polynomial.rs` | CoCoA's `Reductors` class (`TmpGReductor.H:65-100`) holds the active basis with what is likely a hash-bucketed divisor index for the same purpose. | Mirrors CoCoA's structural choice. Soundness preserved by full exponent-divides check after bucket pre-filter. |
| **AST-level int-literal folding in `+` and `*`** (Plan v9): `simple_optimize_z3` now consolidates `Int(a) + Int(b) → Int(a+b)` and `Int(a) * Int(b) → Int(a*b)` with canonical position. | `picus-smt/src/optimizer.rs::simple_opt_expr_z3` | cvc5's `theory_ff_rewriter.cpp:45-150` postRewriteFfAdd / postRewriteFfMul. | Same canonical form pre-encoding. picus's polynomial-level merging (`Polynomial::from_terms`) already produced the equivalent canonical form post-encoding; this addition makes the alignment explicit at the AST layer too. |
| **`GbStrategy::ByHomog` and `GbStrategy::Auto`** (picus-only): a homogenize → GB → dehomogenize pipeline available as an alternative to direct Buchberger. Default is `Direct`, matching cvc5/CoCoA's typical ff-theory `AffineAlg` choice (CoCoA's HOMOG path is HOMOG-only and not used for general R1CS inputs). | `picus-solver/src/ideal.rs`, `picus-solver/src/gb_homog.rs` | none used by cvc5 ff theory | Available for users with homogeneous-input workloads; not the default. |
| **Sub-iter resumable cache** (Plan v10, 1.7.15): the encoding artifacts plus per-partition `IncrementalGB` in-flight state are saved as `partial_build` when a fresh cache rebuild is cancelled mid-build; the next solve call with the matching constraint-side digest resumes via `continue_partial`, draining the saved open S-pair queues with a fresh cancel token. Counters surfaced via `PICUS_GB_STATS=1`. | `picus-solver/src/incremental_context.rs::PartialBuild`, `ff/buchberger.rs::IncrementalGB::run_only` / `set_cancel_token` / `is_quiescent` | cvc5 has no equivalent — its `SubTheory` reruns the GB on every `postCheck`. | Sound: each `IncrementalGB::basis()` after `run_only` draining its queue is the same GB Buchberger would produce in one shot; resumption is a re-attachment of cancel-budget, not a state mutation. |
| **F4-lite degree-batched matrix reduction** (Plan v10, 1.7.15, **opt-in via `PICUS_USE_F4=1`**): sugar-batched S-pair processing — symbolic preprocessing (BFS closure under reducibility) + sparse matrix construction + sparse row-echelon over GF(p), reducer rows pivoted first. Wired into `BuchbergerState::run_f4` with size-1 batch fallback to direct geobucket. **Not an alignment item** — cvc5+CoCoA's solver uses classical Buchberger (CoCoA `GReductor`); F4 is out of scope for cvc5+CoCoA and exists in picus as a research direction. | `picus-solver/src/ff/f4.rs` | none — CoCoA implements only classical Buchberger. | Sound (5 unit tests + multi-pair property test cross-checks against per-pair geobucket; full 110-circuit gate produces 0 mismatches with the flag enabled); current per-batch matrix-construction overhead exceeds amortization savings on the present circuit set, so F4-lite remains gated off by default. Kept as scaffolding for future tuning. |

These are deliberate deviations from cvc5/CoCoA's algorithm. They exist because picus is a standalone uniqueness checker with a fixed scope (R1CS uniqueness verification), and can specialise its search policy in ways cvc5's role as an SMT theory plugin (which must compose with the SAT/DPLL(T) layer above it) does not allow.

## 4. Feature Matrix

| Feature | cvc5 | picus-solver | Status |
|---------|------|-------------|--------|
| Core ideal operations (GB, membership, reduce) | ✅ | ✅ | Complete |
| Multi-disequality (Rabinowitsch trick) | ✅ | ✅ | Complete |
| Pattern detection (bit constraints, linear monomials, bitsums) | ✅ | ✅ | Complete, wired into solver pipeline |
| Bit propagation (constant + equal bitsum) | ✅ | ✅ | Complete, auto-populated from parse |
| Split GB solver | ✅ | ✅ | Complete (admit predicate matches cvc5) |
| Single GB solver (DegRevLex → Lex → findZero) | ✅ | ✅ | Complete, selectable via `SolverMode` |
| Model construction (univariate roots, minpoly, round-robin) | ✅ | ✅ | Complete |
| UNSAT core (trivial mode) | ✅ | ✅ | Complete |
| UNSAT core (GB-trace mode, `ffTraceGb`) | ✅ | ✅ | Complete for single-GB mode (see `docs/TODO.md`) |
| Incremental push/pop | ✅ | ✅ | Complete |
| Cooperative timeout | ✅ | ✅ | Complete (`CancelToken` via `abort_early_if`) |
| Polynomial normalization (divide by LC) | ✅ | ✅ | Complete |
| Degree-overflow safety | N/A | ✅ | `catch_unwind` on unexpected GB-engine panics |
| Statistics tracking | ✅ | ✅ | `SolverStats` module |
| Picus integration (`NativeFfBackend`) | N/A | ✅ | Uses Split GB pipeline with cancel token |
| CLI `--solver native` | N/A | ✅ | Available in `picus-cli` |
| Boolean abstraction (or, ite, =>) | ✅ | ❌ | Out of scope (SAT layer) |
| Uninterpreted functions | ✅ | ❌ | Out of scope (theory combination) |

## 5. Reproducing Results

### Run tests

```bash
cd picus/
rustup run nightly cargo test -p picus-solver --release
```

### Run Criterion benchmarks

```bash
rustup run nightly cargo bench -p picus-solver --bench solver_bench
```

### Run cvc5 comparison

```bash
# Build cvc5 first (requires m4, cmake, g++):
cd /path/to/cvc5-repo
./configure.sh --auto-download --cocoa --gpl
cd build && make -j$(nproc)

# Run benchmark:
cd picus/crates/picus-solver/benches
./benchmark_cvc5.sh 50
```

## 6. Known Limitations

- **Non-trivial UNSAT core tracing** (`ffTraceGb`): implemented for single-GB mode via Buchberger observer hooks in the in-tree GB engine. The core is approximate (conservative on initial inter-reduce; no reduction-step-level tracking). Split-GB mode returns trivial cores. See `docs/TODO.md`.
- **`picus-cli` full build requires cvc5-ff-sys**: the workspace includes `cvc5-ff-sys` which builds cvc5 and GMP from source (requires `bison`, `flex`, and `m4` on PATH, plus `clang` for bindgen). The `picus-solver` crate itself builds independently without these dependencies.
- **`Or` constraint handling in `NativeFfBackend`**: encodes all branches as conjunctions (unsound for disjunction). This matches the current behavior where AB0 optimization is disabled for the cvc5-ff backend. See `docs/TODO.md`.
- **Performance gap on dense-ideal circuits**: the 17-bench KPI suite (60 s timeout) currently solves 13/17, vs cvc5's 16/17. The 4 timeouts are `Pedersen@pedersen.r1cs` (cvc5 also times out on this one), `modulusagainst2p.r1cs`, `inTest.r1cs`, and `chunkedadd1.r1cs`. These are dense-ideal problems where naive sequential Buchberger hits its combinatorial wall regardless of pair-pruning heuristics; the literature solutions are F4/F5 (batched Macaulay-matrix reduction) or Montgomery-form arithmetic for the BN128 prime, both out of scope for the in-tree engine. This is a performance limitation, not a correctness issue — all circuits that the native solver does resolve produce results identical to cvc5 (110/0-mismatch on the 110-circuit correctness gate).
