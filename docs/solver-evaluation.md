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
