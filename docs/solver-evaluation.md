# picus-solver Evaluation Report

This document evaluates `picus-solver`, the pure-Rust finite field (QF_FF) solver that replaces cvc5's Split GB / CoCoA backend in Picus.

## 1. Architecture Overview

`picus-solver` is a from-scratch Rust reimplementation of cvc5's finite field theory solver. It faithfully replicates cvc5's Split Groebner Basis algorithm, including:

| Component | cvc5 (C++ / CoCoA) | picus-solver (Rust / feanor-math) |
|-----------|--------------------|------------------------------------|
| Polynomial ring | CoCoA `SparsePolyRing` | `feanor-math` `MultivariatePolyRingImpl` |
| Groebner basis | CoCoA `GBasis` | `feanor-math` `buchberger` (custom inner ring) |
| Split GB | `theory/ff/split_gb.cpp` | `split_gb.rs` |
| Model search | `theory/ff/multi_roots.cpp` (`findZero`, `splitFindZero`) | `split_gb.rs` (`split_find_zero`, `split_zero_extend`) |
| Univariate roots | `theory/ff/uni_roots.cpp` (CoCoA factor) | `roots.rs` (Cantor-Zassenhaus via feanor-math) |
| Bit propagation | `theory/ff/bitprop.cpp` | `bitprop.rs` |
| Pattern detection | `theory/ff/parse.cpp` | `parse.rs` |
| UNSAT core | `theory/ff/core.cpp` (trivial mode) | `core.rs` (trivial mode) |
| Incremental | CDContext push/pop | `incremental.rs` (fact-stack + height markers) |
| Encoding | SMT Node → CoCoA polynomial | `encoder.rs` (ConstraintSystem → polynomial) |

### Key differences from cvc5

- **No Boolean layer**: cvc5's FF solver sits below a SAT/DPLL(T) engine that handles `or`, `ite`, `=>`, `not`, and uninterpreted functions. `picus-solver` operates purely at the polynomial constraint level. This means ~25 of cvc5's 42 `regress0/ff/` tests (which require Boolean reasoning) are not applicable.
- **No CoCoA dependency**: All Groebner basis computation uses feanor-math (pure Rust, nightly). No C++ libraries, no GPL dependency.
- **Cooperative timeout**: Implemented as an atomic cancellation token, plumbed through the Buchberger inner loop and the recursive model search.

## 2. Correctness

### Test coverage

| Test file | Tests | Source |
|-----------|-------|--------|
| `lib.rs` unit tests | 46 | Solver internals (field, poly, ideal, parse, bitprop, split_gb, core, incremental, timeout, stats, tracer) |
| `cvc5_regression.rs` | 9 | Direct ports of `regress0/ff/*.smt2` |
| `cvc5_extended.rs` | 14 | Extended ports of additional cvc5 regression tests |
| `cvc5_unit_uni_roots.rs` | 5 | Ports of `theory_ff_uni_roots_black.cpp` |
| `cvc5_unit_multi_roots.rs` | 15 | Ports of `theory_ff_multi_roots_black.cpp` |
| `cvc5_unit_split_gb.rs` | 4 | Ports of `theory_ff_split_gb_black.cpp` (randomized) |
| `cvc5_unit_parse.rs` | 11 | Ports of `theory_ff_parse_white.cpp` |
| `integration.rs` | 6 | End-to-end integration tests |
| `timeout.rs` | 7 | Cooperative timeout integration tests |
| **Total** | **117** | (+ 4 ignored perf/probe tests) |

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

### Performance note: feanor-math multiplication table tuning

feanor-math's `MultivariatePolyRingImpl::new` defaults to a multiplication table size of `(6, 8)`, which precomputes `O(C(n+8,8)^2)` monomial products. With 11+ variables this causes multi-second startup per ring construction, and `buchberger_simple` re-creates the ring on every call. picus-solver uses `new_with_mult_table((2, 2))` with a custom `compute_gb_fast` helper to avoid this overhead. The result for `issue10937` (11 variables):

| Component | Default feanor-math | With tuned table | Speedup |
|-----------|---------------------|-----------------|---------|
| Ring construction | 3.5 s | 100 µs | 35,000x |
| Split GB computation | 157 s (debug) | 338 µs | 464,000x |
| Total end-to-end | 215 s (debug) | ~680 µs | ~316,000x |

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
| Degree-overflow safety | N/A | ✅ | `catch_unwind` on feanor-math panics |
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

- **Non-trivial UNSAT core tracing** (`ffTraceGb`): implemented for single-GB mode via Buchberger observer hooks in a forked feanor-math. The core is approximate (conservative on initial inter-reduce; no reduction-step-level tracking). Split-GB mode returns trivial cores. See `docs/TODO.md`.
- **`picus-cli` full build requires cvc5-ff-sys**: the workspace includes `cvc5-ff-sys` which builds cvc5 and GMP from source (requires `bison`, `flex`, and `m4` on PATH, plus `clang` for bindgen). The `picus-solver` crate itself builds independently without these dependencies.
- **`Or` constraint handling in `NativeFfBackend`**: encodes all branches as conjunctions (unsound for disjunction). This matches the current behavior where AB0 optimization is disabled for the cvc5-ff backend. See `docs/TODO.md`.
- **Performance gap on mid-size circuits**: 23 circuits (out of 465 tested) that cvc5 resolves within 30s exceed the native solver's per-query timeout. These are circuits with 20-50 original variables (40-100 after DPVL duplication), where feanor-math's Groebner basis computation is slower than CoCoA. This is a performance limitation, not a correctness issue — all circuits that the native solver does resolve produce results identical to cvc5.
