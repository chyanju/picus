# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

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
