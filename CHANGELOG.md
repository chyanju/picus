# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

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
