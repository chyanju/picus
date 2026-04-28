# Future Work

Items removed during cleanup are available in git history. This file tracks planned features and removed components for reference.

## Known Limitations

### AB0 optimization disabled for cvc5 QF_FF

**What is AB0?** An SMT constraint rewrite that transforms `A*B = 0` into `or(A = 0, B = 0)`. This is mathematically sound (finite fields are integral domains), and it helps the solver by splitting nonlinear constraints into simpler disjunctions.

**Why is it disabled?** cvc5 versions 1.2.0 through 1.3.3 have a bug in the QF_FF solver where `or` disjunctions can produce spurious SAT results — the returned model violates one or more assertions. This was discovered on the Multiplexer circuit: cvc5 reported `unsafe` with a model that did not satisfy the constraints, while z3 correctly reported `safe`.

**Impact:** Disabling AB0 for cvc5 means certain circuits that rely on the `A*B=0` splitting for efficient solving may time out. Specifically, the `BitElementMulAny` circuit (solved by the original Racket version in ~93s with AB0 enabled) now times out at 120s. This affects 2 out of 163 benchmarks.

**Why users can't control this:** AB0 is not a propagation lemma — it's an internal constraint optimization pass applied during SMT query construction. It is not exposed through the `--lemmas` CLI flag (which controls propagation lemmas only). The AB0 code for cvc5 is retained in the source (`optimizer.rs`, marked `#[allow(dead_code)]`) and can be re-enabled when a future cvc5 release fixes the `or` bug in QF_FF.

**Tracking:** The cvc5 team should be notified of this issue. Once fixed, re-enable AB0 for cvc5 by changing `optimizer.rs:optimize_p0()` to call `ab0_optimize_cvc5()` instead of returning `cnsts.clone()`.

## Removed Components

### BabyJubJub propagation lemma (`baby.rs`)
Domain-specific propagation lemma for Edwards curve point addition (constants a=168700, d=168696). Was an unimplemented stub. Needed for circuits using BabyJubJub curve operations (EdDSA signatures, Pedersen commitments). Removal commit: v1.3.0.

### Constraint graph (`constraint_graph.rs`)
Signal-constraint undirected graph built via `petgraph`. Connects signals that appear in the same R1CS constraint. Was fully implemented (~135 lines, supports scoped subgraph extraction) but had no callers. Intended for compositional counterexample generation. Removal commit: v1.3.0.

### Compositional counterexample generation (`cex.rs`)
Scope-by-scope counterexample construction using the constraint graph. Was an unimplemented stub. The current approach uses counterexamples provided directly by the SMT solver when it returns SAT. Removal commit: v1.3.0.

### Precondition system (`precondition.rs`)
JSON-based precondition files that could seed the known-set with assumed-unique signals or inject additional constraints. Removed in v1.2.0 CLI simplification. The module and its `serde`/`serde_json` dependencies were removed in v1.3.0.

## Planned Features

- **Buchberger B-criterion for S-pair pruning**: Picus 1.7.10 added the Gebauer-Möller M-criterion at S-pair generation time, mirroring CoCoA's `myGMInsert`. The companion B-criterion (CoCoA's `myApplyBCriterion` in `TmpGReductor.C`), which retroactively prunes the existing open queue when a new basis element is added, is not yet implemented. Without it, the M-criterion's per-generation walk overhead is not fully amortized, and certain dense-ideal circuits (e.g. `chunkedadd1`, `test-rollup-tx-states` in the 17-bench KPI) regressed in 1.7.10. A sound B-criterion implementation needs the full lcm comparison from CoCoA (TmpGPair.C `BCriterion_OK`), since picus has previously shipped a buggy chain criterion that produced incomplete GBs. Estimated as the natural next correctness-preserving optimisation pass.
- **Yices2 backend**: Yices2 v2.7.0 added finite field support (QF_FFA) via MCSat. However, as of v2.7.0, the solver hangs on negated equality atoms (`not (= x y)`), which are required for all uniqueness queries. Additionally, the pre-built binaries do not export the FF C API symbols (`yices_ff_type`, etc.), requiring users to build from source for API access. Revisit when a future Yices2 release fixes the negated equality issue.
- **Incremental solving**: Use z3/cvc5 push/pop to avoid re-asserting the full constraint set for each query.
- **Plonkish/AIR constraint formats**: Extend beyond R1CS to support Halo2 (Plonkish) and STARK (AIR) arithmetizations.
- **BabyJubJub lemma**: Re-implement the domain-specific propagation lemma for Edwards curve circuits.
- **Compositional CEX**: Re-implement scope-by-scope counterexample generation for better diagnostics on large circuits.
- **Multiple counter-examples**: When a circuit is unsafe, allow enumerating additional counter-examples by re-invoking the solver with previously found counter-examples banned. This would help users understand the scope of a vulnerability.

## Partially Implemented

- **Non-trivial UNSAT core tracing (`ffTraceGb`)**: Implemented for single-GB mode (`SolverMode::SingleGb`). The in-tree GB engine (`src/ff/buchberger.rs`) exposes `BuchbergerObserver` callbacks (`on_initial_basis`, `on_new_poly`, `on_inter_reduce`). The `tracer` module in picus-solver builds a polynomial dependency DAG using these callbacks, then extracts the subset of input polynomial indices responsible for producing the trivial element (UNSAT proof). This mirrors cvc5's `Tracer` class (`theory/ff/core.cpp`). Limitations: (a) initial inter-reduction conflates all inputs conservatively (each surviving element is marked as depending on all inputs), so the core may be coarser than cvc5's when inter-reduction is significant; (b) reduction-step-level tracking (which polynomials are used as divisors during S-poly reduction) is not yet implemented — only S-polynomial parent indices are tracked. Split-GB mode still returns trivial (all-input) cores, matching cvc5's behavior.
