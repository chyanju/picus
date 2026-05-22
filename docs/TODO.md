# Future Work

## Known Limitations

### `basis2` over a small prime where `2^n > p`

`basis2` skips when the number of bits would let two distinct
patterns sum to the same target modulo `p`. This is the correct
behaviour for soundness, but it leaves no propagation handle on
small-prime bit-decomposition shapes; SMT does the work. If a future
research lemma needs to exploit this pattern soundly, it would need
range refinement that rules out the wrap-around.

### `native_ff` over small primes returns spurious UNSAT on some queries

The Phase 1 / Phase 4 regression suite contains an `#[ignore]`d test
(`basis2_native_ff_finds_counterexample`) where `native_ff` returns
UNSAT on a GF(11) bit-decomposition uniqueness query that the cvc5
QF_FF backend correctly resolves to SAT. The aboz analogue on GF(7)
works, so the bug is structural — likely in the way Rabinowitsch
disequality interacts with the small-prime field polynomials, or in
the bitsum handling of the encoder. Needs investigation before
landing more multi-prime work.

## Removed Components

| Component | File | Removed in | Status |
|-----------|------|-----------|--------|
| BabyJubJub propagation lemma | `baby.rs` | v1.3.0 | Was an unimplemented stub |
| Constraint graph | `constraint_graph.rs` | v1.3.0 | Fully implemented; no callers |
| Compositional counter-example generation | `cex.rs` | v1.3.0 | Was an unimplemented stub |
| Precondition system | `precondition.rs` | v1.2.0 / v1.3.0 | JSON-based known-set seeding |
| AB0 optimizer (`ab0_optimize_z3`) | `picus-smt/src/optimizer.rs` | v1.7.30 | Replaced by direct PolyIR lowering |

## Planned

- **Yices2 backend.** Yices2 v2.7.0 added QF_FFA support. Blocked: the
  released build hangs on negated equality atoms (`not (= x y)`), which
  every uniqueness query needs, and the prebuilt binaries do not export
  the finite-field C API symbols.
- **Incremental SMT solving.** Use z3/cvc5 push/pop to avoid re-asserting
  the full constraint set for each per-signal query.
- **Plonkish / AIR support.** Extend the input parser beyond R1CS.
- **BabyJubJub lemma.** Domain-specific propagation for Edwards-curve
  point addition.
- **Compositional counter-example generation.** Scope-by-scope CEX
  construction for large-circuit diagnostics.
- **Multiple counter-examples.** Re-invoke the solver with previously
  found CEXes banned to enumerate alternatives.

## SMT-LIB v2 frontend

The `picus-solver::smt2::SmtSession` evaluator covers every command
used by the `cvc5/test/regress/cli/regress0/ff/` suite (`set-logic`,
`set-info`, `set-option` including `:tlimit-per`, `define-sort`,
`declare-fun` / `declare-const`, `define-fun`, `assert` with
`(! ... :named NAME)` annotations, `push n` / `pop n`, `check-sat`,
`get-value`) plus `get-model`, `get-unsat-core`, `echo`, `reset`,
`reset-assertions`, `exit`. The remaining SMT-LIB spec edges that
cvc5 supports but no cvc5 FF regression exercises (a strictly
minimal `get-unsat-core`, multi-prime systems in a single query,
`get-proof`, whitespace-bearing `echo` strings) are deferred until a
real workload requires them.

## Partially Implemented

### Non-trivial UNSAT core tracing (`ffTraceGb`)

Implemented for both `SolverMode::SingleGb` and `SolverMode::SplitGb`.
The in-tree GB engine (`src/ff/buchberger/`) exposes
`BuchbergerObserver` callbacks (`on_initial_reducers`,
`on_initial_basis`, `on_new_poly`, `on_inter_reduce`). The `tracer`
module builds a polynomial dependency DAG from these callbacks and
extracts the subset of input polynomial indices responsible for the
trivial element (UNSAT proof).

For Split-GB, `split_gb::split_gb_cancel_traced` wires
`Ideal::extend_with_cancel_traced` into the fixpoint loop, maintaining
a per-active-basis-element `BTreeSet<usize>` of original-input deps.
Cross-partition propagations carry the source poly's deps forward; on
whole-ring detection the trivial element's tracer-input indices are
flattened back to original-input indices.

Limitations:

- Initial inter-reduction conflates inputs conservatively: each survivor
  is marked as depending on all inputs, so the core may be coarser when
  inter-reduction is significant.
- Reduction-step-level tracking (which polynomials are used as divisors
  during S-poly reduction) is not implemented; only S-polynomial parent
  indices are tracked.
- Cross-iteration tracer events for an already-extended split partition
  re-register existing basis polys as fresh tracer inputs, so the
  per-iteration dep map is coarsened to the union of basis-deps and
  new-poly-deps; precise per-poly tracking within Buchberger is
  preserved per-call but the union is taken across iterations.
