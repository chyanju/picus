# Future Work

## Known Limitations

### AB0 optimization disabled for cvc5 QF_FF

AB0 rewrites `A * B = 0` to `or(A = 0, B = 0)`. The rewrite is sound over
a field but is disabled for the cvc5 backend: cvc5 1.2.0–1.3.3 returns
inconsistent models for `or` disjunctions in QF_FF (one or more assertions
violated by the returned model).

`ab0_optimize_z3` in `picus-smt/src/optimizer.rs` retains the
rewrite pattern. To re-enable for cvc5 once the upstream `or`/QF_FF
bug is fixed, port the rewrite (dropping the `(mod _ p)` wrappers
that the cvc5 path drops elsewhere) and route `optimize_p0` to it
for `SolverKind::Cvc5`.

AB0 is an internal query-construction pass and is not exposed via
`--lemmas` (which controls propagation lemmas).

## Removed Components

| Component | File | Removed in | Status |
|-----------|------|-----------|--------|
| BabyJubJub propagation lemma | `baby.rs` | v1.3.0 | Was an unimplemented stub |
| Constraint graph | `constraint_graph.rs` | v1.3.0 | Fully implemented; no callers |
| Compositional counter-example generation | `cex.rs` | v1.3.0 | Was an unimplemented stub |
| Precondition system | `precondition.rs` | v1.2.0 / v1.3.0 | JSON-based known-set seeding |

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
