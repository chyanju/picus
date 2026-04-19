# Future Work

Items removed during cleanup are available in git history. This file tracks planned features and removed components for reference.

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

- **Incremental solving**: Use z3/cvc5 push/pop to avoid re-asserting the full constraint set for each query.
- **cvc5 static compilation**: Bundle cvc5 via the `static` feature in `cvc5-sys` to eliminate the system-installed `libcvc5.so` requirement.
- **Plonkish/AIR constraint formats**: Extend beyond R1CS to support Halo2 (Plonkish) and STARK (AIR) arithmetizations.
- **BabyJubJub lemma**: Re-implement the domain-specific propagation lemma for Edwards curve circuits.
- **Compositional CEX**: Re-implement scope-by-scope counterexample generation for better diagnostics on large circuits.
