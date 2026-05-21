//! CDCL Boolean SAT solver.
//!
//! Self-contained; the `cdclt` module composes [`Solver`] with a
//! theory plug-in for CDCL(T).
//!
//! Algorithm: two-literal watching for unit propagation, 1-UIP
//! conflict analysis with clause learning. Decision heuristic =
//! lowest-index Undef variable, positive polarity. Learnt clauses
//! persist for the lifetime of the solver (no deletion).

pub mod clause;
pub mod lit;
pub mod solver;

pub use clause::{Clause, ClauseArena, ClauseRef};
pub use lit::{LBool, Lit, Var};
pub use solver::{SolveResult, Solver};
