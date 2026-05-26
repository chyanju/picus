//! CDCL(T) orchestrator: SAT + theory plug-in.
//!
//! Mirrors cvc5's TheoryEngine + sub-theory layering. The SAT engine
//! ([`crate::sat::Solver`]) is the Boolean reasoner; an arbitrary
//! [`theory::Theory`] implementation acts as the theory plug-in. The
//! FF theory ([`ff_theory::FfTheory`]) is the concrete instance for
//! QF_FF queries and wraps [`crate::core::solve_encoded_with_cancel`].

pub mod atoms;
pub mod cnf;
pub mod ff_theory;
pub mod orchestrator;
pub mod theory;

pub use orchestrator::solve_formula;
