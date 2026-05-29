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
pub mod multi_prime;
pub mod orchestrator;
pub mod theory;

pub use orchestrator::solve_formula;

use num_bigint::BigUint;
use num_traits::Zero;

/// Modular inverse of `coeff` in GF(`prime`) via Fermat's little theorem
/// (`coeff^(prime-2) mod prime`). Returns `None` when no inverse is
/// computable by this route — `coeff == 0`, or `prime <= 2` for a
/// non-unit coefficient — which the single-variable-equality solving in
/// [`atoms`] and [`ff_theory`] both treat as "cannot derive a value".
/// `coeff == 1` short-circuits to `1`, so the prime bound is irrelevant
/// in that common case.
pub(crate) fn field_inverse(coeff: &BigUint, prime: &BigUint) -> Option<BigUint> {
    if coeff.is_zero() {
        return None;
    }
    if coeff == &BigUint::from(1u32) {
        return Some(BigUint::from(1u32));
    }
    if prime <= &BigUint::from(2u32) {
        return None;
    }
    Some(coeff.modpow(&(prime - 2u32), prime))
}

#[cfg(test)]
mod tests;
