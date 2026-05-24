//! Representation-agnostic interface for monomials.
//!
//! Both the dense [`super::monomial::Monomial`] and the sparse
//! [`super::sparse_monomial::SparseMonomial`] implement [`MonomialRepr`].
//! The polynomial layer and Gröbner-basis engine are generic over it, so
//! the representation can be switched at runtime (see `RuntimeConfig`)
//! while sharing one engine. The dense implementation is also the
//! differential-test oracle for the sparse one.

use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;

use num_bigint::BigUint;

use super::field::FieldElem;
use super::monomial::MonomialOrder;
use super::polynomial::PolyRing;

/// Operations on a monomial `x_0^{e_0} ... x_{n-1}^{e_{n-1}}` that the
/// engine relies on. Implementations must agree bit-for-bit on results
/// (validated by `repr_oracle`).
///
/// Equality/hash must be canonical: two monomials with the same exponent
/// vector compare equal and hash equal, regardless of internal layout.
pub trait MonomialRepr: Clone + PartialEq + Eq + Hash + Debug {
    /// The constant monomial `1` over `n_vars` variables.
    fn one(n_vars: usize) -> Self;
    /// Build from a full-length exponent vector (length = n_vars).
    fn from_exponents(exps: Vec<u16>) -> Self;
    /// `x_var^exp` over `n_vars` variables.
    fn single_var(n_vars: usize, var: usize, exp: u16) -> Self;

    fn n_vars(&self) -> usize;
    fn total_degree(&self) -> u32;
    fn is_one(&self) -> bool;
    /// Exponent of `var` (0 if absent).
    fn exponent(&self, var: usize) -> u16;
    /// The full-length exponent vector (length = n_vars). For the sparse
    /// representation this materialises; hot paths should prefer
    /// [`Self::for_each_nonzero`].
    fn to_dense(&self) -> Vec<u16>;
    /// Visit every `(var, exp)` with `exp > 0`, ascending by `var`.
    fn for_each_nonzero(&self, f: impl FnMut(usize, u16));

    /// Component-wise sum (`self * other`).
    fn mul(&self, other: &Self) -> Self;
    fn mul_assign(&mut self, other: &Self);
    /// `self` divides `other` (component-wise `<=`).
    fn divides(&self, other: &Self) -> bool;
    /// `self / divisor`; caller guarantees `divisor.divides(self)`.
    fn div(&self, divisor: &Self) -> Self;
    /// Component-wise max.
    fn lcm(&self, other: &Self) -> Self;
    /// Component-wise min.
    fn gcd(&self, other: &Self) -> Self;
    /// No shared variable.
    fn is_coprime(&self, other: &Self) -> bool;
    fn cmp_with_order(&self, other: &Self, order: MonomialOrder) -> Ordering;
}

/// Representation-agnostic interface for polynomials at the IR layer
/// (lowering, propagation, SMT lowering). The dense [`super::polynomial::
/// Polynomial`] and the sparse [`super::sparse_polynomial::SparsePolynomial`]
/// both implement it; `PolyIR` and the propagation lemmas are generic
/// over it so the IR can be built in either representation.
///
/// This is the L1 surface — construction, ring arithmetic, evaluation,
/// and term iteration. Gröbner reduction (the GB-engine hot path) is
/// deliberately *not* here: the native backend lowers the IR to the
/// (index-keyed) `ConstraintSystem` and the GB engine works on its own
/// dense polynomials. The shared [`PolyRing`] carries the field, the
/// variable count, and the monomial order for both representations.
pub trait PolyRepr: Clone + Debug {
    type Mono: MonomialRepr;

    fn zero() -> Self;
    fn constant(c: FieldElem, ring: &PolyRing) -> Self;
    fn variable(var: usize, ring: &PolyRing) -> Self;
    /// Build from `(monomial, coeff)` pairs: drop zero coeffs, sort by
    /// the ring order, combine like monomials.
    fn from_terms(terms: Vec<(Self::Mono, FieldElem)>, ring: &PolyRing) -> Self;

    fn is_zero(&self) -> bool;
    fn num_terms(&self) -> usize;

    fn add(&self, other: &Self, ring: &PolyRing) -> Self;
    fn sub(&self, other: &Self, ring: &PolyRing) -> Self;
    fn mul(&self, other: &Self, ring: &PolyRing) -> Self;
    fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Self;
    fn negate(&self, ring: &PolyRing) -> Self;
    fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem;

    /// Each term as `(coeff, sorted nonzero (var, exp) pairs)`.
    fn collect_terms_idx(&self, ring: &PolyRing) -> Vec<(BigUint, Vec<(usize, u16)>)>;
}
