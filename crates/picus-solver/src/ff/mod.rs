//! Inlined finite-field algebra engine.
//!
//! This module provides a self-contained, purpose-built implementation of:
//! * GF(p) arithmetic for BN128-size primes (~254 bits)
//! * Multivariate polynomials over GF(p) (explicit exponent vectors)
//! * Buchberger's algorithm
//! * Univariate polynomial root finding (Cantor-Zassenhaus)
//!
//! Designed to replace the dependency on `feanor-math` for the picus-solver crate.

pub mod field;
pub mod monomial;
pub mod divmask;
pub mod polynomial;
pub mod geobucket;
pub mod spair;
pub mod buchberger;
pub mod univariate;

pub use field::{PrimeField, FieldElem};
pub use monomial::{Monomial, MonomialOrder};
pub use divmask::{DivMask, DivMaskScheme};
pub use polynomial::{PolyRing, Polynomial, TermRef};
pub use spair::SPair;
pub use buchberger::{
    BuchbergerConfig, BuchbergerObserver, GBasis, Ideal, IncrementalGB, NoObserver,
    groebner_basis, groebner_basis_observed, groebner_basis_incremental, interreduce,
};
pub use univariate::{UnivariatePoly, find_roots};
