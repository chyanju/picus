//! Gröbner-basis and root-finding engines over the GF(p) algebra defined in
//! [`picus_core::ff`].
//!
//! - Buchberger's algorithm with Gebauer-Möller / sugar pair management and
//!   geobucket reduction, plus the F4-lite matrix path.
//! - Hilbert numerator + quotient-dimension oracle over finished bases.
//! - Univariate root finding via Cantor-Zassenhaus.

// Algebra primitives (field, dense/sparse polynomials, reduction) live in
// picus-core; re-bound here so the in-crate engine refers to them as
// `crate::ff::*`.
pub(crate) use picus_core::ff::*;

pub mod buchberger;
pub mod f4;
pub mod hilbert;
pub mod spair;
pub mod sparse_gb;
pub mod univariate;

#[cfg(test)]
mod repr_oracle;

pub use buchberger::{
    groebner_basis, groebner_basis_incremental, groebner_basis_observed, interreduce,
    BuchbergerConfig, BuchbergerObserver, GBasis, IncrementalGB, NoObserver,
};
pub use spair::SPair;
pub use univariate::{find_roots, UnivariatePoly};
