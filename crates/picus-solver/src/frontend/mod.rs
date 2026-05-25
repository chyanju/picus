//! Frontend: lowering a polynomial system to the GB-solvable encoding.
//!
//! - [`encoder`]: constraint system to GB polynomials.
//! - [`parse`]: polynomial pattern detection.
//! - [`rewriter`]: FF term canonicalization.
//! - [`bitprop`]: bit-propagation from known bitsum structure.
//! - [`bench_fixtures`]: SMT-LIB QF_FF source builders for benches/tools.

pub mod bench_fixtures;
pub mod bitprop;
pub mod encoder;
pub mod parse;
pub(crate) mod rewriter;
