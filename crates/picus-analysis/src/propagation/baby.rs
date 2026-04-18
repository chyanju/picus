//! BabyJubJub elliptic curve addition lemma (stub).

use picus_r1cs::grammar::*;
use std::collections::HashSet;

use super::binary01::RangeValue;

/// Apply the BabyJubJub lemma (currently a no-op).
pub fn apply_lemma(
    _ks: &mut HashSet<usize>,
    _us: &mut HashSet<usize>,
    _cnsts: &RCmds,
    _range_vec: &[RangeValue],
) {
    // Stub: the original Racket code had this lemma commented out.
}
