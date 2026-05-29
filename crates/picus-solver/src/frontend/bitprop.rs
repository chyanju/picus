//! Bit propagation: derive new equalities from known bitsum structure.
//!
//! Mirrors cvc5's split-GB `BitProp`.
//!
//! The key observation: if a polynomial `b = b_0 + 2*b_1 + ... + 2^k*b_k`
//! is known (via the GB) to equal a constant `v`, **and** all `b_i` are
//! bit-constrained, the bit decomposition propagates immediately:
//! `b_i = (i-th bit of v)`. Similarly, if two bitsums `a` and `b` are known
//! to be equal and all their inputs are bits, then `a_i = b_i` for all `i`.
//!
//! Overflow: if `v >= 2^k`, the bitsum cannot represent `v`, so the
//! conjunction is UNSAT. This is signalled by emitting the constant `1`
//! as a propagated polynomial; a downstream GB call then produces the
//! trivial ideal.

use std::collections::HashSet;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::ff::field::FieldElem;
use crate::frontend::encoder::bitsum_fits;
use crate::gb::ideal::Ideal;
use crate::metric;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;

/// State for bit propagation across multiple GBs.
pub struct BitProp<'r> {
    pub poly_ring: &'r FfPolyRing,
    /// Variables known to be bit-constrained (by user-asserted `x*(x-1)=0`).
    pub bits: HashSet<usize>,
    /// Known bitsums. Each bitsum is a list of variable indices
    /// `[b_0, ..., b_k]` representing `b_0 + 2*b_1 + ... + 2^k * b_k`.
    /// Scalar coefficient is implicit (unit) — non-unit bitsums are
    /// pre-extracted before registration.
    pub bitsums: Vec<Vec<usize>>,
}

/// Owned snapshot of [`BitProp`]'s logical state. [`BitProp`] borrows
/// the poly ring; this owned form reconstitutes via
/// [`BitProp::from_state`].
#[derive(Clone, Default, Debug)]
pub struct BitPropState {
    pub bits: HashSet<usize>,
    pub bitsums: Vec<Vec<usize>>,
}

impl<'r> BitProp<'r> {
    pub fn new(poly_ring: &'r FfPolyRing) -> Self {
        BitProp { poly_ring, bits: HashSet::new(), bitsums: Vec::new() }
    }

    /// Mark `var` as bit-constrained.
    pub fn add_bit(&mut self, var: usize) { self.bits.insert(var); }

    /// Register a known bitsum (variable indices, lowest bit first).
    pub fn add_bitsum(&mut self, bits: Vec<usize>) { self.bitsums.push(bits); }

    /// Snapshot the logical state into an owned form (for caching).
    pub fn to_state(&self) -> BitPropState {
        BitPropState {
            bits: self.bits.clone(),
            bitsums: self.bitsums.clone(),
        }
    }

    /// Reconstruct a `BitProp` from a saved state and a poly_ring borrow.
    pub fn from_state(poly_ring: &'r FfPolyRing, state: BitPropState) -> Self {
        BitProp {
            poly_ring,
            bits: state.bits,
            bitsums: state.bitsums,
        }
    }

    /// Test whether `var` is bit-constrained: either it is a globally
    /// asserted bit (`self.bits`, populated from user `x*(x-1)=0`
    /// constraints) or some basis in `split_basis` proves `var^2-var ∈ I`.
    ///
    /// The per-basis proof is recomputed on every call and **never** cached
    /// into `self.bits`: `split_basis` varies across the DFS search (a
    /// variable pinned to 0/1 on one branch is not bit-constrained on
    /// another, and the search never rolls `self.bits` back on backtrack),
    /// so persisting a branch-local proof as a global fact is unsound — it
    /// would let `get_bit_equalities` treat a non-bit variable as a bit on a
    /// sibling branch and emit a spurious overflow contradiction (false
    /// UNSAT). `self.bits` therefore holds only globally-valid bits.
    pub fn is_bit(&self, var: usize, split_basis: &[Ideal<'r>]) -> bool {
        if self.bits.contains(&var) {
            return true;
        }
        let pr = self.poly_ring;
        let x = pr.var(var);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let bit_poly = pr.sub(x2, x);
        split_basis.iter().any(|b| b.contains(&bit_poly))
    }

    /// Derive new equalities (as polynomials whose `=0` form is asserted)
    /// from the structure of the bitsums and the current GB.  See cvc5's
    /// `BitProp::getBitEqualities` for the original algorithm.
    pub fn get_bit_equalities(&self, split_basis: &[Ideal<'r>]) -> Vec<Poly> {
        self.get_bit_equalities_with_cancel(split_basis, None)
    }

    /// Cancel-aware variant. Returns whatever propagated equalities were
    /// derived before cancellation; partial output is still sound (every
    /// emitted poly is a valid consequence of the basis).
    ///
    /// Takes `&self`: never mutates `BitProp`. In particular, must not
    /// cache a branch-local bit proof into `self.bits` — a variable that is
    /// a bit only on the current DFS branch would then be treated as a
    /// global bit on a sibling branch (unsound: false UNSAT).
    #[metric("bitprop::get_bit_equalities")]
    pub fn get_bit_equalities_with_cancel(
        &self,
        split_basis: &[Ideal<'r>],
        cancel: Option<&CancelToken>,
    ) -> Vec<Poly> {
        let pr = self.poly_ring;
        let ring = &pr.ring;
        let fp = &pr.field();
        let mut output: Vec<Poly> = Vec::new();

        let bitsums = &self.bitsums;
        let mut non_constant_bitsums: Vec<Vec<usize>> = Vec::new();

        // Phase 1: bitsums that reduce to a constant in some basis.
        for bs in bitsums {
            if let Some(c) = cancel {
                if c.is_cancelled() { return output; }
            }
            // Build the polynomial b_0 + 2*b_1 + ... + 2^k*b_k.
            let bs_poly = bitsum_poly(pr, bs);
            let mut handled = false;
            // Pinning bits from a mod-p residue is sound only when the
            // bitsum cannot overflow p (2^len <= p); otherwise the residue
            // has multiple integer preimages (GF(7): A≡0 admits 0 and 7), so
            // leave such bitsums unhandled here.
            let fits = bitsum_fits(bs.len(), pr.field().prime());
            for basis in split_basis {
                if !fits {
                    break;
                }
                let nf = match cancel {
                    Some(c) => basis.reduce_with_cancel(&bs_poly, c),
                    None => basis.reduce(&bs_poly),
                };
                // is normal form a constant?
                let appearing = ring.appearing_indeterminates(&nf);
                if !appearing.is_empty() {
                    continue;
                }
                // It is a constant.  Check all bits are bit-constrained.
                let all_bits = bs.iter().all(|&v| self.is_bit(v, split_basis));
                if !all_bits { continue; }

                // val = the constant
                let val_el = constant_term_value(pr, &nf);
                let val: BigUint = pr.field().to_biguint(&val_el);
                let two_k = BigUint::from(1u32) << bs.len();
                if val >= two_k {
                    // overflow → contradiction
                    output.clear();
                    output.push(pr.one());
                    return output;
                }
                // Propagate b_i = bit_i(val)
                for (i, &v) in bs.iter().enumerate() {
                    let bit = (&val >> i) & BigUint::from(1u32);
                    let bit_el = if bit.is_zero() { fp.zero() } else { fp.one() };
                    let bit_poly = pr.constant(bit_el);
                    let diff = pr.sub(pr.var(v), bit_poly);
                    output.push(diff);
                }
                handled = true;
                break;
            }
            if !handled {
                non_constant_bitsums.push(bs.clone());
            }
        }

        // Phase 2: pairs of non-constant bitsums known to be equal.
        let n = non_constant_bitsums.len();
        for i in 0..n {
            if let Some(c) = cancel {
                if c.is_cancelled() { return output; }
            }
            for j in 0..i {
                let a = &non_constant_bitsums[i];
                let b = &non_constant_bitsums[j];
                let a_poly = bitsum_poly(pr, a);
                let b_poly = bitsum_poly(pr, b);
                let diff = pr.sub(a_poly, b_poly);
                let any_contains = match cancel {
                    Some(c) => split_basis.iter().any(|bs| bs.contains_with_cancel(&diff, c)),
                    None => split_basis.iter().any(|bs| bs.contains(&diff)),
                };
                if !any_contains { continue; }

                let min = a.len().min(b.len());
                let max = a.len().max(b.len());
                // A ≡ B (mod p) implies bitwise equality only when both
                // bitsums fit in p (2^max <= p); else they can collide mod p
                // (GF(7): 7 ≡ 0, so (1,1,1) and (0,0,0) are equal mod 7) and
                // bitwise propagation would delete a real solution (false UNSAT).
                if !bitsum_fits(max, pr.field().prime()) { continue; }

                let all_bits = a.iter().chain(b.iter()).all(|&v| self.is_bit(v, split_basis));
                if !all_bits { continue; }

                for k in 0..min {
                    let p = pr.sub(pr.var(a[k]), pr.var(b[k]));
                    output.push(p);
                }
                if a.len() != min || b.len() != min {
                    let longer = if a.len() > min { a } else { b };
                    for k in min..max {
                        output.push(pr.var(longer[k]));
                    }
                }
            }
        }
        output
    }
}

/// Construct the polynomial  `b_0 + 2*b_1 + ... + 2^k*b_k`  for a bitsum.
fn bitsum_poly(pr: &FfPolyRing, bits: &[usize]) -> Poly {
    let fp = &pr.field();
    let two = fp.int_hom().map(2);
    let mut result = pr.zero();
    let mut coeff = fp.one();
    for &b in bits {
        let term = pr.scale(fp.clone_el(&coeff), pr.var(b));
        result = pr.add(result, term);
        coeff = fp.mul_ref(&coeff, &two);
    }
    result
}

/// Get the constant term of a polynomial (assumes it's already a constant).
fn constant_term_value(pr: &FfPolyRing, p: &Poly) -> FieldElem {
    let ring = &pr.ring;
    let fp = &pr.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut deg = 0usize;
        for v in 0..pr.n_vars() {
            deg += ring.exponent_at(&m, v);
        }
        if deg == 0 {
            fp.add_assign(&mut acc, fp.clone_el(c));
        }
    }
    acc
}

#[cfg(test)]
#[path = "bitprop_tests.rs"]
mod tests;
