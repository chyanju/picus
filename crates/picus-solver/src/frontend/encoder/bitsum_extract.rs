//! Bitsum subpattern extraction for the encoder: detect bit-constrained
//! variables and rewrite `c·b_0 + 2c·b_1 + ... + 2^k·c·b_k` sub-sums in
//! equalities into `__bitsum_N` aux variables. Sole soundness gate is the
//! `floor(log2 p)` chain-length cap ([`bitsum_fits`]), shared with the
//! `bitprop` Phase 1/2 guards. Re-exported from `encoder` so
//! `auto_extract_bitsums` / `bitsum_fits` resolve here.

use std::collections::{BTreeMap, HashSet};

use num_bigint::BigUint;
use num_traits::Zero;

use super::constraint_system::{ConstraintSystem, PolyTerm};
use super::VarIdx;

/// Minimum chain length for [`auto_extract_bitsums`] to
/// extract a detected bitsum.
const MIN_AUTO_BITSUM_LEN: usize = 2;

/// Whether a `len`-bit unsigned bitsum embeds into GF(p) without mod-p
/// aliasing: needs `2^len <= p`, so distinct bit patterns have distinct
/// residues. When `2^len > p` (e.g. GF(7), len=3: 0 and 7 collide mod 7),
/// two different patterns can be equal mod p — then neither a constant
/// pin nor a bitwise-equality propagation is sound. Single source for the
/// `find_bitsum_chain` length cap and the `bitprop` Phase 1/2 guards.
pub(crate) fn bitsum_fits(len: usize, p: &BigUint) -> bool {
    (BigUint::from(1u32) << len) <= *p
}

/// Rewrite equalities to extract bitsum subpatterns into
/// `ConstraintSystem::bitsums`. Operates on [`PolyTerm`] lists:
/// `bits: HashSet<VarIdx>`, chain extender indexed by coefficient
/// via `BTreeMap<BigUint, Vec<(VarIdx, idx)>>`. No String allocation.
///
/// Algorithm:
/// 1. Collect `bits`: variables appearing in `system.bitsums`, plus
///    any variable `b` with an equality of the form `b·(b − 1) = 0`
///    (matched by [`detect_bit_constraint`]).
/// 2. For each equality, repeatedly find the longest sub-sum
///    `c·b_0 + 2c·b_1 + ... + 2^k·c·b_k` where each `b_i ∈ bits`
///    appears as a single-variable degree-1 term. Base coefficients
///    are tried in ascending symmetric-residue order
///    (`min(c, p − c)`, ties broken by raw value).
/// 3. On a chain of length ≥ [`MIN_AUTO_BITSUM_LEN`]: drop the
///    chain's terms from the equality, append a `c · __bitsum_N`
///    term, append the bit list to `system.bitsums`. The encoder
///    emits `b_0 + 2·b_1 + ... + 2^k·b_k − __bitsum_N = 0` into
///    `bitsum_polys` (split-GB seeder routes those to basis 0 only).
///
/// Soundness gate: chain length capped at `floor(log2(prime))` (via
/// [`bitsum_fits`]) so distinct bit patterns never collide modulo
/// `prime`. The same invariant gates the `basis2` propagation lemma in
/// `picus-analysis`. For cryptographic primes the cap is ~254; for
/// small primes used in regression tests (GF(7), GF(11), GF(13))
/// it's 2-3.
pub fn auto_extract_bitsums(
    system: &ConstraintSystem,
) -> ConstraintSystem {
    let p = &system.prime;

    // Bit-constrained variable set: variables with a `b·(b - 1) = 0`
    // equality plus any explicit bitsum entries.
    let mut bits: HashSet<VarIdx> = HashSet::new();
    for bs in &system.bitsums {
        for &v in bs {
            bits.insert(v);
        }
    }
    for eq in &system.equalities {
        if let Some(bit_idx) = detect_bit_constraint(eq, p) {
            bits.insert(bit_idx);
        }
    }
    if bits.is_empty() {
        return system.clone();
    }

    let mut rewritten_equalities: Vec<Vec<PolyTerm>> =
        Vec::with_capacity(system.equalities.len());
    let mut new_bitsums: Vec<Vec<VarIdx>> = system.bitsums.clone();

    // The aux variable for each extracted bitsum must match the slot
    // `encode_impl` allocates for it; both sides route through
    // `super::bitsum_aux_index` (user vars, then diseq witnesses, then one
    // `__bitsum_N` aux per bitsum) so the two cannot drift.
    let n_user = system.var_names.len();
    let n_diseq = system.disequalities.len();

    for eq in &system.equalities {
        let mut current_eq: Vec<PolyTerm> = eq.clone();
        let max_iters = current_eq.len() + 1;
        for _ in 0..max_iters {
            match find_bitsum_chain(&current_eq, &bits, p, MIN_AUTO_BITSUM_LEN) {
                Some((bit_list, base_coeff, consumed)) => {
                    let aux_idx = super::bitsum_aux_index(n_user, n_diseq, new_bitsums.len());
                    new_bitsums.push(bit_list);

                    let mut new_terms: Vec<PolyTerm> = current_eq
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !consumed.contains(i))
                        .map(|(_, t)| t.clone())
                        .collect();
                    new_terms.push(PolyTerm {
                        coeff: base_coeff,
                        vars: vec![(aux_idx, 1)],
                    });
                    current_eq = new_terms;
                }
                None => break,
            }
        }
        rewritten_equalities.push(current_eq);
    }

    ConstraintSystem {
        prime: system.prime.clone(),
        var_names: system.var_names.clone(),
        equalities: rewritten_equalities,
        disequalities: system.disequalities.clone(),
        assignments: system.assignments.clone(),
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

/// Match `b·(b - 1) = 0` on an [`PolyTerm`] list. The list is
/// expected to already be normalised by `rewrite_system`, so
/// `b^2` lives as `[(b_idx, 2)]` and `b` lives as `[(b_idx, 1)]`.
/// Returns the `VarIdx` of `b` on match.
fn detect_bit_constraint(eq: &[PolyTerm], p: &BigUint) -> Option<VarIdx> {
    let nonzero: Vec<&PolyTerm> = eq.iter().filter(|t| !t.coeff.is_zero()).collect();
    if nonzero.len() != 2 {
        return None;
    }
    let is_quad = |t: &&PolyTerm| t.vars.len() == 1 && t.vars[0].1 == 2;
    let is_lin = |t: &&PolyTerm| t.vars.len() == 1 && t.vars[0].1 == 1;
    let (quad, lin) = if is_quad(&nonzero[0]) && is_lin(&nonzero[1]) {
        (nonzero[0], nonzero[1])
    } else if is_quad(&nonzero[1]) && is_lin(&nonzero[0]) {
        (nonzero[1], nonzero[0])
    } else {
        return None;
    };
    if quad.vars[0].0 != lin.vars[0].0 {
        return None;
    }
    let sum = (&quad.coeff + &lin.coeff) % p;
    if !sum.is_zero() {
        return None;
    }
    Some(quad.vars[0].0)
}

/// Looks
/// for `c·b_0 + 2c·b_1 + ... + 2^(k-1)·c·b_{k-1}` where each `b_i`
/// is a known bit (degree 1 in a single index, coefficient
/// `(2^i · base) mod p`). Soundness gate: chain length capped at
/// `floor(log2(p))`.
fn find_bitsum_chain(
    eq: &[PolyTerm],
    bits: &HashSet<VarIdx>,
    p: &BigUint,
    min_len: usize,
) -> Option<(Vec<VarIdx>, BigUint, HashSet<usize>)> {
    let mut by_coeff: BTreeMap<BigUint, Vec<(VarIdx, usize)>> = BTreeMap::new();
    for (idx, t) in eq.iter().enumerate() {
        if t.coeff.is_zero() {
            continue;
        }
        if t.vars.len() == 1 && t.vars[0].1 == 1 && bits.contains(&t.vars[0].0) {
            by_coeff
                .entry(&t.coeff % p)
                .or_default()
                .push((t.vars[0].0, idx));
        }
    }
    if by_coeff.is_empty() {
        return None;
    }

    let abs_residue = |c: &BigUint| -> BigUint {
        let neg = p - c;
        if c < &neg {
            c.clone()
        } else {
            neg
        }
    };
    let mut candidates: Vec<BigUint> = by_coeff.keys().cloned().collect();
    candidates.sort_by(|a, b| {
        let ra = abs_residue(a);
        let rb = abs_residue(b);
        ra.cmp(&rb).then(a.cmp(b))
    });

    let two = BigUint::from(2u32);

    let max_chain_bits: usize = {
        // Largest n with 2^n <= p (see `bitsum_fits`): a chain of this
        // length cannot alias modulo p.
        let mut n = 0usize;
        while bitsum_fits(n + 1, p) {
            n += 1;
        }
        n
    };

    let mut best: Option<(Vec<VarIdx>, BigUint, HashSet<usize>)> = None;

    for base in &candidates {
        let mut chain_vars: Vec<VarIdx> = Vec::new();
        let mut chain_idxs: HashSet<usize> = HashSet::new();
        let mut used_vars: HashSet<VarIdx> = HashSet::new();

        let mut cur = base.clone();
        loop {
            if chain_vars.len() >= max_chain_bits {
                break;
            }
            let bucket = match by_coeff.get(&cur) {
                Some(b) => b,
                None => break,
            };
            let next = bucket
                .iter()
                .filter(|(v, _)| !used_vars.contains(v))
                .min_by_key(|(_, idx)| *idx);
            match next {
                Some(&(var, idx)) => {
                    used_vars.insert(var);
                    chain_vars.push(var);
                    chain_idxs.insert(idx);
                    cur = (&cur * &two) % p;
                }
                None => break,
            }
        }

        if chain_vars.len() >= min_len {
            let pick = match &best {
                None => true,
                Some((b_vars, _, _)) => chain_vars.len() > b_vars.len(),
            };
            if pick {
                best = Some((chain_vars, base.clone(), chain_idxs));
            }
        }
    }

    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::ConstraintSystemBuilder;

    // ────────── bitsum_fits ──────────

    #[test]
    fn bitsum_fits_holds_when_2_pow_len_le_prime() {
        // GF(7): len 2 → 4 ≤ 7 ✓; len 3 → 8 > 7 ✗.
        let p = BigUint::from(7u32);
        assert!(bitsum_fits(0, &p));
        assert!(bitsum_fits(1, &p));
        assert!(bitsum_fits(2, &p));
        assert!(!bitsum_fits(3, &p));
        assert!(!bitsum_fits(4, &p));
    }

    #[test]
    fn bitsum_fits_bn128_supports_long_chains() {
        // BN128 is 254-bit but p < 2^254, so the cap is at len 253.
        let p = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        ).unwrap();
        assert!(bitsum_fits(253, &p));
        assert!(!bitsum_fits(254, &p));
        assert!(!bitsum_fits(255, &p));
    }

    // ────────── auto_extract_bitsums ──────────

    fn cs_with(prime: u64, build: impl FnOnce(&mut ConstraintSystemBuilder)) -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(prime));
        build(&mut b);
        b.build()
    }

    #[test]
    fn auto_extract_no_bit_constrained_vars_is_passthrough() {
        // No bit constraints + no explicit bitsums → returns clone unchanged.
        let cs = cs_with(7, |b| {
            let x = b.var("x");
            let y = b.var("y");
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
                PolyTerm { coeff: BigUint::from(2u32), vars: vec![(y, 1)] },
            ]);
        });
        let out = auto_extract_bitsums(&cs);
        // Same number of equalities, same number of bitsums (none).
        assert_eq!(out.equalities.len(), cs.equalities.len());
        assert_eq!(out.bitsums.len(), 0);
    }

    #[test]
    fn auto_extract_finds_chain_when_bits_declared() {
        // Variables b0, b1 marked as bits via b·(b-1)=0 constraints, plus
        // an equality of the form `b0 + 2·b1 + 3 = 0` (matches bitsum
        // base coeff 1 with k=1). Should extract `[b0, b1]` as a bitsum.
        let cs = cs_with(7, |b| {
            let b0 = b.var("b0");
            let b1 = b.var("b1");
            // b0·(b0-1) = b0^2 - b0 = 0
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 2)] },
                PolyTerm { coeff: BigUint::from(6u32), vars: vec![(b0, 1)] }, // -1 mod 7 = 6
            ]);
            // b1·(b1-1) = 0
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b1, 2)] },
                PolyTerm { coeff: BigUint::from(6u32), vars: vec![(b1, 1)] },
            ]);
            // The bitsum-shaped equality: 1·b0 + 2·b1 + 3 = 0
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 1)] },
                PolyTerm { coeff: BigUint::from(2u32), vars: vec![(b1, 1)] },
                PolyTerm { coeff: BigUint::from(3u32), vars: vec![] },
            ]);
        });
        let out = auto_extract_bitsums(&cs);
        // Should detect [b0, b1] as a bitsum.
        assert_eq!(out.bitsums.len(), 1);
        assert_eq!(out.bitsums[0].len(), 2);
    }

    #[test]
    fn auto_extract_respects_bitsum_fits_cap() {
        // Over GF(7), bitsum_fits caps chain length at 2 (since 2^3 > 7).
        // Even if 3 bit-constrained vars are present with c, 2c, 4c
        // coefficients, the extractor must NOT extract a chain longer
        // than the cap.
        let cs = cs_with(7, |b| {
            let b0 = b.var("b0");
            let b1 = b.var("b1");
            let b2 = b.var("b2");
            for bv in [b0, b1, b2] {
                b.add_equality(vec![
                    PolyTerm { coeff: BigUint::from(1u32), vars: vec![(bv, 2)] },
                    PolyTerm { coeff: BigUint::from(6u32), vars: vec![(bv, 1)] },
                ]);
            }
            // c·b0 + 2c·b1 + 4c·b2 with c=1 (would-be 3-chain). 4 mod 7 = 4.
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 1)] },
                PolyTerm { coeff: BigUint::from(2u32), vars: vec![(b1, 1)] },
                PolyTerm { coeff: BigUint::from(4u32), vars: vec![(b2, 1)] },
            ]);
        });
        let out = auto_extract_bitsums(&cs);
        // No bitsum of length > 2 may be extracted under GF(7).
        for bs in &out.bitsums {
            assert!(bs.len() <= 2, "chain length {} exceeds GF(7) cap of 2", bs.len());
        }
    }

    #[test]
    fn auto_extract_preserves_existing_bitsums() {
        // Pre-existing bitsum entries must still appear in the output.
        let cs = cs_with(11, |b| {
            let b0 = b.var("b0");
            let b1 = b.var("b1");
            b.add_bitsum(vec![b0, b1]); // explicit
        });
        let out = auto_extract_bitsums(&cs);
        assert!(out.bitsums.len() >= 1);
        assert_eq!(out.bitsums[0], vec![0, 1]);
    }
}
