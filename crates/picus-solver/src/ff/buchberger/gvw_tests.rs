use super::super::{groebner_basis, interreduce, BuchbergerConfig};
use super::groebner_basis_gvw;
use crate::ff::field::PrimeField;
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{DensePoly, PolyRing};
use num_bigint::BigUint;
use std::sync::Arc;

fn ring(n: usize) -> Arc<PolyRing> {
    PolyRing::new(
        PrimeField::new(BigUint::from(101u32)),
        (0..n).map(|i| format!("x{i}")).collect(),
        MonomialOrder::DegRevLex,
    )
}

fn poly(r: &PolyRing, terms: &[(Vec<u16>, i64)]) -> DensePoly {
    let t: Vec<(Monomial, _)> = terms
        .iter()
        .map(|(e, c)| (Monomial::from_exponents(e.clone()), r.field.from_i64(*c)))
        .collect();
    DensePoly::from_terms(t, r)
}

/// Canonical reduced-GB fingerprint: interreduce (→ monic reduced GB,
/// which is unique for a fixed order) then sort the per-polynomial hashes.
fn canon(gb: Vec<DensePoly>, r: &Arc<PolyRing>) -> Vec<u64> {
    let mut h: Vec<u64> = interreduce(gb, r).iter().map(|p| p.content_hash()).collect();
    h.sort_unstable();
    h
}

fn per_pair(gens: &[DensePoly], r: &Arc<PolyRing>) -> Vec<u64> {
    let cfg = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
    let gb = groebner_basis(gens.to_vec(), r, &cfg).expect("per-pair gb");
    canon(gb.basis, r)
}

fn gvw(gens: &[DensePoly], r: &Arc<PolyRing>) -> Vec<u64> {
    let gb = groebner_basis_gvw(gens.to_vec(), r, MonomialOrder::DegRevLex, None).expect("gvw gb");
    canon(gb, r)
}

#[test]
fn gvw_resolves_inconsistent_system() {
    // x0 - 1 and x0 - 2 over GF(101): the GB is {1} (whole ring).
    let r = ring(1);
    let gens = [
        poly(&r, &[(vec![1], 1), (vec![0], -1)]),
        poly(&r, &[(vec![1], 1), (vec![0], -2)]),
    ];
    let gb = groebner_basis_gvw(gens.to_vec(), &r, MonomialOrder::DegRevLex, None).unwrap();
    assert!(
        gb.iter()
            .any(|p| !p.is_zero() && p.leading_monomial(&r).map_or(false, |m| m.is_one())),
        "inconsistent system must yield a nonzero constant"
    );
}

#[test]
fn gvw_matches_per_pair_on_hand_systems() {
    // A handful of small systems with genuine S-pair work: the GVW reduced
    // GB must equal the per-pair reduced GB element-for-element.
    let r2 = ring(2);
    let r3 = ring(3);
    let systems: Vec<(Arc<PolyRing>, Vec<DensePoly>)> = vec![
        // x*y - 1, x^2 - y
        (
            r2.clone(),
            vec![
                poly(&r2, &[(vec![1, 1], 1), (vec![0, 0], -1)]),
                poly(&r2, &[(vec![2, 0], 1), (vec![0, 1], -1)]),
            ],
        ),
        // x^2 - y, y^2 - x  (a cyclic-ish system)
        (
            r2.clone(),
            vec![
                poly(&r2, &[(vec![2, 0], 1), (vec![0, 1], -1)]),
                poly(&r2, &[(vec![0, 2], 1), (vec![1, 0], -1)]),
            ],
        ),
        // xy - z, yz - x, xz - y  (symmetric 3-var)
        (
            r3.clone(),
            vec![
                poly(&r3, &[(vec![1, 1, 0], 1), (vec![0, 0, 1], -1)]),
                poly(&r3, &[(vec![0, 1, 1], 1), (vec![1, 0, 0], -1)]),
                poly(&r3, &[(vec![1, 0, 1], 1), (vec![0, 1, 0], -1)]),
            ],
        ),
    ];
    for (r, gens) in &systems {
        assert_eq!(
            gvw(gens, r),
            per_pair(gens, r),
            "GVW reduced GB != per-pair reduced GB"
        );
    }
}
