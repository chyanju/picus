use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn pr_xy() -> FfPolyRing {
    let field = PrimeField::new(BigUint::from(17u32));
    FfPolyRing::new(field, vec!["x".into(), "y".into()])
}

#[test]
fn test_homog_ring_shape() {
    let pr = pr_xy();
    let h = HomogRing::new(&pr);
    assert_eq!(h.base.n_vars(), 2);
    assert_eq!(h.ext.n_vars(), 3);
    assert_eq!(h.h_idx, 2);
}

#[test]
fn test_lift_preserves_zero() {
    let pr = pr_xy();
    let h = HomogRing::new(&pr);
    let z = pr.zero();
    let lifted = h.lift(&z);
    assert!(h.ext.ring.is_zero(&lifted));
}

#[test]
fn test_lift_dehom_roundtrip_on_homog_input() {
    // x + y is already degree-1 homogeneous → lift, dehom should be identity.
    let pr = pr_xy();
    let h = HomogRing::new(&pr);
    let x = pr.var(0);
    let y = pr.var(1);
    let p = pr.add(x, y);
    let q = h.lift(&p);
    let p2 = h.dehom(&q);
    // Compare via subtraction zero test
    let diff = pr.sub(p, p2);
    assert!(pr.is_zero(&diff));
}

#[test]
fn test_homogenize_mixed_degree() {
    // f = x^2 + y + 1 (degrees 2, 1, 0; max_d = 2)
    // homog should be: x^2 + y·h + h^2
    let pr = pr_xy();
    let h = HomogRing::new(&pr);
    let x = pr.var(0);
    let y = pr.var(1);
    let one = pr.one();
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let f = pr.add(pr.add(xx, pr.clone_poly(&y)), one);
    let lifted = h.lift(&f);
    let homog = h.homogenize(&lifted);
    // dehom(homog) should give back f exactly (h := 1).
    let back = h.dehom(&homog);
    let diff = pr.sub(pr.clone_poly(&f), back);
    assert!(pr.is_zero(&diff), "dehom(homog(lift(f))) should equal f");

    // Every term of `homog` must have total degree exactly 2.
    let ext_ring = &h.ext.ring;
    for (_, m) in ext_ring.terms(&homog) {
        let d: usize = (0..h.ext.n_vars())
            .map(|i| ext_ring.exponent_at(&m, i))
            .sum();
        assert_eq!(d, 2, "homogenized polynomial must be degree-2 homogeneous");
    }
}

#[test]
fn test_homogenize_already_homog() {
    // f = x + y is degree-1 homog; lift_and_homogenize should equal lift.
    let pr = pr_xy();
    let h = HomogRing::new(&pr);
    let f = pr.add(pr.var(0), pr.var(1));
    let lifted = h.lift(&f);
    let homog = h.lift_and_homogenize(&f);
    let diff = h.ext.sub(lifted, homog);
    assert!(h.ext.is_zero(&diff));
}
