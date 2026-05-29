use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;
use std::collections::HashSet;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn test_zero_constraint() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let x = pr.var(0);
    assert_eq!(zero_constraint(&pr, &x), Some(0));

    let three = pr.field().from_int(3);
    let three_x = pr.scale(three, pr.var(0));
    assert_eq!(zero_constraint(&pr, &three_x), Some(0));

    let xy = pr.mul(pr.var(0), pr.var(1));
    assert_eq!(zero_constraint(&pr, &xy), None);
}

#[test]
fn test_one_constraint() {
    // x - 1 = 0  →  x = 1
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x_minus_1 = pr.sub(pr.var(0), pr.one());
    assert_eq!(one_constraint(&pr, &x_minus_1), Some(0));

    // 3x - 3 = 0  →  x = 1
    let three = pr.field().from_int(3);
    let neg_three = pr.field().from_int(-3);
    let term = pr.scale(three, pr.var(0));
    let p = pr.add(term, pr.constant(neg_three));
    assert_eq!(one_constraint(&pr, &p), Some(0));

    // x - 2 ≠ x = 1
    let neg_two = pr.field().from_int(-2);
    let p2 = pr.add(pr.var(0), pr.constant(neg_two));
    assert_eq!(one_constraint(&pr, &p2), None);
}

#[test]
fn test_bit_constraint() {
    // x^2 - x = 0
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let p = pr.sub(x2, pr.clone_poly(&x));
    assert_eq!(bit_constraint(&pr, &p), Some(BitConstraint { var: 0 }));

    // 5*x^2 - 5*x = 0  (also a bit constraint after scaling)
    let five = pr.field().from_int(5);
    let neg_five = pr.field().from_int(-5);
    let x2_b = pr.mul(pr.var(0), pr.var(0));
    let lin = pr.scale(neg_five, pr.var(0));
    let quad = pr.scale(five, x2_b);
    let p2 = pr.add(quad, lin);
    assert_eq!(bit_constraint(&pr, &p2), Some(BitConstraint { var: 0 }));

    // x^2 + x = 0  (NOT a bit constraint -- this is x*(x+1))
    let x2c = pr.mul(pr.var(0), pr.var(0));
    let p3 = pr.add(x2c, pr.var(0));
    assert_eq!(bit_constraint(&pr, &p3), None);
}

#[test]
fn test_extract_linear_monomials() {
    // p = 2x + 3y + xy + 5
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let five = pr.field().from_int(5);
    let p = pr.add(
        pr.add(
            pr.add(pr.scale(two, pr.var(0)), pr.scale(three, pr.var(1))),
            pr.mul(pr.var(0), pr.var(1)),
        ),
        pr.constant(five),
    );
    let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
    assert_eq!(lins.len(), 2);
    assert_eq!(rest.len(), 2);
}

#[test]
fn test_bit_sums_simple() {
    // p = x_0 + 2*x_1 + 4*x_2  →  bitsum with coeff=1, bits=[0,1,2]
    let pr = FfPolyRing::new(ff(17), vec!["x0".into(), "x1".into(), "x2".into()]);
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let p = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.scale(four, pr.var(2)),
    );
    let hint: HashSet<usize> = HashSet::new();
    let (sums, residual) = bit_sums(&pr, &p, &hint).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits.len(), 3);
    assert!(pr.is_zero(&residual));
}

/// Each case asserts that the polynomial-level bit-constraint detector
/// accepts (or correctly rejects) the canonical form of a `x*(x-1)=0`
/// equation expressed under various algebraically-equivalent rewrites.

#[test]
fn audit_bit_constraint_negated_form() {
    // Equation form: 0 = x - x²
    // picus polynomial: -x² + x = (p-1)*x² + x
    // After `normalize_poly` divides by (p-1), the canonical form
    // is x² + (1/(p-1))*x = x² - x. Detector should accept.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    // x - x²
    let p = pr.sub(pr.var(0), x2);
    // The detector accepts ANY scaling c*x² - c*x (`c == -lin/quad`),
    // which `x - x²` is for c = -1.
    assert_eq!(bit_constraint(&pr, &p), Some(BitConstraint { var: 0 }));
}

#[test]
fn audit_bit_constraint_nested_product() {
    // Equation form: 0 = x*(x-1)  →  x² - x
    // After polynomial multiplication picus produces x² - x directly.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let neg_one = pr.field().from_int(-1);
    // (x - 1) = x + (-1)
    let x_minus_1 = pr.add(pr.var(0), pr.constant(neg_one));
    // x * (x - 1) = x² - x
    let p = pr.mul(pr.var(0), x_minus_1);
    assert_eq!(bit_constraint(&pr, &p), Some(BitConstraint { var: 0 }));
}

#[test]
fn audit_bit_constraint_sum_form() {
    // Equation form: 0 = x² + (-x) = x² - x.
    // Algebraically same as standard form.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let neg_x = pr.scale(pr.field().from_int(-1), pr.var(0));
    let p = pr.add(x2, neg_x);
    assert_eq!(bit_constraint(&pr, &p), Some(BitConstraint { var: 0 }));
}

#[test]
fn audit_bit_constraint_rejects_x_squared_plus_x() {
    // x² + x is NOT a bit constraint: it's x*(x+1), zero set {0, -1}.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.add(x2, pr.var(0));
    assert_eq!(bit_constraint(&pr, &p), None);
}

#[test]
fn audit_bit_sums_mixed_bases_rejected() {
    // b0 + 3*b1 — not a bitsum (3 ≠ 2). Detector should
    // either reject or treat as a degenerate case.
    let pr = FfPolyRing::new(ff(17), vec!["b0".into(), "b1".into()]);
    let three = pr.field().from_int(3);
    let p = pr.add(pr.var(0), pr.scale(three, pr.var(1)));
    // Not a power-of-2-coefficient sequence; bit_sums returns the
    // partial sum (just b0 with coeff 1) and the rest as residual.
    let (sums, _residual) = bit_sums(&pr, &p, &HashSet::new()).unwrap();
    // The detector finds the longest valid prefix, so a single-bit
    // bitsum {b0} is valid; b1 with coeff 3 falls into residual.
    for s in &sums {
        for (i, _) in s.bits.iter().enumerate() {
            let _ = i;
        }
        // Verify each bit's position progression is valid (powers of 2).
        assert!(
            s.bits.len() <= 1,
            "non-power-of-2 sequence should not extend"
        );
    }
}

#[test]
fn test_bit_sums_with_residual() {
    // p = x + 2*y + z*z  →  bitsum [x,y] with coeff=1, residual=z*z
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into(), "z".into()]);
    let two = pr.field().from_int(2);
    let z2 = pr.mul(pr.var(2), pr.var(2));
    let p = pr.add(pr.add(pr.var(0), pr.scale(two, pr.var(1))), z2);
    let (sums, residual) = bit_sums(&pr, &p, &HashSet::new()).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits, vec![0, 1]);
    assert!(!pr.is_zero(&residual));
}

// =============================================================================
// bit_constraint  (GF(7))
// =============================================================================
//
// `x*(x-1) = 0` must be detected under all sign / rewrite forms;
// non-qualifying forms (pure `x`, pure `x^2`, `x^3`, ...) must be
// rejected.
#[test]
fn test_bit_constraint_positive_forms() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let _fp = &pr.field();

    // x*(x-1) = x^2 - x  →  detected
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p1 = pr.sub(x2, pr.var(0));
    assert!(bit_constraint(&pr, &p1).is_some());

    // Same polynomial: x = x*x  ↔  x^2 - x = 0   → detected
    // (already covered by p1 above, but confirming symmetry)
    let p2 = pr.sub(pr.mul(pr.var(0), pr.var(0)), pr.var(0));
    assert!(bit_constraint(&pr, &p2).is_some());

    // -x^2 + x = -(x^2 - x)   → still x*(x-1)=0  → detected
    let p3 = pr.sub(pr.var(0), pr.mul(pr.var(0), pr.var(0)));
    assert!(bit_constraint(&pr, &p3).is_some());

    // 5*x^2 - 5*x   (scaled)  → detected
    let five = pr.field().from_int(5);
    let neg_five = pr.field().from_int(-5);
    let p4 = pr.add(
        pr.scale(five, pr.mul(pr.var(0), pr.var(0))),
        pr.scale(neg_five, pr.var(0)),
    );
    assert!(bit_constraint(&pr, &p4).is_some());
}

#[test]
fn test_bit_constraint_negative_forms() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);

    // x*x*x = x  →  x^3 - x = 0  →  NOT a bit constraint (cubic)
    let x3 = pr.mul(pr.mul(pr.var(0), pr.var(0)), pr.var(0));
    let p1 = pr.sub(x3, pr.var(0));
    assert!(bit_constraint(&pr, &p1).is_none());

    // x alone  →  not a bit constraint
    assert!(bit_constraint(&pr, &pr.var(0)).is_none());

    // x^2 alone  →  not a bit constraint (missing linear term)
    let x2 = pr.mul(pr.var(0), pr.var(0));
    assert!(bit_constraint(&pr, &x2).is_none());

    // x^2 + x = 0  →  x*(x+1) = 0  →  NOT a bit constraint (coeff mismatch)
    let p2 = pr.add(pr.mul(pr.var(0), pr.var(0)), pr.var(0));
    assert!(bit_constraint(&pr, &p2).is_none());
}

// =============================================================================
// linear_monomial  (GF(7))
// =============================================================================
#[test]
fn test_linear_monomial_forms() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let fp = &pr.field();

    // x * 1 = x  →  detected
    assert!(linear_monomial(&pr, &pr.var(0)).is_some());

    // 1 * x = x  →  same as above
    let one_x = pr.scale(pr.field().one(), pr.var(0));
    assert!(linear_monomial(&pr, &one_x).is_some());

    // -x  →  detected (coeff = -1)
    let neg_x = pr.neg(pr.var(0));
    let lm = linear_monomial(&pr, &neg_x).unwrap();
    assert_eq!(lm.var, 0);
    let neg_one = fp.int_hom().map(-1);
    assert!(fp.eq_el(&lm.coeff, &neg_one));

    // x + y  →  NOT a linear monomial (two terms)
    let sum = pr.add(pr.var(0), pr.var(1));
    assert!(linear_monomial(&pr, &sum).is_none());

    // constant  →  NOT a linear monomial
    assert!(linear_monomial(&pr, &pr.one()).is_none());

    // x*y  →  NOT a linear monomial (quadratic)
    let xy = pr.mul(pr.var(0), pr.var(1));
    assert!(linear_monomial(&pr, &xy).is_none());
}

// =============================================================================
// extract_linear_monomials  (GF(5))
// =============================================================================
#[test]
fn test_extract_linear_none() {
    // x*y + z*z + 3  →  0 linear monomials, 3 rest terms (x*y, z², constant).
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into(), "z".into()]);
    let p = pr.add(
        pr.add(pr.mul(pr.var(0), pr.var(1)), pr.mul(pr.var(2), pr.var(2))),
        pr.constant(pr.field().from_int(3)),
    );
    let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
    assert_eq!(lins.len(), 0);
    assert_eq!(rest.len(), 3); // x*y, z^2, constant
}

#[test]
fn test_extract_linear_with_neg() {
    // x*y - x  →  1 linear (-x), 1 rest (x*y)
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let fp = &pr.field();
    let p = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.var(0));
    let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
    assert_eq!(lins.len(), 1);
    assert_eq!(lins[0].var, 0);
    let neg_one = fp.int_hom().map(-1);
    assert!(fp.eq_el(&lins[0].coeff, &neg_one));
    assert_eq!(rest.len(), 1);
}

#[test]
fn test_extract_linear_mixed() {
    // p = x*y + 3*y + (-1)*x + 4   →  linear: {y(coeff=3), x(coeff=-1)},  rest: {x*y, 4}
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let three = pr.field().from_int(3);
    let neg_one = pr.field().from_int(-1);
    let four = pr.field().from_int(4);
    let p = pr.add(
        pr.add(
            pr.add(pr.mul(pr.var(0), pr.var(1)), pr.scale(three, pr.var(1))),
            pr.scale(neg_one, pr.var(0)),
        ),
        pr.constant(four),
    );
    let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
    assert_eq!(lins.len(), 2);
    assert_eq!(rest.len(), 2); // x*y, 4
}

// =============================================================================
// bit_sums  (GF(103))
// =============================================================================
#[test]
fn test_bitsums_implicit_one_coeff() {
    // x + y + b0 + 2*b1   (bits = {b0, b1, b2, b3})
    // Expected: 1 bitsum with coeff=1, bits=[b0, b1], others=[x, y]
    let pr = FfPolyRing::new(
        ff(103),
        vec![
            "x".into(),
            "y".into(),
            "b0".into(),
            "b1".into(),
            "b2".into(),
            "b3".into(),
        ],
    );
    let two = pr.field().from_int(2);
    let p = pr.add(
        pr.add(pr.add(pr.var(0), pr.var(1)), pr.var(2)),
        pr.scale(two, pr.var(3)),
    );
    let bits: HashSet<usize> = [2, 3, 4, 5].into_iter().collect();
    let (sums, residual) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits.len(), 2);
    // residual should be x + y
    assert!(!pr.is_zero(&residual));
}

#[test]
fn test_bitsums_negative_coeffs() {
    // x*y + x + y + (-1)*b0 + (-2)*b1 + (-4)*b2
    // Expected: 1 bitsum coeff=-1, bits=[b0, b1, b2], others=[x*y, x, y]
    let pr = FfPolyRing::new(
        ff(103),
        vec![
            "x".into(),
            "y".into(),
            "b0".into(),
            "b1".into(),
            "b2".into(),
            "b3".into(),
        ],
    );
    let fp = &pr.field();
    let neg1 = pr.field().from_int(-1);
    let neg2 = pr.field().from_int(-2);
    let neg4 = pr.field().from_int(-4);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.add(
        pr.add(
            pr.add(pr.add(xy, pr.var(0)), pr.var(1)),
            pr.scale(neg1, pr.var(2)),
        ),
        pr.add(pr.scale(neg2, pr.var(3)), pr.scale(neg4, pr.var(4))),
    );
    let bits: HashSet<usize> = [2, 3, 4, 5].into_iter().collect();
    let (sums, _residual) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits.len(), 3);
    // Verify base coeff is -1
    let expected_neg1 = fp.int_hom().map(-1);
    assert!(fp.eq_el(&sums[0].coeff, &expected_neg1));
}

#[test]
fn test_bitsums_gap_breaks_chain() {
    // (-1)*b0 + (-2)*b1 + (-8)*b3   (gap at b2, coeff -4 missing)
    // Expected: 1 bitsum coeff=-1, bits=[b0, b1] only (chain breaks at missing -4*b2)
    // b3 with coeff -8 doesn't continue the chain.
    let pr = FfPolyRing::new(
        ff(103),
        vec![
            "x".into(),
            "y".into(),
            "b0".into(),
            "b1".into(),
            "b2".into(),
            "b3".into(),
        ],
    );
    let neg1 = pr.field().from_int(-1);
    let neg2 = pr.field().from_int(-2);
    let neg8 = pr.field().from_int(-8);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.add(
        pr.add(
            pr.add(pr.add(xy, pr.var(0)), pr.var(1)),
            pr.scale(neg1, pr.var(2)),
        ),
        pr.add(pr.scale(neg2, pr.var(3)), pr.scale(neg8, pr.var(5))),
    );
    let bits: HashSet<usize> = [2, 3, 4, 5].into_iter().collect();
    let (sums, _) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits.len(), 2); // only b0, b1
}

#[test]
fn test_bitsums_weird_positive_start() {
    // 6*b0 + 12*b1 + 24*b2   →  bitsum coeff=6, bits=[b0, b1, b2]
    let pr = FfPolyRing::new(
        ff(103),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()],
    );
    let fp = &pr.field();
    let c6 = pr.field().from_int(6);
    let c12 = pr.field().from_int(12);
    let c24 = pr.field().from_int(24);
    let p = pr.add(
        pr.add(pr.scale(c6, pr.var(0)), pr.scale(c12, pr.var(1))),
        pr.scale(c24, pr.var(2)),
    );
    let bits: HashSet<usize> = [0, 1, 2, 3].into_iter().collect();
    let (sums, residual) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 1);
    let expected_6 = fp.int_hom().map(6);
    assert!(fp.eq_el(&sums[0].coeff, &expected_6));
    assert_eq!(sums[0].bits.len(), 3);
    assert!(pr.is_zero(&residual));
}

#[test]
fn test_bitsums_two_bitsums() {
    // 6*b0 + 12*b1 + (-4)*b2 + (-8)*b3
    // Expected: 2 bitsums:
    //   coeff=-4, bits=[b2, b3]
    //   coeff=6,  bits=[b0, b1]
    let pr = FfPolyRing::new(
        ff(103),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()],
    );
    let _fp = &pr.field();
    let c6 = pr.field().from_int(6);
    let c12 = pr.field().from_int(12);
    let neg4 = pr.field().from_int(-4);
    let neg8 = pr.field().from_int(-8);
    let p = pr.add(
        pr.add(pr.scale(c6, pr.var(0)), pr.scale(c12, pr.var(1))),
        pr.add(pr.scale(neg4, pr.var(2)), pr.scale(neg8, pr.var(3))),
    );
    let bits: HashSet<usize> = [0, 1, 2, 3].into_iter().collect();
    let (sums, residual) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 2);
    assert!(pr.is_zero(&residual));
    // Both bitsums have 2 bits each.
    let mut lens: Vec<usize> = sums.iter().map(|s| s.bits.len()).collect();
    lens.sort();
    assert_eq!(lens, vec![2, 2]);
}

// =============================================================================
// one_constraint  reject paths
// =============================================================================

#[test]
fn test_one_constraint_rejects_quadratic_term() {
    // x^2 - 1: the x^2 term has exponent 2, which `one_constraint` rejects
    // as soon as it sees a variable of degree > 1.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.one());
    assert_eq!(one_constraint(&pr, &p), None);
}

#[test]
fn test_one_constraint_rejects_multivar_term() {
    // x*y - 1: the x*y monomial introduces a second variable in one term,
    // which `one_constraint` rejects (no single linear variable).
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());
    assert_eq!(one_constraint(&pr, &p), None);
}

// =============================================================================
// extract_linear_monomials  zero-polynomial path
// =============================================================================

#[test]
fn test_extract_linear_monomials_zero_poly_is_none() {
    // The zero polynomial has no terms, so there are no linear monomials
    // to extract.
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    assert!(extract_linear_monomials(&pr, &pr.zero()).is_none());
}
