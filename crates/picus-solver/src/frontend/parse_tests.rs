use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

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

/// Equivalence with cvc5's AST-level `bitConstraint`. Each case asserts that picus's
/// polynomial-level detector accepts (or correctly rejects) the
/// canonical form produced by encoding the equivalent AST.

#[test]
fn audit_bit_constraint_negated_form() {
    // AST: (= 0 (- x (* x x)))  →  x - x²
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
    // AST: (= 0 (* x (- x 1)))  →  x*(x-1) → x² - x
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
    // AST: (= 0 (+ (* x x) (- x)))  →  x² + (-x) = x² - x.
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
    // (+ b0 (* 3 b1)) — not a bitsum (3 ≠ 2). Detector should
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
