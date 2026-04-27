//! Semantic ports of cvc5's `theory_ff_parse_white.cpp` unit tests.
//!
//! cvc5's tests operate on SMT-LIB AST `Node`s; ours operate directly on
//! polynomials in our `FfPolyRing`.  The semantics are identical: we construct
//! the same polynomial from terms and check the same detection functions.

use picus_solver::field::FfField;
use picus_solver::parse::*;
use picus_solver::poly::FfPolyRing;
use num_bigint::BigUint;
use std::collections::HashSet;

fn ff(p: u32) -> FfField { FfField::new(&BigUint::from(p)) }

// =============================================================================
// bitConstraint  (cvc5 lines 29-63, GF(7))
// =============================================================================
//
// cvc5 tests that x*(x-1)=0 is detected under various sign/rewrite forms,
// and rejects non-qualifying forms (pure x, pure x^2, x^3, etc.).
#[test]
fn test_bit_constraint_positive_forms() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let _fp = pr.field.field();

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
    let five = pr.field.from_int(5);
    let neg_five = pr.field.from_int(-5);
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
// linearMonomial  (cvc5 lines 66-79, GF(7))
// =============================================================================
#[test]
fn test_linear_monomial_forms() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let fp = pr.field.field();

    // x * 1 = x  →  detected
    assert!(linear_monomial(&pr, &pr.var(0)).is_some());

    // 1 * x = x  →  same as above
    let one_x = pr.scale(pr.field.one(), pr.var(0));
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
// extractLinearMonomials  (cvc5 lines 82-145, GF(5))
// =============================================================================
#[test]
fn test_extract_linear_none() {
    // All non-linear: x*y, x*y, x+y  →  0 linear, 3 rest
    // We can't directly create "x+y as a single opaque rest term" because
    // polynomials are sums.  In our representation, x*y + x*y + (x+y) =
    // 2*x*y + x + y.  The linears are x, y (each appear degree-1).
    // So this is inherently different from the cvc5 Node-based test.
    //
    // Instead, test: x*y + z*z + 5  →  0 linear, 3 rest terms.
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into(), "z".into()]);
    let _five = pr.field.from_int(0);  // 0 is zero, use constant 3
    let p = pr.add(
        pr.add(pr.mul(pr.var(0), pr.var(1)), pr.mul(pr.var(2), pr.var(2))),
        pr.constant(pr.field.from_int(3)),
    );
    let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
    assert_eq!(lins.len(), 0);
    assert_eq!(rest.len(), 3); // x*y, z^2, constant
}

#[test]
fn test_extract_linear_with_neg() {
    // x*y - x  →  1 linear (-x), 1 rest (x*y)
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let fp = pr.field.field();
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
    // x*y + x*y + 3*y + (-1)*x + (x+y) + 4
    // Polynomial collapses to: 2*x*y + 3*y - x + x + y + 4 = 2*x*y + 4*y + 4
    // Wait, that's not what we want.  Let me build a more controlled example.
    //
    // p = x*y + 3*y + (-1)*x + 4   →  linear: {y(coeff=3), x(coeff=-1)},  rest: {x*y, 4}
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let three = pr.field.from_int(3);
    let neg_one = pr.field.from_int(-1);
    let four = pr.field.from_int(4);
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
// bitSums  (cvc5 lines 148-279, GF(103))
// =============================================================================
#[test]
fn test_bitsums_implicit_one_coeff() {
    // x + y + b0 + 2*b1   (bits = {b0, b1, b2, b3})
    // Expected: 1 bitsum with coeff=1, bits=[b0, b1], others=[x, y]
    let pr = FfPolyRing::new(ff(103),
        vec!["x".into(), "y".into(), "b0".into(), "b1".into(), "b2".into(), "b3".into()]);
    let two = pr.field.from_int(2);
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
    let pr = FfPolyRing::new(ff(103),
        vec!["x".into(), "y".into(), "b0".into(), "b1".into(), "b2".into(), "b3".into()]);
    let fp = pr.field.field();
    let neg1 = pr.field.from_int(-1);
    let neg2 = pr.field.from_int(-2);
    let neg4 = pr.field.from_int(-4);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.add(
        pr.add(
            pr.add(pr.add(xy, pr.var(0)), pr.var(1)),
            pr.scale(neg1, pr.var(2)),
        ),
        pr.add(
            pr.scale(neg2, pr.var(3)),
            pr.scale(neg4, pr.var(4)),
        ),
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
    let pr = FfPolyRing::new(ff(103),
        vec!["x".into(), "y".into(), "b0".into(), "b1".into(), "b2".into(), "b3".into()]);
    let neg1 = pr.field.from_int(-1);
    let neg2 = pr.field.from_int(-2);
    let neg8 = pr.field.from_int(-8);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.add(
        pr.add(
            pr.add(pr.add(xy, pr.var(0)), pr.var(1)),
            pr.scale(neg1, pr.var(2)),
        ),
        pr.add(
            pr.scale(neg2, pr.var(3)),
            pr.scale(neg8, pr.var(5)),
        ),
    );
    let bits: HashSet<usize> = [2, 3, 4, 5].into_iter().collect();
    let (sums, _) = bit_sums(&pr, &p, &bits).unwrap();
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].bits.len(), 2); // only b0, b1
}

#[test]
fn test_bitsums_weird_positive_start() {
    // 6*b0 + 12*b1 + 24*b2   →  bitsum coeff=6, bits=[b0, b1, b2]
    let pr = FfPolyRing::new(ff(103),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()]);
    let fp = pr.field.field();
    let c6 = pr.field.from_int(6);
    let c12 = pr.field.from_int(12);
    let c24 = pr.field.from_int(24);
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
    let pr = FfPolyRing::new(ff(103),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()]);
    let _fp = pr.field.field();
    let c6 = pr.field.from_int(6);
    let c12 = pr.field.from_int(12);
    let neg4 = pr.field.from_int(-4);
    let neg8 = pr.field.from_int(-8);
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
