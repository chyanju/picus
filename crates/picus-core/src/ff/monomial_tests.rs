use super::*;

fn mono(exps: &[u16]) -> Monomial {
    Monomial::from_exponents(exps.to_vec())
}

#[test]
fn basic_ops() {
    let a = mono(&[2, 1, 0]);
    let b = mono(&[1, 2, 1]);
    assert_eq!(a.total_degree(), 3);
    assert_eq!(b.total_degree(), 4);
    let prod = a.mul(&b);
    assert_eq!(prod.exponents(), &[3, 3, 1]);
    assert_eq!(prod.total_degree(), 7);
    let lcm = a.lcm(&b);
    assert_eq!(lcm.exponents(), &[2, 2, 1]);
    let gcd = a.gcd(&b);
    assert_eq!(gcd.exponents(), &[1, 1, 0]);
}

#[test]
fn divides_and_div() {
    let a = mono(&[1, 1, 0]);
    let b = mono(&[2, 1, 1]);
    assert!(a.divides(&b));
    assert!(!b.divides(&a));
    let q = b.div(&a);
    assert_eq!(q.exponents(), &[1, 0, 1]);
    assert_eq!(q.total_degree(), 2);
}

#[test]
fn coprime() {
    assert!(mono(&[1, 0, 0]).is_coprime(&mono(&[0, 2, 1])));
    assert!(!mono(&[1, 1, 0]).is_coprime(&mono(&[0, 1, 0])));
}

#[test]
fn lex_ordering() {
    // x_0^2 > x_0 x_1 (because of the first index)
    let a = mono(&[2, 0, 0]);
    let b = mono(&[1, 1, 0]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Greater);
}

#[test]
fn degrevlex_ordering() {
    // Same total degree (3): x0^2 x1 vs x1^2 x2.
    // In DegRevLex, x0^2 x1 > x1^2 x2 because the rightmost-nonzero
    // exponent in x1^2 x2 is x2 (var 2, exp 1) vs x1 (var 1, exp 1) —
    // i.e. x1^2 x2 has a nonzero exponent further to the right, so it ranks LOWER.
    let a = mono(&[2, 1, 0]);
    let b = mono(&[0, 2, 1]);
    assert_eq!(a.total_degree(), b.total_degree());
    assert_eq!(
        a.cmp_with_order(&b, MonomialOrder::DegRevLex),
        Ordering::Greater
    );

    // Different degrees: x0^3 vs x0 x1
    let c = mono(&[3, 0, 0]);
    let d = mono(&[1, 1, 0]);
    assert_eq!(
        c.cmp_with_order(&d, MonomialOrder::DegRevLex),
        Ordering::Greater
    );
}

// ── Constructors ────────────────────────────────────────────────────────

#[test]
fn prop_one_is_constant() {
    // Monomial::one(n) is the constant 1: all zero exponents and degree 0.
    for n in 0..5 {
        let m = Monomial::one(n);
        assert_eq!(m.n_vars(), n);
        assert_eq!(m.total_degree(), 0);
        assert!(m.is_one(), "one(n).is_one() must be true");
        assert!(m.exponents().iter().all(|&e| e == 0));
    }
}

#[test]
fn prop_single_var_constructs_correctly() {
    // single_var(n, var, exp) is the monomial x_var^exp; exponent vector
    // is all-zero except slot `var` which is `exp`.
    let m = Monomial::single_var(4, 2, 7);
    assert_eq!(m.n_vars(), 4);
    assert_eq!(m.total_degree(), 7);
    assert_eq!(m.exponent(0), 0);
    assert_eq!(m.exponent(1), 0);
    assert_eq!(m.exponent(2), 7);
    assert_eq!(m.exponent(3), 0);
    assert!(!m.is_one());
}

#[test]
fn prop_from_exponents_computes_total_degree() {
    // total_degree is the sum of exponents (over u32 to avoid overflow).
    let m = Monomial::from_exponents(vec![3, 0, 5, 2]);
    assert_eq!(m.total_degree(), 10);
    let zero = Monomial::from_exponents(vec![0, 0, 0]);
    assert!(zero.is_one());
    assert_eq!(zero.total_degree(), 0);
}

// ── mul / div / divides / lcm / gcd algebraic identities ────────────────

#[test]
fn prop_mul_is_commutative() {
    let a = mono(&[2, 1, 0, 3]);
    let b = mono(&[0, 4, 1, 2]);
    let ab = a.mul(&b);
    let ba = b.mul(&a);
    assert_eq!(ab, ba, "monomial mul commutative");
    assert_eq!(ab.total_degree(), a.total_degree() + b.total_degree());
}

#[test]
fn prop_mul_assign_matches_mul() {
    // mul_assign equivalent to mul for the same operand pair.
    let a = mono(&[1, 2, 3]);
    let b = mono(&[4, 0, 1]);
    let prod = a.mul(&b);
    let mut a2 = a.clone();
    a2.mul_assign(&b);
    assert_eq!(a2, prod);
}

#[test]
fn prop_mul_by_one_is_identity() {
    // a * 1 == a == 1 * a
    let a = mono(&[2, 3, 5]);
    let one = Monomial::one(3);
    assert_eq!(a.mul(&one), a);
    assert_eq!(one.mul(&a), a);
}

#[test]
fn prop_divides_reflexive() {
    // Every monomial divides itself.
    let a = mono(&[2, 1, 3, 0]);
    assert!(a.divides(&a));
}

#[test]
fn prop_one_divides_everything() {
    // The constant 1 divides every monomial.
    let one = Monomial::one(3);
    for exps in &[vec![0, 0, 0], vec![5, 0, 0], vec![1, 2, 3], vec![100, 50, 25]] {
        let m = Monomial::from_exponents(exps.clone());
        assert!(one.divides(&m), "1 divides any monomial: {exps:?}");
    }
}

#[test]
fn prop_div_inverse_of_mul() {
    // (a * b) / a == b when the divisor divides.
    let a = mono(&[1, 2, 0]);
    let b = mono(&[3, 0, 1]);
    let ab = a.mul(&b);
    assert!(a.divides(&ab));
    let q = ab.div(&a);
    assert_eq!(q, b, "(a*b)/a != b");
    assert_eq!(q.total_degree(), b.total_degree());
}

#[test]
fn prop_lcm_idempotent_and_symmetric() {
    // lcm(a,a) = a; lcm(a,b) = lcm(b,a); lcm is componentwise max.
    let a = mono(&[2, 5, 0]);
    let b = mono(&[3, 1, 4]);
    assert_eq!(a.lcm(&a), a);
    assert_eq!(a.lcm(&b), b.lcm(&a));
    let l = a.lcm(&b);
    assert_eq!(l.exponents(), &[3, 5, 4]);
    assert_eq!(l.total_degree(), 12);
}

#[test]
fn prop_lcm_divides_property() {
    // Both a and b divide lcm(a, b).
    let a = mono(&[2, 5, 0]);
    let b = mono(&[3, 1, 4]);
    let l = a.lcm(&b);
    assert!(a.divides(&l));
    assert!(b.divides(&l));
}

#[test]
fn prop_gcd_idempotent_and_symmetric() {
    // gcd(a,a) = a; gcd(a,b) = gcd(b,a); gcd is componentwise min.
    let a = mono(&[2, 5, 0]);
    let b = mono(&[3, 1, 4]);
    assert_eq!(a.gcd(&a), a);
    assert_eq!(a.gcd(&b), b.gcd(&a));
    let g = a.gcd(&b);
    assert_eq!(g.exponents(), &[2, 1, 0]);
    assert_eq!(g.total_degree(), 3);
}

#[test]
fn prop_gcd_divides_both() {
    // gcd(a, b) divides both a and b.
    let a = mono(&[2, 5, 0]);
    let b = mono(&[3, 1, 4]);
    let g = a.gcd(&b);
    assert!(g.divides(&a));
    assert!(g.divides(&b));
}

#[test]
fn prop_gcd_times_lcm_eq_mul_for_monomials() {
    // For monomials, gcd(a,b) * lcm(a,b) == a * b (componentwise min + max = sum).
    let a = mono(&[2, 5, 0, 3]);
    let b = mono(&[3, 1, 4, 3]);
    let lhs = a.gcd(&b).mul(&a.lcm(&b));
    let rhs = a.mul(&b);
    assert_eq!(lhs, rhs);
}

#[test]
fn prop_coprime_means_disjoint_support() {
    // Disjoint supports must be coprime; sharing any variable means not coprime.
    assert!(mono(&[0, 0, 0]).is_coprime(&mono(&[1, 2, 3]))); // empty support
    assert!(mono(&[1, 2, 3]).is_coprime(&mono(&[0, 0, 0])));
    assert!(mono(&[3, 0, 0]).is_coprime(&mono(&[0, 0, 5])));
    assert!(!mono(&[1, 1, 0]).is_coprime(&mono(&[0, 1, 0])));
    assert!(!mono(&[2, 0, 0]).is_coprime(&mono(&[5, 0, 0]))); // same variable
}

// ── Order comparisons: spec-driven ────────────────────────────────────

#[test]
fn prop_cmp_equal_monomials() {
    // Same monomial compares Equal under any order.
    let a = mono(&[2, 1, 3]);
    let b = mono(&[2, 1, 3]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Equal);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::DegRevLex), Ordering::Equal);
}

#[test]
fn prop_lex_is_antisymmetric() {
    // For a != b under Lex: a<b iff b>a; never both.
    let a = mono(&[1, 2, 3]);
    let b = mono(&[2, 0, 0]);
    let ab = a.cmp_with_order(&b, MonomialOrder::Lex);
    let ba = b.cmp_with_order(&a, MonomialOrder::Lex);
    assert_ne!(ab, Ordering::Equal);
    assert_eq!(ab, ba.reverse(), "antisymmetric");
}

#[test]
fn prop_degrevlex_total_degree_dominates() {
    // Under DegRevLex, higher total degree always wins regardless of structure.
    // a has deg 1, b has deg 5; b should win.
    let a = mono(&[1, 0, 0]);
    let b = mono(&[0, 5, 0]);
    assert_eq!(
        a.cmp_with_order(&b, MonomialOrder::DegRevLex),
        Ordering::Less
    );
    assert_eq!(
        b.cmp_with_order(&a, MonomialOrder::DegRevLex),
        Ordering::Greater
    );
}

#[test]
fn prop_lex_first_index_dominates() {
    // Under Lex, only the FIRST differing index matters. x0 > x1^999.
    let a = mono(&[1, 0, 0]);
    let b = mono(&[0, 999, 0]);
    assert_eq!(
        a.cmp_with_order(&b, MonomialOrder::Lex),
        Ordering::Greater,
        "Lex: x0 > x1^999 because first nonzero index breaks tie"
    );
}

// ── MonomialRepr trait forwarding ───────────────────────────────────────

#[test]
fn prop_monomialrepr_to_dense_roundtrip() {
    use crate::ff::repr::MonomialRepr;
    // Trait method to_dense round-trips through from_exponents.
    let exps = vec![1u16, 2, 0, 3];
    let m = <Monomial as MonomialRepr>::from_exponents(exps.clone());
    let dense = <Monomial as MonomialRepr>::to_dense(&m);
    assert_eq!(dense, exps);
}

#[test]
fn prop_monomialrepr_for_each_nonzero() {
    use crate::ff::repr::MonomialRepr;
    // for_each_nonzero visits each nonzero (var, exp) pair.
    let m = mono(&[0, 3, 0, 5, 0]);
    let mut visited: Vec<(usize, u16)> = Vec::new();
    <Monomial as MonomialRepr>::for_each_nonzero(&m, |i, e| visited.push((i, e)));
    assert_eq!(visited, vec![(1, 3), (3, 5)]);
}

// ── Eq / Hash invariants ────────────────────────────────────────────────

#[test]
fn prop_eq_implies_hash() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    // Equal monomials must hash equally.
    let a = mono(&[2, 1, 3]);
    let b = Monomial::from_exponents(vec![2, 1, 3]);
    assert_eq!(a, b);
    let mut ha = DefaultHasher::new();
    let mut hb = DefaultHasher::new();
    a.hash(&mut ha);
    b.hash(&mut hb);
    assert_eq!(ha.finish(), hb.finish(), "Eq => Hash agreement");
}

// ── Overflow guard ──────────────────────────────────────────────────────

#[test]
#[should_panic(expected = "exponent overflow")]
fn prop_mul_u16_overflow_panics() {
    // u16 max is 65535; adding two near-max exponents must panic per doc:
    // "Multiplication uses `checked_add` and panics on overflow."
    let a = mono(&[60000, 0]);
    let b = mono(&[6000, 0]);
    let _ = a.mul(&b);
}

#[test]
#[should_panic(expected = "exponent overflow")]
fn prop_mul_assign_u16_overflow_panics() {
    let mut a = mono(&[60000, 0]);
    let b = mono(&[6000, 0]);
    a.mul_assign(&b);
}
