//! Tests for [`SparseMonomial`]. Pins the canonical form (only nonzero
//! `(var, exp)` pairs, ascending by var; equality/hash independent of
//! internal layout) and the divisibility / lcm / gcd / ordering laws every
//! monomial implementation has to obey. The dense [`Monomial`] is the
//! differential oracle via `repr_oracle`.

use crate::ff::sparse_monomial::SparseMonomial;
use crate::ff::monomial::MonomialOrder;
use crate::ff::repr::MonomialRepr;
use crate::ff::divmask::DivMask;
use std::cmp::Ordering;

// ── helpers ─────────────────────────────────────────────────────────────

fn sm(exps: Vec<u16>) -> SparseMonomial {
    <SparseMonomial as MonomialRepr>::from_exponents(exps)
}

// ── Canonical form: no zero exponents, ascending var ───────────────────

#[test]
fn prop_from_exponents_drops_zero_exponents() {
    // Exponent vector with zeros interspersed; internal layout must skip
    // the zeros (otherwise PartialEq/Hash break the "canonical" promise).
    let m = sm(vec![0, 3, 0, 2, 0]);
    // total_degree = sum of nonzero exponents = 5.
    assert_eq!(m.total_degree(), 5);
    assert_eq!(m.n_vars(), 5);
    // Exponents: var 1 -> 3, var 3 -> 2; all others zero.
    assert_eq!(m.exponent(0), 0);
    assert_eq!(m.exponent(1), 3);
    assert_eq!(m.exponent(2), 0);
    assert_eq!(m.exponent(3), 2);
    assert_eq!(m.exponent(4), 0);
}

#[test]
fn prop_eq_hash_canonical_across_zero_padding() {
    // The doc states equality/hash are sound regardless of internal layout
    // (canonical form ⇒ derived Eq/Hash work). Two monomials with the same
    // logical exponent vector must compare equal AND hash equal.
    use std::collections::HashSet;
    let a = sm(vec![0, 3, 0, 2, 0]);
    let b = sm(vec![0, 3, 0, 2, 0]);
    assert_eq!(a, b);
    let mut h: HashSet<SparseMonomial> = HashSet::new();
    h.insert(a);
    assert!(h.contains(&b), "eq monomials hash differently");
}

#[test]
fn prop_one_and_is_one() {
    // The constant `1` monomial has no nonzero exponents and total degree 0.
    let one = <SparseMonomial as MonomialRepr>::one(4);
    assert!(one.is_one());
    assert_eq!(one.total_degree(), 0);
    assert_eq!(one.n_vars(), 4);
    for i in 0..4 {
        assert_eq!(one.exponent(i), 0);
    }
    // from_exponents of an all-zero vector also yields `1`.
    let one2 = sm(vec![0, 0, 0, 0]);
    assert_eq!(one, one2);
}

#[test]
fn prop_single_var_factory() {
    // `single_var(n, v, e)` builds `x_v^e` over n vars.
    let m = <SparseMonomial as MonomialRepr>::single_var(5, 2, 4);
    assert_eq!(m.n_vars(), 5);
    assert_eq!(m.total_degree(), 4);
    assert_eq!(m.exponent(2), 4);
    for i in [0, 1, 3, 4] {
        assert_eq!(m.exponent(i), 0);
    }
    // `single_var` with exp 0 collapses to `one`.
    let m0 = <SparseMonomial as MonomialRepr>::single_var(3, 1, 0);
    assert!(m0.is_one());
}

#[test]
fn prop_to_dense_roundtrip() {
    // to_dense produces a full-length exponent vector; from_exponents on
    // that vector must round-trip.
    for exps in [
        vec![0u16, 3, 0, 2, 0],
        vec![1, 0, 1, 0, 1],
        vec![0, 0, 0, 0, 0],
        vec![5, 5, 5, 5, 5],
    ] {
        let m = sm(exps.clone());
        let dense = m.to_dense();
        assert_eq!(dense, exps);
        let m2 = sm(dense);
        assert_eq!(m, m2);
    }
}

#[test]
fn prop_for_each_nonzero_ascending_and_complete() {
    // Visits each nonzero pair exactly once, ascending by var. Matches
    // `exponent(v)` for the visited vars; zero for the rest.
    let m = sm(vec![0, 3, 0, 2, 7]);
    let mut visited: Vec<(usize, u16)> = Vec::new();
    m.for_each_nonzero(|v, e| visited.push((v, e)));
    assert_eq!(visited, vec![(1, 3), (3, 2), (4, 7)]);
    // Total degree matches the sum.
    let s: u32 = visited.iter().map(|(_, e)| *e as u32).sum();
    assert_eq!(s, m.total_degree());
}

// ── Multiplicative structure: mul / divides / div / lcm / gcd ──────────

#[test]
fn prop_mul_componentwise_sum() {
    // mul sums component-wise; total_deg of product = sum of components.
    let a = sm(vec![2, 0, 1, 0]);
    let b = sm(vec![1, 3, 0, 2]);
    let c = MonomialRepr::mul(&a, &b);
    assert_eq!(c.exponent(0), 3);
    assert_eq!(c.exponent(1), 3);
    assert_eq!(c.exponent(2), 1);
    assert_eq!(c.exponent(3), 2);
    assert_eq!(c.total_degree(), a.total_degree() + b.total_degree());
}

#[test]
fn prop_mul_by_one_identity() {
    // a * 1 = a, 1 * a = a.
    let a = sm(vec![2, 0, 1, 0]);
    let one = <SparseMonomial as MonomialRepr>::one(4);
    assert_eq!(MonomialRepr::mul(&a, &one), a);
    assert_eq!(MonomialRepr::mul(&one, &a), a);
}

#[test]
fn prop_mul_assign_matches_mul() {
    // mul_assign matches mul (it's documented as `*self = self * other`).
    let a = sm(vec![2, 0, 1, 0]);
    let b = sm(vec![1, 3, 0, 2]);
    let prod = MonomialRepr::mul(&a, &b);
    let mut a2 = a.clone();
    MonomialRepr::mul_assign(&mut a2, &b);
    assert_eq!(a2, prod);
}

#[test]
fn prop_divides_reflexive_and_one() {
    // a | a and 1 | a always.
    let a = sm(vec![2, 0, 1, 3]);
    assert!(MonomialRepr::divides(&a, &a));
    let one = <SparseMonomial as MonomialRepr>::one(4);
    assert!(MonomialRepr::divides(&one, &a));
    if !a.is_one() {
        assert!(!MonomialRepr::divides(&a, &one), "non-1 should not divide 1");
    }
}

#[test]
fn prop_divides_componentwise() {
    // a | b iff for every var v, a.exp(v) <= b.exp(v).
    let a = sm(vec![1, 0, 2]);
    let b = sm(vec![3, 1, 2]);
    let c = sm(vec![3, 1, 1]); // c.exp(2) < a.exp(2) so a should NOT divide c
    assert!(MonomialRepr::divides(&a, &b));
    assert!(!MonomialRepr::divides(&a, &c));
    // Componentwise greater also fails: b has total degree > a, not divisor.
    assert!(!MonomialRepr::divides(&b, &a));
}

#[test]
fn prop_div_inverse_of_mul() {
    // (a*b) / b == a (mul + div round trip).
    let a = sm(vec![2, 0, 1, 0]);
    let b = sm(vec![1, 3, 0, 2]);
    let ab = MonomialRepr::mul(&a, &b);
    let a2 = MonomialRepr::div(&ab, &b);
    assert_eq!(a, a2);
    let b2 = MonomialRepr::div(&ab, &a);
    assert_eq!(b, b2);
}

#[test]
fn prop_div_self_is_one() {
    // a / a = 1.
    let a = sm(vec![2, 0, 1, 3]);
    let q = MonomialRepr::div(&a, &a);
    assert!(q.is_one());
}

#[test]
fn prop_lcm_symmetric_and_componentwise_max() {
    // lcm(a, b) is componentwise max; lcm is symmetric.
    let a = sm(vec![2, 0, 1, 0]);
    let b = sm(vec![1, 3, 0, 2]);
    let l = MonomialRepr::lcm(&a, &b);
    assert_eq!(l.exponent(0), 2);
    assert_eq!(l.exponent(1), 3);
    assert_eq!(l.exponent(2), 1);
    assert_eq!(l.exponent(3), 2);
    let l2 = MonomialRepr::lcm(&b, &a);
    assert_eq!(l, l2);
    // a | lcm and b | lcm.
    assert!(MonomialRepr::divides(&a, &l));
    assert!(MonomialRepr::divides(&b, &l));
}

#[test]
fn prop_gcd_symmetric_and_componentwise_min() {
    // gcd(a, b) is componentwise min; gcd is symmetric.
    let a = sm(vec![2, 0, 1, 5]);
    let b = sm(vec![1, 3, 0, 2]);
    let g = MonomialRepr::gcd(&a, &b);
    assert_eq!(g.exponent(0), 1);
    assert_eq!(g.exponent(1), 0);
    assert_eq!(g.exponent(2), 0);
    assert_eq!(g.exponent(3), 2);
    let g2 = MonomialRepr::gcd(&b, &a);
    assert_eq!(g, g2);
    // gcd | a and gcd | b.
    assert!(MonomialRepr::divides(&g, &a));
    assert!(MonomialRepr::divides(&g, &b));
}

#[test]
fn prop_lcm_gcd_identity() {
    // For nonzero exponent vectors:  lcm * gcd  has total degree equal to
    // a.total_degree() + b.total_degree() (componentwise max+min = sum).
    let a = sm(vec![2, 1, 0, 5]);
    let b = sm(vec![1, 3, 4, 2]);
    let l = MonomialRepr::lcm(&a, &b);
    let g = MonomialRepr::gcd(&a, &b);
    assert_eq!(
        l.total_degree() + g.total_degree(),
        a.total_degree() + b.total_degree(),
        "lcm.deg + gcd.deg != a.deg + b.deg"
    );
}

#[test]
fn prop_is_coprime_matches_gcd() {
    // a, b coprime iff gcd(a, b) = 1 (no shared variable).
    let a = sm(vec![2, 0, 1, 0]);
    let b = sm(vec![0, 3, 0, 2]); // disjoint support from a
    assert!(MonomialRepr::is_coprime(&a, &b));
    assert!(MonomialRepr::gcd(&a, &b).is_one());
    let c = sm(vec![1, 3, 0, 2]); // shares var 0 with a
    assert!(!MonomialRepr::is_coprime(&a, &c));
    assert!(!MonomialRepr::gcd(&a, &c).is_one());
}

// ── Ordering: Lex and DegRevLex ─────────────────────────────────────────

#[test]
fn prop_lex_picks_lowest_differing_var() {
    // doc: "lowest variable where the exponents differ decides; higher
    // exponent there is the larger monomial".
    // x0 vs x1^5 — under Lex, var 0 differs first, x0 has nonzero there ⇒ x0 > x1^5.
    let a = sm(vec![1, 0]);
    let b = sm(vec![0, 5]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Greater);
    assert_eq!(b.cmp_with_order(&a, MonomialOrder::Lex), Ordering::Less);
    // x0^2 > x0 (higher exponent at lowest differing var).
    let a = sm(vec![2, 0]);
    let b = sm(vec![1, 0]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), Ordering::Greater);
}

#[test]
fn prop_lex_equal_monomials() {
    // a vs a — Equal under both orders.
    let a = sm(vec![2, 1, 0]);
    assert_eq!(a.cmp_with_order(&a, MonomialOrder::Lex), Ordering::Equal);
    assert_eq!(a.cmp_with_order(&a, MonomialOrder::DegRevLex), Ordering::Equal);
}

#[test]
fn prop_degrevlex_total_degree_dominates() {
    // higher total degree ⇒ larger, regardless of revlex tiebreak.
    let a = sm(vec![5, 0]); // deg 5
    let b = sm(vec![1, 1]); // deg 2
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::DegRevLex), Ordering::Greater);
}

#[test]
fn prop_degrevlex_revlex_tiebreak() {
    // Same total degree ⇒ revlex: SMALLER exponent at highest differing var = larger.
    // Compare x0^2*x1 vs x0*x1^2  (both deg 3).
    // Highest var = 1; a has exponent 1 there, b has exponent 2. a has the
    // smaller exponent at the highest differing var, so a > b under DegRevLex.
    let a = sm(vec![2, 1]);
    let b = sm(vec![1, 2]);
    assert_eq!(a.cmp_with_order(&b, MonomialOrder::DegRevLex), Ordering::Greater);
    assert_eq!(b.cmp_with_order(&a, MonomialOrder::DegRevLex), Ordering::Less);
}

#[test]
fn prop_degrevlex_one_is_smallest() {
    // The constant 1 has total degree 0; any nonzero monomial is larger.
    let one = <SparseMonomial as MonomialRepr>::one(3);
    let a = sm(vec![1, 0, 0]);
    assert_eq!(one.cmp_with_order(&a, MonomialOrder::DegRevLex), Ordering::Less);
    assert_eq!(a.cmp_with_order(&one, MonomialOrder::DegRevLex), Ordering::Greater);
    // Under Lex too: any monomial with a positive exponent at a lower var
    // dominates 1.
    assert_eq!(one.cmp_with_order(&a, MonomialOrder::Lex), Ordering::Less);
    assert_eq!(a.cmp_with_order(&one, MonomialOrder::Lex), Ordering::Greater);
}

#[test]
fn prop_lex_order_is_total_strict_antisymmetric() {
    // Sanity: for distinct monomials, ordering is antisymmetric under Lex.
    let xs: Vec<SparseMonomial> = vec![
        sm(vec![0, 0, 0]),
        sm(vec![1, 0, 0]),
        sm(vec![0, 1, 0]),
        sm(vec![0, 0, 1]),
        sm(vec![2, 1, 0]),
        sm(vec![1, 1, 1]),
    ];
    for i in 0..xs.len() {
        for j in 0..xs.len() {
            let cij = xs[i].cmp_with_order(&xs[j], MonomialOrder::Lex);
            let cji = xs[j].cmp_with_order(&xs[i], MonomialOrder::Lex);
            assert_eq!(cij.reverse(), cji, "Lex antisymmetry [{i},{j}]");
        }
    }
}

#[test]
fn prop_degrevlex_order_is_total_strict_antisymmetric() {
    let xs: Vec<SparseMonomial> = vec![
        sm(vec![0, 0, 0]),
        sm(vec![1, 0, 0]),
        sm(vec![0, 1, 0]),
        sm(vec![0, 0, 1]),
        sm(vec![2, 1, 0]),
        sm(vec![1, 1, 1]),
        sm(vec![3, 0, 0]),
        sm(vec![0, 2, 1]),
    ];
    for i in 0..xs.len() {
        for j in 0..xs.len() {
            let cij = xs[i].cmp_with_order(&xs[j], MonomialOrder::DegRevLex);
            let cji = xs[j].cmp_with_order(&xs[i], MonomialOrder::DegRevLex);
            assert_eq!(cij.reverse(), cji, "DegRevLex antisymmetry [{i},{j}]");
        }
    }
}

// ── DivMask soundness: never rejects a true divisor ─────────────────────

#[test]
fn prop_divmask_consistent_with_actual_divisibility() {
    // Soundness side of the DivMask filter: if a | b (truly divides), then
    // mask(a).divides_consistent_with(mask(b)) must hold. False positives
    // are fine (resolved by the full divides check) — false negatives are
    // SOUNDNESS bugs (a real divisor rejected).
    let pairs = [
        // (a, b) with a | b
        (sm(vec![0, 0, 0, 0]), sm(vec![3, 1, 2, 0])), // 1 divides anything
        (sm(vec![1, 0, 0, 0]), sm(vec![1, 0, 0, 0])),
        (sm(vec![1, 0, 0, 0]), sm(vec![2, 1, 0, 0])),
        (sm(vec![0, 1, 0, 0]), sm(vec![2, 1, 0, 0])),
        (sm(vec![1, 1, 0, 0]), sm(vec![2, 1, 1, 0])),
        (sm(vec![0, 0, 0, 1]), sm(vec![1, 1, 1, 1])),
    ];
    for (a, b) in &pairs {
        assert!(MonomialRepr::divides(a, b), "test setup: a should divide b");
        let ma = a.divmask();
        let mb = b.divmask();
        assert!(ma.divides_consistent_with(mb),
            "DivMask UNSOUNDLY rejected a true divisor (a={a:?} b={b:?})");
    }
}

#[test]
fn prop_divmask_one_is_empty_bits() {
    // The constant 1 has no nonzero exponents, so its DivMask has no bits.
    let one = <SparseMonomial as MonomialRepr>::one(4);
    assert_eq!(one.divmask(), DivMask::empty());
}

// ── Edge cases ──────────────────────────────────────────────────────────

#[test]
fn prop_zero_var_monomial() {
    // n_vars = 0 ⇒ only the constant 1 is representable.
    let one = <SparseMonomial as MonomialRepr>::one(0);
    assert!(one.is_one());
    assert_eq!(one.n_vars(), 0);
    assert_eq!(one.total_degree(), 0);
    // mul, lcm, gcd of 1 with itself: still 1.
    assert!(MonomialRepr::mul(&one, &one).is_one());
    assert!(MonomialRepr::lcm(&one, &one).is_one());
    assert!(MonomialRepr::gcd(&one, &one).is_one());
    assert!(MonomialRepr::divides(&one, &one));
    assert!(MonomialRepr::is_coprime(&one, &one));
}

#[test]
fn prop_high_exponents_safe_within_u16() {
    // Exponents stored as u16 — totals well below overflow are fine.
    let a = sm(vec![100, 200, 300]);
    assert_eq!(a.total_degree(), 600);
    let b = sm(vec![50, 50, 50]);
    let c = MonomialRepr::mul(&a, &b);
    assert_eq!(c.total_degree(), 750);
    assert_eq!(c.exponent(0), 150);
}
