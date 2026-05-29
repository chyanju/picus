use super::*;
use num_bigint::BigUint;

fn idx_term(coeff: u64, vars: &[(u32, u16)]) -> PolyTerm {
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: vars.to_vec(),
    }
}

#[test]
fn indexed_merge_like_terms() {
    let p = BigUint::from(101u32);
    // 2*x + 3*x → 5*x. Var index 0.
    let mut t = vec![idx_term(2, &[(0, 1)]), idx_term(3, &[(0, 1)])];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].coeff, BigUint::from(5u32));
    assert_eq!(t[0].vars, vec![(0, 1)]);
}

#[test]
fn indexed_cancel_to_empty() {
    let p = BigUint::from(101u32);
    // x + (p-1)x = 0 mod p
    let mut t = vec![idx_term(1, &[(0, 1)]), idx_term(100, &[(0, 1)])];
    normalize_term_list(&mut t, &p);
    assert!(t.is_empty());
}

#[test]
fn indexed_sort_within_term_then_merge() {
    let p = BigUint::from(101u32);
    // x*y vs y*x — both represented as `(0,1),(1,1)` after
    // intra-term sort; should merge into `2*x*y`.
    let mut t = vec![
        idx_term(1, &[(1, 1), (0, 1)]),
        idx_term(1, &[(0, 1), (1, 1)]),
    ];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].coeff, BigUint::from(2u32));
    assert_eq!(t[0].vars, vec![(0, 1), (1, 1)]);
}

#[test]
fn indexed_intra_term_exponent_merge() {
    let p = BigUint::from(101u32);
    // [(0,1), (0,1)] should collapse to [(0,2)] (x · x = x^2)
    let mut t = vec![idx_term(1, &[(0, 1), (0, 1)])];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].vars, vec![(0, 2)]);
}

#[test]
fn indexed_reduce_coeff_mod_prime() {
    let p = BigUint::from(7u32);
    let mut t = vec![idx_term(10, &[(0, 1)])];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].coeff, BigUint::from(3u32));
}

#[test]
fn indexed_distinct_degrees_kept_separate() {
    let p = BigUint::from(101u32);
    // x^2 and (p-1)*x — distinct monomials.
    let mut t = vec![idx_term(1, &[(0, 2)]), idx_term(100, &[(0, 1)])];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 2);
}

#[test]
fn indexed_intra_term_merge_then_compact_swap() {
    let p = BigUint::from(101u32);
    // Within one term: [(0,1), (0,1), (1,1)] → the two var-0 entries merge
    // to (0,2); the trailing distinct var-1 entry must be compacted forward
    // (the `read != write` swap), giving [(0,2), (1,1)] = x^2 * y.
    let mut t = vec![idx_term(1, &[(0, 1), (0, 1), (1, 1)])];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].coeff, BigUint::from(1u32));
    assert_eq!(t[0].vars, vec![(0, 2), (1, 1)]);
}

#[test]
fn indexed_drop_zero_coeff() {
    let p = BigUint::from(101u32);
    let mut t = vec![
        idx_term(0, &[(0, 1)]),
        idx_term(1, &[(1, 1)]),
        idx_term(0, &[(2, 1)]),
    ];
    normalize_term_list(&mut t, &p);
    assert_eq!(t.len(), 1);
    assert_eq!(t[0].vars, vec![(1, 1)]);
}
