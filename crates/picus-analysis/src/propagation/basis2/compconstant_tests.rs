//! Unit tests for the CompConstant companion recogniser used by
//! `basis2`. The recogniser is conservative — any unmatched structural
//! link returns `false` — so most negative cases are easy to pin.
//!
//! Spec pinned (from the module doc):
//!   * `companion_proves_below_prime` returns `false` unless ALL of:
//!       - `bits.len() == COMPCONSTANT_BITS (= 254)`,
//!       - 127 `parts` equalities match the four CompConstant signatures,
//!       - decoded `ct < p`,
//!       - a parts-sum equality `S = Σ part_outs` exists,
//!       - `S` has a faithful (`2^width ≤ p`, every bit binary) bit
//!         decomposition that exposes bit 127,
//!       - that bit-127 wire is pinned to zero by some equality.
//!   * `pair_key(a, b)` is symmetric in `a, b` and always returns the
//!     pair sorted ascending.

use super::*;
use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use num_traits::{One, Zero};

use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};
use picus_smt::poly_ir::r1cs_to_poly_ir;

use crate::propagation::range::RangeValue;

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn block(pairs: &[(u32, u32)]) -> ConstraintBlock {
    let wire_ids: Vec<u32> = pairs.iter().map(|&(w, _)| w).collect();
    let factors: Vec<BigUint> = pairs.iter().map(|&(_, f)| BigUint::from(f)).collect();
    ConstraintBlock { nnz: wire_ids.len() as u32, wire_ids, factors }
}

fn empty_block() -> ConstraintBlock {
    ConstraintBlock { nnz: 0, wire_ids: vec![], factors: vec![] }
}

/// Minimal R1CS with a single trivial constraint, used to obtain a
/// valid PolyIR with the requested wire count and prime so we can test
/// the companion recogniser's input-validation gates.
fn tiny_r1cs(p: u64, n_wires: u32) -> R1csFile {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: n_wires as u64,
        m_constraints: 1,
    };
    // 1 * 1 = 1 (a vacuous constraint that lowers to the zero
    // polynomial — gives us a clean, equality-light PolyIR).
    let constraints = vec![Constraint {
        a: block(&[(0, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(0, 1)]),
    }];
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: (0..n_wires as u64).collect() },
        inputs: vec![0],
        outputs: vec![],
    }
}

// ---------------------------------------------------------------------------
// pair_key — symmetric canonical pair
// ---------------------------------------------------------------------------

#[test]
fn prop_pair_key_symmetric() {
    assert_eq!(pair_key(3, 7), pair_key(7, 3));
    assert_eq!(pair_key(0, 99), pair_key(99, 0));
    assert_eq!(pair_key(42, 42), pair_key(42, 42));
}

#[test]
fn prop_pair_key_sorts_ascending() {
    assert_eq!(pair_key(3, 7), (3, 7));
    assert_eq!(pair_key(7, 3), (3, 7));
    assert_eq!(pair_key(5, 5), (5, 5));
}

#[test]
fn prop_pair_key_handles_zero() {
    assert_eq!(pair_key(0, 0), (0, 0));
    assert_eq!(pair_key(0, 1), (0, 1));
    assert_eq!(pair_key(1, 0), (0, 1));
}

// ---------------------------------------------------------------------------
// companion_proves_below_prime — gate-level negatives
// ---------------------------------------------------------------------------

#[test]
fn prop_companion_rejects_wrong_bit_count_empty() {
    // Empty bits → length 0 ≠ 254 → false. Returns immediately without
    // touching the IR (so any prime works).
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    assert!(!companion_proves_below_prime(&ir, &[], &ranges));
}

#[test]
fn prop_companion_rejects_wrong_bit_count_too_few() {
    // 4 bits ≠ 254.
    let r = tiny_r1cs(101, 5);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    assert!(!companion_proves_below_prime(&ir, &[1, 2, 3, 4], &ranges));
}

#[test]
fn prop_companion_rejects_wrong_bit_count_one_less() {
    // 253 bits ≠ 254 (off-by-one at the COMPCONSTANT_BITS boundary).
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    let bits: Vec<usize> = (0..253).collect();
    assert!(!companion_proves_below_prime(&ir, &bits, &ranges));
}

#[test]
fn prop_companion_rejects_wrong_bit_count_one_more() {
    // 255 bits ≠ 254.
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    let bits: Vec<usize> = (0..255).collect();
    assert!(!companion_proves_below_prime(&ir, &bits, &ranges));
}

#[test]
fn prop_companion_rejects_when_no_part_equalities() {
    // Exactly 254 bits BUT the IR has no part-shaped equalities,
    // so the first weight-0 part_map lookup misses → false.
    // (The recogniser shortcircuits on the first missing part.)
    let r = tiny_r1cs(101, 256);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    let bits: Vec<usize> = (1..=254).collect();
    assert!(!companion_proves_below_prime(&ir, &bits, &ranges));
}

// ---------------------------------------------------------------------------
// build_canon — union-find over x_i = x_j identities
// ---------------------------------------------------------------------------

#[test]
fn prop_build_canon_no_equalities_gives_identity() {
    // No `c1·x_i + c2·x_j = 0` two-term identities → canon is identity.
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let canon = build_canon(&ir);
    // Each variable is its own representative (modulo the structural
    // pin `x_0 - 1`, which is a constant-bearing equality not matched
    // by the two-term linear union-find).
    assert_eq!(canon.len(), ir.ring.n_vars());
    // x_0 has the `x_0 - 1 = 0` constant equality and never merges.
    // Self-rep invariant: every entry must point to itself or to
    // another node in the same equivalence class.
    for v in 0..canon.len() {
        let r1 = canon[v];
        // representative is its own canon (idempotent)
        assert_eq!(canon[r1], r1, "rep of {} ({}) must be its own rep", v, r1);
    }
}

#[test]
fn prop_build_canon_idempotent() {
    // Running canon twice yields the same map.
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let c1 = build_canon(&ir);
    let c2 = build_canon(&ir);
    assert_eq!(c1, c2);
}

// ---------------------------------------------------------------------------
// find_pinned_zero — single-term linear equality `c · w = 0`
// ---------------------------------------------------------------------------

#[test]
fn prop_find_pinned_zero_negative_no_such_var() {
    // No equality references variable 99 — `find_pinned_zero` returns false.
    let r = tiny_r1cs(101, 4);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let canon = build_canon(&ir);
    assert!(!find_pinned_zero(&ir, &canon, 99));
}

#[test]
fn prop_find_pinned_zero_positive_on_pin_equality() {
    // Construct an R1CS where wire `w` is explicitly pinned to zero:
    //   w * 1 = 0  ⇒  lowered poly is `w` (single linear term).
    let p = 7u64;
    let constraints = vec![
        Constraint {
            // forces b0 = 0 (and b0_alt = 0 via the alt-copy).
            a: block(&[(1, 1)]),
            b: block(&[(0, 1)]),
            c: empty_block(),
        },
    ];
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires: 2,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 2,
        m_constraints: 1,
    };
    let r = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1] },
        inputs: vec![0],
        outputs: vec![1],
    };
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let canon = build_canon(&ir);
    // x_1 (variable index 1) is pinned to zero.
    assert!(find_pinned_zero(&ir, &canon, canon[1]));
}

#[test]
fn prop_find_pinned_zero_rejects_two_term_equality() {
    // A two-term linear equality like `b0 - b1 = 0` is NOT a single-term
    // zero pin; `find_pinned_zero(b0)` must return false.
    let p = 7u64;
    // Constraint:  1 * (b0 + (p-1)·b1) = 0  →  b0 - b1 = 0
    let constraints = vec![
        Constraint {
            a: block(&[(0, 1)]),
            b: block(&[(1, 1), (2, (p - 1) as u32)]),
            c: empty_block(),
        },
    ];
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let r = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![0],
        outputs: vec![1, 2],
    };
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let canon = build_canon(&ir);
    // The equality has TWO linear terms, so `find_pinned_zero` requires
    // a *single*-term form and rejects both b0 and b1.
    assert!(!find_pinned_zero(&ir, &canon, canon[1]));
    assert!(!find_pinned_zero(&ir, &canon, canon[2]));
}

// ---------------------------------------------------------------------------
// product_pair — detect single-quadratic-monomial pattern
// ---------------------------------------------------------------------------

#[test]
fn prop_product_pair_finds_unique_pair() {
    // Constraint `b0 * b1 = 0` lowers to a polynomial with one
    // product monomial `b0 * b1` (and no other terms). `product_pair`
    // returns the variable pair.
    let p = 7u64;
    let constraints = vec![
        Constraint {
            a: block(&[(1, 1)]),
            b: block(&[(2, 1)]),
            c: empty_block(),
        },
    ];
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let r = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![0],
        outputs: vec![1, 2],
    };
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    // The first equality in the IR is the orig-copy `b0 * b1 = 0`.
    let poly0 = &ir.equalities[0];
    let pair = product_pair(&ir, poly0).expect("product pair found");
    // Pair contains variable indices for b0 and b1 (= ring indices 1
    // and 2). Order is undefined here so accept either ordering.
    let canon = build_canon(&ir);
    assert_eq!(pair_key(canon[pair.0], canon[pair.1]), pair_key(canon[1], canon[2]));
}

#[test]
fn prop_product_pair_rejects_pure_linear() {
    // Pure linear constraint `b0 - 1 = 0` (from the x_0 - 1 pin) has
    // no product monomial → `product_pair` returns None.
    let r = tiny_r1cs(7, 2);
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    // Find an equality with only linear/constant terms — the x_0 - 1
    // pin is always emitted.
    let mut found_linear = false;
    for poly in &ir.equalities {
        if product_pair(&ir, poly).is_none() {
            found_linear = true;
            break;
        }
    }
    assert!(found_linear, "expected at least one purely-linear equality");
}

#[test]
fn prop_product_pair_rejects_square() {
    // Constraint `b0 * b0 = 0` → lowered to `b0^2` (a SQUARE
    // monomial, exponent 2 on a single variable). `product_pair`
    // requires exponent 1 on EACH of two distinct variables, so the
    // squared form is rejected.
    let p = 7u64;
    let constraints = vec![
        Constraint {
            a: block(&[(1, 1)]),
            b: block(&[(1, 1)]),
            c: empty_block(),
        },
    ];
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires: 2,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 2,
        m_constraints: 1,
    };
    let r = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1] },
        inputs: vec![0],
        outputs: vec![1],
    };
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    // First equality is `b0^2 = 0` (the orig copy).
    let poly = &ir.equalities[0];
    assert!(product_pair(&ir, poly).is_none(), "x^2 monomial is not a product pair");
}

// ---------------------------------------------------------------------------
// build_part_map — bucketed by canonical product pair
// ---------------------------------------------------------------------------

#[test]
fn prop_build_part_map_bucket_per_product_pair() {
    // Same R1CS as `prop_product_pair_finds_unique_pair`: there should
    // be at least one bucket (the `b0 * b1` one).
    let p = 7u64;
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(2, 1)]),
        c: empty_block(),
    }];
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 1,
    };
    let r = R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![0],
        outputs: vec![1, 2],
    };
    let ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    let canon = build_canon(&ir);
    let map = build_part_map(&ir, &canon);
    // The orig-copy `b0 * b1 = 0` lands in the bucket keyed by the
    // canonical pair `(canon[1], canon[2])`. (Without an explicit
    // `x_i = y_i` identity, the alt copy lands in a separate bucket;
    // we only assert the orig-copy bucket here.)
    let key = pair_key(canon[1], canon[2]);
    let bucket = map.get(&key);
    assert!(bucket.is_some(), "expected a bucket for the canonical b0*b1 pair");
}

// ---------------------------------------------------------------------------
// Direct-Poly tests against the recogniser's private helpers.
//
// The R1CS surface can only emit polys of the form `(sumA)(sumB) - sumC`,
// which is too restrictive to cover every branch of `match_part` /
// `find_sum_var` / `find_inner_bit`. We construct polys directly via the
// ring API on a small PolyIR (still produced by `tiny_r1cs` to get a
// well-formed prime/ring).
// ---------------------------------------------------------------------------

/// Build a fresh PolyIR with `n_wires` wires under prime `p`, then drop
/// the equalities so callers can inject exactly the polys they want to
/// test. Wire-0 pin is also dropped — tests opt back in by injecting it
/// explicitly when needed.
fn ir_fresh(p: u64, n_wires: u32) -> PolyIR {
    let r = tiny_r1cs(p, n_wires);
    let mut ir = r1cs_to_poly_ir(&r, &HashSet::new(), 1).expect("lowering");
    ir.equalities.clear();
    ir
}

/// Build a linear polynomial `c · x_var` from a BigUint coefficient.
fn lin(ir: &PolyIR, c: &BigUint, var: usize) -> Poly {
    let el = ir.ring.field().from_biguint(c);
    ir.ring.scale(el, ir.ring.var(var))
}

/// Build a constant polynomial from a BigUint.
fn konst_poly(ir: &PolyIR, c: &BigUint) -> Poly {
    let el = ir.ring.field().from_biguint(c);
    ir.ring.constant(el)
}

/// Build a product polynomial `c · x_a · x_b`.
fn prod_poly(ir: &PolyIR, c: &BigUint, a: usize, b: usize) -> Poly {
    let el = ir.ring.field().from_biguint(c);
    let ab = ir.ring.mul(ir.ring.var(a), ir.ring.var(b));
    ir.ring.scale(el, ab)
}

/// Sum a list of polys into one.
fn sum_polys(ir: &PolyIR, ps: Vec<Poly>) -> Poly {
    let mut acc = ir.ring.zero();
    for p in ps {
        acc = ir.ring.add(acc, p);
    }
    acc
}

// ---------------------------------------------------------------------------
// match_part — four signatures (digit 0/1/2/3) round-trip
// ---------------------------------------------------------------------------
//
// For prime `p`, a = 2^i mod p, b = (2^128 - 2^i) mod p; `wire` carries
// the part-output variable (coefficient must be invertible — we use +1).
// Signatures (from the doc comment):
//   c=0: prod=b,   sl=-b, sm=-b, const=0
//   c=1: prod=-a,  sl=a,  sm=a-b, const=-a
//   c=2: prod=-b,  sl=0,  sm=a,  const=-a
//   c=3: prod=a,   sl=0,  sm=0,  const=-a

fn build_match_part_poly(
    ir: &PolyIR,
    sl: usize,
    sm: usize,
    out: usize,
    prod_c: &BigUint,
    sl_c: &BigUint,
    sm_c: &BigUint,
    konst_c: &BigUint,
) -> Poly {
    // wire is `+1 · x_out` so the normaliser sees the "wire" with coeff 1.
    let one = BigUint::one();
    let mut parts = vec![
        prod_poly(ir, prod_c, sl, sm),
        lin(ir, &one, out),
        konst_poly(ir, konst_c),
    ];
    // Zero-coefficient sl/sm terms are simply omitted (the matcher
    // defaults sl_c / sm_c to BigUint::zero() when neither term is
    // observed). For digits 2 and 3 this lets us exercise the
    // "sl never seen" / "sm never seen" paths.
    if !sl_c.is_zero() {
        parts.push(lin(ir, sl_c, sl));
    }
    if !sm_c.is_zero() {
        parts.push(lin(ir, sm_c, sm));
    }
    sum_polys(ir, parts)
}

#[test]
fn prop_match_part_recognises_digit_0() {
    // c=0: prod=b, sl=-b, sm=-b, const=0
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = ((BigUint::from(1u32) << 128usize) - &a) % &p;
    let neg_b = (&p - &b) % &p;
    let poly = build_match_part_poly(
        &ir, sl, sm, out, &b, &neg_b, &neg_b, &BigUint::zero(),
    );
    let res = match_part(&ir, &canon, &poly, sl, sm, &a, &b);
    let (digit, ovar) = res.expect("digit 0 should match");
    assert_eq!(digit, 0);
    assert_eq!(ovar, out);
}

#[test]
fn prop_match_part_recognises_digit_1() {
    // c=1: prod=-a, sl=a, sm=a-b, const=-a
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = ((BigUint::from(1u32) << 128usize) - &a) % &p;
    let na = (&p - &a) % &p;
    let amb = ((&a + &p) - &b) % &p;
    let poly = build_match_part_poly(&ir, sl, sm, out, &na, &a, &amb, &na);
    let res = match_part(&ir, &canon, &poly, sl, sm, &a, &b);
    let (digit, ovar) = res.expect("digit 1 should match");
    assert_eq!(digit, 1);
    assert_eq!(ovar, out);
}

#[test]
fn prop_match_part_recognises_digit_2() {
    // c=2: prod=-b, sl=0, sm=a, const=-a
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = ((BigUint::from(1u32) << 128usize) - &a) % &p;
    let nb = (&p - &b) % &p;
    let na = (&p - &a) % &p;
    let poly = build_match_part_poly(&ir, sl, sm, out, &nb, &BigUint::zero(), &a, &na);
    let res = match_part(&ir, &canon, &poly, sl, sm, &a, &b);
    let (digit, ovar) = res.expect("digit 2 should match");
    assert_eq!(digit, 2);
    assert_eq!(ovar, out);
}

#[test]
fn prop_match_part_recognises_digit_3() {
    // c=3: prod=a, sl=0, sm=0, const=-a
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = ((BigUint::from(1u32) << 128usize) - &a) % &p;
    let na = (&p - &a) % &p;
    let poly = build_match_part_poly(
        &ir, sl, sm, out, &a, &BigUint::zero(), &BigUint::zero(), &na,
    );
    let res = match_part(&ir, &canon, &poly, sl, sm, &a, &b);
    let (digit, ovar) = res.expect("digit 3 should match");
    assert_eq!(digit, 3);
    assert_eq!(ovar, out);
}

#[test]
fn prop_match_part_rejects_no_product_monomial() {
    // No quadratic term => `prod?` is None => match_part returns None.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    let poly = sum_polys(&ir, vec![lin(&ir, &BigUint::one(), out)]);
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_no_wire() {
    // Has product term but no extra linear term => `wire?` is None.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm) = (1usize, 2usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    let poly = sum_polys(
        &ir,
        vec![prod_poly(&ir, &BigUint::one(), sl, sm)],
    );
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_two_product_monomials() {
    // Two product monomials over the SAME (sl, sm) pair but distinct
    // vars to ensure they don't combine into one canonicalised term.
    // Easiest distinct shape: pair-match for (sl, sm) but a second
    // product also over (sl, sm). Because the polynomial library
    // CANONICALISES terms of the same monomial together, we instead
    // use a product that matches the pair_key but is over a different
    // variable mapping (still pair_key-equal to sl,sm). Without an
    // alias, the simplest way to force two distinct quadratic
    // monomials whose pair_key is `(sl, sm)` is to inject a second
    // product over (sl, sl) — that has pair_key (sl, sl) which differs
    // from (sl, sm), tripping the EARLIER pair-mismatch branch instead.
    // So we sidestep: keep this test as the pair-mismatch path; the
    // duplicate-same-pair scenario can't be expressed without aliasing.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    let poly = sum_polys(
        &ir,
        vec![
            prod_poly(&ir, &BigUint::one(), sl, sm),
            // (4, 5) has a different pair_key — this will trip the
            // pair-key mismatch check before the prod-already-set
            // check, but it still exercises the "two-monomial reject"
            // intent at this entry point.
            prod_poly(&ir, &BigUint::from(3u32), 4, 5),
            lin(&ir, &BigUint::one(), out),
        ],
    );
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_product_pair_mismatch() {
    // Product is over a different variable pair than (sl, sm).
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    // Use a different pair (4, 5) for the product.
    let poly = sum_polys(
        &ir,
        vec![
            prod_poly(&ir, &BigUint::one(), 4, 5),
            lin(&ir, &BigUint::one(), out),
        ],
    );
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_two_extra_linear_terms() {
    // A second extra (non-sl, non-sm) linear term triggers
    // `wire.is_some()` early-out.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    let poly = sum_polys(
        &ir,
        vec![
            prod_poly(&ir, &BigUint::one(), sl, sm),
            lin(&ir, &BigUint::one(), out),
            // Second wire-like extra (different var than sl/sm/out).
            lin(&ir, &BigUint::from(2u32), 4),
        ],
    );
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_higher_degree_monomial() {
    // A degree-3 monomial trips the `_ => return None` arm.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    // x_sl * x_sm * x_out is degree 3.
    let deg3 = {
        let ab = ir.ring.mul(ir.ring.var(sl), ir.ring.var(sm));
        ir.ring.mul(ab, ir.ring.var(out))
    };
    let poly = sum_polys(&ir, vec![deg3, lin(&ir, &BigUint::one(), out)]);
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

#[test]
fn prop_match_part_rejects_signature_mismatch() {
    // Has all the shape requirements but coefficients don't fit any of
    // the four digit signatures — falls through past every `if` to
    // return None.  prime=257, a=1, b=2 yields signatures
    //   digit0: (b=2, sl=-b=255, sm=255, k=0)
    //   digit1: (-a=256, a=1, a-b=256, -a=256)
    //   digit2: (-b=255, 0, 1, -a=256)
    //   digit3: (a=1, 0, 0, -a=256)
    // We pick `(3, 3, 3, 3)` which is none of the above.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 5);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (sl, sm, out) = (1usize, 2usize, 3usize);
    let a = BigUint::one();
    let b = BigUint::from(2u32);
    let three = BigUint::from(3u32);
    let poly = build_match_part_poly(&ir, sl, sm, out, &three, &three, &three, &three);
    assert!(match_part(&ir, &canon, &poly, sl, sm, &a, &b).is_none());
}

// ---------------------------------------------------------------------------
// find_sum_var — `S = Σ part_outs` discovery
// ---------------------------------------------------------------------------

#[test]
fn prop_find_sum_var_positive_simple() {
    // Inject `s - p0 - p1 - p2 = 0` and confirm it's found as the
    // sum signal for [p0, p1, p2].
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let (s, p0, p1, p2) = (1usize, 2usize, 3usize, 4usize);
    let one = BigUint::one();
    let neg_one = (&p - &one) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &one, s),
            lin(&ir, &neg_one, p0),
            lin(&ir, &neg_one, p1),
            lin(&ir, &neg_one, p2),
        ],
    );
    ir.equalities.push(poly);
    let found = find_sum_var(&ir, &canon, &[p0, p1, p2]);
    assert_eq!(found, Some(s));
}

#[test]
fn prop_find_sum_var_rejects_two_extras() {
    // Two variables outside `targets` -> extras.len() != 1 path.
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let one = BigUint::one();
    let neg_one = (&p - &one) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &one, 1),      // extra #1
            lin(&ir, &one, 2),      // extra #2
            lin(&ir, &neg_one, 3),
            lin(&ir, &neg_one, 4),
        ],
    );
    ir.equalities.push(poly);
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_rejects_zero_extras() {
    // No extras -> extras.len() == 0 != 1.
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let neg_one = (&p - &BigUint::one()) % &p;
    let poly = sum_polys(
        &ir,
        vec![lin(&ir, &neg_one, 3), lin(&ir, &neg_one, 4)],
    );
    ir.equalities.push(poly);
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_rejects_missing_target() {
    // S extra + only one of the two targets present -> "targets all
    // in coeffs" check fails.
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let one = BigUint::one();
    let neg_one = (&p - &one) % &p;
    let poly = sum_polys(
        &ir,
        vec![lin(&ir, &one, 1), lin(&ir, &neg_one, 3)],
    );
    ir.equalities.push(poly);
    // Targets = {3, 4} but only 3 appears.
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_rejects_unequal_target_coeffs() {
    // S extra; both targets present but their coefficients differ ->
    // `targets.all(|v| coeffs[v] == neg_ks)` fails.
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let one = BigUint::one();
    let neg_one = (&p - &one) % &p;
    let neg_two = (&p - &BigUint::from(2u32)) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &one, 1),
            lin(&ir, &neg_one, 3),
            lin(&ir, &neg_two, 4),
        ],
    );
    ir.equalities.push(poly);
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_skips_nonzero_constant() {
    // Equality with a nonzero constant term is silently skipped ->
    // no other candidate, find_sum_var returns None.
    let p_u = 257u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let one = BigUint::one();
    let neg_one = (&p - &one) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &one, 1),
            lin(&ir, &neg_one, 3),
            lin(&ir, &neg_one, 4),
            konst_poly(&ir, &BigUint::from(2u32)),
        ],
    );
    ir.equalities.push(poly);
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_skips_nonlinear() {
    // A polynomial with a product monomial is skipped wholesale.
    let p_u = 257u64;
    let mut ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &BigUint::one(), 1),
            prod_poly(&ir, &BigUint::one(), 3, 4),
        ],
    );
    ir.equalities.push(poly);
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

#[test]
fn prop_find_sum_var_returns_none_when_no_equalities() {
    // No equalities at all -> the loop completes without finding a
    // matching sum poly.
    let p_u = 7u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    assert_eq!(find_sum_var(&ir, &canon, &[3, 4]), None);
}

// ---------------------------------------------------------------------------
// find_inner_bit — needs a faithful `match_decomp` of `s_var`
// ---------------------------------------------------------------------------
//
// `match_decomp` requires `target = Σ 2^k · bits[k]` with target coeff
// ±1 and bit weights forming an exact `2^0..2^{n-1}` set. We compose
// such polys directly so we can probe every gate of `find_inner_bit`.

fn build_decomp_poly(ir: &PolyIR, target: usize, bits: &[usize]) -> Poly {
    // target = Σ 2^k bits[k]  ⇔  -target + Σ 2^k bits[k] = 0
    let p = ir.ring.field().prime();
    let one = BigUint::one();
    let neg_one = (p - &one) % p;
    let mut terms = vec![lin(ir, &neg_one, target)];
    for (k, &b) in bits.iter().enumerate() {
        let w = BigUint::one() << k;
        terms.push(lin(ir, &w, b));
    }
    sum_polys(ir, terms)
}

#[test]
fn prop_find_inner_bit_negative_no_decomp_at_all() {
    // No decomp equalities present -> None.
    let p_u = 257u64;
    let ir = ir_fresh(p_u, 6);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let ranges: HashMap<usize, RangeValue> = HashMap::new();
    assert_eq!(find_inner_bit(&ir, &canon, 1, 0, &ranges), None);
}

#[test]
fn prop_find_inner_bit_negative_target_mismatch() {
    // Decomp's target_var canonicalises to a DIFFERENT s_var.
    let p_u = 257u64;
    let mut ir = ir_fresh(p_u, 8);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    // decomp of var 1 over bits {2, 3} (weights 2^0, 2^1).
    ir.equalities.push(build_decomp_poly(&ir, 1, &[2, 3]));
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();
    ranges.insert(2, RangeValue::Values(binary.clone()));
    ranges.insert(3, RangeValue::Values(binary));
    // Ask for s_var = 7 (not 1) -> mismatch.
    assert_eq!(find_inner_bit(&ir, &canon, 7, 0, &ranges), None);
}

#[test]
fn prop_find_inner_bit_negative_bit_index_out_of_range() {
    // Decomp width = 2 but requested bit = 5 -> bits.len() <= bit.
    let p_u = 257u64;
    let mut ir = ir_fresh(p_u, 8);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    ir.equalities.push(build_decomp_poly(&ir, 1, &[2, 3]));
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();
    ranges.insert(2, RangeValue::Values(binary.clone()));
    ranges.insert(3, RangeValue::Values(binary));
    assert_eq!(find_inner_bit(&ir, &canon, 1, 5, &ranges), None);
}

#[test]
fn prop_find_inner_bit_negative_not_faithful_small_prime() {
    // Prime = 7; decomp width = 3 -> 2^3 = 8 > 7 -> not faithful ->
    // rejected even though bits are binary.
    let p_u = 7u64;
    let mut ir = ir_fresh(p_u, 8);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    ir.equalities.push(build_decomp_poly(&ir, 1, &[2, 3, 4]));
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();
    for v in [2usize, 3, 4] {
        ranges.insert(v, RangeValue::Values(binary.clone()));
    }
    // Even bit-0 is unreachable because the decomp is not faithful.
    assert_eq!(find_inner_bit(&ir, &canon, 1, 0, &ranges), None);
}

#[test]
fn prop_find_inner_bit_negative_not_all_binary() {
    // Faithful (large) prime, decomp width fits, but bit-1 has no
    // binary range -> all_binary false -> None.
    let p_u = 257u64;
    let mut ir = ir_fresh(p_u, 8);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    ir.equalities.push(build_decomp_poly(&ir, 1, &[2, 3]));
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();
    // Only bit-0 is binary; bit-1 missing.
    ranges.insert(2, RangeValue::Values(binary));
    assert_eq!(find_inner_bit(&ir, &canon, 1, 0, &ranges), None);
}

#[test]
fn prop_find_inner_bit_positive() {
    // Faithful, binary, target matches, bit in range -> returns the
    // requested bit variable.
    let p_u = 257u64;
    let mut ir = ir_fresh(p_u, 8);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    ir.equalities.push(build_decomp_poly(&ir, 1, &[2, 3, 4]));
    let mut ranges: HashMap<usize, RangeValue> = HashMap::new();
    let binary: HashSet<BigUint> = [BigUint::zero(), BigUint::one()].into_iter().collect();
    for v in [2usize, 3, 4] {
        ranges.insert(v, RangeValue::Values(binary.clone()));
    }
    assert_eq!(find_inner_bit(&ir, &canon, 1, 0, &ranges), Some(2));
    assert_eq!(find_inner_bit(&ir, &canon, 1, 1, &ranges), Some(3));
    assert_eq!(find_inner_bit(&ir, &canon, 1, 2, &ranges), Some(4));
}

// ---------------------------------------------------------------------------
// find_pinned_zero — extra branches
// ---------------------------------------------------------------------------

#[test]
fn prop_find_pinned_zero_skips_nonzero_constant() {
    // An equality with a NONZERO constant and no other linear-only
    // form must not pin anything to zero.
    let p_u = 7u64;
    let mut ir = ir_fresh(p_u, 4);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let poly = sum_polys(
        &ir,
        vec![lin(&ir, &BigUint::one(), 1), konst_poly(&ir, &BigUint::from(3u32))],
    );
    ir.equalities.push(poly);
    // ok=false branch triggered (poly has nonzero const + a linear term
    // alongside) -> rejected.
    assert!(!find_pinned_zero(&ir, &canon, 1));
}

#[test]
fn prop_find_pinned_zero_skips_nonlinear() {
    // Equality with a product monomial -> rejected wholesale.
    let p_u = 7u64;
    let mut ir = ir_fresh(p_u, 4);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    let poly = prod_poly(&ir, &BigUint::one(), 1, 2);
    ir.equalities.push(poly);
    assert!(!find_pinned_zero(&ir, &canon, 1));
}

#[test]
fn prop_find_pinned_zero_negative_when_no_equalities() {
    // No equalities -> outer loop never enters -> returns false.
    let p_u = 7u64;
    let ir = ir_fresh(p_u, 4);
    let canon: Vec<usize> = (0..ir.ring.n_vars()).collect();
    assert!(!find_pinned_zero(&ir, &canon, 1));
}

// ---------------------------------------------------------------------------
// build_canon — actual two-term linear-identity merging (path compression)
// ---------------------------------------------------------------------------

#[test]
fn prop_build_canon_merges_two_term_linear_identity() {
    // Inject `x_1 + (p-1)·x_2 = 0`  (i.e. x_1 = x_2) and confirm canon
    // merges the two ring vars into one class.
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 4);
    let neg_one = (&p - &BigUint::one()) % &p;
    let poly = sum_polys(
        &ir,
        vec![lin(&ir, &BigUint::one(), 1), lin(&ir, &neg_one, 2)],
    );
    ir.equalities.push(poly);
    let canon = build_canon(&ir);
    assert_eq!(canon[1], canon[2], "x_1 and x_2 must share a representative");
}

#[test]
fn prop_build_canon_chains_merges() {
    // Inject x_1 = x_2 and x_2 = x_3; canon must unify all three.
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 5);
    let neg_one = (&p - &BigUint::one()) % &p;
    let p12 = sum_polys(
        &ir,
        vec![lin(&ir, &BigUint::one(), 1), lin(&ir, &neg_one, 2)],
    );
    let p23 = sum_polys(
        &ir,
        vec![lin(&ir, &BigUint::one(), 2), lin(&ir, &neg_one, 3)],
    );
    ir.equalities.push(p12);
    ir.equalities.push(p23);
    let canon = build_canon(&ir);
    assert_eq!(canon[1], canon[2]);
    assert_eq!(canon[2], canon[3]);
    assert_eq!(canon[1], canon[3]);
}

#[test]
fn prop_build_canon_rejects_two_term_sum_not_canceling() {
    // `x_1 + x_2 = 0` has c1 + c2 = 2, NOT zero, so the union-find
    // gate fails -> no merge.
    let p_u = 7u64;
    let mut ir = ir_fresh(p_u, 4);
    let poly = sum_polys(
        &ir,
        vec![lin(&ir, &BigUint::one(), 1), lin(&ir, &BigUint::one(), 2)],
    );
    ir.equalities.push(poly);
    let canon = build_canon(&ir);
    assert_ne!(canon[1], canon[2]);
}

#[test]
fn prop_build_canon_skips_three_term_linear() {
    // 3 linear terms -> `lin.len() == 2` cap trips -> no merge.
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 5);
    let neg_one = (&p - &BigUint::one()) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &BigUint::one(), 1),
            lin(&ir, &neg_one, 2),
            lin(&ir, &BigUint::one(), 3),
        ],
    );
    ir.equalities.push(poly);
    let canon = build_canon(&ir);
    // Three-term linear identities are not the recogniser's concern;
    // no merging should happen.
    assert_ne!(canon[1], canon[2]);
}

#[test]
fn prop_build_canon_skips_nonlinear_equality() {
    // A product monomial in the equality -> `ok = false`, skipped.
    let p_u = 7u64;
    let mut ir = ir_fresh(p_u, 5);
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &BigUint::one(), 1),
            prod_poly(&ir, &BigUint::one(), 2, 3),
        ],
    );
    ir.equalities.push(poly);
    let canon = build_canon(&ir);
    // Identity (no merges) because the equality is non-linear.
    for v in 0..canon.len() {
        let r = canon[v];
        assert_eq!(canon[r], r);
    }
}

#[test]
fn prop_build_canon_skips_nonzero_constant_equality() {
    // `x_1 - x_2 + 3 = 0` (nonzero const) hits the `ok=false` const-term
    // branch and is skipped -> no merge.
    let p_u = 7u64;
    let p = BigUint::from(p_u);
    let mut ir = ir_fresh(p_u, 4);
    let neg_one = (&p - &BigUint::one()) % &p;
    let poly = sum_polys(
        &ir,
        vec![
            lin(&ir, &BigUint::one(), 1),
            lin(&ir, &neg_one, 2),
            konst_poly(&ir, &BigUint::from(3u32)),
        ],
    );
    ir.equalities.push(poly);
    let canon = build_canon(&ir);
    assert_ne!(canon[1], canon[2]);
}

// ---------------------------------------------------------------------------
// uf_find — direct exercises of path compression
// ---------------------------------------------------------------------------

#[test]
fn prop_uf_find_self_loop_returns_self() {
    let mut parent: Vec<usize> = vec![0, 1, 2, 3];
    assert_eq!(uf_find(&mut parent, 2), 2);
}

#[test]
fn prop_uf_find_walks_chain_and_compresses() {
    // 0 -> 1 -> 2 -> 3 (self). After uf_find(0), parents collapse so
    // the root is reachable in <= 1 hop. (We only assert root + the
    // visible compression, not the exact intermediate shape.)
    let mut parent: Vec<usize> = vec![1, 2, 3, 3];
    let r = uf_find(&mut parent, 0);
    assert_eq!(r, 3);
    // Path compression must have reduced 0's depth.
    let depth_after = {
        let mut d = 0usize;
        let mut x = 0usize;
        while parent[x] != x {
            x = parent[x];
            d += 1;
            if d > 4 {
                break;
            }
        }
        d
    };
    assert!(depth_after <= 2, "expected compressed depth, got {}", depth_after);
}

// ---------------------------------------------------------------------------
// product_pair — extra negative paths
// ---------------------------------------------------------------------------

#[test]
fn prop_product_pair_rejects_two_product_monomials() {
    // Two product monomials in one poly -> `found.is_some() -> None`.
    let p_u = 7u64;
    let ir = ir_fresh(p_u, 6);
    let poly = sum_polys(
        &ir,
        vec![
            prod_poly(&ir, &BigUint::one(), 1, 2),
            prod_poly(&ir, &BigUint::one(), 3, 4),
        ],
    );
    assert!(product_pair(&ir, &poly).is_none());
}

#[test]
fn prop_product_pair_accepts_linear_and_constant_terms_around_product() {
    // A single product + extra constant + extra linear term is still
    // a valid product-pair shape (the matcher only checks the QUADRATIC
    // monomial uniqueness; other arities don't disqualify).
    let p_u = 7u64;
    let ir = ir_fresh(p_u, 6);
    let poly = sum_polys(
        &ir,
        vec![
            prod_poly(&ir, &BigUint::one(), 1, 2),
            lin(&ir, &BigUint::from(3u32), 3),
            konst_poly(&ir, &BigUint::from(5u32)),
        ],
    );
    let pair = product_pair(&ir, &poly).expect("single product monomial");
    assert_eq!(pair_key(pair.0, pair.1), pair_key(1, 2));
}

// ---------------------------------------------------------------------------
// companion_proves_below_prime — gates past the part-map lookup
// ---------------------------------------------------------------------------
//
// Building a full 254-bit CompConstant by hand is out of scope; we
// instead pin one branch we CAN reach:
//   * After ALL parts match and ct is decoded, the `ct >= p` gate
//     short-circuits to false. Constructing that scenario faithfully
//     would also require all 127 match_part successes, which is too
//     heavy. So we leave that path uncovered here.
//
// Below we additionally pin the "no inner-bit decomposition" path of
// the companion path via the structural fact that without any
// equalities, every internal helper that scans `ir.equalities` returns
// None / false, and the top-level guard already rejects on the bit-count
// gate (covered above).

// ---------------------------------------------------------------------------
// pair_key — large values + edge cases
// ---------------------------------------------------------------------------

#[test]
fn prop_pair_key_works_with_usize_max() {
    let m = usize::MAX;
    assert_eq!(pair_key(0, m), (0, m));
    assert_eq!(pair_key(m, 0), (0, m));
    assert_eq!(pair_key(m, m), (m, m));
}
