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
