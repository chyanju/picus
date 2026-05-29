//! Tests for the `propagation` module helpers: `mod_inverse` and
//! `wire_connectivity_score`.
//!
//! Spec invariants:
//!   - `mod_inverse(a, p)` returns the unique `x` in `[0, p)` with
//!     `a*x ≡ 1 (mod p)` when `gcd(a, p) = 1`, else `None`.
//!   - For a prime `p`, every non-zero `a` in `[1, p)` has an inverse.
//!   - `wire_connectivity_score` counts DISTINCT constraints touching
//!     each wire (one constraint contributes at most once per wire even
//!     if the wire appears in multiple monomials).

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::One;
use picus_core::ff::field::PrimeField;
use picus_core::poly::FfPolyRing;
use picus_smt::poly_ir::PolyIR;

use super::{mod_inverse, wire_connectivity_score};

// ───── mod_inverse ───────────────────────────────────────────────

#[test]
fn prop_mod_inverse_small_primes_round_trip() {
    // For every prime p in the small sweep and every non-zero a in
    // [1, p), the inverse must satisfy a * inv(a) ≡ 1 (mod p).
    for &p in &[2u64, 3, 5, 7, 11, 13, 101] {
        let pb = BigUint::from(p);
        for a in 1..p {
            let ab = BigUint::from(a);
            let inv = mod_inverse(&ab, &pb)
                .unwrap_or_else(|| panic!("a={} mod p={} should be invertible", a, p));
            let prod = (&ab * &inv) % &pb;
            assert_eq!(
                prod,
                BigUint::one(),
                "a*inv(a) ≡ 1 fails: a={}, inv={}, p={}",
                a,
                inv,
                p
            );
            // Inverse is canonical: in [0, p).
            assert!(inv < pb, "inverse must lie in [0, p)");
        }
    }
}

#[test]
fn prop_mod_inverse_zero_returns_none() {
    // gcd(0, p) = p ≠ 1, so 0 has no inverse.
    let p = BigUint::from(7u32);
    assert!(mod_inverse(&BigUint::from(0u32), &p).is_none());
}

#[test]
fn prop_mod_inverse_non_coprime_returns_none() {
    // p = 6 (composite), a = 4: gcd(4, 6) = 2 ≠ 1.
    let p = BigUint::from(6u32);
    let a = BigUint::from(4u32);
    assert!(mod_inverse(&a, &p).is_none());
}

#[test]
fn prop_mod_inverse_one_is_one() {
    let p = BigUint::from(7u32);
    let inv = mod_inverse(&BigUint::one(), &p).expect("1 always invertible");
    assert_eq!(inv, BigUint::one());
}

#[test]
fn prop_mod_inverse_self_inverse_for_p_minus_one() {
    // (p-1) * (p-1) = p^2 - 2p + 1 ≡ 1 (mod p), so p-1 is self-inverse.
    for &p in &[7u64, 11, 13, 101] {
        let pb = BigUint::from(p);
        let a = &pb - 1u32;
        let inv = mod_inverse(&a, &pb).expect("p-1 invertible");
        assert_eq!(inv, a, "p-1 must be self-inverse for p={}", p);
    }
}

// ───── wire_connectivity_score ───────────────────────────────────

/// Build a tiny PolyIR with a hand-crafted equality list.
///
/// Uses `n_wires` wires (so the ring carries `2 * n_wires` variables).
/// `equalities` is built by the caller before this is called.
fn make_tiny_ir(prime: u64, n_wires: usize, equalities_builder: impl FnOnce(&Arc<FfPolyRing>) -> Vec<picus_core::poly::IrPoly>) -> PolyIR {
    let p = BigUint::from(prime);
    let field = PrimeField::new(p);
    let mut names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        names.push(format!("y{}", i));
    }
    let ring = Arc::new(FfPolyRing::new(field, names));
    let equalities = equalities_builder(&ring);
    PolyIR {
        ring,
        n_wires,
        input_indices: HashSet::new(),
        equalities,
        disjunctions: Vec::new(),
        known_signals: HashSet::new(),
        target_signal: 0,
        disequalities: Vec::new(),
        assignments: Vec::new(),
        bitsums: Vec::new(),
        add_field_polys: false,
    }
}

#[test]
fn prop_connectivity_empty_ir_yields_empty_map() {
    let ir = make_tiny_ir(7, 3, |_| Vec::new());
    let score = wire_connectivity_score(&ir);
    assert!(score.is_empty(), "no constraints ⇒ no wire is scored");
}

#[test]
fn prop_connectivity_single_constraint_x1_plus_x2() {
    // One constraint: x1 + x2 = 0. Wires 1 and 2 each touch 1 constraint.
    let ir = make_tiny_ir(7, 3, |ring| {
        let p = ring.add(ring.var(1), ring.var(2));
        vec![p]
    });
    let score = wire_connectivity_score(&ir);
    assert_eq!(score.get(&1).copied(), Some(1));
    assert_eq!(score.get(&2).copied(), Some(1));
    assert_eq!(score.get(&0).copied(), None, "wire 0 not touched");
}

#[test]
fn prop_connectivity_same_wire_two_terms_counts_once_per_constraint() {
    // One constraint: x1 + x1*x1 = 0. Wire 1 appears twice in this
    // poly's support; doc says "distinct constraints" => count = 1.
    let ir = make_tiny_ir(7, 3, |ring| {
        let x1 = ring.var(1);
        let p = ring.add(ring.clone_poly(&x1), ring.mul(ring.clone_poly(&x1), x1));
        vec![p]
    });
    let score = wire_connectivity_score(&ir);
    assert_eq!(
        score.get(&1).copied(),
        Some(1),
        "wire 1 touches one constraint, not two"
    );
}

#[test]
fn prop_connectivity_two_constraints_share_wire() {
    // Two constraints, both touching wire 1: x1 + x2, x1 + x3.
    let ir = make_tiny_ir(7, 4, |ring| {
        let c1 = ring.add(ring.var(1), ring.var(2));
        let c2 = ring.add(ring.var(1), ring.var(3));
        vec![c1, c2]
    });
    let score = wire_connectivity_score(&ir);
    assert_eq!(score.get(&1).copied(), Some(2), "wire 1 in 2 constraints");
    assert_eq!(score.get(&2).copied(), Some(1));
    assert_eq!(score.get(&3).copied(), Some(1));
}

#[test]
fn prop_connectivity_alt_copy_var_maps_back_to_same_wire() {
    // y1 (index n_wires+1) maps to wire 1 via var_to_wire. So a
    // constraint over `y1 + x2` should still score wire 1.
    let ir = make_tiny_ir(7, 3, |ring| {
        // y1 is variable index n_wires+1 = 4
        let p = ring.add(ring.var(4), ring.var(2));
        vec![p]
    });
    let score = wire_connectivity_score(&ir);
    assert_eq!(
        score.get(&1).copied(),
        Some(1),
        "alt-copy y1 must score under wire 1"
    );
}

#[test]
fn prop_connectivity_x_and_y_same_constraint_count_once() {
    // x1 + y1 = 0 in one constraint. Both variables map back to wire 1
    // via `var_to_wire`; the inner HashSet dedups them, so wire 1 is
    // counted ONCE for this constraint.
    let ir = make_tiny_ir(7, 3, |ring| {
        // x1 (idx 1) + y1 (idx n_wires+1 = 4)
        let p = ring.add(ring.var(1), ring.var(4));
        vec![p]
    });
    let score = wire_connectivity_score(&ir);
    assert_eq!(
        score.get(&1).copied(),
        Some(1),
        "x1 and y1 in same constraint dedup to one count on wire 1"
    );
}
