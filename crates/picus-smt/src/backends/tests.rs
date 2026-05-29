//! Tests for `backends/mod.rs` — `SolverResult`, `UnknownReason`,
//! the inventory dispatch helpers, and the feature-gated SMT-LIB
//! emitters (only when the relevant Cargo feature is on).

use super::*;
use crate::Theory;

// ─── SolverResult / UnknownReason wiring ──────────────────────────

#[test]
fn test_solver_result_variants_constructible() {
    // Smoke: the three variants compile and pattern-match.
    use std::collections::HashMap;
    let _a: SolverResult = SolverResult::Unsat;
    let _b: SolverResult = SolverResult::Sat(HashMap::new());
    let _c: SolverResult = SolverResult::Unknown(UnknownReason::Timeout);
}

#[test]
fn test_unknown_reason_variants_constructible() {
    let _a = UnknownReason::Timeout;
    let _b = UnknownReason::IncompleteTheory;
    let _c = UnknownReason::BackendError("oops".into());
    // Trivially Clone (derived on UnknownReason).
    let _d = _c.clone();
}

// ─── all_backend_descriptors ─────────────────────────────────────

#[test]
fn prop_all_backend_descriptors_sorted_by_name_theory() {
    // Doc spec: "Stable order by `(name, theory)`".
    let descs = all_backend_descriptors();
    let keys: Vec<(&str, u8)> = descs
        .iter()
        .map(|d| (d.name, super::theory_key(d.theory)))
        .collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted);
}

#[test]
fn prop_all_backend_descriptors_includes_native_ff() {
    // The native FF backend is registered unconditionally (no feature gate).
    let found = all_backend_descriptors()
        .into_iter()
        .any(|d| d.name == "native" && d.theory == Theory::Ff);
    assert!(found);
}

#[test]
fn test_all_backend_descriptors_no_duplicate_name_theory_pairs() {
    // Each (name, theory) pair should appear at most once; otherwise
    // `create_backend_by_name` would have ambiguous dispatch.
    let descs = all_backend_descriptors();
    let mut seen: Vec<(&str, Theory)> = Vec::new();
    for d in &descs {
        let key = (d.name, d.theory);
        assert!(
            !seen.contains(&key),
            "duplicate descriptor for ({}, {:?})",
            d.name,
            d.theory
        );
        seen.push(key);
    }
}

// ─── create_backend_by_name ──────────────────────────────────────

#[test]
fn prop_create_backend_by_name_native_ff_returns_some() {
    let b = create_backend_by_name("native", Theory::Ff);
    assert!(b.is_some());
}

#[test]
fn prop_create_backend_by_name_unknown_returns_none() {
    let b = create_backend_by_name("does-not-exist", Theory::Ff);
    assert!(b.is_none());
}

#[test]
fn prop_create_backend_by_name_wrong_theory_returns_none() {
    // Native backend is Ff-only; asking for Nia must miss.
    let b = create_backend_by_name("native", Theory::Nia);
    assert!(b.is_none());
}

// ─── Feature-gated SMT-LIB emitters ──────────────────────────────

#[cfg(any(feature = "cvc5", feature = "z3"))]
mod nia_smtlib {
    use crate::backends::poly_to_smtlib_nia;
    use crate::poly_ir::{r1cs_to_poly_ir, PolyIR};
    use num_bigint::BigUint;
    use picus_r1cs::grammar::{
        Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
    };
    use std::collections::HashSet;

    fn make_ir(p: BigUint, n_wires: usize) -> PolyIR {
        let r1cs = R1csFile {
            magic: *b"r1cs",
            version: 1,
            n_sections: 3,
            header: HeaderSection {
                field_size: 32,
                prime_number: p,
                n_wires: n_wires as u32,
                n_pub_out: 0,
                n_pub_in: 0,
                n_prv_in: 0,
                n_labels: 0,
                m_constraints: 0,
            },
            constraints: ConstraintSection {
                constraints: Vec::new(),
            },
            w2l: W2lSection { labels: Vec::new() },
            inputs: vec![0],
            outputs: Vec::new(),
        };
        r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap()
    }

    #[test]
    fn prop_nia_empty_poly_is_zero_literal() {
        // Doc spec: "an empty polynomial reduces to literal `0`".
        let ir = make_ir(BigUint::from(7u32), 3);
        let zero = ir.ring.zero();
        let s = poly_to_smtlib_nia(&ir, &zero);
        assert_eq!(s, "0");
    }

    #[test]
    fn prop_nia_constant_is_bare_coeff() {
        // Single-term constant ⇒ atoms.len() == 1 ⇒ bare coefficient.
        let ir = make_ir(BigUint::from(7u32), 3);
        let c = ir.constant(&BigUint::from(3u32));
        let s = poly_to_smtlib_nia(&ir, &c);
        assert_eq!(s, "3");
    }

    #[test]
    fn prop_nia_linear_term_uses_mul_sexpr() {
        // (coeff x_1) ⇒ `(* coeff x1)`.
        let ir = make_ir(BigUint::from(7u32), 3);
        let t = ir.linear_term(&BigUint::from(2u32), 1);
        let s = poly_to_smtlib_nia(&ir, &t);
        assert!(s.starts_with("(* "), "linear term uses (*: {}", s);
        assert!(s.contains("x1"));
    }

    #[test]
    fn prop_nia_two_terms_wrapped_in_add_sexpr() {
        let ir = make_ir(BigUint::from(7u32), 3);
        let a = ir.linear_term(&BigUint::from(2u32), 1);
        let b = ir.linear_term(&BigUint::from(3u32), 2);
        let sum = ir.ring.add(a, b);
        let s = poly_to_smtlib_nia(&ir, &sum);
        assert!(s.starts_with("(+ "), "two-term sum: {}", s);
    }
}

#[cfg(feature = "cvc5")]
mod ff_smtlib {
    use crate::backends::poly_to_smtlib_ff;
    use crate::poly_ir::{r1cs_to_poly_ir, PolyIR};
    use num_bigint::BigUint;
    use picus_r1cs::grammar::{
        ConstraintSection, HeaderSection, R1csFile, W2lSection,
    };
    use std::collections::HashSet;

    fn make_ir(p: BigUint, n_wires: usize) -> PolyIR {
        let r1cs = R1csFile {
            magic: *b"r1cs",
            version: 1,
            n_sections: 3,
            header: HeaderSection {
                field_size: 32,
                prime_number: p,
                n_wires: n_wires as u32,
                n_pub_out: 0,
                n_pub_in: 0,
                n_prv_in: 0,
                n_labels: 0,
                m_constraints: 0,
            },
            constraints: ConstraintSection {
                constraints: Vec::new(),
            },
            w2l: W2lSection { labels: Vec::new() },
            inputs: vec![0],
            outputs: Vec::new(),
        };
        r1cs_to_poly_ir(&r1cs, &HashSet::new(), 1).unwrap()
    }

    #[test]
    fn prop_ff_empty_poly_is_zero_ff_literal() {
        // Doc spec: "#fNmP" form; empty ⇒ `#f0mP`.
        let ir = make_ir(BigUint::from(7u32), 3);
        let zero = ir.ring.zero();
        let s = poly_to_smtlib_ff(&ir, &zero);
        assert_eq!(s, "#f0m7");
    }

    #[test]
    fn prop_ff_constant_is_bare_ff_literal() {
        let ir = make_ir(BigUint::from(7u32), 3);
        let c = ir.constant(&BigUint::from(3u32));
        let s = poly_to_smtlib_ff(&ir, &c);
        assert_eq!(s, "#f3m7");
    }

    #[test]
    fn prop_ff_linear_uses_ff_mul() {
        let ir = make_ir(BigUint::from(7u32), 3);
        let t = ir.linear_term(&BigUint::from(2u32), 1);
        let s = poly_to_smtlib_ff(&ir, &t);
        assert!(s.starts_with("(ff.mul "), "ff term: {}", s);
        assert!(s.contains("x1"));
        assert!(s.contains("#f2m7"));
    }

    #[test]
    fn prop_ff_two_terms_use_ff_add() {
        let ir = make_ir(BigUint::from(7u32), 3);
        let a = ir.linear_term(&BigUint::from(2u32), 1);
        let b = ir.linear_term(&BigUint::from(3u32), 2);
        let sum = ir.ring.add(a, b);
        let s = poly_to_smtlib_ff(&ir, &sum);
        assert!(s.starts_with("(ff.add "), "ff sum: {}", s);
    }
}
