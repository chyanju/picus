//! Tests for `lib.rs` — `SolverKind`, `Theory`, `validate_combination`,
//! `create_backend`, and the round-trip via `FromStr`/`as_str`. These
//! exercise the public solver-selection facade users hit via `--solver`.

use super::*;
use std::str::FromStr;

// ─── SolverKind ────────────────────────────────────────────────────

#[test]
fn prop_solver_kind_as_str_roundtrip_via_from_str() {
    // Doc spec: `as_str` is the canonical lowercase name; matches
    // `FromStr` arms (except `None` is the propagation-only sentinel).
    for k in [
        SolverKind::Z3,
        SolverKind::Cvc5,
        SolverKind::Native,
        SolverKind::None,
    ] {
        let s = k.as_str();
        let parsed = SolverKind::from_str(s).expect("known names parse");
        assert_eq!(parsed, k, "round-trip {:?} → {} → ...", k, s);
    }
}

#[test]
fn test_solver_kind_as_str_exact_names() {
    assert_eq!(SolverKind::Z3.as_str(), "z3");
    assert_eq!(SolverKind::Cvc5.as_str(), "cvc5");
    assert_eq!(SolverKind::Native.as_str(), "native");
    assert_eq!(SolverKind::None.as_str(), "none");
}

#[test]
fn test_solver_kind_from_str_unknown_is_err_not_panic() {
    let r = SolverKind::from_str("definitely-not-a-solver");
    assert!(r.is_err(), "unknown name must be Err, got {:?}", r);
}

#[test]
fn test_solver_kind_from_str_err_lists_none() {
    // Spec: error message surfaces every known backend; `none` is
    // always present (the propagation-only sentinel).
    let r = SolverKind::from_str("xyzzy");
    let msg = r.unwrap_err();
    assert!(msg.contains("none"), "err message lists 'none': {}", msg);
    assert!(msg.contains("xyzzy"), "err message echoes input: {}", msg);
}

#[test]
fn test_solver_kind_from_str_empty_is_err() {
    assert!(SolverKind::from_str("").is_err());
}

#[test]
fn test_solver_kind_from_str_case_sensitive() {
    // Canonical names are lowercase; uppercase variants are unknown.
    assert!(SolverKind::from_str("Z3").is_err());
    assert!(SolverKind::from_str("Native").is_err());
}

// ─── Theory ────────────────────────────────────────────────────────

#[test]
fn prop_theory_from_str_roundtrip() {
    for (name, t) in [("ff", Theory::Ff), ("nia", Theory::Nia)] {
        let parsed = Theory::from_str(name).unwrap();
        assert_eq!(parsed, t);
    }
}

#[test]
fn test_theory_from_str_unknown_is_err_not_panic() {
    let r = Theory::from_str("smt");
    assert!(r.is_err());
}

#[test]
fn test_theory_from_str_empty_is_err() {
    assert!(Theory::from_str("").is_err());
}

// ─── validate_combination ─────────────────────────────────────────

#[test]
fn prop_validate_z3_ff_rejected() {
    // Spec: Z3 doesn't support QF_FF.
    let r = validate_combination(SolverKind::Z3, Theory::Ff);
    assert!(r.is_err(), "Z3+Ff must be rejected: {:?}", r);
}

#[test]
fn prop_validate_native_nia_rejected() {
    // Spec: native only supports QF_FF.
    let r = validate_combination(SolverKind::Native, Theory::Nia);
    assert!(r.is_err(), "Native+Nia must be rejected: {:?}", r);
}

#[test]
fn prop_validate_native_ff_ok() {
    assert!(validate_combination(SolverKind::Native, Theory::Ff).is_ok());
}

#[test]
fn prop_validate_z3_nia_ok() {
    assert!(validate_combination(SolverKind::Z3, Theory::Nia).is_ok());
}

#[test]
fn prop_validate_cvc5_both_ok() {
    assert!(validate_combination(SolverKind::Cvc5, Theory::Ff).is_ok());
    assert!(validate_combination(SolverKind::Cvc5, Theory::Nia).is_ok());
}

#[test]
fn prop_validate_none_accepts_any_theory() {
    // Spec: `SolverKind::None` is the propagation-only sentinel; the
    // theory selection is moot.
    assert!(validate_combination(SolverKind::None, Theory::Ff).is_ok());
    assert!(validate_combination(SolverKind::None, Theory::Nia).is_ok());
}

// ─── create_backend ───────────────────────────────────────────────

#[test]
fn prop_create_backend_none_returns_ok_none() {
    // Doc spec: returns `Ok(None)` for `SolverKind::None`.
    let r = create_backend(SolverKind::None, Theory::Ff).unwrap();
    assert!(r.is_none(), "None solver → Ok(None)");
}

#[test]
fn test_create_backend_native_ff_is_some() {
    // The native FF backend is registered in this crate via
    // `inventory::submit!` (default feature is on); it must be
    // dispatchable.
    let r = create_backend(SolverKind::Native, Theory::Ff).unwrap();
    assert!(r.is_some(), "native+ff backend must be registered");
}

#[test]
fn test_create_backend_native_nia_is_err() {
    // Validation should reject before lookup.
    let r = create_backend(SolverKind::Native, Theory::Nia);
    assert!(r.is_err());
}

#[test]
fn test_create_backend_z3_ff_is_err() {
    let r = create_backend(SolverKind::Z3, Theory::Ff);
    assert!(r.is_err());
}

// ─── SUBP_CONSTANT_NAMES ─────────────────────────────────────────

#[test]
fn test_subp_constant_names_contain_documented_set() {
    // Doc spec names exactly: p, ps1..ps5, zero, one.
    let expected = ["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"];
    for n in &expected {
        assert!(
            SUBP_CONSTANT_NAMES.contains(n),
            "expected {} in SUBP_CONSTANT_NAMES",
            n
        );
    }
    assert_eq!(SUBP_CONSTANT_NAMES.len(), expected.len());
}

#[test]
fn test_subp_constant_names_unique() {
    // No accidental duplicates would confuse the post-processor's
    // membership check.
    let mut v: Vec<&str> = SUBP_CONSTANT_NAMES.to_vec();
    v.sort();
    let n = v.len();
    v.dedup();
    assert_eq!(v.len(), n, "SUBP_CONSTANT_NAMES has duplicates");
}

// ─── all_backend_descriptors / create_backend_by_name ──────────

#[test]
fn test_all_backend_descriptors_sorted() {
    // Spec: stable order by `(name, theory)`.
    let descs = backends::all_backend_descriptors();
    let keys: Vec<(&str, u8)> = descs
        .iter()
        .map(|d| {
            let t = match d.theory {
                Theory::Ff => 0u8,
                Theory::Nia => 1u8,
            };
            (d.name, t)
        })
        .collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted, "descriptors must be sorted");
}

#[test]
fn test_create_backend_by_name_native_ff_found() {
    let b = backends::create_backend_by_name("native", Theory::Ff);
    assert!(b.is_some(), "native+ff must be registered");
}

#[test]
fn test_create_backend_by_name_unknown_is_none() {
    let b = backends::create_backend_by_name("nope-not-a-name", Theory::Ff);
    assert!(b.is_none());
}
