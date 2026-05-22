//! The four built-in SMT backends register themselves via
//! `inventory::submit!`. This test confirms every one is discoverable
//! through the public registry and that `create_backend` dispatches by
//! name (not by hard-coded match table).

use picus_smt::backends::{all_backend_descriptors, create_backend_by_name};
use picus_smt::{create_backend, SolverKind, Theory};

/// The set of `(name, theory)` backends expected under the current
/// feature configuration. Always includes `(native, Ff)`; cvc5 and
/// z3 entries are gated by their respective features.
fn expected_pairs() -> Vec<(&'static str, Theory)> {
    let mut v: Vec<(&'static str, Theory)> = Vec::new();
    v.push(("native", Theory::Ff));
    #[cfg(feature = "cvc5")]
    {
        v.push(("cvc5", Theory::Ff));
        v.push(("cvc5", Theory::Nia));
    }
    #[cfg(feature = "z3")]
    {
        v.push(("z3", Theory::Nia));
    }
    v
}

#[test]
fn every_enabled_backend_is_in_the_inventory() {
    let descriptors = all_backend_descriptors();
    let pairs: Vec<(&str, Theory)> = descriptors.iter().map(|d| (d.name, d.theory)).collect();
    for expected in expected_pairs() {
        assert!(
            pairs.contains(&expected),
            "missing inventory entry {:?} in {:?}",
            expected,
            pairs
        );
    }
}

#[test]
fn create_backend_by_name_returns_an_instance() {
    for (name, theory) in expected_pairs() {
        let b = create_backend_by_name(name, theory);
        assert!(
            b.is_some(),
            "create_backend_by_name({:?}, {:?}) returned None",
            name,
            theory
        );
    }
}

#[test]
fn create_backend_uses_inventory_lookup() {
    // Every enabled combination resolves to an instance.
    #[allow(unused_mut)]
    let mut kinds: Vec<(SolverKind, Theory)> = vec![(SolverKind::Native, Theory::Ff)];
    #[cfg(feature = "cvc5")]
    {
        kinds.push((SolverKind::Cvc5, Theory::Ff));
        kinds.push((SolverKind::Cvc5, Theory::Nia));
    }
    #[cfg(feature = "z3")]
    {
        kinds.push((SolverKind::Z3, Theory::Nia));
    }
    for (kind, theory) in kinds {
        let r = create_backend(kind, theory);
        assert!(
            matches!(r, Ok(Some(_))),
            "create_backend({:?}, {:?}) failed: {:?}",
            kind,
            theory,
            r.err()
        );
    }
    // `None` is the propagation-only sentinel — no backend instance.
    let none = create_backend(SolverKind::None, Theory::Ff);
    assert!(matches!(none, Ok(None)));
}

#[test]
fn create_backend_rejects_invalid_combinations() {
    // Z3 doesn't implement QF_FF; native doesn't implement QF_NIA.
    assert!(create_backend(SolverKind::Z3, Theory::Ff).is_err());
    assert!(create_backend(SolverKind::Native, Theory::Nia).is_err());
}

/// Under `--no-default-features` neither cvc5 nor z3 are registered;
/// `create_backend` must surface a clean error rather than silently
/// constructing nothing.
#[cfg(not(feature = "cvc5"))]
#[test]
fn cvc5_disabled_creates_no_backend() {
    assert!(create_backend(SolverKind::Cvc5, Theory::Ff).is_err());
    assert!(create_backend(SolverKind::Cvc5, Theory::Nia).is_err());
}

#[cfg(not(feature = "z3"))]
#[test]
fn z3_disabled_creates_no_backend() {
    assert!(create_backend(SolverKind::Z3, Theory::Nia).is_err());
}
