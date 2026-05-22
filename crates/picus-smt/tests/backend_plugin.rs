//! The four built-in SMT backends register themselves via
//! `inventory::submit!`. This test confirms every one is discoverable
//! through the public registry and that `create_backend` dispatches by
//! name (not by hard-coded match table).

use picus_smt::backends::{all_backend_descriptors, create_backend_by_name};
use picus_smt::{create_backend, SolverKind, Theory};

#[test]
fn all_four_built_in_backends_register() {
    let descriptors = all_backend_descriptors();
    let pairs: Vec<(&str, Theory)> = descriptors.iter().map(|d| (d.name, d.theory)).collect();
    for expected in [
        ("cvc5", Theory::Ff),
        ("cvc5", Theory::Nia),
        ("native", Theory::Ff),
        ("z3", Theory::Nia),
    ] {
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
    for (name, theory) in [
        ("cvc5", Theory::Ff),
        ("cvc5", Theory::Nia),
        ("native", Theory::Ff),
        ("z3", Theory::Nia),
    ] {
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
    // `create_backend` builds via the inventory registry, not a hard
    // match table; so every built-in combination resolves.
    for (kind, theory) in [
        (SolverKind::Cvc5, Theory::Ff),
        (SolverKind::Cvc5, Theory::Nia),
        (SolverKind::Native, Theory::Ff),
        (SolverKind::Z3, Theory::Nia),
    ] {
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
