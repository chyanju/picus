//! Tests for the propagation-lemma plugin interface.
//!
//! Spec invariants:
//!   - `all_descriptors()` returns lemmas sorted by name (reproducible
//!     execution order across runs).
//!   - `all_names()` matches the names of `all_descriptors()` in order.
//!   - Every registered lemma's `factory()` builds an instance whose
//!     `.name()` matches the descriptor's `.name`.
//!   - The current core lemma set (aboz / basis2 / bim / binary01 /
//!     linear / range / lemma file is the interface, the lemma names live
//!     in their respective files). At minimum, all of these baseline names
//!     must be present.

use crate::propagation::lemma::{all_descriptors, all_names, PropagationLemma};

#[test]
fn prop_all_descriptors_sorted_by_name() {
    let descs = all_descriptors();
    let names: Vec<&str> = descs.iter().map(|d| d.name).collect();
    let mut sorted = names.clone();
    sorted.sort();
    assert_eq!(names, sorted, "descriptors must be sorted by name");
}

#[test]
fn prop_all_names_matches_descriptors() {
    let descs = all_descriptors();
    let names = all_names();
    assert_eq!(descs.len(), names.len());
    for (d, n) in descs.iter().zip(names.iter()) {
        assert_eq!(d.name, *n, "name mismatch between descriptor / name");
    }
}

#[test]
fn prop_factory_produces_matching_name() {
    // Every factory must build a fresh instance whose run-time name
    // equals the descriptor's name. A mismatch would break the
    // `--lemmas` flag selection (CLI matches by descriptor name).
    for d in all_descriptors() {
        let inst: Box<dyn PropagationLemma> = (d.factory)();
        assert_eq!(
            inst.name(),
            d.name,
            "factory for {:?} produced instance with name {:?}",
            d.name,
            inst.name()
        );
    }
}

#[test]
fn prop_descriptor_names_unique() {
    // Duplicate names would make `LemmaSet::parse` ambiguous.
    let names = all_names();
    let mut sorted = names.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(
        names.len(),
        sorted.len(),
        "lemma names must be unique across the inventory"
    );
}

#[test]
fn prop_known_lemmas_registered() {
    // The repo always ships these baseline lemmas; a missing entry
    // means an inventory link/build regression.
    let names = all_names();
    for required in &["aboz", "binary01", "linear", "bim", "basis2"] {
        assert!(
            names.contains(required),
            "expected baseline lemma {:?} to be registered (have: {:?})",
            required,
            names
        );
    }
}

#[test]
fn prop_factory_name_stable_across_instances() {
    // Two invocations of the same factory must produce instances with
    // the same `name()`. (Caches built lazily on `run` should not affect
    // the static `name`.)
    if let Some(d) = all_descriptors().first() {
        let a: Box<dyn PropagationLemma> = (d.factory)();
        let b: Box<dyn PropagationLemma> = (d.factory)();
        assert_eq!(a.name(), b.name(), "name is stable across instances");
        assert_eq!(a.name(), d.name);
    }
}
