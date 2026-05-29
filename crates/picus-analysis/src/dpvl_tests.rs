use super::*;

/// Drift guard: every `DpvlOverlay` field must be consumed by
/// `apply_overlay`. Each overlay field is set to a value distinct
/// from the compiled default and the merged config is asserted equal
/// to an explicit all-overridden `expected`. A knob added to
/// `DpvlConfig` / `DpvlOverlay` but not wired into `apply_overlay`
/// stays at its default and fails the assert; the explicit struct
/// literals also fail to compile until the new field is added here.
/// (Mirrors `picus_core::config`'s engine-overlay drift guard so all
/// three layered-config sites are guarded, not just the engine one.)
#[test]
fn apply_overlay_consumes_every_field() {
    let overlay = DpvlOverlay {
        solver: Some("cvc5".to_string()),
        theory: Some("nia".to_string()),
        selector: Some("first".to_string()),
        timeout_ms: Some(1234),
        lemmas: Some("none".to_string()),
        dump_smt: Some(PathBuf::from("/tmp/picus-x")),
    };
    let expected = DpvlConfig {
        solver: SolverKind::Cvc5,
        theory: Theory::Nia,
        selector: SelectorKind::First,
        timeout_ms: 1234,
        lemmas: LemmaSet::none(),
        dump_smt: Some(PathBuf::from("/tmp/picus-x")),
    };

    // Every chosen value must differ from the compiled default, so a
    // missed field would actually be observable.
    assert_ne!(
        expected,
        DpvlConfig::default(),
        "test values must differ from defaults to be meaningful"
    );

    let mut cfg = DpvlConfig::default();
    cfg.apply_overlay(&overlay).expect("overlay should apply");
    assert_eq!(
        cfg, expected,
        "apply_overlay did not propagate every overlay field"
    );
}

// ---------------------------------------------------------------------------
// LemmaSet — spec-driven tests.
//
// Doc spec (verbatim from dpvl.rs):
//   * `LemmaSet::all()`   — every registered lemma enabled.
//   * `LemmaSet::none()`  — no lemmas enabled (solver-only mode).
//   * `parse` formats:
//       - `all`            — enable every registered lemma
//       - `none`           — disable every registered lemma
//       - `all-X,Y`        — all except `X` and `Y`
//       - `none+X,Y`       — none except `X` and `Y`
//       - `X,Y`            — explicit list (same as `none+X,Y`)
//   * Unknown names are an error.
//   * `is_enabled(name)`  — membership test.
//   * `any_enabled()`     — at least one lemma enabled.
//   * `Display`           — canonical spec: `none`, `all`, or sorted CSV.
// ---------------------------------------------------------------------------

/// `all()` enables exactly the live registry — same count and every
/// registered name is enabled.
#[test]
fn prop_lemma_set_all_matches_registry() {
    let s = LemmaSet::all();
    let names = all_names();
    assert!(s.any_enabled(), "registry must not be empty");
    for n in &names {
        assert!(s.is_enabled(n), "all() should enable {}", n);
    }
}

/// `none()` enables nothing.
#[test]
fn prop_lemma_set_none_is_empty() {
    let s = LemmaSet::none();
    assert!(!s.any_enabled());
    for n in all_names() {
        assert!(!s.is_enabled(n), "none() must not enable {}", n);
    }
}

/// `parse("all")` and `parse("none")` round-trip to the constructor results.
#[test]
fn prop_lemma_set_parse_all_and_none() {
    assert_eq!(LemmaSet::parse("all").unwrap(), LemmaSet::all());
    assert_eq!(LemmaSet::parse("none").unwrap(), LemmaSet::none());
}

/// `parse` is case-insensitive — implementation lowercases the input
/// before matching, per `let s = s.trim().to_lowercase();`.
#[test]
fn prop_lemma_set_parse_case_insensitive() {
    assert_eq!(LemmaSet::parse("ALL").unwrap(), LemmaSet::all());
    assert_eq!(LemmaSet::parse("None").unwrap(), LemmaSet::none());
}

/// `parse` trims leading/trailing whitespace on the whole spec.
#[test]
fn prop_lemma_set_parse_trims_outer_whitespace() {
    assert_eq!(LemmaSet::parse("  all  ").unwrap(), LemmaSet::all());
    assert_eq!(LemmaSet::parse("  none ").unwrap(), LemmaSet::none());
}

/// `all-X` removes exactly `X` from the all-enabled set.
#[test]
fn prop_lemma_set_parse_all_minus_one() {
    // Pick a known-registered name. `linear` is registered.
    let s = LemmaSet::parse("all-linear").unwrap();
    assert!(!s.is_enabled("linear"));
    // Every other registered name still enabled.
    for n in all_names() {
        if n != "linear" {
            assert!(s.is_enabled(n), "all-linear should keep {}", n);
        }
    }
}

/// `all-X,Y` removes both X and Y.
#[test]
fn prop_lemma_set_parse_all_minus_two() {
    let s = LemmaSet::parse("all-linear,binary01").unwrap();
    assert!(!s.is_enabled("linear"));
    assert!(!s.is_enabled("binary01"));
    for n in all_names() {
        if n != "linear" && n != "binary01" {
            assert!(s.is_enabled(n));
        }
    }
}

/// `none+X` enables exactly X.
#[test]
fn prop_lemma_set_parse_none_plus() {
    let s = LemmaSet::parse("none+linear").unwrap();
    assert!(s.is_enabled("linear"));
    assert!(s.any_enabled());
    for n in all_names() {
        if n != "linear" {
            assert!(!s.is_enabled(n));
        }
    }
}

/// Bare list `X,Y` is the same as `none+X,Y`.
#[test]
fn prop_lemma_set_parse_bare_list_equals_none_plus() {
    let bare = LemmaSet::parse("linear,binary01").unwrap();
    let none_plus = LemmaSet::parse("none+linear,binary01").unwrap();
    assert_eq!(bare, none_plus);
    assert!(bare.is_enabled("linear"));
    assert!(bare.is_enabled("binary01"));
}

/// Unknown lemma name is an error, not a silent skip.
#[test]
fn prop_lemma_set_parse_unknown_name_errors() {
    assert!(LemmaSet::parse("does-not-exist").is_err());
    assert!(LemmaSet::parse("all-does-not-exist").is_err());
    assert!(LemmaSet::parse("none+does-not-exist").is_err());
}

/// Error message names the offending lemma, so the CLI surfaces a useful diag.
#[test]
fn prop_lemma_set_parse_error_mentions_name() {
    let err = LemmaSet::parse("bogus_lemma").unwrap_err();
    assert!(
        err.contains("bogus_lemma"),
        "error '{}' should mention the unknown name",
        err
    );
}

/// `Display` round-trips through `parse` for `none` and `all`.
#[test]
fn prop_lemma_set_display_roundtrip_extremes() {
    let n = LemmaSet::none();
    assert_eq!(format!("{}", n), "none");
    assert_eq!(LemmaSet::parse(&format!("{}", n)).unwrap(), n);

    let a = LemmaSet::all();
    assert_eq!(format!("{}", a), "all");
    assert_eq!(LemmaSet::parse(&format!("{}", a)).unwrap(), a);
}

/// `Display` round-trips through `parse` for arbitrary subsets.
#[test]
fn prop_lemma_set_display_roundtrip_subset() {
    let s = LemmaSet::parse("linear,binary01").unwrap();
    let rendered = format!("{}", s);
    // Not `all` (one or more lemmas missing) nor `none` (set has two).
    assert_ne!(rendered, "all");
    assert_ne!(rendered, "none");
    let reparsed = LemmaSet::parse(&rendered).unwrap();
    assert_eq!(reparsed, s);
}

/// `Display` for a partial set sorts the names — reproducible across HashSet
/// iteration orders.
#[test]
fn prop_lemma_set_display_partial_is_sorted() {
    // Two registered names in non-sorted insertion order.
    let s = LemmaSet::parse("linear,binary01").unwrap();
    let rendered = format!("{}", s);
    let names: Vec<&str> = rendered.split(',').collect();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "display should sort names");
}

/// `any_enabled` ⇔ at least one lemma in the set.
#[test]
fn prop_lemma_set_any_enabled_matches_membership() {
    assert!(!LemmaSet::none().any_enabled());
    assert!(LemmaSet::all().any_enabled());
    assert!(LemmaSet::parse("linear").unwrap().any_enabled());
}

// ---------------------------------------------------------------------------
// DpvlConfig / DpvlOverlay
// ---------------------------------------------------------------------------

/// Default config has the documented spec: native solver, FF theory,
/// counter selector, 5000ms timeout, all lemmas enabled, no SMT dump.
#[test]
fn prop_dpvl_config_default_values() {
    let d = DpvlConfig::default();
    assert_eq!(d.solver, SolverKind::Native);
    assert_eq!(d.theory, Theory::Ff);
    assert_eq!(d.selector, SelectorKind::Counter);
    assert_eq!(d.timeout_ms, 5000);
    assert_eq!(d.lemmas, LemmaSet::all());
    assert_eq!(d.dump_smt, None);
}

/// Empty overlay leaves the default untouched.
#[test]
fn prop_apply_overlay_empty_is_noop() {
    let mut cfg = DpvlConfig::default();
    let before = cfg.clone();
    let overlay = DpvlOverlay::default();
    cfg.apply_overlay(&overlay).expect("empty overlay applies");
    assert_eq!(cfg, before, "empty overlay must not mutate config");
}

/// Bad string in overlay surfaces as an `Err`, not a silent default.
#[test]
fn prop_apply_overlay_bad_selector_errors() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        selector: Some("not-a-selector".to_string()),
        ..Default::default()
    };
    assert!(cfg.apply_overlay(&overlay).is_err());
}

/// Bad lemma name in overlay surfaces as an `Err`.
#[test]
fn prop_apply_overlay_bad_lemmas_errors() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        lemmas: Some("bogus_lemma_name".to_string()),
        ..Default::default()
    };
    assert!(cfg.apply_overlay(&overlay).is_err());
}

/// Only the `Some` fields of an overlay are applied — `None` fields leave
/// the existing value untouched.
#[test]
fn prop_apply_overlay_partial_only_touches_set_fields() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        timeout_ms: Some(42),
        ..Default::default()
    };
    cfg.apply_overlay(&overlay).expect("apply partial overlay");
    assert_eq!(cfg.timeout_ms, 42);
    // Untouched fields keep their defaults.
    let d = DpvlConfig::default();
    assert_eq!(cfg.solver, d.solver);
    assert_eq!(cfg.theory, d.theory);
    assert_eq!(cfg.selector, d.selector);
    assert_eq!(cfg.lemmas, d.lemmas);
    assert_eq!(cfg.dump_smt, d.dump_smt);
}

/// `DpvlError::Lower` is `From<LowerError>` — typed-error wiring sanity check
/// (`#[from] LowerError`). Verifies both variants exist and that the
/// `From` conversion wires through to the `Lower` arm, so callers can
/// distinguish lowering failures from backend failures.
#[test]
fn test_dpvl_error_from_lower_error_variant() {
    use picus_smt::poly_ir::LowerError;
    fn classify(e: &DpvlError) -> &'static str {
        match e {
            DpvlError::Lower(_) => "lower",
            DpvlError::Backend(_) => "backend",
        }
    }
    let lower = LowerError::WireOutOfBounds {
        wire: 99,
        n_wires: 4,
        ctx: "unit-test",
    };
    let e: DpvlError = lower.into();
    assert_eq!(classify(&e), "lower");

    let be = DpvlError::Backend("backend init failed".into());
    assert_eq!(classify(&be), "backend");
}

// ---------------------------------------------------------------------------
// run_dpvl — end-to-end driver tests.
//
// These exercise the loop layered in `DpvlContext::iterate` directly, not
// just the per-piece config plumbing covered above:
//   * the `r1cs_to_poly_ir` lowering call (and its `LowerError` -> `DpvlError`
//     conversion),
//   * `create_backend` (and its `Err` -> `DpvlError::Backend` conversion),
//   * the `target_set.iter().all(|t| ks.contains(t))` early-Safe exit when
//     outputs are empty / inputs-only,
//   * the `backend.is_none()` early-Unknown exit when running propagation-only,
//   * `DpvlResult` Clone / Debug.
// ---------------------------------------------------------------------------

use picus_r1cs::grammar::{
    Constraint, ConstraintBlock, ConstraintSection, HeaderSection, R1csFile, W2lSection,
};

fn block(pairs: &[(u32, u32)]) -> ConstraintBlock {
    let wire_ids: Vec<u32> = pairs.iter().map(|&(w, _)| w).collect();
    let factors: Vec<BigUint> = pairs.iter().map(|&(_, f)| BigUint::from(f)).collect();
    ConstraintBlock {
        nnz: wire_ids.len() as u32,
        wire_ids,
        factors,
    }
}

/// Build a minimal R1CS with a single trivial `1 * 1 = 1` constraint over
/// GF(`p`) with `n_wires` wires, the given `inputs` and `outputs`. Used as
/// scaffolding to drive `run_dpvl` end-to-end with no real propagation
/// content — the tests below assert only on the Safe/Unknown/error shape
/// that comes from the loop wiring, not on solver output.
fn trivial_r1cs(p: u64, n_wires: u32, inputs: Vec<usize>, outputs: Vec<usize>) -> R1csFile {
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(p),
        n_wires,
        n_pub_out: outputs.len() as u32,
        n_pub_in: (inputs.len() as u32).saturating_sub(1),
        n_prv_in: 0,
        n_labels: n_wires as u64,
        m_constraints: 1,
    };
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
        w2l: W2lSection {
            labels: (0..n_wires as u64).collect(),
        },
        inputs,
        outputs,
    }
}

/// Build an R1CS whose constraint block references a wire id beyond
/// `n_wires`. The lowering step (`r1cs_to_poly_ir`) must reject this and
/// `run_dpvl` must surface it as `DpvlError::Lower`, not panic.
fn r1cs_with_oob_wire() -> R1csFile {
    let n_wires: u32 = 2;
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: n_wires as u64,
        m_constraints: 1,
    };
    // Wire id 9 is way past `n_wires=2`. `block_to_linear` should reject.
    let constraints = vec![Constraint {
        a: block(&[(9, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(0, 0)]),
    }];
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1],
        },
        inputs: vec![0],
        outputs: vec![],
    }
}

/// `run_dpvl` should propagate a `LowerError` from `r1cs_to_poly_ir`
/// through the `#[from]` impl on `DpvlError::Lower`. The choice of
/// solver is irrelevant — lowering happens before backend creation.
#[test]
fn test_run_dpvl_lowering_error_surfaces_as_dpvl_error_lower() {
    let r = r1cs_with_oob_wire();
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg);
    match result {
        Err(DpvlError::Lower(_)) => {}
        other => panic!("expected DpvlError::Lower, got {:?}", other),
    }
}

/// `SolverKind::Native` + `Theory::Nia` is rejected by
/// `validate_combination`; `create_backend` returns `Err`, which
/// `run_dpvl` maps via `DpvlError::Backend`.
#[test]
fn test_run_dpvl_invalid_solver_theory_combo_surfaces_as_backend_error() {
    let r = trivial_r1cs(7, 2, vec![0], vec![]);
    let cfg = DpvlConfig {
        solver: SolverKind::Native,
        theory: Theory::Nia,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg);
    match result {
        Err(DpvlError::Backend(_)) => {}
        other => panic!("expected DpvlError::Backend, got {:?}", other),
    }
}

/// Empty outputs ⇒ target set is empty ⇒ the
/// `target_set.iter().all(|t| ks.contains(t))` quantifier is vacuously
/// true on the first loop iteration ⇒ `DpvlResult::Safe` returns
/// immediately. Drives the early-Safe exit with neither propagation nor
/// backend involvement.
#[test]
fn test_run_dpvl_empty_target_set_returns_safe() {
    let r = trivial_r1cs(7, 2, vec![0], vec![]);
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Safe),
        "empty outputs ⇒ vacuously-Safe; got {:?}",
        result
    );
}

/// Output wire is also an input ⇒ already in `ks` ⇒ Safe on the first
/// iteration. This is the "target already known" early-Safe exit,
/// distinct from the empty-target-set one above.
#[test]
fn test_run_dpvl_target_is_input_returns_safe() {
    // n_wires=2, wire 0 = one, wire 1 is BOTH input and output.
    let r = trivial_r1cs(7, 2, vec![0, 1], vec![1]);
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Safe),
        "target ∈ inputs ⇒ Safe; got {:?}",
        result
    );
}

/// Outputs not all known + `SolverKind::None` ⇒ `backend.is_none()` ⇒
/// returns `Unknown` without ever calling `select` / `solve`. Drives the
/// propagation-only no-backend early-Unknown exit.
#[test]
fn test_run_dpvl_no_backend_with_unknown_target_returns_unknown() {
    // wire 1 is an output but NOT an input ⇒ stays in `us` after the
    // (no-op) propagation round ⇒ backend.is_none() ⇒ Unknown.
    let r = trivial_r1cs(7, 2, vec![0], vec![1]);
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        // LemmaSet::none() ⇒ `lemmas.is_empty()` ⇒ propagate is skipped,
        // exercising that branch too.
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Unknown),
        "no backend + unknown target ⇒ Unknown; got {:?}",
        result
    );
}

/// Same as the prior test, but with `LemmaSet::all()` so the
/// `lemmas.is_empty()` guard is FALSE and `propagate` IS called. Still
/// no backend, so still `Unknown` — but this exercises the other arm of
/// the empty-lemmas branch (propagate runs but doesn't promote the
/// output wire to known, because it isn't derivable from the trivial
/// `1*1=1` constraint).
#[test]
fn test_run_dpvl_propagation_runs_but_target_unreached_returns_unknown() {
    let r = trivial_r1cs(7, 2, vec![0], vec![1]);
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::all(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Unknown),
        "propagation can't reach wire 1 from trivial constraint; got {:?}",
        result
    );
}

/// `apply_overlay` with `solver = Some("native")` parses through
/// `SolverKind::from_str` and updates the field. Covers the `solver`
/// arm of `apply_overlay` (the all-fields drift-guard test doesn't
/// isolate it).
#[test]
fn test_apply_overlay_solver_field_only() {
    let mut cfg = DpvlConfig::default();
    cfg.solver = SolverKind::None;
    let overlay = DpvlOverlay {
        solver: Some("native".to_string()),
        ..Default::default()
    };
    cfg.apply_overlay(&overlay).expect("native is a valid solver");
    assert_eq!(cfg.solver, SolverKind::Native);
}

/// `apply_overlay` with `theory = Some("nia")` parses through
/// `Theory::from_str` and updates the field.
#[test]
fn test_apply_overlay_theory_field_only() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        theory: Some("nia".to_string()),
        ..Default::default()
    };
    cfg.apply_overlay(&overlay).expect("nia is a valid theory");
    assert_eq!(cfg.theory, Theory::Nia);
}

/// Bad solver name in overlay surfaces as an `Err`, not a silent
/// default — mirrors the existing bad-selector / bad-lemmas tests.
#[test]
fn test_apply_overlay_bad_solver_errors() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        solver: Some("not-a-solver".to_string()),
        ..Default::default()
    };
    assert!(cfg.apply_overlay(&overlay).is_err());
}

/// Bad theory name in overlay surfaces as an `Err`.
#[test]
fn test_apply_overlay_bad_theory_errors() {
    let mut cfg = DpvlConfig::default();
    let overlay = DpvlOverlay {
        theory: Some("not-a-theory".to_string()),
        ..Default::default()
    };
    assert!(cfg.apply_overlay(&overlay).is_err());
}

/// `dump_smt` set in isolation lands on the config; other fields keep
/// their defaults.
#[test]
fn test_apply_overlay_dump_smt_field_only() {
    let mut cfg = DpvlConfig::default();
    let p = PathBuf::from("/tmp/picus-dump-smt-only");
    let overlay = DpvlOverlay {
        dump_smt: Some(p.clone()),
        ..Default::default()
    };
    cfg.apply_overlay(&overlay).expect("apply");
    assert_eq!(cfg.dump_smt, Some(p));
    let d = DpvlConfig::default();
    assert_eq!(cfg.solver, d.solver);
    assert_eq!(cfg.theory, d.theory);
    assert_eq!(cfg.selector, d.selector);
    assert_eq!(cfg.timeout_ms, d.timeout_ms);
}

/// `apply_overlay` is monotone in the order applied: a later layer
/// overrides an earlier layer. The doc comment ("Merged via
/// `apply_overlay`; later layers win.") pins this directly.
#[test]
fn test_apply_overlay_later_layer_wins() {
    let mut cfg = DpvlConfig::default();
    let first = DpvlOverlay {
        timeout_ms: Some(1000),
        selector: Some("first".to_string()),
        ..Default::default()
    };
    let second = DpvlOverlay {
        timeout_ms: Some(2000),
        ..Default::default()
    };
    cfg.apply_overlay(&first).expect("first");
    cfg.apply_overlay(&second).expect("second");
    assert_eq!(cfg.timeout_ms, 2000, "later layer overrides timeout_ms");
    assert_eq!(
        cfg.selector,
        SelectorKind::First,
        "untouched field keeps the prior layer's value"
    );
}

/// `DpvlOverlay::default()` is all-None — exercises the `Default` impl
/// (`#[derive(Default)]` does fire here but it's worth a regression pin
/// so a future hand-written impl can't silently flip a field).
#[test]
fn test_dpvl_overlay_default_is_all_none() {
    let o = DpvlOverlay::default();
    assert!(o.solver.is_none());
    assert!(o.theory.is_none());
    assert!(o.selector.is_none());
    assert!(o.timeout_ms.is_none());
    assert!(o.lemmas.is_none());
    assert!(o.dump_smt.is_none());
}

/// `DpvlError`'s `Display` impl: `Lower(e)` delegates to `e`'s display
/// (prefixed) and `Backend(s)` echoes `s`. Exercises `thiserror`'s
/// generated `Display`.
#[test]
fn test_dpvl_error_display_strings() {
    use picus_smt::poly_ir::LowerError;
    let lower = DpvlError::Lower(LowerError::WireOutOfBounds {
        wire: 7,
        n_wires: 4,
        ctx: "ut",
    });
    let lower_str = format!("{}", lower);
    assert!(
        lower_str.contains("R1CS lowering failed"),
        "Lower display should mention 'R1CS lowering failed', got '{}'",
        lower_str
    );
    let backend = DpvlError::Backend("oops".to_string());
    assert_eq!(format!("{}", backend), "oops");
}

/// `DpvlResult` is `Clone + Debug`. The `Unsafe` arm carries a model
/// `HashMap` — clone it and check the contents survive.
#[test]
fn test_dpvl_result_clone_preserves_variant_and_payload() {
    let safe = DpvlResult::Safe;
    let _ = safe.clone();
    let unknown = DpvlResult::Unknown;
    let _ = unknown.clone();

    let mut model: HashMap<String, BigUint> = HashMap::new();
    model.insert("x1".to_string(), BigUint::from(42u32));
    let unsafe_r = DpvlResult::Unsafe(model.clone());
    let cloned = unsafe_r.clone();
    match cloned {
        DpvlResult::Unsafe(m) => {
            assert_eq!(m.get("x1"), Some(&BigUint::from(42u32)));
        }
        other => panic!("expected Unsafe, got {:?}", other),
    }
}

/// Drift guard for `DpvlError` shape: a non-exhaustive `match` here
/// must remain exhaustive across all error variants. Adding a third
/// variant would force this test to be updated, surfacing the new
/// error class at review time.
#[test]
fn test_dpvl_error_variant_set_is_pinned() {
    fn enumerate(e: &DpvlError) -> u8 {
        match e {
            DpvlError::Lower(_) => 1,
            DpvlError::Backend(_) => 2,
        }
    }
    assert_eq!(enumerate(&DpvlError::Backend("x".into())), 2);
}

/// `parse` allows a single bare name (no commas) — confirms the
/// `s[..]` fallback when the input has neither `all-` nor `none+`
/// prefix. (`prop_lemma_set_parse_bare_list_equals_none_plus` covers
/// multi-name; this one covers the single-name case explicitly.)
#[test]
fn test_lemma_set_parse_single_bare_name() {
    let s = LemmaSet::parse("linear").unwrap();
    assert!(s.is_enabled("linear"));
    for n in all_names() {
        if n != "linear" {
            assert!(!s.is_enabled(n), "{} should not be enabled", n);
        }
    }
}

/// `parse` accepts whitespace around individual names in a CSV list.
/// `name.trim()` is applied per element, so ` linear , binary01 ` is
/// equivalent to `linear,binary01`.
#[test]
fn test_lemma_set_parse_trims_csv_elements() {
    let s = LemmaSet::parse("  linear , binary01  ").unwrap();
    assert!(s.is_enabled("linear"));
    assert!(s.is_enabled("binary01"));
}

/// `parse` accepts whitespace around names inside an `all-…` list.
#[test]
fn test_lemma_set_parse_all_minus_trims() {
    let s = LemmaSet::parse("all- linear , binary01 ").unwrap();
    assert!(!s.is_enabled("linear"));
    assert!(!s.is_enabled("binary01"));
}

/// `parse` accepts whitespace inside a `none+…` list, same trim rule.
#[test]
fn test_lemma_set_parse_none_plus_trims() {
    let s = LemmaSet::parse("none+  linear , binary01 ").unwrap();
    assert!(s.is_enabled("linear"));
    assert!(s.is_enabled("binary01"));
}

/// Build an R1CS over GF(7) where output wire 2 is forced equal to
/// input wire 1 via the constraint `wire1 * 1 = wire2`. The `linear`
/// propagation lemma must recognise this and promote wire 2 to known
/// without ever invoking the backend.
fn linear_forced_r1cs() -> R1csFile {
    // n_wires = 3:  w0=one, w1=input, w2=output.
    let n_wires: u32 = 3;
    let header = HeaderSection {
        field_size: 32,
        prime_number: BigUint::from(7u32),
        n_wires,
        n_pub_out: 1,
        n_pub_in: 1,
        n_prv_in: 0,
        n_labels: n_wires as u64,
        m_constraints: 1,
    };
    // (1 * w1) * (1 * w0) = (1 * w2), i.e. w1 = w2.
    let constraints = vec![Constraint {
        a: block(&[(1, 1)]),
        b: block(&[(0, 1)]),
        c: block(&[(2, 1)]),
    }];
    R1csFile {
        magic: *b"r1cs",
        version: 1,
        n_sections: 3,
        header,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection {
            labels: vec![0, 1, 2],
        },
        inputs: vec![0, 1],
        outputs: vec![2],
    }
}

/// End-to-end Safe via propagation alone: the `linear` lemma promotes
/// the output wire once it sees the forced equality, so target_set ends
/// up a subset of `ks` before the backend is ever consulted. Drives
/// the `propagate` fixed-point loop's "made_progress" branch.
#[test]
fn test_run_dpvl_propagation_promotes_target_returns_safe() {
    let r = linear_forced_r1cs();
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::all(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Safe),
        "linear lemma should promote w2 from w1 ⇒ Safe; got {:?}",
        result
    );
}

/// Same R1CS as the propagation-Safe test, but with `LemmaSet::none()`
/// disabling every lemma. Without lemmas the output wire stays
/// unknown, and `SolverKind::None` ⇒ `Unknown`. Confirms the previous
/// test's Safe verdict is actually coming from a lemma rather than
/// some other promotion path.
#[test]
fn test_run_dpvl_propagation_disabled_misses_promotion() {
    let r = linear_forced_r1cs();
    let cfg = DpvlConfig {
        solver: SolverKind::None,
        theory: Theory::Ff,
        selector: SelectorKind::Counter,
        timeout_ms: 100,
        lemmas: LemmaSet::none(),
        dump_smt: None,
    };
    let result = run_dpvl(&r, &cfg).expect("run_dpvl");
    assert!(
        matches!(result, DpvlResult::Unknown),
        "no lemmas + no backend ⇒ Unknown; got {:?}",
        result
    );
}

/// `parse` error message lists the valid lemmas, so a CLI typo can
/// see the available choices. Order should be sorted (the impl sorts
/// before joining).
#[test]
fn test_lemma_set_parse_error_lists_valid_names() {
    let err = LemmaSet::parse("nope").unwrap_err();
    assert!(err.contains("Valid"), "error should list valid names: '{}'", err);
    // At least one well-known registered lemma name shows up.
    assert!(
        err.contains("linear") || err.contains("binary01") || err.contains("aboz"),
        "error should mention at least one registered lemma; got '{}'",
        err
    );
}

