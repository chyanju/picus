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
