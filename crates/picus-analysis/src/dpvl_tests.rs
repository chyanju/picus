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
