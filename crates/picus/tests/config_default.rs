//! The shipped `picus.default.toml` must mirror the compiled defaults:
//! parsing it as an overlay and applying it onto `PicusConfig::default()`
//! must reproduce `PicusConfig::default()`. This keeps the documented
//! config file honest as knobs are added.

use picus::{PicusConfig, ReprKind, SolverKind};

const DEFAULT_TOML: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../picus.default.toml"));

#[test]
fn default_toml_matches_compiled_defaults() {
    let overlay =
        PicusConfig::parse_overlay_toml(DEFAULT_TOML).expect("picus.default.toml parses");
    let mut cfg = PicusConfig::default();
    cfg.apply_overlay(&overlay).expect("overlay applies");
    assert_eq!(
        cfg,
        PicusConfig::default(),
        "picus.default.toml drifted from PicusConfig::default(); update the file"
    );
}

#[test]
fn unknown_key_is_rejected() {
    let bad = "[engine]\nnot_a_real_knob = true\n";
    assert!(PicusConfig::parse_overlay_toml(bad).is_err());
}

#[test]
fn partial_overlay_only_overrides_present_fields() {
    let toml = "[analysis]\nsolver = \"native\"\n[engine]\nuse_f4 = true\n";
    let overlay = PicusConfig::parse_overlay_toml(toml).unwrap();
    let mut cfg = PicusConfig::default();
    cfg.apply_overlay(&overlay).unwrap();
    // Present keys override.
    assert_eq!(cfg.analysis.solver, SolverKind::Native);
    assert!(cfg.engine.use_f4);
    // Absent keys keep the base values.
    let base = PicusConfig::default();
    assert_eq!(cfg.analysis.timeout_ms, base.analysis.timeout_ms);
    assert_eq!(cfg.engine.poly_repr, base.engine.poly_repr);
    assert_eq!(cfg.engine.poly_repr, ReprKind::Sparse);
}

#[test]
fn bad_enum_value_is_a_config_error() {
    let toml = "[analysis]\nsolver = \"nope\"\n";
    let overlay = PicusConfig::parse_overlay_toml(toml).unwrap();
    let mut cfg = PicusConfig::default();
    assert!(cfg.apply_overlay(&overlay).is_err());
}
