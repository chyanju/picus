use super::*;

/// Drift guard: every `EngineOverlay` field must be consumed by
/// `apply_overlay`. Sets every overlay field to a value distinct from
/// the compiled default and asserts the merged config equals an explicit
/// all-overridden `expected`. If a knob is added to `RuntimeConfig` /
/// `EngineOverlay` but not wired into `apply_overlay`, that field stays
/// at its default and the assert fails. The explicit struct literals
/// also fail to compile until the new field is added here, forcing this
/// test to track the config surface.
#[test]
fn apply_overlay_consumes_every_field() {
    let overlay = EngineOverlay {
        gb_strategy: Some(GbStrategy::ByHomog),
        use_f4: Some(true),
        dnf_cap: Some(42),
        dnf_enabled: Some(true),
        cdclt_iter_cap: Some(7),
        gb_stats_enabled: Some(true),
        gb_trace_enabled: Some(true),
        profile_enabled: Some(true),
        cache_enabled: Some(false),
        aboz_emit_disjunctions: Some(false),
        poly_repr: Some(ReprKind::Dense),
        linear_elim: Some(true),
        track_inter_reduce_deps: Some(false),
        split_triangular: Some(true),
        membership_fastpath: Some(true),
        matrix_elim_order: Some(true),
        dynamic_order: Some(true),
        reducer_index_cache: Some(true),
        frobenius_cache: Some(true),
        branching_incremental_gb: Some(true),
        cdclt_multi_prime_router: Some(true),
        cdclt_equality_engine: Some(true),
        f4_hilbert_select: Some(true),
        f4_sparse_reducer_cache: Some(true),
        cdclt_incremental_theory: Some(true),
    };
    let expected = RuntimeConfig {
        gb_strategy: GbStrategy::ByHomog,
        use_f4: true,
        dnf_cap: 42,
        dnf_enabled: true,
        cdclt_iter_cap: 7,
        gb_stats_enabled: true,
        gb_trace_enabled: true,
        profile_enabled: true,
        cache_enabled: false,
        aboz_emit_disjunctions: false,
        poly_repr: ReprKind::Dense,
        linear_elim: true,
        track_inter_reduce_deps: false,
        split_triangular: true,
        membership_fastpath: true,
        matrix_elim_order: true,
        dynamic_order: true,
        reducer_index_cache: true,
        frobenius_cache: true,
        branching_incremental_gb: true,
        cdclt_multi_prime_router: true,
        cdclt_equality_engine: true,
        f4_hilbert_select: true,
        f4_sparse_reducer_cache: true,
        cdclt_incremental_theory: true,
    };

    // Every chosen value must differ from the compiled default, so a
    // missed field would actually be observable.
    assert_ne!(
        expected,
        RuntimeConfig::default(),
        "test values must differ from defaults to be meaningful"
    );

    let mut cfg = RuntimeConfig::default();
    cfg.apply_overlay(&overlay);
    assert_eq!(
        cfg, expected,
        "apply_overlay did not propagate every overlay field"
    );
}
