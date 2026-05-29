use super::*;
use crate::config::{ConfigGuard, GbStrategy, RuntimeConfig};
use crate::ff::field::PrimeField;
use crate::poly::FfPolyRing;
use num_bigint::BigUint;

fn pr3() -> FfPolyRing {
    FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into(), "z".into()],
    )
}

// ────────── is_total_deg_homogeneous ──────────

#[test]
fn homogeneous_empty_poly_is_homogeneous() {
    let pr = pr3();
    let p = pr.zero();
    assert!(is_total_deg_homogeneous(&pr, &p));
}

#[test]
fn homogeneous_constant_is_homogeneous() {
    let pr = pr3();
    let p = pr.one();
    assert!(is_total_deg_homogeneous(&pr, &p));
}

#[test]
fn homogeneous_pure_quadratic_is_homogeneous() {
    // x*y + y*z + x*z (all total-deg 2)
    let pr = pr3();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let yz = pr.mul(pr.var(1), pr.var(2));
    let xz = pr.mul(pr.var(0), pr.var(2));
    let p = pr.add(pr.add(xy, yz), xz);
    assert!(is_total_deg_homogeneous(&pr, &p));
}

#[test]
fn homogeneous_mixed_degree_is_not_homogeneous() {
    // x^2 + y (degs 2 and 1)
    let pr = pr3();
    let xx = pr.mul(pr.var(0), pr.var(0));
    let p = pr.add(xx, pr.var(1));
    assert!(!is_total_deg_homogeneous(&pr, &p));
}

#[test]
fn homogeneous_linear_plus_const_is_not_homogeneous() {
    // x + 1 (degs 1 and 0)
    let pr = pr3();
    let p = pr.add(pr.var(0), pr.one());
    assert!(!is_total_deg_homogeneous(&pr, &p));
}

// ────────── resolve_auto ──────────

#[test]
fn resolve_auto_all_homog_picks_direct() {
    let pr = pr3();
    // All-quadratic-homogeneous generator set.
    let p1 = pr.mul(pr.var(0), pr.var(0));
    let p2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![p1, p2];
    assert_eq!(resolve_auto(&pr, &gens), GbStrategy::Direct);
}

#[test]
fn resolve_auto_mixed_degree_picks_by_homog() {
    let pr = pr3();
    let xx = pr.mul(pr.var(0), pr.var(0));
    // Non-homogeneous: x^2 + 1.
    let p1 = pr.add(xx, pr.one());
    let gens = vec![p1];
    assert_eq!(resolve_auto(&pr, &gens), GbStrategy::ByHomog);
}

#[test]
fn resolve_auto_empty_input_picks_direct() {
    let pr = pr3();
    assert_eq!(resolve_auto(&pr, &[]), GbStrategy::Direct);
}

#[test]
fn resolve_auto_skips_zero_polys() {
    // Zero polynomials don't disqualify the all-homogeneous check.
    let pr = pr3();
    let zero = pr.zero();
    let xx = pr.mul(pr.var(0), pr.var(0));
    let gens = vec![zero, xx];
    assert_eq!(resolve_auto(&pr, &gens), GbStrategy::Direct);
}

// ────────── resolve_strategy (via ConfigGuard) ──────────

#[test]
fn resolve_strategy_direct_is_passthrough() {
    let pr = pr3();
    let mut c = RuntimeConfig::default();
    c.gb_strategy = GbStrategy::Direct;
    let _g = ConfigGuard::install(c);
    // Even non-homogeneous gens get Direct.
    let p = pr.add(pr.var(0), pr.one());
    assert_eq!(resolve_strategy(&pr, &[p]), GbStrategy::Direct);
}

#[test]
fn resolve_strategy_by_homog_is_passthrough() {
    let pr = pr3();
    let mut c = RuntimeConfig::default();
    c.gb_strategy = GbStrategy::ByHomog;
    let _g = ConfigGuard::install(c);
    let p = pr.mul(pr.var(0), pr.var(0));
    assert_eq!(resolve_strategy(&pr, &[p]), GbStrategy::ByHomog);
}

#[test]
fn resolve_strategy_auto_expands_via_resolve_auto() {
    let pr = pr3();
    let mut c = RuntimeConfig::default();
    c.gb_strategy = GbStrategy::Auto;
    let _g = ConfigGuard::install(c);
    let p = pr.add(pr.var(0), pr.one()); // non-homogeneous
    assert_eq!(resolve_strategy(&pr, &[p]), GbStrategy::ByHomog);
}

// ────────── unwrap_dense_vec / wrap_dense_vec round-trip ──────────

#[test]
fn dense_vec_round_trip_preserves_polys() {
    let pr = pr3();
    let order = FfOrder::DegRevLex;
    let ring = ring_for_order(&pr, order);
    // Two arbitrary polys.
    let p1 = pr.mul(pr.var(0), pr.var(1));
    let p2 = pr.add(pr.var(2), pr.one());
    let polys = vec![p1, p2];
    let dense = unwrap_dense_vec(polys.clone(), &ring);
    assert_eq!(dense.len(), 2);
    let wrapped = wrap_dense_vec(dense);
    assert_eq!(wrapped.len(), 2);
}

// ────────── finish_gb (cancel vs error semantics) ──────────

#[test]
fn finish_gb_returns_backup_on_cancel() {
    let pr = pr3();
    let backup = vec![pr.var(0)];
    let cancel = CancelToken::cancelled();
    let out = finish_gb(
        Err(EngineError::Internal("simulated".into())),
        &cancel,
        backup.clone(),
        "test",
    );
    // On cancel, the backup is returned (caller's is_cancelled() check
    // discards it; we just verify the path here).
    assert_eq!(out.len(), backup.len());
}

#[test]
fn finish_gb_returns_empty_on_genuine_error() {
    let pr = pr3();
    let backup = vec![pr.var(0)];
    let cancel = CancelToken::none();
    let out = finish_gb(
        Err(EngineError::Internal("simulated".into())),
        &cancel,
        backup,
        "test",
    );
    // Without cancel, a genuine engine error must yield an empty
    // basis (downstream cannot mistake unreduced gens for a GB).
    assert!(out.is_empty(), "expected empty basis on engine error");
}

#[test]
fn finish_gb_passes_through_on_ok() {
    let pr = pr3();
    let basis = vec![pr.var(0), pr.var(1)];
    let cancel = CancelToken::none();
    let out = finish_gb(Ok(basis.clone()), &cancel, vec![], "test");
    assert_eq!(out.len(), basis.len());
}

// ────────── last_dispatched_algorithm thread-local ──────────

#[test]
fn last_dispatched_records_chosen_algorithm() {
    let pr = pr3();
    let _g = ConfigGuard::install({
        let mut c = RuntimeConfig::default();
        c.gb_strategy = GbStrategy::Direct;
        c
    });
    // Run a small GB to set the thread-local.
    let p = pr.mul(pr.var(0), pr.var(1));
    let _ = compute_gb_with_order(&pr, vec![p], &CancelToken::none(), FfOrder::DegRevLex);
    let name = last_dispatched_algorithm();
    assert!(
        name.is_some(),
        "last_dispatched_algorithm should be populated"
    );
}
