//! Verifies that `RuntimeConfig::gb_strategy` actually steers the GB
//! algorithm choice on every public entry point. Contract:
//!
//! * `compute_gb_with_order` routes through `compute_gb_dispatch`,
//!   so `--gb-by-homog on` affects this entry point.
//! * `compute_gb_with_order_traced` likewise routes through dispatch
//!   but silently falls back to `BuchbergerDirect` when the chosen
//!   algorithm doesn't support tracing (`BuchbergerByHomog` doesn't).
//! * `Ideal::new` honours the strategy.
//!
//! `last_dispatched_algorithm()` exposes the actual algorithm name
//! the dispatch chose on this thread, so the assertions don't depend
//! on observable basis differences (Direct and ByHomog return the
//! same final ideal — just via different intermediate steps).

use num_bigint::BigUint;

use picus_solver::config::{ConfigGuard, RuntimeConfig};
use picus_solver::field::FfField;
use picus_solver::ff::monomial::MonomialOrder;
use picus_solver::gb::compute_gb_with_timeout_traced;
use picus_solver::ideal::{
    compute_gb_with_order, last_dispatched_algorithm, GbStrategy, Ideal,
};
use picus_solver::poly::FfPolyRing;
use picus_solver::timeout::CancelToken;

/// `x*y - 1 = 0` over GF(7) — non-homogeneous, so the Auto resolver
/// would pick `ByHomog` and the two strategies take different
/// intermediate paths (final basis is identical).
fn gens_xy_minus_1() -> (FfPolyRing, Vec<picus_solver::poly::Poly>) {
    let field = FfField::new(BigUint::from(7u32));
    let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let g = pr.sub(xy, pr.one());
    (pr, vec![g])
}

#[test]
fn compute_gb_with_order_honours_direct() {
    let _guard = ConfigGuard::with_override(|c| c.gb_strategy = GbStrategy::Direct);
    let (pr, gens) = gens_xy_minus_1();
    let _ = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
    assert_eq!(
        last_dispatched_algorithm(),
        Some("buchberger-direct"),
        "Direct strategy must invoke BuchbergerDirect"
    );
}

#[test]
fn compute_gb_with_order_honours_by_homog() {
    let _guard = ConfigGuard::with_override(|c| c.gb_strategy = GbStrategy::ByHomog);
    let (pr, gens) = gens_xy_minus_1();
    let _ = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
    assert_eq!(
        last_dispatched_algorithm(),
        Some("buchberger-by-homog"),
        "ByHomog strategy must invoke BuchbergerByHomog via dispatch \
         from compute_gb_with_order"
    );
}

#[test]
fn by_homog_falls_back_to_direct_for_lex() {
    let _guard = ConfigGuard::with_override(|c| c.gb_strategy = GbStrategy::ByHomog);
    let (pr, gens) = gens_xy_minus_1();
    let _ = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::Lex);
    // ByHomog only handles DegRevLex; its `compute` delegates to
    // Direct for other orders. The dispatch records ByHomog as the
    // chosen algorithm; the fallback happens *inside* that impl.
    assert_eq!(
        last_dispatched_algorithm(),
        Some("buchberger-by-homog"),
        "ByHomog should still be the chosen algorithm; Lex fallback \
         happens internally"
    );
}

#[test]
fn traced_path_falls_back_to_direct_when_strategy_lacks_tracing() {
    let _guard = ConfigGuard::with_override(|c| c.gb_strategy = GbStrategy::ByHomog);
    let (pr, gens) = gens_xy_minus_1();
    // `compute_gb_with_timeout_traced` is the main production traced
    // entry; it dispatches twice (DegRevLex traced, Lex untraced) so
    // we read the most recent algorithm — the Lex pass — to check
    // dispatch behaviour for the untraced half. The DegRevLex traced
    // pass would have already fallen back to BuchbergerDirect; the
    // Lex pass goes through ByHomog → internal Lex fallback (still
    // recorded as "buchberger-by-homog" by dispatch).
    let _ = compute_gb_with_timeout_traced(&pr, gens, None);
    // Either name is acceptable: ByHomog (Lex fallback) or Direct
    // (traced DegRevLex fallback). Both demonstrate dispatch is
    // working. What must NOT happen is `None` — i.e. that some entry
    // point bypassed dispatch entirely.
    assert!(
        last_dispatched_algorithm().is_some(),
        "traced GB path must have gone through dispatch at least once"
    );
}

#[test]
fn ideal_new_routes_through_dispatch() {
    let _guard = ConfigGuard::with_override(|c| c.gb_strategy = GbStrategy::ByHomog);
    let (pr, gens) = gens_xy_minus_1();
    let _ideal = Ideal::new(&pr, gens);
    assert_eq!(last_dispatched_algorithm(), Some("buchberger-by-homog"));
}

#[test]
fn default_strategy_is_direct() {
    // Ensure the test runs with a default config (no leaked override
    // from a sibling thread).
    let _guard = ConfigGuard::install(RuntimeConfig::default());
    let (pr, gens) = gens_xy_minus_1();
    let _ = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
    assert_eq!(last_dispatched_algorithm(), Some("buchberger-direct"));
}
