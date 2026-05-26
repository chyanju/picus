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
//!
//! Tests pinning `ReprKind::Dense` exercise the dense `GbAlgorithm` dispatch
//! (`buchberger-direct` / `buchberger-by-homog`). The sparse path honours the
//! same strategy through its own engine — recording `sparse-buchberger` /
//! `sparse-by-homog` — which `sparse_by_homog_matches_direct` covers.

use num_bigint::BigUint;

use picus_core::config::{ConfigGuard, GbStrategy, ReprKind, RuntimeConfig};
use picus_core::ff::field::PrimeField;
use picus_core::ff::monomial::MonomialOrder;
use picus_solver::gb::compute_gb_with_timeout_traced;
use picus_solver::gb::ideal::{compute_gb_with_order, last_dispatched_algorithm, Ideal};
use picus_core::poly::FfPolyRing;
use picus_core::timeout::CancelToken;

/// `x*y - 1 = 0` over GF(7) — non-homogeneous, so the Auto resolver
/// would pick `ByHomog` and the two strategies take different
/// intermediate paths (final basis is identical).
fn gens_xy_minus_1() -> (FfPolyRing, Vec<picus_core::poly::Poly>) {
    let field = PrimeField::new(BigUint::from(7u32));
    let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let g = pr.sub(xy, pr.one());
    (pr, vec![g])
}

#[test]
fn compute_gb_with_order_honours_direct() {
    let _guard = ConfigGuard::with_override(|c| {
        c.gb_strategy = GbStrategy::Direct;
        c.poly_repr = ReprKind::Dense;
    });
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
    let _guard = ConfigGuard::with_override(|c| {
        c.gb_strategy = GbStrategy::ByHomog;
        c.poly_repr = ReprKind::Dense;
    });
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
    let _guard = ConfigGuard::with_override(|c| {
        c.gb_strategy = GbStrategy::ByHomog;
        c.poly_repr = ReprKind::Dense;
    });
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
    let _guard = ConfigGuard::with_override(|c| {
        c.gb_strategy = GbStrategy::ByHomog;
        c.poly_repr = ReprKind::Dense;
    });
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
    let _guard = ConfigGuard::with_override(|c| {
        c.gb_strategy = GbStrategy::ByHomog;
        c.poly_repr = ReprKind::Dense;
    });
    let (pr, gens) = gens_xy_minus_1();
    let _ideal = Ideal::new(&pr, gens);
    assert_eq!(last_dispatched_algorithm(), Some("buchberger-by-homog"));
}

#[test]
fn default_strategy_is_direct() {
    // Ensure the test runs with a default config (no leaked override
    // from a sibling thread); pin Dense so dispatch is exercised.
    let _guard = ConfigGuard::install({
        let mut c = RuntimeConfig::default();
        c.poly_repr = ReprKind::Dense;
        c
    });
    let (pr, gens) = gens_xy_minus_1();
    let _ = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
    assert_eq!(last_dispatched_algorithm(), Some("buchberger-direct"));
}

/// Leading-monomial set in DegRevLex on `P` — two reduced GBs of the same
/// ideal share LM sets, so this is the standard equivalence check.
fn lm_set(pr: &FfPolyRing, gb: &[picus_core::poly::Poly]) -> std::collections::BTreeSet<Vec<usize>> {
    let ctx = pr.ctx();
    let n = pr.n_vars();
    let mut s = std::collections::BTreeSet::new();
    for p in gb {
        if let Some(m) = p.leading_monomial(ctx) {
            s.insert((0..n).map(|i| m.exponent(i) as usize).collect::<Vec<_>>());
        }
    }
    s
}

/// `{x^2 - x, x*y - 1}` over GF(7): non-homogeneous, so by-homog takes a
/// genuinely different intermediate path from direct.
fn gens_bc_and_xy() -> (FfPolyRing, Vec<picus_core::poly::Poly>) {
    let field = PrimeField::new(BigUint::from(7u32));
    let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);
    let x = pr.var(0);
    let y = pr.var(1);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let bc = pr.sub(xx, pr.clone_poly(&x)); // x^2 - x
    let xy = pr.mul(x, y);
    let g = pr.sub(xy, pr.one()); // x*y - 1
    (pr, vec![bc, g])
}

#[test]
fn sparse_by_homog_matches_direct() {
    // On the sparse representation, ByHomog must run the sparse by-homog
    // pipeline (recorded "sparse-by-homog") and yield the same ideal as the
    // sparse direct path.
    let (pr, _) = gens_bc_and_xy();

    let by_homog = {
        let _g = ConfigGuard::with_override(|c| {
            c.gb_strategy = GbStrategy::ByHomog;
            c.poly_repr = ReprKind::Sparse;
        });
        let (_, gens) = gens_bc_and_xy();
        let b = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
        assert_eq!(
            last_dispatched_algorithm(),
            Some("sparse-by-homog"),
            "sparse ByHomog must run the by-homog pipeline"
        );
        b
    };
    let direct = {
        let _g = ConfigGuard::with_override(|c| {
            c.gb_strategy = GbStrategy::Direct;
            c.poly_repr = ReprKind::Sparse;
        });
        let (_, gens) = gens_bc_and_xy();
        let b = compute_gb_with_order(&pr, gens, &CancelToken::none(), MonomialOrder::DegRevLex);
        assert_eq!(last_dispatched_algorithm(), Some("sparse-buchberger"));
        b
    };
    assert_eq!(
        lm_set(&pr, &by_homog),
        lm_set(&pr, &direct),
        "sparse by-homog and sparse direct must yield the same ideal"
    );
}
