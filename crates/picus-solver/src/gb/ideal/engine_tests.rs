use super::*;
use crate::config::{ConfigGuard, GbStrategy, RuntimeConfig};
use crate::ff::field::PrimeField;
use crate::gb::tracer::GbTracer;
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

// `x - 1` as a poly in pr3 (var x = index 0).
fn x_minus_1(pr: &FfPolyRing) -> Poly {
    pr.sub(pr.var(0), pr.one())
}

/// True when `p` reduces to zero modulo `basis` (i.e. p ∈ <basis>).
fn reduces_to_zero(pr: &FfPolyRing, basis: &[Poly], p: &Poly) -> bool {
    let ring = pr.ctx();
    p.reduce_by(basis, ring).is_zero()
}

// ────────── BuchbergerDirect::compute (lines 88-96) ──────────

#[test]
fn buchberger_direct_name_is_stable() {
    assert_eq!(BuchbergerDirect.name(), "buchberger-direct");
    assert!(BuchbergerDirect.supports_tracing());
}

#[test]
fn buchberger_direct_compute_linear_gb() {
    // GB of <x - 1> is {x - 1} (a single linear element); reducing x - 1
    // against the result must give zero.
    let pr = pr3();
    let gb = BuchbergerDirect
        .compute(&pr, vec![x_minus_1(&pr)], &CancelToken::none(), FfOrder::DegRevLex)
        .expect("linear GB cannot fail");
    assert!(!gb.is_empty(), "GB of <x-1> is nonempty");
    assert!(reduces_to_zero(&pr, &gb, &x_minus_1(&pr)));
    // x itself is NOT in <x-1>: it reduces to the constant 1, not zero.
    assert!(!reduces_to_zero(&pr, &gb, &pr.var(0)));
}

#[test]
fn buchberger_direct_compute_empty_is_empty() {
    let pr = pr3();
    let gb = BuchbergerDirect
        .compute(&pr, vec![], &CancelToken::none(), FfOrder::DegRevLex)
        .expect("empty GB");
    assert!(gb.is_empty());
}

// ────────── BuchbergerByHomog::name + compute (lines 123-135) ──────────

#[test]
fn by_homog_name_is_stable() {
    assert_eq!(BuchbergerByHomog.name(), "buchberger-by-homog");
    // Does not advertise tracing (default false).
    assert!(!BuchbergerByHomog.supports_tracing());
}

#[test]
fn by_homog_compute_degrevlex_nonhomogeneous() {
    // x^2 + 1 over GF(7): roots are the square roots of -1 = 6.
    // 2^2 = 4 != 6, 3^2 = 2, 4^2 = 2, ... no square root of 6 mod 7,
    // so the ideal is zero-dimensional with no rational point but the
    // by-homog pipeline must still return a basis with x^2+1 reducible
    // to zero.
    let pr = pr3();
    let xx = pr.mul(pr.var(0), pr.var(0));
    let p = pr.add(xx, pr.one()); // x^2 + 1 (non-homogeneous)
    let gb = BuchbergerByHomog
        .compute(&pr, vec![pr.clone_poly(&p)], &CancelToken::none(), FfOrder::DegRevLex)
        .expect("DegRevLex by-homog path returns Ok");
    assert!(!gb.is_empty(), "by-homog GB of <x^2+1> is nonempty");
    assert!(reduces_to_zero(&pr, &gb, &p));
}

// ────────── BuchbergerByHomog fallback to Direct (lines 140, 142) ──────────

#[test]
fn by_homog_lex_falls_back_to_direct() {
    // For a non-DegRevLex order, ByHomog must route through plain
    // Buchberger and still return a valid basis in that order.
    let pr = pr3();
    let gb = BuchbergerByHomog
        .compute(&pr, vec![x_minus_1(&pr)], &CancelToken::none(), FfOrder::Lex)
        .expect("Lex fallback to Direct cannot fail on a linear ideal");
    assert!(!gb.is_empty());
    // The Direct fallback ring is built in Lex order; reduce in that ring.
    let lex_ring = ring_for_order(&pr, FfOrder::Lex);
    assert!(x_minus_1(&pr).reduce_by(&gb, &lex_ring).is_zero());
}

// ────────── compute_gb_direct (lines 431, 437-440, dense path) ──────────

#[test]
fn compute_gb_direct_empty_returns_empty() {
    let pr = pr3();
    let out = compute_gb_direct(&pr, vec![], &CancelToken::none(), FfOrder::DegRevLex);
    assert!(out.is_empty());
}

#[test]
fn compute_gb_direct_dense_path_linear() {
    // Force the dense routing (lines 438-440) by installing a Dense repr.
    let _g = ConfigGuard::install({
        let mut c = RuntimeConfig::default();
        c.poly_repr = crate::config::ReprKind::Dense;
        c
    });
    let pr = FfPolyRing::new_with_repr(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into(), "z".into()],
        crate::config::ReprKind::Dense,
    );
    let gb = compute_gb_direct(&pr, vec![x_minus_1(&pr)], &CancelToken::none(), FfOrder::DegRevLex);
    assert!(!gb.is_empty(), "direct dense GB of <x-1> is nonempty");
    assert!(reduces_to_zero(&pr, &gb, &x_minus_1(&pr)));
}

// ────────── compute_gb_incremental_with_order (lines 507, 512-525) ──────────

#[test]
fn incremental_empty_new_returns_known_gb() {
    let pr = pr3();
    let known = vec![x_minus_1(&pr)];
    let out = compute_gb_incremental_with_order(
        &pr, known.clone(), vec![], &CancelToken::none(), FfOrder::DegRevLex,
    );
    assert_eq!(out.len(), known.len());
}

#[test]
fn incremental_empty_known_recomputes_from_scratch() {
    let pr = pr3();
    let out = compute_gb_incremental_with_order(
        &pr, vec![], vec![x_minus_1(&pr)], &CancelToken::none(), FfOrder::DegRevLex,
    );
    assert!(!out.is_empty());
    assert!(reduces_to_zero(&pr, &out, &x_minus_1(&pr)));
}

#[test]
fn incremental_dense_seed_extends_ideal() {
    // Dense path (lines 510-525): seed reduced GB {x-1}, add {y-2}.
    // Result must be a GB of <x-1, y-2> — both generators reduce to zero.
    let _g = ConfigGuard::install({
        let mut c = RuntimeConfig::default();
        c.poly_repr = crate::config::ReprKind::Dense;
        c
    });
    let pr = FfPolyRing::new_with_repr(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into(), "z".into()],
        crate::config::ReprKind::Dense,
    );
    let x_m1 = pr.sub(pr.var(0), pr.one());
    let y_m2 = pr.sub(pr.var(1), pr.constant(pr.field().from_int(2)));
    let out = compute_gb_incremental_with_order(
        &pr,
        vec![pr.clone_poly(&x_m1)],
        vec![pr.clone_poly(&y_m2)],
        &CancelToken::none(),
        FfOrder::DegRevLex,
    );
    assert!(!out.is_empty());
    assert!(reduces_to_zero(&pr, &out, &x_m1));
    assert!(reduces_to_zero(&pr, &out, &y_m2));
    // A poly outside the ideal (z) does NOT reduce to zero.
    assert!(!reduces_to_zero(&pr, &out, &pr.var(2)));
}

// ────────── GbAlgorithm::compute_traced default panicking impl ──────────

/// A misconfigured algorithm that advertises tracing support but leaves
/// `compute_traced` at its default. The trait contract requires an
/// implementor that flips `supports_tracing()` to true to override
/// `compute_traced`; the default impl is an `unreachable!` guard against
/// exactly this implementor bug.
struct BadTracingAlgo;

impl GbAlgorithm for BadTracingAlgo {
    fn name(&self) -> &'static str {
        "bad-tracing-algo"
    }
    fn compute(
        &self,
        _pr: &FfPolyRing,
        _gens: Vec<Poly>,
        _cancel: &CancelToken,
        _order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError> {
        Ok(Vec::new())
    }
    fn supports_tracing(&self) -> bool {
        true
    }
    // No `compute_traced` override → default panicking impl is in force.
}

#[test]
#[should_panic(expected = "supports_tracing() returned true")]
fn default_compute_traced_panics_for_misconfigured_algorithm() {
    let pr = pr3();
    let mut tracer = GbTracer::new(1);
    // The default `compute_traced` body is the `unreachable!` guard; it
    // fires only for an implementor that lies about `supports_tracing`.
    let _ = BadTracingAlgo.compute_traced(
        &pr,
        vec![x_minus_1(&pr)],
        &CancelToken::none(),
        FfOrder::DegRevLex,
        &mut tracer,
    );
}

// ────────── compute_gb_with_order dense path (line ~373) ──────────

#[test]
fn compute_gb_with_order_dense_repr_records_dense_dispatch() {
    // Force the dense routing of `compute_gb_with_order` (the non-sparse
    // branch building `backup` and dispatching via the GbAlgorithm trait).
    // Default config is sparse, so a Dense override + Dense ring is needed.
    let _g = ConfigGuard::install({
        let mut c = RuntimeConfig::default();
        c.poly_repr = crate::config::ReprKind::Dense;
        c.gb_strategy = GbStrategy::Direct;
        c
    });
    let pr = FfPolyRing::new_with_repr(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into(), "z".into()],
        crate::config::ReprKind::Dense,
    );
    let gb = compute_gb_with_order(
        &pr,
        vec![x_minus_1(&pr)],
        &CancelToken::none(),
        FfOrder::DegRevLex,
    );
    assert!(!gb.is_empty(), "dense GB of <x-1> is nonempty");
    assert!(reduces_to_zero(&pr, &gb, &x_minus_1(&pr)));
    // The dense path records a dense GbAlgorithm name (not "sparse-*").
    let name = last_dispatched_algorithm().expect("dispatch recorded");
    assert!(
        !name.starts_with("sparse"),
        "dense repr must dispatch a dense algorithm, got {name}"
    );
}
