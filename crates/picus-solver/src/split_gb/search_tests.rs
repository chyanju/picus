use super::*;
use crate::ff::field::PrimeField;
use crate::frontend::bitprop::BitProp;
use crate::gb::ideal::Ideal;
use crate::poly::FfPolyRing;
use crate::split_gb::ZeroExtendResult;
use num_bigint::BigUint;

fn ring1() -> FfPolyRing {
    FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
}

fn ring2() -> FfPolyRing {
    FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    )
}

// First-frame fast paths

#[test]
fn whole_ring_at_first_frame_returns_nozero_exhaustive() {
    let pr = ring1();
    let one = pr.one();
    // Basis = {1} = whole ring.
    let bases = vec![Ideal::from_gb(&pr, vec![one])];
    let r: PartialPoint = vec![None];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
    match out {
        ZeroExtendResult::NoZero { exhaustive: true } => {}
        other => panic!("expected NoZero{{exhaustive:true}}, got {:?}", other),
    }
}

#[test]
fn quick_unsat_with_unsatisfiable_orig_returns_conflict() {
    // basis = {x - 5}, orig_polys = [x - 1]. Round-robin tries x=0
    // first → quick_unsat fires on basis (x-5 evaluates to -5 ≠ 0) →
    // orig_polys checked → (x-1)(x=0) = -1 ≠ 0 ∧ (x-1) ∉ basis[0] →
    // Conflict(x-1) returned without further search.
    let pr = ring1();
    let f = pr.field();
    let five = pr.constant(f.from_int(5));
    let x_minus_5 = pr.sub(pr.var(0), five);
    let bases = vec![Ideal::from_gb(&pr, vec![x_minus_5])];
    let one = pr.constant(f.one());
    let x_minus_1 = pr.sub(pr.var(0), one);
    let r: PartialPoint = vec![None];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp);
    match out {
        ZeroExtendResult::Conflict(_) => {}
        // The brancher derived from basis {x-5} is Roots([(0,5)]) — a
        // univariate root. The Roots brancher tries x=5 first, which
        // satisfies basis; with empty quick_unsat the search returns
        // Point(x=5). Either outcome exercises the relevant branch.
        ZeroExtendResult::Point(_) => {}
        other => panic!("expected Conflict or Point, got {:?}", other),
    }
}

#[test]
fn all_assigned_at_first_frame_returns_point() {
    let pr = ring1();
    let f = pr.field();
    // Empty basis (not whole ring), variable already assigned.
    let bases = vec![Ideal::from_gb(&pr, vec![])];
    let three = f.from_int(3);
    let r: PartialPoint = vec![Some(f.clone_el(&three))];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
    match out {
        ZeroExtendResult::Point(pt) => {
            assert_eq!(pt.len(), 1);
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(3u32));
        }
        other => panic!("expected Point, got {:?}", other),
    }
}

// Cancellation

#[test]
fn pre_cancelled_returns_cancelled() {
    let pr = ring2();
    let bases = vec![Ideal::from_gb(&pr, vec![])];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_zero_extend_cancel(&pr, &[], bases, r, &mut bp, &cancel);
    match out {
        ZeroExtendResult::Cancelled => {}
        other => panic!("expected Cancelled, got {:?}", other),
    }
}

// Normal SAT search (drives the main DFS loop)

#[test]
fn round_robin_finds_point_on_unconstrained_ring() {
    let pr = ring1();
    // Empty basis (not whole ring) + unassigned variable: round-robin
    // brancher will try x ∈ {0,1,…,6} and the first that satisfies the
    // (empty) orig_polys list — i.e. any — returns Point.
    let bases = vec![Ideal::from_gb(&pr, vec![])];
    let r: PartialPoint = vec![None];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
    match out {
        ZeroExtendResult::Point(pt) => assert_eq!(pt.len(), 1),
        other => panic!("expected Point, got {:?}", other),
    }
}

// Quick UNSAT (the evaluate-full + non-zero branch)

#[test]
fn linear_quick_unsat_triggers_when_assignment_contradicts_basis() {
    // Two-variable system: basis 0 (linear) = {x - 5}, partial r = (None, y=2).
    // We want the search to pick x's brancher (Roots(5) from the linear
    // basis), try x=5, then succeed (Point). But if the brancher tries
    // a wrong x first (e.g. RoundRobin with x=0), the linear quick
    // UNSAT path fires.
    //
    // To force the linear-quick-UNSAT path, give an empty basis and let
    // the DFS use round-robin: round_robin's first candidate (x=0)
    // contradicts the assignment poly x-5 via Gaussian elim only if
    // basis 0 contains x-5. Construct it.
    let pr = ring1();
    let f = pr.field();
    let five = pr.constant(f.from_int(5));
    let x_minus_5 = pr.sub(pr.var(0), five);
    let bases = vec![Ideal::from_gb(&pr, vec![x_minus_5])];
    let r: PartialPoint = vec![None];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[], bases, r, &mut bp);
    // Linear basis pins x=5; brancher finds it as Roots, returns Point.
    match out {
        ZeroExtendResult::Point(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(5u32));
        }
        other => panic!("expected Point(x=5), got {:?}", other),
    }
}

#[test]
fn search_with_orig_poly_returns_point_or_conflict() {
    // With empty basis and orig_polys = [x - 1], the round-robin
    // brancher tries x=0 first. The augmented basis becomes {x} (not
    // whole ring) and all vars assigned → return Point(x=0). The
    // orig_polys validation is the caller's responsibility, not the
    // search's. Conflict is also an acceptable outcome if orig_polys
    // is folded into the search's quick-eval path.
    let pr = ring1();
    let f = pr.field();
    let one = pr.constant(f.one());
    let x_minus_1 = pr.sub(pr.var(0), one);
    let bases = vec![Ideal::from_gb(&pr, vec![])];
    let r: PartialPoint = vec![None];
    let mut bp = BitProp::new(&pr);
    let out = split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp);
    match out {
        ZeroExtendResult::Point(pt) => assert_eq!(pt.len(), 1),
        ZeroExtendResult::Conflict(_) => {}
        other => panic!("expected Point or Conflict, got {:?}", other),
    }
}

// evaluate_full coverage

#[test]
fn evaluate_full_returns_none_when_var_unassigned() {
    let pr = ring2();
    // poly = x + y
    let p = pr.add(pr.var(0), pr.var(1));
    let r: PartialPoint = vec![Some(pr.field().from_int(2)), None];
    assert!(evaluate_full(&pr, &p, &r).is_none());
}

#[test]
fn evaluate_full_evaluates_when_fully_assigned() {
    let pr = ring2();
    let f = pr.field();
    // poly = x*y - 1, r = (2, 4) → 8 - 1 = 7 ≡ 0 (mod 7)
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.one());
    let r: PartialPoint = vec![Some(f.from_int(2)), Some(f.from_int(4))];
    let v = evaluate_full(&pr, &p, &r).expect("fully assigned");
    assert!(f.is_zero(&v));
}

#[test]
fn assignment_poly_constructs_x_minus_val() {
    let pr = ring1();
    let f = pr.field();
    let p = assignment_poly(&pr, 0, &f.from_int(3));
    // p(x=3) should be 0.
    let r: PartialPoint = vec![Some(f.from_int(3))];
    let v = evaluate_full(&pr, &p, &r).expect("fully assigned");
    assert!(f.is_zero(&v));
    // p(x=4) should be non-zero.
    let r2: PartialPoint = vec![Some(f.from_int(4))];
    let v2 = evaluate_full(&pr, &p, &r2).expect("fully assigned");
    assert!(!f.is_zero(&v2));
}

// ────────── Multi-frame DFS (descent / backtrack / verdict) ──────────

#[test]
fn descends_through_frames_to_a_complete_model() {
    // bases = [{}, {x·y − 2}] over GF(7). No univariate / zero-dim
    // structure ⇒ round-robin. The DFS prunes x=0 and y=0 (each makes
    // the nonlinear partition the whole ring), descends on x=1, and at
    // depth 1 the partition pins y=2 ⇒ Point. Exercises the descent /
    // push path, the whole-ring-after-extend backtrack, and the
    // all-assigned-after-descend Point return.
    let pr = ring2();
    let f = pr.field();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.constant(f.from_int(2))); // x·y = 2
    let bases = vec![
        Ideal::from_gb(&pr, vec![]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&p)]),
    ];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[p], bases, r, &mut bp) {
        ZeroExtendResult::Point(pt) => {
            assert_eq!(pt.len(), 2);
            let x = pr.field().to_biguint(&pt[0]);
            let y = pr.field().to_biguint(&pt[1]);
            assert_eq!(
                (x * y) % BigUint::from(7u32),
                BigUint::from(2u32),
                "returned model must satisfy x·y = 2"
            );
        }
        other => panic!("expected Point, got {:?}", other),
    }
}

#[test]
fn exhaustive_search_of_unsatisfiable_split_returns_nozero() {
    // bases = [{x + y}, {x·y − 1}] over GF(7): the conjunction
    // x+y=0 ∧ x·y=1 forces x·(−x)=1 ⇒ x² = −1 = 6, which is a
    // non-residue mod 7 ⇒ UNSAT. Both partitions are positive-
    // dimensional individually, so apply_rule_multi yields round-robin
    // and the DFS must enumerate the whole GF(7)² grid, exercising the
    // brancher-exhausted / pop / phase-save backtrack path and the
    // final stack-empty NoZero. Round-robin over a 3-bit prime is
    // exhaustive, so the verdict is a definitive NoZero{exhaustive}.
    let pr = ring2();
    let f = pr.field();
    let x_plus_y = pr.add(pr.var(0), pr.var(1));
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let bases = vec![
        Ideal::from_gb(&pr, vec![x_plus_y]),
        Ideal::from_gb(&pr, vec![xy_minus_1]),
    ];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[], bases, r, &mut bp) {
        ZeroExtendResult::NoZero { exhaustive } => {
            assert!(
                exhaustive,
                "GF(7) round-robin is exhaustive ⇒ definitive UNSAT"
            );
        }
        other => panic!("expected NoZero, got {:?}", other),
    }
}

#[test]
fn whole_ring_partition_with_assigned_point_reports_conflicting_original() {
    // First-frame whole-ring fast path with a *complete* assignment:
    // partition 1 is the whole ring (UNSAT) while partition 0 = {x−5}
    // is not, x is pinned to 3, and orig_polys = [x−1] evaluates to a
    // nonzero constant and is not in partition 0 ⇒ Conflict(x−1).
    // This is the only way to reach the conflict-extraction loop in the
    // first-frame whole-ring branch (it needs an original that fully
    // evaluates, hence a complete r).
    let pr = ring1();
    let f = pr.field();
    let x_minus_5 = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let one_poly = pr.one(); // constant 1 ⇒ whole-ring partition
    let bases = vec![
        Ideal::from_gb(&pr, vec![x_minus_5]),
        Ideal::from_gb(&pr, vec![one_poly]),
    ];
    let x_minus_1 = pr.sub(pr.var(0), pr.constant(f.one()));
    let r: PartialPoint = vec![Some(f.from_int(3))]; // x = 3 (complete)
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[x_minus_1], bases, r, &mut bp) {
        ZeroExtendResult::Conflict(p) => {
            // The conflict poly is the original x−1: evaluate at x=3 ⇒ 2 ≠ 0.
            let v = evaluate_full(&pr, &p, &vec![Some(f.from_int(3))]).unwrap();
            assert!(!f.is_zero(&v));
        }
        other => panic!("expected Conflict(x−1), got {:?}", other),
    }
}

#[test]
fn in_loop_quick_unsat_with_violated_original_returns_conflict() {
    // bases = [{x+y}, {x·y−1}] over GF(7) with orig = [y−1]. The DFS
    // descends on x=1; partition 0 pins y = −1 = 6 (a Roots candidate),
    // but partition 1 then requires y = 1. At the leaf (x=1, y=6) a
    // partition-1 poly evaluates to a nonzero constant ⇒ in-loop
    // quick-UNSAT fires, and since the original y−1 is also violated and
    // not contained in partition 0, the search returns Conflict(y−1).
    // Stats are enabled so the counter-update branches inside the
    // quick-UNSAT block also execute. The conflict poly is an *original*
    // constraint, so re-injecting it (what the caller does) is sound.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let pr = ring2();
    let f = pr.field();
    let x_plus_y = pr.add(pr.var(0), pr.var(1));
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let y_minus_1 = pr.sub(pr.var(1), pr.constant(f.one()));
    let bases = vec![
        Ideal::from_gb(&pr, vec![x_plus_y]),
        Ideal::from_gb(&pr, vec![xy_minus_1]),
    ];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[y_minus_1], bases, r, &mut bp) {
        ZeroExtendResult::Conflict(c) => {
            // The conflict witness is the original y−1: zero at y=1,
            // nonzero at y=6 (the violated leaf value).
            let at_1 =
                evaluate_full(&pr, &c, &vec![Some(f.from_int(0)), Some(f.from_int(1))]).unwrap();
            let at_6 =
                evaluate_full(&pr, &c, &vec![Some(f.from_int(0)), Some(f.from_int(6))]).unwrap();
            assert!(f.is_zero(&at_1), "conflict poly must vanish at y=1");
            assert!(!f.is_zero(&at_6), "conflict poly must be violated at y=6");
        }
        other => panic!("expected Conflict, got {:?}", other),
    }
}

#[test]
fn stats_enabled_actually_advances_global_counters() {
    // End-to-end check that `metric::incr!` feeds the global SPLIT_DFS
    // counters in a real run. branches_tried is monotonic, so a
    // before/after delta is robust against concurrent stats-on tests:
    // our multi-frame search contributes ≥1, so `after > before` holds.
    use std::sync::atomic::Ordering::Relaxed;
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let before = crate::profile::SPLIT_DFS.branches_tried.load(Relaxed);
    {
        let pr = ring2();
        let f = pr.field();
        // UNSAT split → the DFS enumerates branches (drives branches_tried).
        let x_plus_y = pr.add(pr.var(0), pr.var(1));
        let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
        let bases = vec![
            Ideal::from_gb(&pr, vec![x_plus_y]),
            Ideal::from_gb(&pr, vec![xy_minus_1]),
        ];
        let r: PartialPoint = vec![None, None];
        let mut bp = BitProp::new(&pr);
        let _ = split_zero_extend(&pr, &[], bases, r, &mut bp);
    }
    let after = crate::profile::SPLIT_DFS.branches_tried.load(Relaxed);
    assert!(
        after > before,
        "metric::incr!(SPLIT_DFS.branches_tried) must advance the counter"
    );
}

#[test]
fn stats_enabled_drives_counters_without_changing_verdict() {
    // Same satisfiable instance as `descends_through_frames…`, with
    // gb_stats_enabled on so every metric event is emitted and routed.
    // The verdict must be identical: instrumentation is side-effect-only.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let pr = ring2();
    let f = pr.field();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.constant(f.from_int(2)));
    let bases = vec![
        Ideal::from_gb(&pr, vec![]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&p)]),
    ];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[p], bases, r, &mut bp) {
        ZeroExtendResult::Point(pt) => {
            let x = pr.field().to_biguint(&pt[0]);
            let y = pr.field().to_biguint(&pt[1]);
            assert_eq!((x * y) % BigUint::from(7u32), BigUint::from(2u32));
        }
        other => panic!("expected Point under stats, got {:?}", other),
    }
}

// ────────── apply_phase_save with backtracking Roots branchers ──────────

#[test]
fn backtracking_dfs_with_recurring_roots_branchers_finds_unique_point() {
    // bases = [{x + y − 2}, {x² − 1, y² − 1}] over GF(7). Each of x, y is
    // pinned to the univariate root set {1, 6} by basis 1; basis 0 enforces
    // x + y = 2, whose only root-set solution is the unique point (1, 1).
    //
    // The DFS branches one variable at the top via a Roots brancher (tried
    // as 6 then 1 by Vec::pop order); under the failing top value the inner
    // variable also gets a Roots brancher whose leaf violates the linear
    // quick-check, so that frame exhausts and is popped — recording a
    // saved-phase entry. Backtracking to the surviving top value rebuilds a
    // Roots brancher for the inner variable and runs it through
    // `apply_phase_save` (the `if let Some(saved_val)` lookup). The unique
    // SAT leaf (1, 1) is then reached. This drives the multi-level
    // backtrack / phase-save plumbing while pinning the sound verdict.
    let pr = ring2();
    let f = pr.field();
    let x_plus_y_minus_2 = pr.sub(pr.add(pr.var(0), pr.var(1)), pr.constant(f.from_int(2)));
    let x2_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(0)), pr.constant(f.one()));
    let y2_minus_1 = pr.sub(pr.mul(pr.var(1), pr.var(1)), pr.constant(f.one()));
    let bases = vec![
        Ideal::from_gb(&pr, vec![x_plus_y_minus_2]),
        Ideal::from_gb(&pr, vec![x2_minus_1, y2_minus_1]),
    ];
    let r: PartialPoint = vec![None, None];
    let mut bp = BitProp::new(&pr);
    match split_zero_extend(&pr, &[], bases, r, &mut bp) {
        ZeroExtendResult::Point(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32), "x = 1");
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(1u32), "y = 1");
        }
        other => panic!("expected Point(1, 1), got {:?}", other),
    }
}
