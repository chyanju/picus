use super::*;
use crate::ff::field::PrimeField;
use crate::frontend::bitprop::BitProp;
use crate::gb::ideal::Ideal;
use num_bigint::BigUint;
use oorandom::Rand64;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn test_admit() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let lin1 = pr.var(0); // 1 term, deg 1 -> admit by both
    let lin2 = pr.add(pr.var(0), pr.var(1)); // 2 terms, deg 1
    let nonlin = pr.mul(pr.var(0), pr.var(1));
    let lin3 = pr.add(pr.add(pr.var(0), pr.var(1)), pr.one()); // 3 terms, deg 1
    assert!(admit(&pr, 0, &lin1));
    assert!(admit(&pr, 1, &lin1));
    assert!(admit(&pr, 0, &lin2));
    assert!(admit(&pr, 1, &lin2));
    assert!(!admit(&pr, 0, &nonlin));
    assert!(!admit(&pr, 1, &nonlin));
    // lin3: 3 terms, deg 1 -> basis 0 admits (deg<=1), basis 1 rejects (terms>2)
    assert!(admit(&pr, 0, &lin3));
    assert!(!admit(&pr, 1, &lin3));
}

#[test]
fn test_split_gb_simple_sat() {
    // x*y - 1 = 0,  x = 2  →  y = 4 in GF(7)
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p1 = pr.sub(xy, pr.one());
    let two = pr.field().from_int(2);
    let p2 = pr.sub(pr.var(0), pr.constant(two));

    let mut bp = BitProp::new(&pr);
    let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p2)], vec![p1, p2]];
    let basis = split_gb(&pr, gens, &mut bp);
    assert!(!basis.iter().any(|b| b.is_whole_ring()));
    let pt = match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => pt,
        other => panic!("expected SAT, got {:?}", other),
    };
    // Check x = 2, y = 4 (or the other valid roots; should satisfy x*y=1).
    let x_val = pr.field().to_biguint(&pt[0]);
    let y_val = pr.field().to_biguint(&pt[1]);
    assert_eq!(x_val, BigUint::from(2u32));
    let prod = (x_val * y_val) % BigUint::from(7u32);
    assert_eq!(prod, BigUint::from(1u32));
}

#[test]
fn test_split_gb_unsat() {
    // x = 2, x = 3 in GF(7): UNSAT
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let two = pr.field().from_int(2);
    let three = pr.field().from_int(3);
    let p1 = pr.sub(pr.var(0), pr.constant(two));
    let p2 = pr.sub(pr.var(0), pr.constant(three));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&p1), pr.clone_poly(&p2)], vec![p1, p2]],
        &mut bp,
    );
    assert!(basis.iter().any(|b| b.is_whole_ring()));
}

#[test]
fn test_apply_rule_round_robin_interleaves() {
    // Positive-dim ideal: empty (no constraints) over GF(5), 2 vars.
    // Should fall through to round-robin. Verify the order:
    // (x,0), (y,0), (x,1), (y,1), (x,2), (y,2), (x,3), (y,3), (x,4), (y,4).
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let gb: Ideal = Ideal::from_gb(&pr, vec![]);
    let r: PartialPoint = vec![None, None];
    let mut brancher = apply_rule(&pr, &gb, &r);
    // first 2 candidates should be (0, 0) and (1, 0): same val, different var.
    let c0 = brancher.next(&pr.field()).unwrap();
    assert_eq!(c0.0, 0);
    assert_eq!(
        pr.field().to_biguint(&c0.1),
        num_bigint::BigUint::from(0u32)
    );
    let c1 = brancher.next(&pr.field()).unwrap();
    assert_eq!(c1.0, 1);
    assert_eq!(
        pr.field().to_biguint(&c1.1),
        num_bigint::BigUint::from(0u32)
    );
    // third candidate: var 0 again, val 1.
    let c2 = brancher.next(&pr.field()).unwrap();
    assert_eq!(c2.0, 0);
    assert_eq!(
        pr.field().to_biguint(&c2.1),
        num_bigint::BigUint::from(1u32)
    );
}

#[test]
fn test_apply_rule_univariate() {
    // GB has y^2 - 4 = 0; should enumerate roots of y over GF(7) (i.e., 2 and 5).
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let four = pr.field().from_int(4);
    let y_sq = pr.mul(pr.var(1), pr.var(1));
    let p = pr.sub(y_sq, pr.constant(four));
    let gb = Ideal::new(&pr, vec![p]);
    let r: PartialPoint = vec![None, None];
    let mut brancher = apply_rule(&pr, &gb, &r);
    let mut cands = Vec::new();
    while let Some(c) = brancher.next(&pr.field()) {
        cands.push(c);
    }
    assert!(cands.iter().all(|(v, _)| *v == 1));
    let vals: Vec<num_bigint::BigUint> = cands
        .iter()
        .map(|(_, v)| pr.field().to_biguint(v))
        .collect();
    assert!(vals.contains(&num_bigint::BigUint::from(2u32)));
    assert!(vals.contains(&num_bigint::BigUint::from(5u32)));
}

#[test]
fn split_find_zero_conflict_reextend_loop_yields_unsat() {
    // bases = [{x+y}, {x·y−1}] over GF(7): x+y=0 ∧ x·y=1 forces
    // x² = −1 = 6, a non-residue mod 7 ⇒ UNSAT. all_gens = [x+y, x·y−1].
    // The first DFS pass descends on a value for x; the linear partition
    // pins y, and at a leaf the nonlinear original x·y−1 evaluates to a
    // nonzero constant and is NOT in basis 0 (it is nonlinear) ⇒ the DFS
    // returns ZeroExtendResult::Conflict(x·y−1). `split_find_zero_cancel`
    // catches the conflict, clones it into every partition's new_polys,
    // re-runs split_gb_extend_cancel (basis growth), and re-enters the
    // fixpoint loop. GF(7) round-robin is exhaustive ⇒ the loop terminates
    // with a definitive Unsat.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let x_plus_y = pr.add(pr.var(0), pr.var(1));
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![x_plus_y]),
        Ideal::from_gb(&pr, vec![xy_minus_1]),
    ];
    let mut bp = BitProp::new(&pr);
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!("expected Unsat after conflict re-extension, got {:?}", other),
    }
}

#[test]
fn split_find_zero_cancel_pre_cancelled_errors() {
    // The loop guard `cancel.is_cancelled()` fires on entry.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
    let mut bp = BitProp::new(&pr);
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &CancelToken::cancelled());
    assert!(matches!(out, Err(Cancelled)));
}

#[test]
fn admit_rejects_partition_index_beyond_one() {
    // The `_ => false` arm of `admit`: any partition index >= 2 never
    // admits, even a degree-1 single-term poly that bases 0 and 1 accept.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let lin = pr.var(0); // deg 1, 1 term
    assert!(admit(&pr, 0, &lin));
    assert!(admit(&pr, 1, &lin));
    assert!(!admit(&pr, 2, &lin), "partition index 2 is never admitted");
    assert!(!admit(&pr, 7, &lin), "any higher partition index is rejected");
}

#[test]
fn split_find_zero_conflict_reextend_via_solve_loop_reaches_extend_branch() {
    // bases = [{x+y}, {x·y−1}] over GF(7) is jointly UNSAT (x²=−1=6, a
    // non-residue). The DFS leaf returns ZeroExtendResult::Conflict on the
    // nonlinear original x·y−1 (it evaluates to a nonzero constant and is
    // not in basis 0), driving `split_find_zero_cancel`'s conflict arm:
    // it clones the conflict into every partition's new_polys and calls
    // `split_gb_extend_cancel` (the `?` re-extension step) before
    // re-entering the fixpoint loop, which then proves UNSAT.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let x_plus_y = pr.add(pr.var(0), pr.var(1));
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![x_plus_y]),
        Ideal::from_gb(&pr, vec![xy_minus_1]),
    ];
    let mut bp = BitProp::new(&pr);
    match split_find_zero_cancel(&pr, split_basis, &mut bp, &CancelToken::none()) {
        Ok(SplitFindZeroOutcome::Unsat) => {}
        other => panic!("expected Ok(Unsat) after re-extension, got {:?}", other),
    }
}

// ────────── try_split_triangular (config-gated split_triangular) ──────────

#[test]
fn triangular_zero_dim_sat_returns_verified_point() {
    // split_triangular on: a zero-dimensional, satisfiable system
    // {x − 2, y − 3} over GF(7). `try_split_triangular` builds the ideal,
    // finds it zero-dimensional, runs `gb::model::find_zero_cancel` (Sat
    // arm), verifies the witness against the combined system, and maps it
    // back to a point. The DFS is bypassed.
    let _g = crate::config::ConfigGuard::with_override(|c| c.split_triangular = true);
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let p_x = pr.sub(pr.var(0), pr.constant(f.from_int(2))); // x = 2
    let p_y = pr.sub(pr.var(1), pr.constant(f.from_int(3))); // y = 3
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![pr.clone_poly(&p_x), pr.clone_poly(&p_y)]),
        Ideal::from_gb(&pr, vec![]),
    ];
    let mut bp = BitProp::new(&pr);
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(2u32));
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(3u32));
        }
        other => panic!("expected triangular SAT(2,3), got {:?}", other),
    }
}

#[test]
fn triangular_zero_dim_unsat_returns_unsat() {
    // split_triangular on: a zero-dimensional system with no GF(7) point.
    // {x² − 3} over GF(7) — 3 is a non-residue (QRs = {1,2,4}). The ideal
    // is zero-dimensional, so `try_split_triangular` runs the complete
    // zero-dim enumeration (`find_zero_cancel` → Unsat) and returns
    // `SplitFindZeroOutcome::Unsat` without the DFS.
    let _g = crate::config::ConfigGuard::with_override(|c| c.split_triangular = true);
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(3))); // x^2 - 3
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![p]), Ideal::from_gb(&pr, vec![])];
    let mut bp = BitProp::new(&pr);
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!("expected triangular UNSAT, got {:?}", other),
    }
}

#[test]
fn triangular_positive_dim_falls_back_to_dfs() {
    // split_triangular on, but the combined system {x·y − 2} over GF(7)
    // is positive-dimensional (2 vars, 1 equation). `try_split_triangular`
    // hits the `!ideal.is_zero_dim()` guard and returns None, so
    // `split_find_zero_cancel` falls through to the brancher DFS, which
    // finds a SAT point satisfying x·y = 2.
    let _g = crate::config::ConfigGuard::with_override(|c| c.split_triangular = true);
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p = pr.sub(xy, pr.constant(f.from_int(2))); // x*y - 2
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&p)]),
    ];
    let mut bp = BitProp::new(&pr);
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            let x = pr.field().to_biguint(&pt[0]);
            let y = pr.field().to_biguint(&pt[1]);
            assert_eq!(
                (x * y) % BigUint::from(7u32),
                BigUint::from(2u32),
                "DFS fallback must satisfy x·y = 2"
            );
        }
        other => panic!("expected SAT via DFS fallback, got {:?}", other),
    }
}

const P: u64 = 11;
const N_VARS: usize = 6;

/// Random non-zero coefficient in GF(11).
fn rand_coeff(ff: &PrimeField, rng: &mut Rand64) -> FieldElem {
    let v = rng.rand_u64() % P;
    ff.from_biguint(&BigUint::from(v))
}

/// Build a random polynomial: `n_terms` terms, each a product of up to
/// `max_degree` (randomly-chosen) indeterminates, with a random coefficient.
/// Retries if the resulting polynomial is zero (feanor-math's Buchberger
/// panics on zero generators).
fn rand_poly(pr: &FfPolyRing, degree: usize, n_terms: usize, rng: &mut Rand64) -> Poly {
    loop {
        let mut out = pr.zero();
        for _ in 0..n_terms {
            let c = rand_coeff(&pr.field(), rng);
            let mut term = pr.constant(pr.field().clone_el(&c));
            let t_deg = 1 + (rng.rand_u64() as usize % degree.max(1));
            for _ in 0..t_deg {
                let j = (rng.rand_u64() as usize) % pr.n_vars();
                term = pr.mul(term, pr.var(j));
            }
            out = pr.add(out, term);
        }
        if !pr.is_zero(&out) {
            return out;
        }
    }
}

/// Evaluate `p` at the given point (length = n_vars).  Returns the field element.
fn eval_poly(pr: &FfPolyRing, p: &Poly, point: &[FieldElem]) -> FieldElem {
    let ring = &pr.ring;
    let fp = &pr.field();
    let mut acc = fp.zero();
    for (c, m) in ring.terms(p) {
        let mut t = fp.clone_el(c);
        for v in 0..pr.n_vars() {
            let e = ring.exponent_at(&m, v);
            for _ in 0..e {
                t = fp.mul_ref(&t, &point[v]);
            }
        }
        fp.add_assign(&mut acc, t);
    }
    acc
}

/// Build a random polynomial with a known root: `rand_poly() - rand_poly()(root)`.
/// Retries if the result is zero.
fn rand_poly_with_root(
    pr: &FfPolyRing,
    degree: usize,
    n_terms: usize,
    root: &[FieldElem],
    rng: &mut Rand64,
) -> Poly {
    loop {
        let p = rand_poly(pr, degree, n_terms, rng);
        let val = eval_poly(pr, &p, root);
        let c = pr.constant(val);
        let out = pr.sub(p, c);
        if !pr.is_zero(&out) {
            return out;
        }
    }
}

// =============================================================================
// Random SAT systems with a planted root
// =============================================================================
//
// Generate 50 systems of ~9 polys each (6 vars, degree ≤ 2, 2 terms per poly)
// with a *planted* random root in GF(11)^6.  Every system is SAT by
// construction: `split_find_zero` must return some point.
//
// We verify the returned model satisfies all constraints.
#[test]
fn test_rand_sat() {
    let n_iters = 50usize;
    let n_eqns = (N_VARS as f64 * 1.5) as usize;
    let mut rng = Rand64::new(0xcafe_babe_cafe_babe);

    for _ in 0..n_iters {
        let ff = PrimeField::new(BigUint::from(P));
        let var_names: Vec<String> = (0..N_VARS).map(|i| format!("x{}", i)).collect();
        let pr = FfPolyRing::new(ff, var_names);

        // Planted root.
        let root: Vec<FieldElem> = (0..N_VARS)
            .map(|_| rand_coeff(&pr.field(), &mut rng))
            .collect();

        // Generate polys and distribute across two bases.
        let mut all_gens: Vec<Poly> = Vec::new();
        let mut bases: Vec<Vec<Poly>> = vec![Vec::new(), Vec::new()];
        for _ in 0..n_eqns {
            let p = rand_poly_with_root(&pr, 2, 2, &root, &mut rng);
            let j = (rng.rand_u64() as usize) % 2;
            bases[j].push(pr.clone_poly(&p));
            all_gens.push(p);
        }

        // Run split_gb then split_find_zero.
        let mut bp = BitProp::new(&pr);
        let split_basis = split_gb(&pr, bases, &mut bp);
        let result = split_find_zero(&pr, split_basis, &mut bp);

        let point = match result {
            SplitFindZeroOutcome::Sat(p) => p,
            other => panic!(
                "RandSat iteration should find a root (one exists by construction); got {:?}",
                other
            ),
        };
        for g in &all_gens {
            let v = eval_poly(&pr, g, &point);
            assert!(
                pr.field().is_zero(&v),
                "returned model must zero every generator"
            );
        }
    }
}

// =============================================================================
// Random (frequently UNSAT) systems with no planted root
// =============================================================================
//
// Generate 40 systems of ~9 polys (degree ≤ 2, 1 term per poly — i.e.
// monomials) with no planted root.  These are *frequently* but not
// uniformly UNSAT.  We check consistency: if `split_find_zero` returns a
// model, it must actually satisfy the constraints.
#[test]
fn test_rand_unsat() {
    let n_iters = 40usize;
    let n_eqns = (N_VARS as f64 * 1.5) as usize;
    let mut rng = Rand64::new(0xdead_beef_dead_beef);

    for _ in 0..n_iters {
        let ff = PrimeField::new(BigUint::from(P));
        let var_names: Vec<String> = (0..N_VARS).map(|i| format!("x{}", i)).collect();
        let pr = FfPolyRing::new(ff, var_names);

        let mut all_gens: Vec<Poly> = Vec::new();
        let mut bases: Vec<Vec<Poly>> = vec![Vec::new(), Vec::new()];
        for _ in 0..n_eqns {
            let p = rand_poly(&pr, 2, 1, &mut rng);
            let j = (rng.rand_u64() as usize) % 2;
            bases[j].push(pr.clone_poly(&p));
            all_gens.push(p);
        }

        let mut bp = BitProp::new(&pr);
        let split_basis = split_gb(&pr, bases, &mut bp);
        let result = split_find_zero(&pr, split_basis, &mut bp);

        if let SplitFindZeroOutcome::Sat(point) = result {
            // SAT → the model must actually satisfy the constraints.
            for g in &all_gens {
                let v = eval_poly(&pr, g, &point);
                assert!(
                    pr.field().is_zero(&v),
                    "returned model must zero every generator"
                );
            }
        }
        // UNSAT is permitted; we don't assert it.
    }
}

// =============================================================================
// Empty Groebner basis
// =============================================================================
//
// An empty GB should:
//   * not be the whole ring
//   * not be zero-dimensional (`0 = I` in n≥1 vars has infinitely many zeros)
//   * contain no variable
#[test]
fn test_gb_empty() {
    let ff = PrimeField::new(BigUint::from(7u64));
    let var_names: Vec<String> = (0..N_VARS).map(|i| format!("x{}", i)).collect();
    let pr = FfPolyRing::new(ff, var_names);

    let gb = Ideal::from_gb(&pr, Vec::new());
    assert!(!gb.is_whole_ring());
    assert!(!gb.is_zero_dim());
    assert_eq!(gb.basis.len(), 0);
    for i in 0..N_VARS {
        let v = pr.var(i);
        assert!(!gb.contains(&v), "empty ideal contains no variable");
    }
}

// =============================================================================
// Random Groebner basis self-consistency
// =============================================================================
//
// For 50 random 4-generator systems (6 vars, GF(11), degree ≤ 2, 2 terms
// each), check:
//   * is_whole_ring() is consistent: basis contains a nonzero constant iff
//     1 ∈ <gens>.
//   * Every basis element is a member of the original ideal (modulo
//     symmetry: `ideal.contains(g)` for all GB elements).
#[test]
fn test_gb_rand() {
    let n_iters = 50usize;
    let n_eqns = 4usize;
    let mut rng = Rand64::new(0x1234_5678_9abc_def0);

    for _ in 0..n_iters {
        let ff = PrimeField::new(BigUint::from(P));
        let var_names: Vec<String> = (0..N_VARS).map(|i| format!("x{}", i)).collect();
        let pr = FfPolyRing::new(ff, var_names);

        let mut gens: Vec<Poly> = Vec::new();
        for _ in 0..n_eqns {
            gens.push(rand_poly(&pr, 2, 2, &mut rng));
        }

        let gens_clone: Vec<Poly> = gens.iter().map(|p| pr.clone_poly(p)).collect();
        let ideal = Ideal::new(&pr, gens);

        // Self-consistency: every generator must be in the ideal it generated.
        for g in &gens_clone {
            assert!(ideal.contains(g), "generator must be in its own ideal");
        }

        // If `is_whole_ring()`, then 1 must reduce to zero.
        if ideal.is_whole_ring() {
            let one = pr.one();
            assert!(ideal.contains(&one), "whole ring must contain 1");
        }

        // Every basis element reduces to zero against itself.
        for b in &ideal.basis {
            assert!(ideal.contains(b));
        }
    }
}

// =============================================================================
// SPEC-DRIVEN property tests for split-GB. Expected values come from FIELD
// MATH / IDEAL THEORY, not from inspecting solver source. A failing test
// here means the spec is violated — either a wrong model, a spurious UNSAT,
// or a missed monotonicity property.
// =============================================================================

/// Evaluate a polynomial at a point and return whether it's zero.
fn evals_to_zero(pr: &FfPolyRing, p: &Poly, pt: &[FieldElem]) -> bool {
    pr.field().is_zero(&eval_poly(pr, p, pt))
}

/// Property (5/9) MODEL CHECKING: every SAT model returned by
/// `split_find_zero` MUST zero every input generator. This is the
/// SOUNDNESS contract of a SAT verdict. Pin: `x·y - 1 = 0` ∧ `x = 2`
/// over GF(7) ⇒ y = 4 (since 2·4 = 8 ≡ 1 mod 7). MATH-derived.
#[test]
fn prop_split_sat_model_zeros_inputs_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let x_eq_2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let originals = vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)];
    let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&x_eq_2)], vec![xy_minus_1, x_eq_2]];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, gens, &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            for g in &originals {
                assert!(
                    evals_to_zero(&pr, g, &pt),
                    "SAT model must zero every original generator"
                );
            }
            // MATH-derived unique-solution check.
            assert_eq!(
                pr.field().to_biguint(&pt[0]),
                BigUint::from(2u32),
                "x = 2 forces x"
            );
            assert_eq!(
                pr.field().to_biguint(&pt[1]),
                BigUint::from(4u32),
                "x·y = 1, x = 2 ⇒ y = 4 in GF(7)"
            );
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Property (7) EDGE PRIMES: solve `x = a, y = b` over multiple primes.
/// MATH: each system pins one (x, y) point. Verify model values.
#[test]
fn prop_split_sat_two_eqs_pin_solution_across_primes() {
    for p in [2u32, 3, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into(), "y".into()]);
        let f = pr.field();
        let a = 1u64; // a < every test prime
        let b = if p > 2 { 2u64 } else { 0u64 };
        let p_x = pr.sub(pr.var(0), pr.constant(f.from_int(a as i64)));
        let p_y = pr.sub(pr.var(1), pr.constant(f.from_int(b as i64)));
        let originals = vec![pr.clone_poly(&p_x), pr.clone_poly(&p_y)];
        let gens: Vec<Vec<Poly>> = vec![vec![pr.clone_poly(&p_x), pr.clone_poly(&p_y)], vec![p_x, p_y]];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(&pr, gens, &mut bp);
        match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => {
                for g in &originals {
                    assert!(
                        evals_to_zero(&pr, g, &pt),
                        "GF({}): model must zero generator",
                        p
                    );
                }
                assert_eq!(
                    pr.field().to_biguint(&pt[0]),
                    BigUint::from(a) % BigUint::from(p),
                    "GF({}): x pinned",
                    p
                );
                assert_eq!(
                    pr.field().to_biguint(&pt[1]),
                    BigUint::from(b) % BigUint::from(p),
                    "GF({}): y pinned",
                    p
                );
            }
            other => panic!("GF({}): expected SAT, got {:?}", p, other),
        }
    }
}

/// Property (5) UNSAT BY ELEMENT DISTINCTNESS: `x - a` and `x - b` with
/// `a ≠ b mod p` together generate the unit ideal (their difference is
/// the nonzero constant `b - a`). Spec: distinct points are incompatible.
/// Try across edge primes.
#[test]
fn prop_distinct_constants_force_unsat_across_primes() {
    for p in [3u32, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into()]);
        let f = pr.field();
        let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        let originals = vec![pr.clone_poly(&p1), pr.clone_poly(&p2)];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(
            &pr,
            vec![
                vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
                vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
            ],
            &mut bp,
        );
        // Either the basis becomes the whole ring at fixpoint OR the DFS
        // proves UNSAT. Both routes assert UNSAT.
        let is_whole = basis.iter().any(|b| b.is_whole_ring());
        if !is_whole {
            match split_find_zero(&pr, basis, &mut bp) {
                SplitFindZeroOutcome::Unsat => {}
                other => panic!("GF({}): expected UNSAT, got {:?}", p, other),
            }
        }
        // The (1 - 0) negation property: input `p1` and `p2` cannot
        // coexist with a witness. Confirm: any putative point fails one.
        for v in 0..p {
            let pt = vec![f.from_int(v as i64)];
            assert!(
                !(evals_to_zero(&pr, &originals[0], &pt) && evals_to_zero(&pr, &originals[1], &pt)),
                "GF({}): no element of GF can satisfy both x=1 and x=2",
                p
            );
        }
    }
}

/// Property (8) DETERMINISM: two independent split-GB runs on the same
/// input must return the same outcome class (Sat / Unsat / Unknown).
/// `split_gb` and `split_find_zero` must be pure functions of input.
#[test]
fn prop_split_determinism_two_calls() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy = pr.mul(pr.var(0), pr.var(1));
    let p1 = pr.sub(xy, pr.constant(f.from_int(2)));
    let mut bp1 = BitProp::new(&pr);
    let basis1 = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p1)]], &mut bp1);
    let r1 = split_find_zero(&pr, basis1, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis2 = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p1)]], &mut bp2);
    let r2 = split_find_zero(&pr, basis2, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2), "split-GB verdict must be deterministic");
}

/// Property (3) IDEMPOTENCE: running `split_gb` on a basis already at
/// fixpoint (i.e. the output of a prior `split_gb` run) gives the same
/// "is whole ring" verdict per partition. Spec: a fixpoint is a fixpoint.
#[test]
fn prop_split_gb_idempotent_whole_ring_flag() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis1 = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&p1), pr.clone_poly(&p2)], vec![p1, p2]],
        &mut bp,
    );
    let whole1: Vec<bool> = basis1.iter().map(|b| b.is_whole_ring()).collect();
    // Feed each fixpoint basis back as input.
    let gens: Vec<Vec<Poly>> = basis1
        .iter()
        .map(|b| b.basis.iter().map(|p| pr.clone_poly(p)).collect())
        .collect();
    let basis2 = split_gb(&pr, gens, &mut bp);
    let whole2: Vec<bool> = basis2.iter().map(|b| b.is_whole_ring()).collect();
    assert_eq!(whole1, whole2, "fixpoint of fixpoint is fixpoint");
}

/// Property (5) UNSAT BY NON-RESIDUE: `x² - 3 = 0` over GF(7). MATH: the
/// quadratic residues of GF(7) are {0, 1, 2, 4} (squares of 0..6 mod 7),
/// so 3 is NOT a QR ⇒ no solution. Must be UNSAT.
#[test]
fn prop_non_residue_squared_eq_is_unsat_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p)]], &mut bp);
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    // Either the whole-ring fixpoint catches it, or DFS proves UNSAT.
    let result = if is_whole {
        SplitFindZeroOutcome::Unsat
    } else {
        split_find_zero(&pr, basis, &mut bp)
    };
    assert!(
        matches!(result, SplitFindZeroOutcome::Unsat),
        "x² = 3 over GF(7) is UNSAT (3 is a non-residue), got {:?}",
        result
    );
    // Ground-truth: brute force confirms zero roots.
    let n = (0..7u32)
        .filter(|&v| (v * v) % 7 == 3)
        .count();
    assert_eq!(n, 0, "ground truth: 3 has no square root in GF(7)");
}

/// Property (5) MODEL VALIDITY for x² - 4 = 0 over GF(7): roots are 2 and
/// 5 (MATH: 2² = 4, 5² = 25 ≡ 4 mod 7). A SAT model must return one of
/// them. Pin: the returned x must satisfy x² ≡ 4.
#[test]
fn prop_quadratic_residue_root_is_valid_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let p = pr.sub(x2, pr.constant(f.from_int(4)));
    let originals = vec![pr.clone_poly(&p)];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p)]], &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert!(evals_to_zero(&pr, &originals[0], &pt));
            let x = pr.field().to_biguint(&pt[0]);
            assert!(
                x == BigUint::from(2u32) || x == BigUint::from(5u32),
                "x² = 4 mod 7 ⇒ x ∈ {{2, 5}}, got {}",
                x
            );
        }
        other => panic!("expected SAT (x ∈ {{2,5}}), got {:?}", other),
    }
}

/// Property (6) BIT-PROP SPEC: `x · (x - 1) = 0` over GF(p) forces
/// x ∈ {0, 1}. Solve and check the returned model. MATH: roots of the
/// polynomial are exactly 0 and 1. Memory says bitprop is a recurring
/// hazard — probe it on multiple primes.
#[test]
fn prop_bit_constraint_forces_zero_or_one() {
    for p in [3u32, 5, 7, 11, 101] {
        let pr = FfPolyRing::new(ff(p), vec!["x".into()]);
        let f = pr.field();
        let xx = pr.mul(pr.var(0), pr.var(0));
        let bit = pr.sub(xx, pr.var(0)); // x² - x = x(x-1)
        let originals = vec![pr.clone_poly(&bit)];
        let mut bp = BitProp::new(&pr);
        let basis = split_gb(
            &pr,
            vec![vec![], vec![pr.clone_poly(&bit)]],
            &mut bp,
        );
        match split_find_zero(&pr, basis, &mut bp) {
            SplitFindZeroOutcome::Sat(pt) => {
                assert!(evals_to_zero(&pr, &originals[0], &pt));
                let x = pr.field().to_biguint(&pt[0]);
                assert!(
                    x == BigUint::from(0u32) || x == BigUint::from(1u32),
                    "GF({}): x(x-1)=0 ⇒ x∈{{0,1}}, got {}",
                    p,
                    x
                );
            }
            other => panic!("GF({}): expected SAT, got {:?}", p, other),
        }
    }
}

/// Property (6) BIT-DECOMPOSITION SPEC: three bit vars `b0, b1, b2` with
/// the bitsum constraint `x = b0 + 2·b1 + 4·b2`. MATH: x ∈ [0, 8). If we
/// also pin `x = 5`, the unique decomposition is b0=1, b1=0, b2=1 (binary
/// representation of 5). Probe the bitprop pipeline on a recurring hazard.
#[test]
fn prop_bitsum_decomposition_matches_binary_repr() {
    let pr = FfPolyRing::new(
        ff(11),
        vec!["b0".into(), "b1".into(), "b2".into(), "x".into()],
    );
    let f = pr.field();
    // Bit constraints: bi · (bi - 1) = 0 for i in 0..3.
    let b0 = pr.var(0);
    let b1 = pr.var(1);
    let b2 = pr.var(2);
    let bit0 = pr.sub(pr.mul(pr.clone_poly(&b0), pr.clone_poly(&b0)), pr.clone_poly(&b0));
    let bit1 = pr.sub(pr.mul(pr.clone_poly(&b1), pr.clone_poly(&b1)), pr.clone_poly(&b1));
    let bit2 = pr.sub(pr.mul(pr.clone_poly(&b2), pr.clone_poly(&b2)), pr.clone_poly(&b2));
    // bitsum: x = b0 + 2 b1 + 4 b2.
    let two_b1 = pr.scale(f.from_int(2), pr.clone_poly(&b1));
    let four_b2 = pr.scale(f.from_int(4), pr.clone_poly(&b2));
    let sum_expr = pr.add(pr.add(pr.clone_poly(&b0), two_b1), four_b2);
    let bitsum_minus_x = pr.sub(sum_expr, pr.var(3));
    // x = 5.
    let x_pin = pr.sub(pr.var(3), pr.constant(f.from_int(5)));

    let originals = vec![
        pr.clone_poly(&bit0),
        pr.clone_poly(&bit1),
        pr.clone_poly(&bit2),
        pr.clone_poly(&bitsum_minus_x),
        pr.clone_poly(&x_pin),
    ];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
        ],
        &mut bp,
    );
    if basis.iter().any(|b| b.is_whole_ring()) {
        panic!("decomposition of 5 in 3 bits is SAT (binary 101), not UNSAT");
    }
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            // Every original must zero at the witness.
            for g in &originals {
                assert!(
                    evals_to_zero(&pr, g, &pt),
                    "SAT model must zero every constraint"
                );
            }
            // MATH: 5 = 1·1 + 2·0 + 4·1, so b0=1, b1=0, b2=1.
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(0u32));
            assert_eq!(pr.field().to_biguint(&pt[2]), BigUint::from(1u32));
            assert_eq!(pr.field().to_biguint(&pt[3]), BigUint::from(5u32));
        }
        other => panic!("expected SAT (b0=1,b1=0,b2=1,x=5), got {:?}", other),
    }
}

/// Property (6) BIT-DECOMPOSITION RANGE SPEC: n-bit decomposition forces
/// x ∈ [0, 2^n). Pin: 3 bits constraint with x pinned to 8 (i.e. 2^3, out
/// of range). MATH: 8 cannot be written as b0+2b1+4b2 with bi ∈ {0,1} —
/// max is 1+2+4 = 7. Must be UNSAT.
#[test]
fn prop_bit_decomposition_out_of_range_is_unsat() {
    let pr = FfPolyRing::new(
        ff(11),
        vec!["b0".into(), "b1".into(), "b2".into(), "x".into()],
    );
    let f = pr.field();
    let b0 = pr.var(0);
    let b1 = pr.var(1);
    let b2 = pr.var(2);
    let bit0 = pr.sub(pr.mul(pr.clone_poly(&b0), pr.clone_poly(&b0)), pr.clone_poly(&b0));
    let bit1 = pr.sub(pr.mul(pr.clone_poly(&b1), pr.clone_poly(&b1)), pr.clone_poly(&b1));
    let bit2 = pr.sub(pr.mul(pr.clone_poly(&b2), pr.clone_poly(&b2)), pr.clone_poly(&b2));
    let two_b1 = pr.scale(f.from_int(2), pr.clone_poly(&b1));
    let four_b2 = pr.scale(f.from_int(4), pr.clone_poly(&b2));
    let sum_expr = pr.add(pr.add(pr.clone_poly(&b0), two_b1), four_b2);
    let bitsum_minus_x = pr.sub(sum_expr, pr.var(3));
    let x_pin = pr.sub(pr.var(3), pr.constant(f.from_int(8))); // 8 ∉ [0, 8)

    let originals = vec![bit0, bit1, bit2, bitsum_minus_x, x_pin];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
            originals.iter().map(|p| pr.clone_poly(p)).collect(),
        ],
        &mut bp,
    );
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    let result = if is_whole {
        SplitFindZeroOutcome::Unsat
    } else {
        split_find_zero(&pr, basis, &mut bp)
    };
    assert!(
        matches!(result, SplitFindZeroOutcome::Unsat),
        "x=8 with 3-bit decomp must be UNSAT (max is 7), got {:?}",
        result
    );
}

/// Property (6) BIT-PROP SOUNDNESS PROBE: the GF(7) quadratic from
/// `core_tests.rs::satisfiable_system_with_bitsum_shaped_linear_part_is_not_false_unsat`
/// has a confirmed-positive root count. Same shape, here at the split-GB
/// layer: a single satisfiable polynomial whose linear part has a `1,2`
/// coefficient run is exposed as a bitsum candidate. Spec: a bitsum
/// pattern alone (without bit constraints proving bit-ness) MUST NOT
/// prune SAT models. Memory R5 H1 / R7 J1 both bitprop, hence probe HARD.
#[test]
fn prop_bitsum_shaped_linear_does_not_force_false_unsat_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["y".into(), "z".into(), "x".into()]);
    let f = pr.field();
    let c = |n: i64| f.from_int(n);
    let q = {
        let terms = [
            pr.mul(pr.var(0), pr.var(0)),
            pr.scale(c(6), pr.mul(pr.var(1), pr.var(1))),
            pr.scale(c(5), pr.mul(pr.var(0), pr.var(2))),
            pr.scale(c(3), pr.mul(pr.var(1), pr.var(2))),
            pr.scale(c(4), pr.mul(pr.var(2), pr.var(2))),
            pr.var(0),
            pr.scale(c(2), pr.var(1)),
            pr.constant(c(2)),
        ];
        let mut acc = pr.zero();
        for t in terms {
            acc = pr.add(acc, t);
        }
        acc
    };
    // Brute force confirms SAT (MATH ground truth, not source).
    let n_sols = (0..7i64)
        .flat_map(|y| (0..7i64).flat_map(move |z| (0..7i64).map(move |x| (y, z, x))))
        .filter(|&(y, z, x)| {
            (y * y + 6 * z * z + 5 * y * x + 3 * z * x + 4 * x * x + y + 2 * z + 2).rem_euclid(7)
                == 0
        })
        .count();
    assert!(n_sols > 0, "GF(7) sanity: q is satisfiable");
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&q)]], &mut bp);
    let is_whole = basis.iter().any(|b| b.is_whole_ring());
    if is_whole {
        panic!(
            "false UNSAT at fixpoint: q has {} GF(7)^3 roots but basis went to whole ring",
            n_sols
        );
    }
    // The DFS may legitimately come back Unknown/Sat — never Unsat.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => panic!(
            "false UNSAT: q has {} GF(7)^3 roots but split-GB returned Unsat",
            n_sols
        ),
        SplitFindZeroOutcome::Sat(_) | SplitFindZeroOutcome::Unknown => {}
    }
}

/// Property (7) GF(2) edge prime: solve `x = 1` over GF(2). MATH: the
/// unique solution is x = 1. GF(2) is the smallest finite field and is
/// usually a corner case for prime-size assumptions.
#[test]
fn prop_gf2_unit_eq_returns_one() {
    let pr = FfPolyRing::new(ff(2), vec!["x".into()]);
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let originals = vec![pr.clone_poly(&p)];
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![pr.clone_poly(&p)], vec![p]], &mut bp);
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert!(evals_to_zero(&pr, &originals[0], &pt));
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
        }
        other => panic!("GF(2): expected SAT(x=1), got {:?}", other),
    }
}

/// Property (1) ALGEBRAIC IDENTITY at solver scale: `x = a` and `x + 0 = a`
/// must give the same verdict (additive identity). Spec: `+0` is a no-op.
#[test]
fn prop_additive_identity_doesnt_change_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p_a = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let zero_poly = pr.zero();
    let p_b = pr.add(pr.sub(pr.var(0), pr.constant(f.from_int(3))), zero_poly);
    let mut bp1 = BitProp::new(&pr);
    let basis_a = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_a)]], &mut bp1);
    let r_a = split_find_zero(&pr, basis_a, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_b = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_b)]], &mut bp2);
    let r_b = split_find_zero(&pr, basis_b, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(
        cls(&r_a),
        cls(&r_b),
        "(p) and (p + 0) must give same verdict"
    );
    if let (SplitFindZeroOutcome::Sat(pt_a), SplitFindZeroOutcome::Sat(pt_b)) = (&r_a, &r_b) {
        assert_eq!(
            pr.field().to_biguint(&pt_a[0]),
            pr.field().to_biguint(&pt_b[0]),
            "same SAT model"
        );
    }
}

/// Property (1) ALGEBRAIC IDENTITY: scaling a constraint by 1 is a no-op.
/// `(x - 3) = 0` and `1·(x - 3) = 0` must give identical verdicts.
#[test]
fn prop_scalar_one_does_not_change_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let p_a = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let p_b = pr.scale(f.one(), pr.clone_poly(&p_a));
    let mut bp1 = BitProp::new(&pr);
    let basis_a = split_gb(&pr, vec![vec![], vec![pr.clone_poly(&p_a)]], &mut bp1);
    let r_a = split_find_zero(&pr, basis_a, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_b = split_gb(&pr, vec![vec![], vec![p_b]], &mut bp2);
    let r_b = split_find_zero(&pr, basis_b, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r_a), cls(&r_b));
}

/// Property (4) BASIS INVARIANT POST-`split_gb`: every input generator
/// MUST belong to the ideal of its partition's output basis (membership
/// is the SOUNDNESS of a Groebner basis). Pin: simple linear system.
#[test]
fn prop_split_gb_basis_contains_inputs() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let p2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
            vec![pr.clone_poly(&p1), pr.clone_poly(&p2)],
        ],
        &mut bp,
    );
    // Every input must reduce to zero against each partition's GB.
    for b in &basis {
        assert!(
            b.contains(&p1),
            "partition basis must contain input p1 (x - 2)"
        );
        assert!(
            b.contains(&p2),
            "partition basis must contain input p2 (y - 3)"
        );
    }
}

/// Property (3) IDEMPOTENCE on the model layer: calling `split_find_zero`
/// twice on the same fresh basis (rebuilt from the same input both times)
/// yields the same outcome class. Spec: function purity.
#[test]
fn prop_split_find_zero_idempotent_outcome_class() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let xy_minus_1 = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let x_eq_2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp1 = BitProp::new(&pr);
    let basis1 = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&x_eq_2)],
            vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)],
        ],
        &mut bp1,
    );
    let r1 = split_find_zero(&pr, basis1, &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis2 = split_gb(
        &pr,
        vec![
            vec![pr.clone_poly(&x_eq_2)],
            vec![pr.clone_poly(&xy_minus_1), pr.clone_poly(&x_eq_2)],
        ],
        &mut bp2,
    );
    let r2 = split_find_zero(&pr, basis2, &mut bp2);
    let cls = |o: &SplitFindZeroOutcome| match o {
        SplitFindZeroOutcome::Sat(_) => "Sat",
        SplitFindZeroOutcome::Unsat => "Unsat",
        SplitFindZeroOutcome::Unknown => "Unknown",
    };
    assert_eq!(cls(&r1), cls(&r2));
}

// =============================================================================
// HARD-PROBE TESTS — split-gb-orchestration risk surface
// =============================================================================
//
// These tests are spec-driven and engineered to FAIL if a bug hides in the
// multi-partition orchestration: differential against monolithic Buchberger,
// cancellation determinism, edge primes (BN128, curve25519), and pathological
// partition shapes (single partition, constants-only, disconnected components).
//
// Spec sources:
//   * Ideal theory: a system is SAT in GF(p) iff there exists a common
//     zero in GF(p)^n; the ideal is the whole ring iff 1 ∈ I.
//   * Split-GB soundness contract: split_find_zero returns SAT iff a model
//     exists; UNSAT iff (and only if) exhaustive search proved no model;
//     Unknown otherwise. SAT models MUST satisfy every original generator.
//   * Cancellation contract: a pre-cancelled CancelToken means split_find_zero
//     MUST NOT return Sat or Unsat (those are verdicts requiring real work).
//   * Partition admissibility (`admit`): partition 0 admits deg≤1; partition 1
//     admits deg≤1 ∧ terms≤2; partition idx≥2 is never admitted (but ideals can
//     still hold higher-degree generators in their basis).

/// BN128 / BN254 scalar field prime (~2^254). Used as a real ZK use case.
fn bn128_field() -> PrimeField {
    PrimeField::new(
        BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap(),
    )
}

/// Curve25519 base field prime (2^255 - 19).
fn curve25519_field() -> PrimeField {
    PrimeField::new(
        BigUint::parse_bytes(
            b"57896044618658097711785492504343953926634992332820282019728792003956564819949",
            10,
        )
        .unwrap(),
    )
}

/// Build a monolithic ideal (single basis containing every original
/// generator). Used as the spec oracle in differential tests against
/// split-GB.
fn monolithic_is_whole_ring(pr: &FfPolyRing, generators: Vec<Poly>) -> bool {
    let ideal = Ideal::new(pr, generators);
    ideal.is_whole_ring()
}

// -----------------------------------------------------------------------------
// (d) Single-partition: split_gb on k=1 must agree with monolithic Buchberger.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: a one-partition split-GB returns a basis whose
/// `is_whole_ring` disagrees with the monolithic Buchberger verdict.
/// SPEC: `Ideal::new` and `split_gb(k=1, gens)` ideal-theoretically build
/// the SAME ideal; their `is_whole_ring()` must match.
#[test]
fn hard_single_partition_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // x = 1 ∧ x = 2 over GF(7) → UNSAT.
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&g1), pr.clone_poly(&g2)]],
        &mut bp,
    );
    let split_whole = basis.iter().any(|b| b.is_whole_ring());
    let mono_whole = monolithic_is_whole_ring(&pr, vec![g1, g2]);
    assert_eq!(
        split_whole, mono_whole,
        "split_gb(k=1) whole-ring verdict must match monolithic Buchberger"
    );
}

/// HYPOTHESIS: a one-partition SAT system causes split_gb to spuriously
/// declare whole-ring.
/// SPEC: a system with at least one common zero in GF(p) is NOT the whole
/// ring (since 1 cannot vanish at that zero).
#[test]
fn hard_single_partition_sat_not_whole_ring() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // x = 2 ∧ y = 3 over GF(5) → SAT (unique point).
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "SAT single-partition cannot reduce to whole ring"
    );
}

// -----------------------------------------------------------------------------
// (a) Multi-partition differential: split-GB whole-ring iff monolithic GB
// is whole-ring (the soundness invariant).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_gb on a SAT system with multiple partitions
/// spuriously detects UNSAT (whole ring).
/// SPEC: x = 1 in partition 0 (linear), and x·y - 1 = 0 with y = 1 in
/// partition 1 (nonlinear), is jointly SAT with model (1, 1); monolithic
/// Buchberger must NOT be whole ring; therefore split_gb must NOT have any
/// whole-ring partition.
#[test]
fn hard_multi_partition_sat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let g_xy = pr.sub(xy, pr.constant(f.one()));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(1)));

    let all = vec![
        pr.clone_poly(&g_x),
        pr.clone_poly(&g_xy),
        pr.clone_poly(&g_y),
    ];
    let mono_whole = monolithic_is_whole_ring(&pr, all);

    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g_x, g_y], vec![g_xy]], &mut bp);
    let split_whole = basis.iter().any(|b| b.is_whole_ring());
    assert_eq!(
        split_whole, mono_whole,
        "split_gb whole-ring verdict must match monolithic Buchberger"
    );
    assert!(
        !split_whole,
        "joint system has model (1,1) ⇒ not whole ring"
    );
}

/// HYPOTHESIS: multi-partition GF(p)-UNSAT system is correctly detected by
/// the orchestrator's exhaustive search.
/// SPEC: x + y = 0 ∧ x·y - 1 = 0 over GF(7) forces x² = -1 = 6, a
/// non-residue mod 7 (QRs are {1, 2, 4}). Joint system has no solution
/// in GF(7), so split_find_zero (which runs an exhaustive small-prime
/// search) must return Unsat. NOTE: monolithic Buchberger on the raw
/// {x+y, x·y-1} (without field polynomials) does NOT collapse to {1};
/// the system has roots in F_49 ⊃ GF(7). The whole-ring comparison only
/// makes sense after adding field polys x^7-x, y^7-y; we skip it.
#[test]
fn hard_multi_partition_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g_lin = pr.add(pr.var(0), pr.var(1));
    let g_nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.one()));
    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_lin)]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_nl)]),
    ];
    let outcome = split_find_zero(&pr, split_basis, &mut bp);
    match outcome {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!(
            "split_find_zero on GF(7)-UNSAT system must return Unsat, got {:?}",
            other
        ),
    }
}

// -----------------------------------------------------------------------------
// (e) Partition containing only constants / pathological edge shapes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: a partition whose initial basis contains 1 (already whole
/// ring) is not detected as UNSAT.
/// SPEC: any basis containing a nonzero constant is the whole ring; the
/// orchestrator must return Unsat without exploring.
#[test]
fn hard_partition_with_one_already_whole_ring() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let mut bp = BitProp::new(&pr);
    // Partition 1 already has the constant 1 ⇒ whole ring from the start.
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![]),
        Ideal::from_gb(&pr, vec![pr.one()]),
    ];
    // The split_find_zero contract on a system with a whole-ring partition
    // and no completing original constraints: the first-frame fast path
    // returns NoZero{exhaustive:true} (Unsat). Sound because 1 ∈ basis
    // means the ideal is the whole ring.
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Unsat => {}
        other => panic!(
            "whole-ring partition (basis = {{1}}) must yield Unsat, got {:?}",
            other
        ),
    }
}

/// HYPOTHESIS: a partition containing only the zero polynomial (which is
/// the trivial ideal {0}) is mishandled.
/// SPEC: zero generators define the ZERO ideal; {0} is NOT the whole ring
/// and trivially has every point of GF(p)^n as a zero, so an empty-input
/// system over k vars must return SAT.
#[test]
fn hard_partition_zero_generators_not_whole_ring() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![], vec![]], &mut bp);
    assert_eq!(basis.len(), 2);
    for b in &basis {
        assert!(
            !b.is_whole_ring(),
            "zero ideal {{0}} is NOT the whole ring"
        );
    }
    // SAT contract: every point is a zero of {0}, so split_find_zero must
    // return some SAT model.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => assert_eq!(pt.len(), 2),
        other => panic!(
            "empty-ideal system must be SAT (every point is a zero), got {:?}",
            other
        ),
    }
}

/// HYPOTHESIS: a system where partition 1 (the nonlinear partition) is
/// empty while partition 0 carries every constraint is mishandled.
/// SPEC: the union of bases is the original ideal; partition shape MUST
/// NOT affect verdict.
#[test]
fn hard_all_constraints_in_one_partition_other_empty() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // x = 3 (deg-1, single term — admitted by partition 0).
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![pr.clone_poly(&g)], vec![]], &mut bp);
    // Partition 0 should have the constraint; partition 1 is empty.
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "consistent single-constraint system is not whole ring"
    );
    // SAT verdict with x = 3 from split_find_zero.
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(3u32));
        }
        other => panic!("expected SAT(x=3), got {:?}", other),
    }
}

// -----------------------------------------------------------------------------
// (b) Pre-cancelled CancelToken → must NOT return Sat or Unsat.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero_cancel with a pre-cancelled token still
/// returns a verdict (Sat or Unsat). That would be UNSOUND — a verdict
/// requires search work.
/// SPEC: pre-cancelled token MUST yield Err(Cancelled).
#[test]
fn hard_pre_cancelled_yields_cancelled_not_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    // Concrete SAT system: x = 3. Without cancel, this is Sat.
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![g])];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled token MUST yield Err(Cancelled), not a verdict"
    );
}

/// HYPOTHESIS: pre-cancelled token on a multi-partition SAT system still
/// yields Sat. Spec: pre-cancelled → Cancelled.
#[test]
fn hard_pre_cancelled_multi_partition_yields_cancelled() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(3)));
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![g1]),
        Ideal::from_gb(&pr, vec![g2]),
    ];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled multi-partition SAT must yield Cancelled"
    );
}

/// HYPOTHESIS: pre-cancelled token on a UNSAT system still yields Unsat.
/// SPEC: pre-cancelled → Cancelled.
#[test]
fn hard_pre_cancelled_unsat_still_cancelled() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let split_basis: SplitGb = vec![Ideal::from_gb(&pr, vec![g1, g2])];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled UNSAT input must yield Cancelled, not Unsat"
    );
}

// -----------------------------------------------------------------------------
// (c) Mid-pipeline cancel: fire AFTER add_generators (split_gb_cancel returns)
//     but BEFORE split_find_zero_cancel; the next phase must report Cancelled.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: cancellation set between split_gb_cancel and
/// split_find_zero_cancel is ignored by the search phase.
/// SPEC: a cancel-aware API MUST honor cancellation on entry.
#[test]
fn hard_mid_pipeline_cancel_between_extend_and_search() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(4)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::new();
    // Phase 1: build the split GB with a non-fired cancel token.
    let split_basis =
        split_gb_cancel(&pr, vec![vec![g]], &mut bp, &cancel).expect("phase 1 should complete");
    // Phase 2: fire cancel BEFORE search.
    cancel.cancel();
    let out = split_find_zero_cancel(&pr, split_basis, &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "mid-pipeline cancel (fired between phases) must be honored, got {:?}",
        out
    );
}

/// HYPOTHESIS: cancellation set between extend_cancel returning and the
/// next call to extend_cancel is ignored.
/// SPEC: cancel-aware APIs honor cancellation on every call entry.
#[test]
fn hard_mid_pipeline_cancel_between_two_extend_calls() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::new();
    let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
    // First extend completes successfully.
    let mid = split_gb_extend_cancel(&pr, starting, vec![vec![g1]], &mut bp, &cancel)
        .expect("first extend should succeed");
    // Cancel before the second extend.
    cancel.cancel();
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let out = split_gb_extend_cancel(&pr, mid, vec![vec![g2]], &mut bp, &cancel);
    assert!(
        matches!(out, Err(Cancelled)),
        "second extend after mid-pipeline cancel must return Cancelled"
    );
}

// -----------------------------------------------------------------------------
// Big primes — BN128 / curve25519. Historically big-prime arithmetic edge
// cases harbor bugs (cf. round 5 H1 bitprop bit-cache, round 7 J1 bit-width
// guard). Probe both with concrete SAT and UNSAT systems whose verdict is
// fixed by elementary number theory.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_gb on a trivial concrete SAT system over BN128 fails
/// (returns Unsat or whole-ring on the input ideal).
/// SPEC: {x - 7, y - 11} over GF(BN128) is jointly SAT with the unique
/// model (7, 11). The basis MUST NOT be whole ring.
#[test]
fn hard_bn128_concrete_sat_not_whole_ring() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(7)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(11)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "BN128 SAT system must not be whole ring"
    );
}

/// HYPOTHESIS: split_gb on a concrete BN128 UNSAT system fails to detect
/// UNSAT (no whole-ring partition).
/// SPEC: {x - 7, x - 13} over GF(BN128) is UNSAT (7 ≠ 13 mod the prime);
/// monolithic Buchberger reduces to the constant (7 - 13) = -6 ≠ 0.
#[test]
fn hard_bn128_concrete_unsat_matches_monolithic() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(7)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(13)));
    let all = vec![pr.clone_poly(&g1), pr.clone_poly(&g2)];
    assert!(
        monolithic_is_whole_ring(&pr, all),
        "spec: monolithic BN128 must detect this UNSAT"
    );
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "split_gb on BN128 UNSAT must produce a whole-ring partition"
    );
}

/// HYPOTHESIS: curve25519 prime arithmetic in the multi-partition flow
/// flips a SAT verdict.
/// SPEC: {x - 42} over GF(curve25519) with partition split: linear
/// partition holds the constraint; the basis must not be whole ring.
#[test]
fn hard_curve25519_concrete_sat_not_whole_ring() {
    let pr = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(42)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g]], &mut bp);
    assert!(
        !basis.iter().any(|b| b.is_whole_ring()),
        "curve25519 SAT must not produce a whole-ring basis"
    );
}

/// HYPOTHESIS: curve25519 UNSAT detection is broken in multi-partition.
/// SPEC: {x - 1, x - 99} over GF(curve25519): UNSAT (1 ≠ 99 mod p).
#[test]
fn hard_curve25519_concrete_unsat_detected() {
    let pr = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(99)));
    let all = vec![pr.clone_poly(&g1), pr.clone_poly(&g2)];
    assert!(
        monolithic_is_whole_ring(&pr, all),
        "spec: monolithic curve25519 must detect this UNSAT"
    );
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "split_gb on curve25519 UNSAT must produce a whole-ring partition"
    );
}

/// HYPOTHESIS: a multi-partition BN128 SAT system returns Sat but the
/// returned model fails to satisfy every original generator (most likely
/// a subtle "model from one partition" bug).
/// SPEC: a SAT verdict's model MUST zero EVERY original generator
/// (across all partitions, before the partition split was applied).
#[test]
fn hard_bn128_multi_partition_sat_model_satisfies_all_originals() {
    let pr = FfPolyRing::new(bn128_field(), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // Cross-partition constraints: x = 5 (linear, partition 0),
    // x·y = 35 ⇒ y = 7 once x = 5 (nonlinear, partition 1).
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let g_xy =
        pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.from_int(35)));
    let all_originals = vec![pr.clone_poly(&g_x), pr.clone_poly(&g_xy)];

    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_x)]),
        Ideal::from_gb(&pr, vec![pr.clone_poly(&g_xy)]),
    ];
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(model) => {
            assert_eq!(model.len(), 2);
            for g in &all_originals {
                let v = eval_poly(&pr, g, &model);
                assert!(
                    pr.field().is_zero(&v),
                    "SAT model must zero every original generator"
                );
            }
        }
        // Unknown is permitted on big primes if the brancher cannot complete
        // enumeration; this test is about SOUNDNESS of any SAT it does return.
        SplitFindZeroOutcome::Unknown => {}
        SplitFindZeroOutcome::Unsat => panic!(
            "system has model (5, 7) — must not return Unsat"
        ),
    }
}

// -----------------------------------------------------------------------------
// "Many partitions": stress the orchestrator with k > 2 (forcing the
// `(0..k)` loops in the fixpoint body to actually iterate).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the orchestrator's `(0..k)` loops are silently wrong for k > 2
/// (where k > 2 partitions are constructed manually — the default builder
/// uses k = 2). Each partition holds independent constraints whose
/// conjunction has a known SAT verdict.
/// SPEC: {x - 1, y - 2, z - 3} distributed across k = 3 partitions has the
/// unique model (1, 2, 3) in GF(7); no partition becomes whole ring.
#[test]
fn hard_many_partitions_sat_no_partition_whole_ring() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let f = pr.field();
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(2)));
    let g_z = pr.sub(pr.var(2), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    // Note: `admit` only admits partition indices 0, 1; partitions ≥ 2 are
    // never admitted via cross-partition propagation. But the
    // `split_gb_cancel` builder still EXTENDS every partition with its OWN
    // new_polys (the per-i `extend_with_cancel` call). So extra partitions
    // hold their own initial generators correctly.
    let basis = split_gb(
        &pr,
        vec![vec![g_x], vec![g_y], vec![g_z]],
        &mut bp,
    );
    assert_eq!(basis.len(), 3);
    for (i, b) in basis.iter().enumerate() {
        assert!(
            !b.is_whole_ring(),
            "partition {} on SAT input must not be whole ring",
            i
        );
    }
}

/// HYPOTHESIS: a system distributed across 3 partitions where partition 2
/// holds the only inconsistent pair fails to be detected as UNSAT.
/// SPEC: x = 1 ∧ x = 2 in partition 2 (over GF(5)) makes partition 2
/// whole-ring after its own extend. Cross-partition propagation isn't
/// needed because the per-partition extend handles each partition
/// independently. The disjunction `any(is_whole_ring)` MUST fire.
#[test]
fn hard_many_partitions_unsat_in_third_partition_detected() {
    let pr = FfPolyRing::new(ff(5), vec!["x".into()]);
    let f = pr.field();
    let g_a = pr.sub(pr.var(0), pr.constant(f.from_int(0)));
    let g_b = pr.sub(pr.var(0), pr.constant(f.from_int(0))); // dup
    let g_inc1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g_inc2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(
        &pr,
        vec![vec![g_a], vec![g_b], vec![g_inc1, g_inc2]],
        &mut bp,
    );
    assert_eq!(basis.len(), 3);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "intra-partition UNSAT in partition 2 must produce whole-ring"
    );
}

// -----------------------------------------------------------------------------
// Repeated / duplicate generators (idempotence).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: adding the same generator twice changes the verdict.
/// SPEC: ideals are sets; duplicates make no semantic difference.
#[test]
fn hard_duplicate_generators_preserve_verdict() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(4)));
    let mut bp1 = BitProp::new(&pr);
    let basis_one = split_gb(&pr, vec![vec![pr.clone_poly(&g)]], &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let basis_dup = split_gb(
        &pr,
        vec![vec![pr.clone_poly(&g), pr.clone_poly(&g), pr.clone_poly(&g)]],
        &mut bp2,
    );
    assert_eq!(
        basis_one.iter().any(|b| b.is_whole_ring()),
        basis_dup.iter().any(|b| b.is_whole_ring()),
        "duplicate generators must not change the whole-ring verdict"
    );
    // Both must agree the SAT model is x = 4.
    let out1 = split_find_zero(&pr, basis_one, &mut bp1);
    let out2 = split_find_zero(&pr, basis_dup, &mut bp2);
    for (i, out) in [&out1, &out2].iter().enumerate() {
        match out {
            SplitFindZeroOutcome::Sat(pt) => {
                assert_eq!(
                    pr.field().to_biguint(&pt[0]),
                    BigUint::from(4u32),
                    "outcome {} must be x = 4",
                    i
                );
            }
            other => panic!("outcome {}: expected SAT(x=4), got {:?}", i, other),
        }
    }
}

// -----------------------------------------------------------------------------
// Disconnected partition components: 4 independent univariate constraints
// in disjoint variable sets stress the orchestration's many-partition
// extend loop without cross-partition propagation interactions.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the orchestrator's multi-partition extend mishandles fully
/// disjoint variable sets (each constraint touches a unique variable, so
/// there's no cross-partition propagation; the verdict comes solely from
/// independent per-partition GB).
/// SPEC: 4 disjoint linear constraints {x0 = 0, x1 = 1, x2 = 2, x3 = 3}
/// in GF(5)^4 has the unique point (0, 1, 2, 3) ⇒ SAT and not whole-ring.
#[test]
fn hard_disconnected_components_sat() {
    let pr = FfPolyRing::new(
        ff(5),
        vec!["x0".into(), "x1".into(), "x2".into(), "x3".into()],
    );
    let f = pr.field();
    let g = |i: usize, v: i64| pr.sub(pr.var(i), pr.constant(f.from_int(v)));
    let mut bp = BitProp::new(&pr);
    // 4 partitions, each with one independent constraint.
    let basis = split_gb(
        &pr,
        vec![vec![g(0, 0)], vec![g(1, 1)], vec![g(2, 2)], vec![g(3, 3)]],
        &mut bp,
    );
    assert_eq!(basis.len(), 4);
    for (i, b) in basis.iter().enumerate() {
        assert!(
            !b.is_whole_ring(),
            "disjoint constraint in partition {} ⇒ not whole ring",
            i
        );
    }
}

// -----------------------------------------------------------------------------
// admit() partition-index boundary on big primes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the `admit` partition-index guard fires differently on big
/// primes (it shouldn't — the predicate is purely structural).
/// SPEC: admit(_, idx ≥ 2, _) = false regardless of the polynomial or
/// the prime, since it doesn't depend on the field at all.
#[test]
fn hard_admit_idx_ge_2_rejects_on_big_primes() {
    let pr_bn128 = FfPolyRing::new(bn128_field(), vec!["x".into()]);
    let lin = pr_bn128.var(0);
    assert!(!admit(&pr_bn128, 2, &lin), "BN128: idx=2 never admits");
    assert!(!admit(&pr_bn128, 7, &lin), "BN128: idx=7 never admits");

    let pr_25519 = FfPolyRing::new(curve25519_field(), vec!["x".into()]);
    let lin2 = pr_25519.var(0);
    assert!(!admit(&pr_25519, 2, &lin2), "curve25519: idx=2 never admits");
}

// -----------------------------------------------------------------------------
// Edge primes — GF(2), GF(3): smallest possible fields.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: GF(2) tiny-prime corner case is mishandled.
/// SPEC: over GF(2), x = 1 is SAT with unique model x = 1. Verifying the
/// split_find_zero pipeline on the smallest prime.
#[test]
fn hard_gf2_sat_single_var() {
    let pr = FfPolyRing::new(ff(2), vec!["x".into()]);
    let f = pr.field();
    let g = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g]], &mut bp);
    assert!(!basis.iter().any(|b| b.is_whole_ring()));
    match split_find_zero(&pr, basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(1u32));
        }
        other => panic!("GF(2): expected SAT(x=1), got {:?}", other),
    }
}

/// HYPOTHESIS: GF(3) tiny-prime UNSAT is not detected.
/// SPEC: x = 1 ∧ x = 2 over GF(3) is UNSAT (1 ≠ 2 mod 3 ⇒ 1 ∈ I).
#[test]
fn hard_gf3_unsat_single_var() {
    let pr = FfPolyRing::new(ff(3), vec!["x".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let basis = split_gb(&pr, vec![vec![g1, g2]], &mut bp);
    assert!(
        basis.iter().any(|b| b.is_whole_ring()),
        "GF(3): {{x-1, x-2}} reduces to gcd = 1 ⇒ whole ring"
    );
}

// -----------------------------------------------------------------------------
// Differential: split_find_zero verdict matches Buchberger whole-ring
// verdict on a curated UNSAT/SAT corpus across multiple primes.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero verdict for a small-prime UNSAT system
/// disagrees with the monolithic Buchberger whole-ring oracle.
/// SPEC: split_find_zero returns Unsat iff exhaustive search proves no
/// model exists; for small primes (round-robin is exhaustive), this is
/// equivalent to monolithic Buchberger declaring whole-ring.
#[test]
fn hard_differential_split_vs_monolithic_corpus() {
    // Each case: (prime, vars, generators, expected_sat).
    let cases: Vec<(PrimeField, Vec<String>, Vec<(usize, i64)>, bool)> = vec![
        // GF(5): x = 2 ∧ y = 3 → SAT (unique).
        (ff(5), vec!["x".into(), "y".into()], vec![(0, 2), (1, 3)], true),
        // GF(7): x = 1 ∧ x = 2 → UNSAT.
        (ff(7), vec!["x".into()], vec![(0, 1), (0, 2)], false),
        // GF(11): x = 5 ∧ y = 7 → SAT.
        (
            ff(11),
            vec!["x".into(), "y".into()],
            vec![(0, 5), (1, 7)],
            true,
        ),
        // GF(257): x = 100 ∧ x = 200 → UNSAT.
        (ff(257), vec!["x".into()], vec![(0, 100), (0, 200)], false),
        // GF(1009): x = 500 → SAT.
        (ff(1009), vec!["x".into()], vec![(0, 500)], true),
    ];
    for (idx, (field, var_names, eqs, expect_sat)) in cases.into_iter().enumerate() {
        let pr = FfPolyRing::new(field, var_names);
        let f = pr.field();
        let mut gens: Vec<Poly> = Vec::new();
        for (var, val) in &eqs {
            let g = pr.sub(pr.var(*var), pr.constant(f.from_int(*val)));
            gens.push(g);
        }
        let all_for_mono: Vec<Poly> = gens.iter().map(|g| pr.clone_poly(g)).collect();
        let mono_whole = monolithic_is_whole_ring(&pr, all_for_mono);
        assert_eq!(
            mono_whole, !expect_sat,
            "case {} monolithic oracle disagrees with expected",
            idx
        );

        let mut bp = BitProp::new(&pr);
        let split_basis: SplitGb =
            vec![Ideal::from_gb(&pr, gens), Ideal::from_gb(&pr, vec![])];
        let outcome = split_find_zero(&pr, split_basis, &mut bp);
        match (outcome, expect_sat) {
            (SplitFindZeroOutcome::Sat(_), true) => {}
            (SplitFindZeroOutcome::Unsat, false) => {}
            (other, _) => panic!(
                "case {}: split_find_zero outcome {:?} disagrees with expected_sat={}",
                idx, other, expect_sat
            ),
        }
    }
}

// -----------------------------------------------------------------------------
// `build_partitions` sanity (the default partition layout shared by
// conjunctive and cached build paths).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: `build_partitions` returns provenance not parallel to its
/// gens (this would be a silent invariant break).
/// SPEC: every per-basis (gens, provenance) pair has equal length.
#[test]
fn hard_build_partitions_provenance_parallel_to_gens() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // 3 originals: one degree-1-single-term (admitted everywhere),
    // one degree-1-3-term (admitted by partition 0 only), one nonlinear.
    let p0 = pr.var(0);
    let p1 = pr.add(
        pr.add(pr.var(0), pr.var(1)),
        pr.constant(f.from_int(2)),
    ); // 3 terms, deg 1
    let p2 = pr.mul(pr.var(0), pr.var(1)); // deg 2
    let originals = vec![pr.clone_poly(&p0), pr.clone_poly(&p1), pr.clone_poly(&p2)];
    let bitsums: Vec<Poly> = vec![];
    let (gens, prov) = build_partitions(&pr, &originals, &bitsums);
    assert_eq!(gens.len(), 2, "default layout has 2 partitions");
    assert_eq!(prov.len(), 2);
    for (i, (g_i, p_i)) in gens.iter().zip(prov.iter()).enumerate() {
        assert_eq!(
            g_i.len(),
            p_i.len(),
            "partition {} provenance length must match gens length",
            i
        );
    }
    // Spec: partition 1 holds ALL originals (in order); partition 0 holds
    // only originals admitted as deg≤1.
    assert_eq!(
        gens[1].len(),
        originals.len(),
        "partition 1 (nonlinear) holds all originals"
    );
    // partition 0 admits p0 (1 term, deg 1) and p1 (3 terms, deg 1) but
    // not p2 (deg 2).
    assert_eq!(
        gens[0].len(),
        2,
        "partition 0 (linear) holds the deg-1 originals"
    );
}

// -----------------------------------------------------------------------------
// Cancellation during a long-running multi-partition extend: cancel
// before the extend call and after the partition has many generators.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: cancellation set before the very first iteration of
/// run_fixpoint inside `split_gb_extend_cancel` is dropped.
/// SPEC: pre-cancelled extend → Err(Cancelled), regardless of how
/// nontrivial the starting basis is.
#[test]
fn hard_extend_cancel_pre_cancelled_with_nontrivial_starting() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let f = pr.field();
    let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let g2 = pr.sub(pr.var(1), pr.constant(f.from_int(4)));
    let mut bp = BitProp::new(&pr);
    // Build a nontrivial starting basis with a never-firing token.
    let starting =
        split_gb_cancel(&pr, vec![vec![g1, g2]], &mut bp, &CancelToken::none())
            .expect("phase 1 ok");
    // Now extend with a fresh, pre-cancelled token.
    let new_g = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.constant(f.from_int(12)));
    let out = split_gb_extend_cancel(
        &pr,
        starting,
        vec![vec![pr.clone_poly(&new_g)]],
        &mut bp,
        &CancelToken::cancelled(),
    );
    assert!(
        matches!(out, Err(Cancelled)),
        "pre-cancelled extend with nontrivial starting basis must return Cancelled"
    );
}

// -----------------------------------------------------------------------------
// Symmetry: the split-GB whole-ring verdict must be invariant under
// permutation of partitions (which partition gets which generator).
// -----------------------------------------------------------------------------

/// HYPOTHESIS: the verdict of split_gb depends on which partition holds
/// each linear constraint.
/// SPEC: for two linear constraints whose conjunction is UNSAT, swapping
/// which partition gets each must not change the whole-ring detection.
#[test]
fn hard_partition_swap_invariance_unsat() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let f = pr.field();
    let make_g = || {
        let g1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
        let g2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
        (g1, g2)
    };
    let mut bp1 = BitProp::new(&pr);
    let (a1, b1) = make_g();
    let basis_ab = split_gb(&pr, vec![vec![a1], vec![b1]], &mut bp1);
    let mut bp2 = BitProp::new(&pr);
    let (a2, b2) = make_g();
    let basis_ba = split_gb(&pr, vec![vec![b2], vec![a2]], &mut bp2);
    // Both must detect UNSAT (some partition is whole ring).
    assert!(
        basis_ab.iter().any(|b| b.is_whole_ring())
            && basis_ba.iter().any(|b| b.is_whole_ring()),
        "partition swap must not change UNSAT detection"
    );
}

// -----------------------------------------------------------------------------
// Cross-engine: split_find_zero verdict matches monolithic
// `gb::model::find_zero_cancel` whole-ring/Sat verdict on a tiny
// zero-dimensional system.
// -----------------------------------------------------------------------------

/// HYPOTHESIS: split_find_zero returns SAT but the SAT model contradicts
/// what an independent monolithic finder would produce.
/// SPEC: for a unique-solution zero-dim system, the SAT model is unique
/// up to GF semantics; both the split path and a monolithic Ideal::new
/// followed by an is_whole_ring check must agree the system is NOT whole-ring.
#[test]
fn hard_zero_dim_unique_sat_split_agrees_with_mono() {
    let pr = FfPolyRing::new(ff(13), vec!["x".into(), "y".into()]);
    let f = pr.field();
    // x = 5 ∧ y = 7 → unique SAT model.
    let g_x = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let g_y = pr.sub(pr.var(1), pr.constant(f.from_int(7)));
    let mono = Ideal::new(
        &pr,
        vec![pr.clone_poly(&g_x), pr.clone_poly(&g_y)],
    );
    assert!(!mono.is_whole_ring(), "spec: SAT system is not whole ring");
    assert!(mono.is_zero_dim(), "spec: pinned system is zero-dim");

    let mut bp = BitProp::new(&pr);
    let split_basis: SplitGb = vec![
        Ideal::from_gb(&pr, vec![g_x]),
        Ideal::from_gb(&pr, vec![g_y]),
    ];
    match split_find_zero(&pr, split_basis, &mut bp) {
        SplitFindZeroOutcome::Sat(pt) => {
            assert_eq!(pr.field().to_biguint(&pt[0]), BigUint::from(5u32));
            assert_eq!(pr.field().to_biguint(&pt[1]), BigUint::from(7u32));
        }
        other => panic!("expected unique SAT(5, 7), got {:?}", other),
    }
}
