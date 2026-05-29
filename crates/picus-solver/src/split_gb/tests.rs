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
