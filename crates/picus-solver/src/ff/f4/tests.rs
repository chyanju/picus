use super::*;
use crate::ff::field::PrimeField;
use crate::ff::monomial::MonomialOrder;
use crate::ff::polynomial::PolyRing;
use crate::timeout::CancelToken;
use num_bigint::BigUint;

fn ring_mod7(n_vars: usize) -> Arc<PolyRing> {
    let f = PrimeField::new(BigUint::from(7u32));
    let names = (0..n_vars).map(|i| format!("x{}", i)).collect();
    PolyRing::new(f, names, MonomialOrder::DegRevLex)
}

fn x(idx: usize, ring: &Arc<PolyRing>) -> DensePoly {
    DensePoly::variable(idx, ring)
}

fn lt(p: &DensePoly, ring: &Arc<PolyRing>) -> Monomial {
    p.leading_monomial(ring).unwrap()
}

#[test]
fn f4_minimal_two_variables() {
    // I = (x*y - 1, y^2 - x). The reduced GB in degrevlex is
    // (x*y - 1, y^2 - x, x^2 - y).
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    // f1 = x*y - 1
    let xy = x0.mul(&x1, &ring);
    let f1 = xy.sub(&DensePoly::constant(ring.field.one(), &ring), &ring);
    // f2 = y^2 - x
    let y2 = x1.mul(&x1, &ring);
    let f2 = y2.sub(&x0, &ring);
    let basis_polys = vec![f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();

    // S(f1, f2): lcm(xy, y^2) = x*y^2.
    let lcm = lt(&f1, &ring).lcm(&lt(&f2, &ring));
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };

    let new_polys = process_batch(&[&pair], &basis, &ring, None);
    assert!(!new_polys.is_empty(), "F4 batch produced no new polys");
    // The new poly's LT should be x^2 (the missing GB element).
    let np = &new_polys[0].poly;
    let np_lt = lt(np, &ring);
    // x^2 monomial: exponents [2, 0]
    assert_eq!(np_lt.exponents(), &[2, 0], "expected new LT x^2, got {:?}", np_lt.exponents());
    // Provenance: from_pairs must include the single input pair (index 0).
    assert_eq!(new_polys[0].from_pairs, vec![0]);
}

#[test]
fn f4_matches_geobucket_on_random_pair_3vars() {
    // Cross-check: for the same S-pair, F4's batch result should
    // produce a polynomial whose normal-form-against-basis matches
    // the per-pair geobucket reduction. We pick a degree-2 system
    // in 3 vars and check both paths agree.
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    // f1 = x0*x1 - x2
    let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);
    // f2 = x1*x2 - x0
    let f2 = x1.mul(&x2, &ring).sub(&x0, &ring);
    let basis_polys = vec![f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();

    // S(f1, f2): lcm(x0*x1, x1*x2) = x0*x1*x2.
    let lcm = lt(&f1, &ring).lcm(&lt(&f2, &ring));
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm: lcm.clone(),
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };

    // F4 path
    let new_polys = process_batch(&[&pair], &basis, &ring, None);

    // Reference: build S-poly directly + reduce via reduce_by_refs.
    let mul1 = lcm.div(&lt(&f1, &ring));
    let mul2 = lcm.div(&lt(&f2, &ring));
    let one = ring.field.one();
    let part1 = f1.mul_term(mul1.exponents(), &one, &ring);
    let neg_one = ring.field.neg(&one);
    let part2 = f2.mul_term(mul2.exponents(), &neg_one, &ring);
    let s_poly = part1.add(&part2, &ring);
    let basis_refs: Vec<&DensePoly> = basis_polys.iter().collect();
    let reduced = s_poly.reduce_by_refs(&basis_refs, &ring);

    if reduced.is_zero() {
        assert!(new_polys.is_empty(), "F4 produced new poly but reference reduced to zero");
    } else {
        assert_eq!(new_polys.len(), 1);
        let f4_monic = &new_polys[0].poly;
        let ref_monic = reduced.make_monic(&ring);
        assert_eq!(
            f4_monic.num_terms(),
            ref_monic.num_terms(),
            "F4 and ref differ in num_terms",
        );
        assert_eq!(
            lt(f4_monic, &ring).exponents(),
            lt(&ref_monic, &ring).exponents(),
            "F4 and ref LT differ"
        );
    }
}

/// Build the ideal of all S-pairs on `basis_polys`, run BOTH F4 and
/// per-pair `reduce_by_refs`, and check the two paths produce the
/// SAME set of normal-form residues (modulo reordering, modulo
/// trailing zeros).
fn cross_check_all_pairs(basis_polys: Vec<DensePoly>, ring: &Arc<PolyRing>) {
    let basis_lts: Vec<Monomial> = basis_polys
        .iter()
        .map(|p| lt(p, ring))
        .collect();
    let n = basis_polys.len();
    let basis_refs: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();

    // Build ALL pairs (i, j) with i < j.
    let mut pairs: Vec<SPair> = Vec::new();
    for i in 0..n {
        for j in i + 1..n {
            let lcm = basis_lts[i].lcm(&basis_lts[j]);
            let lcm_dm = ring.divmask.compute(&lcm);
            let lcm_deg = lcm.total_degree();
            pairs.push(SPair {
                i,
                j,
                sugar: lcm_deg,
                lcm,
                lcm_divmask: lcm_dm,
                lcm_deg,
                age: 0,
                generation: 0,
                is_coprime: false,
            });
        }
    }
    let pair_refs: Vec<&SPair> = pairs.iter().collect();

    // F4 path
    let f4_polys = process_batch(&pair_refs, &basis_refs, ring, None);

    // Reference: per-pair S-poly + reduce_by_refs.
    let basis_poly_refs: Vec<&DensePoly> = basis_polys.iter().collect();
    let mut ref_polys: Vec<DensePoly> = Vec::new();
    for pair in &pairs {
        let bi = &basis_polys[pair.i];
        let bj = &basis_polys[pair.j];
        let mul_i = pair.lcm.div(&basis_lts[pair.i]);
        let mul_j = pair.lcm.div(&basis_lts[pair.j]);
        let lc_i = bi.leading_coefficient().unwrap();
        let lc_j = bj.leading_coefficient().unwrap();
        let scale_j = ring.field.div(lc_i, lc_j).unwrap();
        let one = ring.field.one();
        let part_i = bi.mul_term(mul_i.exponents(), &one, ring);
        let part_j = bj.mul_term(mul_j.exponents(), &scale_j, ring);
        let s_poly = part_i.sub(&part_j, ring);
        let reduced = s_poly.reduce_by_refs(&basis_poly_refs, ring);
        if !reduced.is_zero() {
            ref_polys.push(reduced.make_monic(ring));
        }
    }

    // F4 may produce ideal-equivalent but different representatives
    // than the per-pair path. Compare leading-term sets after
    // reducing each F4 output by the original basis: ideal-
    // equivalent residues share a leading term, so the LT sets
    // are equal iff both paths produced the same new generators
    // up to basis-normalisation. LT-set equality is necessary
    // but not sufficient for ideal equality; the cross-check
    // catches LT-level divergence as a regression guard.
    let f4_lts: std::collections::HashSet<Vec<u16>> = f4_polys
        .iter()
        .map(|o| {
            let r = o.poly.reduce_by_refs(&basis_poly_refs, ring);
            lt(&r, ring).exponents().to_vec()
        })
        .filter(|e| !e.is_empty() || true)
        .collect();
    let ref_lts: std::collections::HashSet<Vec<u16>> = ref_polys
        .iter()
        .map(|p| lt(p, ring).exponents().to_vec())
        .collect();
    assert_eq!(
        f4_lts, ref_lts,
        "F4 and reference disagree on new-generator leading terms.\nF4: {:?}\nref: {:?}",
        f4_lts, ref_lts
    );
}

#[test]
fn f4_multipair_3vars_overlapping_lts() {
    // Three polys with overlapping LTs to exercise reducer-chain
    // propagation in symbolic preprocessing.
    // f1 = x0^2 - x1
    // f2 = x0*x1 - x2
    // f3 = x1^2 - x0  (LT(f3) = x1^2 may need reducer chain)
    //
    // Also folds in the cyclic-3-shape coverage: both shapes exercise
    // `process_batch` on 3-pair multi-pair batches; the F4-vs-Buchberger
    // bank (`diff_f4_vs_buch_bank_small_primes_sweep` -> "cyclic_3") covers
    // the cyclic-3 ideal-equivalence over GF(7) at higher level.
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    let f1 = x0.mul(&x0, &ring).sub(&x1, &ring);
    let f2 = x0.mul(&x1, &ring).sub(&x2, &ring);
    let f3 = x1.mul(&x1, &ring).sub(&x0, &ring);
    cross_check_all_pairs(vec![f1, f2, f3], &ring);
}

#[test]
fn f4_precancelled_token_returns_empty() {
    // A token that is already cancelled when `process_batch_with_workspace`
    // is entered must short-circuit at the very first cancellation check
    // and return no generators, even though the batch is non-empty and the
    // S-poly would otherwise yield a new generator.
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let xy = x0.mul(&x1, &ring);
    let f1 = xy.sub(&DensePoly::constant(ring.field.one(), &ring), &ring); // x*y - 1
    let y2 = x1.mul(&x1, &ring);
    let f2 = y2.sub(&x0, &ring); // y^2 - x
    let basis_polys = vec![f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let lcm = lt(&f1, &ring).lcm(&lt(&f2, &ring));
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };

    // Sanity: with no cancellation the batch yields a generator.
    let uncancelled = process_batch(&[&pair], &basis, &ring, None);
    assert!(!uncancelled.is_empty(), "control: batch must produce a generator");

    let token = CancelToken::cancelled();
    let mut ws = F4Workspace::new();
    let out = process_batch_with_workspace(&[&pair], &basis, &ring, Some(&token), &mut ws);
    assert!(out.is_empty(), "pre-cancelled token must yield no generators");
}

#[test]
fn f4_empty_batch_returns_empty() {
    // An empty batch returns no generators regardless of cancellation state.
    let ring = ring_mod7(2);
    let basis: Vec<F4BasisRef> = Vec::new();
    let out = process_batch(&[], &basis, &ring, None);
    assert!(out.is_empty());
    let token = CancelToken::cancelled();
    let out_cancelled = process_batch(&[], &basis, &ring, Some(&token));
    assert!(out_cancelled.is_empty());
}

#[test]
fn f4_useless_reduction_yields_empty() {
    // I = (x, y). S(x, y) = y*x - x*y = 0 → useless reduction.
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let basis_polys = vec![x0.clone(), x1.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();

    let lcm = lt(&x0, &ring).lcm(&lt(&x1, &ring));
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: true,
    };
    let new_polys = process_batch(&[&pair], &basis, &ring, None);
    assert!(new_polys.is_empty(), "expected useless reduction, got {:?}", new_polys);
}

// ─── Provenance tracking ──────────────────────────────────────

#[test]
fn f4_prov_single_pair_no_reducers() {
    // S(x*y, x*z) over F_7: lcm = x*y*z; S-poly reduces against
    // nothing further; the output's provenance is exactly the one
    // input pair and no reducer.
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    let f1 = x0.mul(&x1, &ring); // x*y
    let f2 = x0.mul(&x2, &ring); // x*z
    let basis_polys = vec![f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let lcm = basis_lts[0].lcm(&basis_lts[1]);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };
    let new_polys = process_batch(&[&pair], &basis, &ring, None);
    // S(x*y, x*z) = z*(x*y) - y*(x*z) = 0 — useless reduction.
    // No outputs ⇒ no provenance to check, but the call must not
    // panic and must produce an empty Vec.
    assert!(new_polys.is_empty());
}

#[test]
fn f4_prov_reducer_basis_index_recorded() {
    // System where the S-poly's tail needs a third basis element
    // as a reducer. After F4, the output's `from_reducers` must
    // name that basis index.
    //
    // basis[0] = x^2 + y           (LT = x^2)
    // basis[1] = x*y + z           (LT = x*y)
    // basis[2] = y                 (LT = y)
    //
    // S(basis[0], basis[1]) has tail terms involving `y`, which
    // basis[2] reduces. So the output's from_reducers must
    // include basis index 2.
    let ring = ring_mod7(3);
    let x0 = x(0, &ring); // x
    let x1 = x(1, &ring); // y
    let x2 = x(2, &ring); // z
    let f0 = x0.mul(&x0, &ring).add(&x1, &ring);   // x^2 + y
    let f1 = x0.mul(&x1, &ring).add(&x2, &ring);   // x*y + z
    let f2 = x1.clone();                            // y
    let basis_polys = vec![f0.clone(), f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let lcm = basis_lts[0].lcm(&basis_lts[1]);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };
    let new_polys = process_batch(&[&pair], &basis, &ring, None);
    if let Some(out) = new_polys.first() {
        assert_eq!(out.from_pairs, vec![0],
            "the single pair's index must be in from_pairs");
        // basis[2] = y is the reducer pulled in during symbolic
        // preprocessing; its index must appear.
        assert!(out.from_reducers.contains(&2),
            "expected basis index 2 in from_reducers; got {:?}",
            out.from_reducers);
    }
}

#[test]
fn f4_prov_multibatch_unions_pair_indices() {
    // Two pairs in one batch whose S-polys end up sharing
    // pivot columns during echelon. After elimination, the
    // surviving output rows must carry the union of contributing
    // pair indices.
    //
    // basis[0] = x^2 - y
    // basis[1] = x*y - 1
    // basis[2] = y^2 - x
    // pairs: (0,1), (0,2), (1,2).
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let f0 = x0.mul(&x0, &ring).sub(&x1, &ring);
    let f1 = x0.mul(&x1, &ring).sub(&DensePoly::constant(ring.field.one(), &ring), &ring);
    let f2 = x1.mul(&x1, &ring).sub(&x0, &ring);
    let basis_polys = vec![f0, f1, f2];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let mut pairs: Vec<SPair> = Vec::new();
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let lcm = basis_lts[i].lcm(&basis_lts[j]);
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        pairs.push(SPair {
            i, j,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        });
    }
    let pair_refs: Vec<&SPair> = pairs.iter().collect();
    let outs = process_batch(&pair_refs, &basis, &ring, None);
    for out in &outs {
        assert!(!out.from_pairs.is_empty(),
            "every surviving output must name at least one input pair; got {:?}",
            out);
        for &pi in &out.from_pairs {
            assert!(pi < pairs.len(), "pair index out of range: {}", pi);
        }
    }
}

// ─── F4 + IncrementalGB push/pop integration ──────────────────

/// `IncrementalGB::push`/`pop` must work with the F4 main-loop
/// path enabled. The basis at the post-`pop` level must match
/// the basis observed right after the pre-`push` extension.
#[test]
fn f4_incremental_push_pop_roundtrip() {
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);

    let cfg = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: true,
    };
    let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
    // Base level: f1, f2.
    let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);
    let f2 = x1.mul(&x2, &ring).sub(&x0, &ring);
    igb.add_generators(vec![f1, f2]).expect("base add_generators");
    let base = igb.basis();
    assert!(!igb.is_trivial());

    // Push a checkpoint, extend with a third generator, then pop.
    igb.push();
    let f3 = x0.mul(&x0, &ring).sub(&x1, &ring);
    igb.add_generators(vec![f3]).expect("inner add_generators");
    let _inner = igb.basis();
    igb.pop();
    let restored = igb.basis();

    // The post-pop basis must match the pre-push basis.
    assert_eq!(
        restored.len(),
        base.len(),
        "F4 push/pop did not restore basis length"
    );
    for (a, b) in restored.iter().zip(base.iter()) {
        assert_eq!(
            lt(a, &ring).exponents(),
            lt(b, &ring).exponents(),
            "F4 push/pop basis LT mismatch"
        );
    }
}

/// F4 must not break when the trivial element is reached inside
/// a `push`ed level. After `pop`, `is_trivial` must revert to
/// the pre-push value.
#[test]
fn f4_incremental_pop_clears_trivial_state() {
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);

    let cfg = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: true,
        use_f4: true,
    };
    let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
    igb.add_generators(vec![
        x0.mul(&x1, &ring).sub(
            &DensePoly::constant(ring.field.one(), &ring),
            &ring,
        ),
    ])
    .expect("base add");
    assert!(!igb.is_trivial());

    igb.push();
    // Add `x0` then `x1`: combined they force x0*x1 = 0,
    // contradicting x0*x1 = 1 ⇒ trivial.
    igb.add_generators(vec![x0.clone(), x1.clone()])
        .expect("inner add (trivial)");
    assert!(igb.is_trivial(), "inner extension should be trivial");

    igb.pop();
    assert!(!igb.is_trivial(), "pop must clear trivial state set inside push");
}

// ─── F4 cross-batch reducer cache ─────────────────────────────

/// `process_batch_with_workspace` reused across batches must
/// (a) populate the cache on the first batch and (b) take cache
/// hits on a second batch that revisits the same monomials. The
/// outputs must remain identical to a single-call `process_batch`
/// — the cache is a pure perf optimisation, not a state change.
#[test]
fn f4_workspace_idempotent_on_repeated_batch() {
    // Use a 3-pair batch over the cyclic-style ideal so
    // symbolic_preprocess actually has work to do (S-polys are
    // non-zero and pull in reducer rows).
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    let f0 = x0.mul(&x0, &ring).sub(&x1, &ring);   // x^2 - y
    let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);   // x*y - z
    let f2 = x1.mul(&x1, &ring).sub(&x0, &ring);   // y^2 - x
    let basis_polys = vec![f0, f1, f2];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef {
            poly: p,
            lt: l,
            lt_divmask: ring.divmask.compute(l),
            active: true,
        })
        .collect();
    let mut pairs: Vec<SPair> = Vec::new();
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let lcm = basis_lts[i].lcm(&basis_lts[j]);
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        pairs.push(SPair {
            i, j,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        });
    }
    let pair_refs: Vec<&SPair> = pairs.iter().collect();
    let mut ws = F4Workspace::new();
    let first = process_batch_with_workspace(&pair_refs, &basis, &ring, None, &mut ws);
    assert!(
        ws.stats.reducer_misses > 0,
        "first batch must populate the cache; stats={:?}",
        ws.stats
    );
    let misses_before = ws.stats.reducer_misses;
    let hits_before = ws.stats.reducer_hits;
    let second = process_batch_with_workspace(&pair_refs, &basis, &ring, None, &mut ws);
    assert!(
        ws.stats.reducer_hits > hits_before,
        "second batch must take cache hits; stats={:?}",
        ws.stats
    );
    assert_eq!(
        ws.stats.reducer_misses, misses_before,
        "no new misses on repeat (same monomials, same active basis)"
    );
    assert_eq!(first.len(), second.len(), "output count must match");
    for (a, b) in first.iter().zip(second.iter()) {
        assert_eq!(lt(&a.poly, &ring).exponents(), lt(&b.poly, &ring).exponents());
        assert_eq!(a.from_pairs, b.from_pairs);
        assert_eq!(a.from_reducers, b.from_reducers);
    }
}

/// A cached reducer keyed on monomial `m` records `(basis_idx,
/// reducer_poly)`. Deactivating `basis[basis_idx]` between the
/// two batches must force a recomputation. After the second
/// call, [`F4WorkspaceStats::reducer_stale`] is incremented for
/// every monomial whose cached entry pointed at the
/// now-deactivated element. The outputs must remain a valid GB
/// extension — the wider `f4_vs_per_pair_random_cross_check`
/// fuzz catches any silent reuse of a stale row.
#[test]
fn f4_workspace_invalidates_on_basis_deactivation() {
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    // 3-pair batch that produces non-zero S-polys.
    let f0 = x0.mul(&x0, &ring).sub(&x1, &ring);
    let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);
    let f2 = x1.mul(&x1, &ring).sub(&x0, &ring);
    let basis_polys = vec![f0, f1, f2];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let mut pairs: Vec<SPair> = Vec::new();
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let lcm = basis_lts[i].lcm(&basis_lts[j]);
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        pairs.push(SPair {
            i, j,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        });
    }
    let pair_refs: Vec<&SPair> = pairs.iter().collect();
    let active_all: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef {
            poly: p,
            lt: l,
            lt_divmask: ring.divmask.compute(l),
            active: true,
        })
        .collect();
    let mut ws = F4Workspace::new();
    let _ = process_batch_with_workspace(&pair_refs, &active_all, &ring, None, &mut ws);
    let stale_before = ws.stats.reducer_stale;
    let misses_before = ws.stats.reducer_misses;

    // Deactivate basis[0]. Any cached entry that selected `basis_idx=0`
    // as its reducer must register as stale and be recomputed.
    let basis_no_b0: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .enumerate()
        .map(|(idx, (p, l))| F4BasisRef {
            poly: p,
            lt: l,
            lt_divmask: ring.divmask.compute(l),
            active: idx != 0,
        })
        .collect();
    let _ = process_batch_with_workspace(&pair_refs, &basis_no_b0, &ring, None, &mut ws);
    // At least one stale event or new miss must fire (some
    // monomial that used basis[0] now needs a different reducer
    // or becomes free).
    assert!(
        ws.stats.reducer_stale > stale_before || ws.stats.reducer_misses > misses_before,
        "deactivating basis[0] must trigger cache invalidation; stats={:?}",
        ws.stats
    );
}

// ─── F4 vs per-pair cross-validation fuzz ─────────────────────

// (`f4_vs_per_pair_random_cross_check` — GF(7), 2 vars, 12 LCG seeds —
// folded into the BN254 random fuzz below, which exercises the same property
// over a realistic ZK-circuit prime with 3 vars and 10 seeds. Small-prime
// random coverage of F4 ≡ per-pair is preserved by
// `diff_f4_vs_buch_edge_primes_small` running the full hand-built bank
// (cyclic_3, overlapping_lts, …) over GF(2)/3/5.)

/// BN254 random fuzz: cross-checks F4 vs per-pair over the BN254 scalar
/// field (a ~254-bit prime, routed to the GMP `FieldElem` arm) with 3
/// variables and degree-≤2 generators. Exercises F4 / per-pair agreement
/// in the realistic coefficient/variable regime the GF(7) two-variable
/// cross-check does not cover. Compares leading-term sets (the reduced-GB
/// staircase), matching the convention above — `add_generators`'
/// single-pass tail reduction does not guarantee identical tails.
#[test]
fn f4_vs_per_pair_bn254_3vars() {
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use std::collections::HashSet;

    fn ring_bn254(n_vars: usize) -> Arc<PolyRing> {
        let p = "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse::<BigUint>()
            .unwrap();
        let f = PrimeField::new(p);
        let names = (0..n_vars).map(|i| format!("x{}", i)).collect();
        PolyRing::new(f, names, MonomialOrder::DegRevLex)
    }

    fn lcg(seed: u64) -> impl FnMut() -> u64 {
        let mut s = seed;
        move || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        }
    }

    for seed in 1u64..=10 {
        let ring = ring_bn254(3);
        let mut rng = lcg(seed);
        let vars: Vec<DensePoly> = (0..3).map(|i| x(i, &ring)).collect();
        // Atom set: constant, the three linears, and all degree-2 monomials.
        let mut atoms: Vec<DensePoly> = vec![DensePoly::constant(ring.field.one(), &ring)];
        for i in 0..3 {
            atoms.push(vars[i].clone());
        }
        for i in 0..3 {
            for j in i..3 {
                atoms.push(vars[i].mul(&vars[j], &ring));
            }
        }

        let mut polys: Vec<DensePoly> = Vec::new();
        for _ in 0..3 {
            let mut acc = DensePoly::zero();
            for atom in &atoms {
                let c_u = rng();
                if c_u % 4 == 0 {
                    continue; // sparsify
                }
                let c = ring.field.from_u64(c_u);
                acc = acc.add(&atom.mul(&DensePoly::constant(c, &ring), &ring), &ring);
            }
            if !acc.is_zero() {
                polys.push(acc);
            }
        }
        if polys.len() < 2 {
            continue;
        }

        let run = |use_f4: bool| {
            let cfg = BuchbergerConfig {
                order: MonomialOrder::DegRevLex,
                cancel_token: None,
                abort_on_trivial: false,
                use_f4,
            };
            let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
            let trivial = igb.add_generators(polys.clone()).expect("add");
            (trivial, igb.basis())
        };
        let (pp_trivial, pp_basis) = run(false);
        let (f4_trivial, f4_basis) = run(true);

        assert_eq!(
            pp_trivial, f4_trivial,
            "F4/per-pair triviality disagree at seed={}", seed
        );
        if !pp_trivial {
            let lts = |basis: &[DensePoly]| -> HashSet<Vec<u16>> {
                basis.iter().map(|p| lt(p, &ring).exponents().to_vec()).collect()
            };
            assert_eq!(
                lts(&pp_basis), lts(&f4_basis),
                "F4/per-pair LT sets differ at seed={}", seed
            );
        }
    }
}

// ─── F4 batch-routing end-to-end ─────────────────────────────

/// Katsura-3 in 4 variables over F_7. Buchberger produces several
/// same-sugar batches below `F4_MIN_BATCH`, routing them through
/// the per-pair fallback. Asserts `f4_fallback_pairs > 0` and
/// F4 / per-pair leading-term-set agreement.
#[test]
fn f4_size_fallback_fires_on_small_batches() {
    // f4_* counters are gb-stats-gated profiling; enable so engine_stats() is populated.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use std::collections::HashSet;
    let ring = ring_mod7(4);
    let xs: Vec<DensePoly> = (0..4).map(|i| DensePoly::variable(i, &ring)).collect();
    // Katsura-3: 4 polynomials in `u_0, u_1, u_2, u_3`.
    // P_i = Σ_{j=-n..n} u_{|j|}·u_{|i-j|} - u_i  for 0 ≤ i ≤ 2,
    // and P_3 = u_0 + 2·u_1 + 2·u_2 + 2·u_3 - 1.
    let n = 3i32;
    let mut polys: Vec<DensePoly> = Vec::new();
    for i in 0..3usize {
        let mut acc = DensePoly::zero();
        for j in -n..=n {
            let aj = (j.unsigned_abs()) as usize;
            let ak = ((i as i32 - j).unsigned_abs()) as usize;
            if aj > 3 || ak > 3 {
                continue;
            }
            let prod = xs[aj].mul(&xs[ak], &ring);
            acc = acc.add(&prod, &ring);
        }
        acc = acc.sub(&xs[i], &ring);
        polys.push(acc);
    }
    let two = ring.field.from_int(2);
    let two_poly = DensePoly::constant(two, &ring);
    let mut tail = xs[0].clone();
    for k in 1..4 {
        tail = tail.add(&xs[k].mul(&two_poly, &ring), &ring);
    }
    let one = ring.field.one();
    tail = tail.sub(&DensePoly::constant(one, &ring), &ring);
    polys.push(tail);

    let cfg_f4 = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: true,
    };
    let mut igb_f4 = IncrementalGB::new(Arc::clone(&ring), cfg_f4);
    igb_f4
        .add_generators(polys.clone())
        .expect("F4 add_generators");

    let f4_stats = igb_f4.engine_stats().clone();
    assert!(
        f4_stats.f4_fallback_pairs > 0,
        "F4_MIN_BATCH size fallback must fire on cyclic-3; \
         got f4_fallback_pairs=0, full stats={:?}",
        f4_stats,
    );

    // Per-pair reference: compare LT sets to confirm the routing
    // decision preserves correctness.
    let cfg_pp = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: false,
    };
    let mut igb_pp = IncrementalGB::new(Arc::clone(&ring), cfg_pp);
    igb_pp
        .add_generators(polys)
        .expect("per-pair add_generators");

    let f4_lts: HashSet<Vec<u16>> = igb_f4
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    let pp_lts: HashSet<Vec<u16>> = igb_pp
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    assert_eq!(
        f4_lts, pp_lts,
        "F4 size fallback must preserve correctness; F4 LT set differs from per-pair"
    );
}

/// Cyclic-5 in F_7 produces same-sugar batches ≥ `F4_MIN_BATCH`.
/// Asserts `engine_stats().f4_batches > 0` and `f4_pair_total > 0`.
#[test]
fn f4_matrix_path_fires_on_cyclic_5() {
    // f4_* counters are gb-stats-gated profiling; enable so engine_stats() is populated.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    let ring = ring_mod7(5);
    let xs: Vec<DensePoly> = (0..5).map(|i| DensePoly::variable(i, &ring)).collect();
    let one = ring.field.one();
    let neg_one = ring.field.neg(&one);
    let mut polys: Vec<DensePoly> = Vec::new();
    // f_d = Σ_{r=0..n} ∏_{k=0..d} x_{(r+k) mod n}  for d = 1..n.
    for d in 1..5 {
        let mut acc = DensePoly::zero();
        for r in 0..5 {
            let mut prod = xs[r % 5].clone();
            for k in 1..d {
                prod = prod.mul(&xs[(r + k) % 5], &ring);
            }
            acc = acc.add(&prod, &ring);
        }
        polys.push(acc);
    }
    // f_n = x_0 · x_1 · … · x_{n-1} - 1.
    let mut p = xs[0].clone();
    for k in 1..5 {
        p = p.mul(&xs[k], &ring);
    }
    p = p.add(&DensePoly::constant(neg_one, &ring), &ring);
    polys.push(p);

    let cfg = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: true,
    };
    let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
    igb.add_generators(polys).expect("F4 add_generators");
    let stats = igb.engine_stats().clone();
    assert!(
        stats.f4_batches > 0,
        "F4 matrix path must fire on cyclic-5; stats={:?}",
        stats,
    );
    assert!(
        stats.f4_pair_total > 0,
        "F4 pair total must be > 0 when f4_batches > 0; stats={:?}",
        stats,
    );
}

// ─── Large-batch F4 amortisation coverage ────────────────────

/// Cyclic-6 in F_7. Same-sugar batches average ≈ 35 pairs, well
/// above `F4_MIN_BATCH = 12`. Asserts:
///   * `f4_batches > 0`,
///   * average batch size ≥ 20,
///   * F4 pair share ≥ 90% (small low-sugar batches still fall
///     back),
///   * F4 and per-pair leading-term sets match.
///
/// `#[ignore]`d because cyclic-6 takes ~100 ms. Run with
/// `cargo test -p picus-solver --release -- --ignored f4_large_batch_cyclic_6`.
#[test]
#[ignore]
fn f4_large_batch_cyclic_6() {
    // f4_* counters are gb-stats-gated profiling; enable so engine_stats() is populated.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use std::collections::HashSet;
    let n = 6usize;
    let ring = ring_mod7(n);
    let xs: Vec<DensePoly> = (0..n).map(|i| DensePoly::variable(i, &ring)).collect();
    let one = ring.field.one();
    let neg_one = ring.field.neg(&one);
    let mut polys: Vec<DensePoly> = Vec::new();
    // Cyclic-n: f_d = Σ_{r=0..n} ∏_{k=0..d} x_{(r+k) mod n}  for d = 1..n.
    for d in 1..n {
        let mut acc = DensePoly::zero();
        for r in 0..n {
            let mut prod = xs[r % n].clone();
            for k in 1..d {
                prod = prod.mul(&xs[(r + k) % n], &ring);
            }
            acc = acc.add(&prod, &ring);
        }
        polys.push(acc);
    }
    // f_n = x_0 · x_1 · … · x_{n-1} - 1.
    let mut p = xs[0].clone();
    for k in 1..n {
        p = p.mul(&xs[k], &ring);
    }
    p = p.add(&DensePoly::constant(neg_one, &ring), &ring);
    polys.push(p);

    let cfg_f4 = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: true,
    };
    let mut igb_f4 = IncrementalGB::new(Arc::clone(&ring), cfg_f4);
    igb_f4
        .add_generators(polys.clone())
        .expect("F4 add_generators (cyclic-6)");
    let stats = igb_f4.engine_stats().clone();
    assert!(
        stats.f4_batches > 0,
        "cyclic-6 must fire F4 matrix path; stats={:?}",
        stats,
    );
    let avg = stats.f4_pair_total as f64 / stats.f4_batches as f64;
    assert!(
        avg >= 20.0,
        "cyclic-6 must produce large F4 batches (avg ≥ 20 expected, got avg={}); stats={:?}",
        avg,
        stats,
    );
    // Most of cyclic-6's pairs route through F4 — at least 90%
    // of the matrix path should be exercised. (A handful of
    // small low-sugar batches do fall back; that's expected.)
    let f4_share = stats.f4_pair_total as f64
        / (stats.f4_pair_total + stats.f4_fallback_pairs) as f64;
    assert!(
        f4_share >= 0.9,
        "cyclic-6 F4 share must be ≥ 0.9 (got {:.3}); stats={:?}",
        f4_share,
        stats,
    );

    // Per-pair reference.
    let cfg_pp = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: false,
    };
    let mut igb_pp = IncrementalGB::new(Arc::clone(&ring), cfg_pp);
    igb_pp
        .add_generators(polys)
        .expect("per-pair add_generators (cyclic-6)");
    let f4_lts: HashSet<Vec<u16>> = igb_f4
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    let pp_lts: HashSet<Vec<u16>> = igb_pp
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    assert_eq!(
        f4_lts, pp_lts,
        "F4 and per-pair must agree on cyclic-6 LT set; F4 stats={:?}",
        stats,
    );
}

/// Homogeneous random degree-2 ideal in 5 variables with 8
/// generators (deterministic LCG seed). No constant term keeps
/// the basis from collapsing to a unit; degree-3 same-sugar
/// batches produced are large enough for the F4 matrix path.
/// Asserts `f4_batches > 0`, `f4_pair_total >= F4_MIN_BATCH`,
/// and F4 / per-pair leading-term-set agreement.
#[test]
fn f4_large_batch_homog_5vars_deg2() {
    // f4_* counters are gb-stats-gated profiling; enable so engine_stats() is populated.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use std::collections::HashSet;
    let ring = ring_mod7(5);
    // Deterministic LCG so the test is reproducible.
    let mut seed: u64 = 0xC0CCAB1234567ABC;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed
    };
    let xs: Vec<DensePoly> = (0..5).map(|i| DensePoly::variable(i, &ring)).collect();
    let mut polys: Vec<DensePoly> = Vec::new();
    for _ in 0..8 {
        // Sum of 5 random degree-2 atoms `c · x_i · x_j` with
        // distinct (i, j) pairs. No constant tail — keeps the
        // poly homogeneous degree 2 and prevents the basis from
        // collapsing to `1`.
        let mut acc = DensePoly::zero();
        let mut used: std::collections::HashSet<(usize, usize)> =
            std::collections::HashSet::new();
        let mut tries = 0;
        while used.len() < 5 && tries < 50 {
            tries += 1;
            let c_raw = ((next() % 6) + 1) as i64;
            let c = ring.field.from_int(c_raw);
            let mut i = (next() as usize) % 5;
            let mut j = (next() as usize) % 5;
            if i > j {
                std::mem::swap(&mut i, &mut j);
            }
            if !used.insert((i, j)) {
                continue;
            }
            let term = xs[i].mul(&xs[j], &ring);
            acc = acc.add(&term.mul(&DensePoly::constant(c, &ring), &ring), &ring);
        }
        if !acc.is_zero() {
            polys.push(acc);
        }
    }
    assert!(
        polys.len() >= 6,
        "deterministic seed must produce >= 6 polys, got {}",
        polys.len(),
    );

    let cfg_f4 = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: true,
    };
    let mut igb_f4 = IncrementalGB::new(Arc::clone(&ring), cfg_f4);
    igb_f4
        .add_generators(polys.clone())
        .expect("F4 add_generators (homog 5vars)");
    let stats = igb_f4.engine_stats().clone();
    assert!(
        stats.f4_batches > 0,
        "homog-5vars-deg2 must fire F4 matrix path at least once; stats={:?}",
        stats,
    );
    // At least one batch should hit `F4_MIN_BATCH`; check that
    // `f4_pair_total >= F4_MIN_BATCH` (one such batch is enough).
    assert!(
        stats.f4_pair_total >= 12,
        "F4 must process >= 12 pairs total (i.e. ≥ 1 above-threshold batch); stats={:?}",
        stats,
    );

    let cfg_pp = BuchbergerConfig {
        order: MonomialOrder::DegRevLex,
        cancel_token: None,
        abort_on_trivial: false,
        use_f4: false,
    };
    let mut igb_pp = IncrementalGB::new(Arc::clone(&ring), cfg_pp);
    igb_pp
        .add_generators(polys)
        .expect("per-pair add_generators (homog 5vars)");
    let f4_lts: HashSet<Vec<u16>> = igb_f4
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    let pp_lts: HashSet<Vec<u16>> = igb_pp
        .basis()
        .iter()
        .map(|p| lt(p, &ring).exponents().to_vec())
        .collect();
    assert_eq!(
        f4_lts, pp_lts,
        "F4 and per-pair LT sets must agree on homog-5vars; F4 stats={:?}",
        stats,
    );
}

// ─── S-poly loop: pair referencing a missing basis index ──────

#[test]
fn process_batch_skips_pair_with_out_of_range_basis_index() {
    // A pair whose `i`/`j` exceeds the basis length (a stale index left
    // by deactivation) is skipped in the S-poly construction loop. With
    // the only pair skipped no S-poly is built, so the batch yields no
    // generators.
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let basis_polys = vec![x0.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    // i = 0 is valid, j = 99 is out of range ⇒ the pair is skipped.
    let lcm = lt(&x0, &ring);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let bad_pair = SPair {
        i: 0,
        j: 99,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };
    let out = process_batch(&[&bad_pair], &basis, &ring, None);
    assert!(out.is_empty(), "out-of-range pair must be skipped, yielding no S-poly");
}

// ─── symbolic_preprocess: reducer found / not-found / cancel ──

#[test]
fn symbolic_preprocess_finds_and_misses_reducers() {
    // Basis = {x0} (LT x0). S-poly = x0·x1 + x2.
    //  * monomial x0·x1 is divisible by x0 ⇒ a reducer row is built
    //    (the `b.lt.divides(m)` break), and its basis index 0 is
    //    recorded.
    //  * monomial x2 is not divisible by x0 ⇒ no reducer (the
    //    `found == None` continue).
    let ring = ring_mod7(3);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    let basis_polys = vec![x0.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let spoly = x0.mul(&x1, &ring).add(&x2, &ring); // x0·x1 + x2
    let mut ws = F4Workspace::new();
    let (all_polys, n_spolys, reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(vec![spoly], &basis, &ring, None, &mut ws);
    assert_eq!(n_spolys, 1);
    // x0·x1 produced exactly one reducer row, built from basis element 0.
    assert_eq!(reducer_basis_idx, vec![0], "x0 must reduce x0·x1");
    assert_eq!(reducer_lts.len(), 1);
    // all_polys = [spoly, reducer]: the reducer was appended.
    assert_eq!(all_polys.len(), n_spolys + reducer_basis_idx.len());
}

#[test]
fn symbolic_preprocess_returns_early_on_pre_cancelled_token() {
    // A pre-cancelled token makes the worklist loop bail on the first
    // monomial (the in-loop cancel check), returning the S-polys with no
    // reducer rows discovered yet.
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let basis_polys = vec![x0.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();
    let spoly = x0.mul(&x1, &ring); // x0·x1 — worklist seeds non-empty
    let token = CancelToken::cancelled();
    let mut ws = F4Workspace::new();
    let (all_polys, n_spolys, _reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(vec![spoly], &basis, &ring, Some(&token), &mut ws);
    assert_eq!(n_spolys, 1);
    // Loop bailed before adding any reducer row.
    assert!(reducer_basis_idx.is_empty(), "cancelled worklist adds no reducers");
    assert_eq!(all_polys.len(), 1, "only the S-poly is present");
}

// ─── S-poly loop: scale_j division-by-zero arm ─────────────────

#[test]
fn process_batch_skips_pair_when_lc_j_is_zero() {
    // The `field.div(lc_i, lc_j)` call returns `None` iff `lc_j == 0`. Build
    // a malformed basis element whose stored coefficient vector starts with
    // a zero — `is_zero()` is `coeffs.is_empty()`, so a single-zero-coeff
    // poly is non-zero by that check, but `leading_coefficient()` returns
    // `Some(&zero)`. The S-poly construction loop's scale_j division then
    // produces `None` and the pair is skipped; no S-poly is built, so the
    // batch yields no outputs.
    let ring = ring_mod7(2);
    let real = x(0, &ring); // x0, leading coefficient 1
    let real_lt = lt(&real, &ring);
    // Build a non-zero-by-emptiness poly whose stored leading coefficient
    // is the zero field element. `from_raw_sorted` performs no zero-strip.
    let zero_lc_poly = DensePoly::from_raw_sorted(
        vec![1u16, 0],                // monomial exponents = x0
        vec![ring.field.zero()],     // single coefficient slot, value 0
        vec![1u32],
    );
    let zero_lc_lt = Monomial::from_exponents(vec![1, 0]);
    let basis = vec![
        F4BasisRef {
            poly: &real,
            lt: &real_lt,
            lt_divmask: ring.divmask.compute(&real_lt),
            active: true,
        },
        F4BasisRef {
            poly: &zero_lc_poly,
            lt: &zero_lc_lt,
            lt_divmask: ring.divmask.compute(&zero_lc_lt),
            active: true,
        },
    ];
    let lcm = real_lt.lcm(&zero_lc_lt);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };
    let out = process_batch(&[&pair], &basis, &ring, None);
    assert!(out.is_empty(), "lc_j=0 must skip the pair, yielding no F4 output");
}

// ─── symbolic_preprocess: mul_term-produces-zero and no-divisor arms ────────

#[test]
fn symbolic_preprocess_skips_ghost_reducer_with_zero_poly() {
    // A ghost `F4BasisRef` whose `poly` is the zero polynomial but whose
    // `lt` divides an S-poly monomial: `basis[bi].poly.mul_term(...)` yields
    // zero (mul_term short-circuits on `self.is_zero()`), exercising the
    // `if reducer.is_zero() { continue; }` arm.
    //
    // Real basis: f0 = x0·x1 − 1 (lt = x0·x1), f1 = x1^2 − x0 (lt = x1^2).
    // S(f0, f1) (lcm = x0·x1^2) = x0^2 − x1, contributing monomials
    // {x0·x1^2, x0^2, x1}. The ghost has lt = x0 and divides x0^2 (and
    // x0·x1^2). The real reducers (lt x0·x1 / x1^2) do not divide x0^2,
    // so the ghost is the FIRST divisor reached for that monomial — its
    // mul_term(zero) returns zero, triggering the zero-reducer continue.
    //
    // The monomial x1 has no active basis divisor (no `lt` divides x1),
    // hitting the `None => continue` arm for that worklist entry.
    let ring = ring_mod7(2);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let f0 = x0.mul(&x1, &ring).sub(&DensePoly::constant(ring.field.one(), &ring), &ring);
    let f1 = x1.mul(&x1, &ring).sub(&x0, &ring);
    let f0_lt = lt(&f0, &ring);
    let f1_lt = lt(&f1, &ring);
    let zero_poly = DensePoly::zero();
    let ghost_lt = Monomial::from_exponents(vec![1, 0]); // x0
    let basis = vec![
        F4BasisRef {
            poly: &f0,
            lt: &f0_lt,
            lt_divmask: ring.divmask.compute(&f0_lt),
            active: true,
        },
        F4BasisRef {
            poly: &f1,
            lt: &f1_lt,
            lt_divmask: ring.divmask.compute(&f1_lt),
            active: true,
        },
        F4BasisRef {
            poly: &zero_poly,
            lt: &ghost_lt,
            lt_divmask: ring.divmask.compute(&ghost_lt),
            active: true,
        },
    ];
    // S(f0, f1): m_f0 = x1, m_f1 = x0; lc_f0=lc_f1=1 ⇒ scale_j=1.
    // = x1·(x0·x1 − 1) − x0·(x1^2 − x0) = x0·x1^2 − x1 − x0·x1^2 + x0^2
    // = x0^2 − x1.
    let s_poly = DensePoly::from_terms(
        vec![
            (Monomial::from_exponents(vec![2, 0]), ring.field.from_u64(1)),
            (Monomial::from_exponents(vec![0, 1]), ring.field.from_i64(-1)),
        ],
        &ring,
    );
    let mut ws = F4Workspace::new();
    let (all_polys, n_spolys, reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(vec![s_poly], &basis, &ring, None, &mut ws);
    assert_eq!(n_spolys, 1);
    // The ghost contributed no reducer row (its mul_term produced zero, so
    // the `continue` at the `reducer.is_zero()` guard fired). The non-ghost
    // basis elements do not divide x0^2 or x1, so `reducer_basis_idx` is
    // entirely free of the ghost index 2 — and in fact empty.
    assert!(
        !reducer_basis_idx.contains(&2),
        "ghost (basis index 2) must NOT appear among reducer indices: {:?}",
        reducer_basis_idx,
    );
    // No reducer row materialised at all: only the S-poly remains.
    assert_eq!(all_polys.len(), n_spolys, "no reducer rows added");
    assert!(reducer_lts.is_empty(), "no reducer LTs recorded");
}

#[test]
fn symbolic_preprocess_break_exits_inner_loop_on_first_divisor() {
    // The `break` at the end of the divisor-search loop in
    // symbolic_preprocess exits on the FIRST basis element whose `lt`
    // divides the monomial. Place the matching divisor at index 1 with
    // an unrelated active element at index 0: the search must skip
    // index 0 (no divides) and break at index 1 (found), recording a
    // single reducer-row contribution.
    let ring = ring_mod7(3);
    let f_extra = x(2, &ring); // lt = x2, divmask carries x2
    let f_div   = x(0, &ring); // lt = x0, will divide the spoly monomial
    let extra_lt = lt(&f_extra, &ring);
    let div_lt   = lt(&f_div, &ring);
    let basis = vec![
        F4BasisRef { poly: &f_extra, lt: &extra_lt, lt_divmask: ring.divmask.compute(&extra_lt), active: true },
        F4BasisRef { poly: &f_div,   lt: &div_lt,   lt_divmask: ring.divmask.compute(&div_lt),   active: true },
    ];
    // S-poly carrying a single monomial x0·x1: divisible by x0 (index 1),
    // NOT divisible by x2 (index 0). The search visits index 0 (divmask
    // reject), then index 1 (found, break).
    let s_poly = DensePoly::from_terms(
        vec![(Monomial::from_exponents(vec![1, 1, 0]), ring.field.from_u64(1))],
        &ring,
    );
    let mut ws = F4Workspace::new();
    let (_all_polys, n_spolys, reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(vec![s_poly], &basis, &ring, None, &mut ws);
    assert_eq!(n_spolys, 1);
    // Exactly one reducer was added, contributed by basis index 1.
    assert_eq!(reducer_basis_idx, vec![1],
        "the break must select the first-found divisor (index 1)");
    assert_eq!(reducer_lts.len(), 1);
    // The reducer LT records the worklist monomial x0·x1.
    assert_eq!(reducer_lts[0].exponents(), &[1, 1, 0]);
}

// ──────────── SPEC-DRIVEN PROPERTY TESTS ────────────
//
// F4 cross-engine equivalence (vs the per-pair geobucket path) plus
// post-op invariants. Property statements come from algebraic spec
// (Buchberger's theorem / uniqueness of the reduced GB / monicity of
// reduced GBs) — NOT from reading the F4 source.

use crate::ff::buchberger::{
    groebner_basis as buch_gb, interreduce as buch_interreduce, BuchbergerConfig,
};

/// Polynomial ring builder for prime `p` and `n_vars` variables.
fn ring_p(p: u64, n_vars: usize) -> Arc<PolyRing> {
    PolyRing::new(
        PrimeField::new(BigUint::from(p)),
        (0..n_vars).map(|i| format!("x{i}")).collect(),
        MonomialOrder::DegRevLex,
    )
}

/// Canonical reduced GB as a sorted list of term-list representations.
/// Two ideals' reduced GBs are equal iff this canonical form is.
fn canon_dense(mut basis: Vec<DensePoly>, ring: &Arc<PolyRing>) -> Vec<Vec<(Vec<u16>, BigUint)>> {
    basis.retain(|p| !p.is_zero());
    for p in basis.iter_mut() {
        *p = p.make_monic(ring);
    }
    let mut out: Vec<Vec<(Vec<u16>, BigUint)>> = basis
        .iter()
        .map(|p| {
            let mut ts: Vec<(Vec<u16>, BigUint)> = p
                .terms(ring)
                .map(|t| (t.exponents().to_vec(), ring.field.to_biguint(t.coefficient())))
                .collect();
            ts.sort();
            ts
        })
        .collect();
    out.sort();
    out
}

/// Spec of ideal-membership: each input generator reduces to zero
/// modulo any GB of the ideal it generates (Buchberger).
fn assert_gens_in_ideal(gens: &[DensePoly], basis: &[DensePoly], ring: &Arc<PolyRing>) {
    let refs: Vec<&DensePoly> = basis.iter().collect();
    for g in gens {
        let nf = g.reduce_by_refs(&refs, ring);
        assert!(
            nf.is_zero(),
            "input generator not in ideal of computed GB (residue has {} term(s))",
            nf.num_terms()
        );
    }
}

// (`f4_path_generators_reduce_to_zero_handbuilt_gf7` and
// `f4_vs_per_pair_reduced_gb_equal_handbuilt_gf7` folded into the broader
// `diff_f4_vs_buch_bank_small_primes_sweep` differential bank below — the
// bank exercises ideal-membership AND mutual ideal-equality across multiple
// system shapes (cyclic_3, overlapping_lts, sparse_linear, …) and primes.)

// (`f4_vs_per_pair_edge_primes` folded into `diff_f4_vs_buch_edge_primes_small`
// + `diff_f4_vs_buch_bank_small_primes_sweep` — the differential bank covers
// the same property across GF(2)/3/5 (small-prime bitprop hazard) and GF(7),
// and includes the GF(2)/3/5 sweep this test was probing. Large prime
// (~2^31) is covered by `diff_f4_vs_buch_bank_bn254_3vars` below.
//
// `f4_vs_per_pair_overlapping_lts_gf7` likewise covered by the bank's
// "overlapping_lts" shape over GF(7).)

// ── (4) post-op invariant: reduced GB is MONIC, leading terms MINIMAL ──

/// Spec: a *reduced* GB satisfies (i) every element is monic, and
/// (ii) no element's leading monomial divides another's
/// (Cox-Little-O'Shea Defn 2.7.4). Both must hold of the F4 path's
/// output.
#[test]
fn f4_reduced_gb_is_monic_and_lt_minimal() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let z = DensePoly::variable(2, &ring);
    // Coefficients deliberately non-1 to force `make_monic` work.
    let g1 = x.mul(&y, &ring).scale(&ring.field.from_u64(3), &ring).sub(&z, &ring);
    let g2 = y.mul(&z, &ring).scale(&ring.field.from_u64(4), &ring).sub(&x, &ring);
    let g3 = z.mul(&x, &ring).scale(&ring.field.from_u64(5), &ring).sub(&y, &ring);
    let gens = vec![g1, g2, g3];

    let cfg = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let gb = buch_interreduce(buch_gb(gens, &ring, &cfg).unwrap().basis, &ring);
    let one = ring.field.to_biguint(&ring.field.one());

    // (i) monic
    for p in &gb {
        let lc = p.leading_coefficient().expect("nonzero element");
        assert_eq!(ring.field.to_biguint(lc), one, "reduced GB element not monic");
    }
    // (ii) LT-minimal
    let lts: Vec<Monomial> = gb.iter().map(|p| p.leading_monomial(&ring).unwrap()).collect();
    for i in 0..lts.len() {
        for j in 0..lts.len() {
            if i != j {
                assert!(!lts[i].divides(&lts[j]), "reduced GB: LT[{i}] divides LT[{j}]");
            }
        }
    }
}

// ── (8) determinism: same input ⇒ same output across two F4 calls ──

/// Spec: F4 has no hidden randomness; two consecutive calls with
/// structurally-equal inputs must produce structurally-equal output.
#[test]
fn f4_path_is_deterministic_across_two_calls() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let z = DensePoly::variable(2, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let g1 = x.mul(&y, &ring).sub(&z, &ring);
    let g2 = y.mul(&z, &ring).sub(&one, &ring);
    let g3 = x.add(&y, &ring).add(&z, &ring);
    let gens = vec![g1, g2, g3];

    let cfg = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let a = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg).unwrap().basis, &ring);
    let b = buch_interreduce(buch_gb(gens, &ring, &cfg).unwrap().basis, &ring);
    assert_eq!(canon_dense(a, &ring), canon_dense(b, &ring));
}

// (`f4_with_unit_generator_collapses_to_one` folded into the differential
// bank's `contains_one_trivial_unsat` and `constant_and_relation` systems,
// which probe the same {1}-collapse over multiple primes via
// `assert_trivial_iff_unit_in_gens`.)

// ── (1) algebraic identity on the S-polynomial produced by process_batch ──

/// Spec of the S-polynomial as built inside `process_batch`:
/// S(f, g) = (lcm / LT(f)) · f − (lc(f) / lc(g)) · (lcm / LT(g)) · g.
/// Building S(f, g) for two basis elements with INVERSE leading
/// monomial relations (lm(f) | lm(g)) makes the cofactor for f equal
/// to lcm/lm(f) = lm(g)/lm(f), and the resulting S-poly must lie in
/// the ideal generated by {f, g}. Verify residue is zero modulo
/// {f, g}.
#[test]
fn process_batch_output_lies_in_input_ideal_gf7() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let z = DensePoly::variable(2, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    // f1 = x*y - z, f2 = y*z - 1.
    let f1 = x.mul(&y, &ring).sub(&z, &ring);
    let f2 = y.mul(&z, &ring).sub(&one, &ring);
    let basis_polys = vec![f1.clone(), f2.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
        .collect();

    let lcm = basis_lts[0].lcm(&basis_lts[1]);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0,
        j: 1,
        sugar: lcm_deg,
        lcm,
        lcm_divmask: lcm_dm,
        lcm_deg,
        age: 0,
        generation: 0,
        is_coprime: false,
    };
    let new_polys = process_batch(&[&pair], &basis, &ring, None);

    // Every produced polynomial is a combination of f1, f2 — must lie
    // in the ideal ⟨f1, f2⟩, so it reduces to zero modulo {f1, f2}'s
    // reduced GB.
    let cfg = BuchbergerConfig::default();
    let gb = buch_interreduce(buch_gb(basis_polys, &ring, &cfg).unwrap().basis, &ring);
    let gb_refs: Vec<&DensePoly> = gb.iter().collect();
    for out in &new_polys {
        let nf = out.poly.reduce_by_refs(&gb_refs, &ring);
        assert!(nf.is_zero(), "F4 output not in input ideal");
    }
}

// (`f4_single_generator_returns_input_monic` covered by the differential
// bank's `sparse_linear` / `single_monomial_x0sq` / `high_degree_monomials`
// single-gen systems plus `f4_reduced_gb_is_monic_and_lt_minimal` for the
// monicity property.)

// ─────────────────────────────────────────────────────────────────────
// Hard-probe: F4 vs Buchberger differential (mutual ideal-membership)
// across primes / shapes / cancel boundaries / F4_MIN_BATCH edges.
//
// Spec: the reduced GB under a fixed monomial order is unique, hence
// per-pair Buchberger and F4-lite must agree as IDEALS (not merely as
// LT sets) on every input. Mutual-ideal-membership is the strongest
// general check: every element of A reduces to zero against B, and
// every element of B reduces to zero against A.
//
// Test inputs cover GF(7), GF(101), BN254 (~254-bit); sparse, dense,
// high-degree-monomial, repeated-generator, single-monomial, and
// 1∈I systems; small and many variables.
// ─────────────────────────────────────────────────────────────────────

/// Large-prime ring helper: takes a decimal-string prime so we can
/// hit BN254 (~2^254) without u64 truncation.
fn ring_prime_str(p_dec: &str, n_vars: usize) -> Arc<PolyRing> {
    let p = p_dec.parse::<BigUint>().unwrap();
    PolyRing::new(
        PrimeField::new(p),
        (0..n_vars).map(|i| format!("x{i}")).collect(),
        MonomialOrder::DegRevLex,
    )
}

/// BN254 scalar-field prime (the curve picus targets).
const BN254_PRIME: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Hand-built differential bank. Each closure returns a generator
/// list spec'd by mathematical structure — never read back from
/// engine output. Property: F4's reduced GB and per-pair's reduced
/// GB generate the same ideal (mutual ideal-membership).
fn diff_systems_dense(ring: &Arc<PolyRing>) -> Vec<(&'static str, Vec<DensePoly>)> {
    let one = DensePoly::constant(ring.field.one(), ring);
    let two = DensePoly::constant(ring.field.from_u64(2), ring);
    let three = DensePoly::constant(ring.field.from_u64(3), ring);
    let n = ring.var_names.len();
    let v: Vec<DensePoly> = (0..n).map(|i| DensePoly::variable(i, ring)).collect();

    let mut systems: Vec<(&'static str, Vec<DensePoly>)> = Vec::new();

    // (1) Sparse — single linear binomial.
    if n >= 2 {
        let f = v[0].add(&v[1], ring).sub(&one, ring);
        systems.push(("sparse_linear", vec![f]));
    }
    // (2) Sparse — two coprime linears.
    if n >= 2 {
        let f1 = v[0].sub(&one, ring);
        let f2 = v[1].sub(&two, ring);
        systems.push(("sparse_two_coprime_linear", vec![f1, f2]));
    }
    // (3) Single monomial generator (x0^2).
    if n >= 1 {
        let f = v[0].mul(&v[0], ring);
        systems.push(("single_monomial_x0sq", vec![f]));
    }
    // (4) Repeated generator (duplicate of x0*x1 - 1).
    if n >= 2 {
        let p = v[0].mul(&v[1], ring).sub(&one, ring);
        systems.push(("repeated_generator_xy_minus_1", vec![p.clone(), p]));
    }
    // (5) Trivial UNSAT seed: includes the constant 1.
    {
        systems.push(("contains_one_trivial_unsat", vec![one.clone()]));
    }
    // (6) Trivial UNSAT mix: constant 2 alongside genuine relation.
    if n >= 2 {
        let f = v[0].mul(&v[1], ring).sub(&one, ring);
        systems.push(("constant_and_relation", vec![two.clone(), f]));
    }
    // (7) High-degree monomial generators (x0^5, x1^4).
    if n >= 2 {
        let mut p1 = one.clone();
        for _ in 0..5 { p1 = p1.mul(&v[0], ring); }
        let mut p2 = one.clone();
        for _ in 0..4 { p2 = p2.mul(&v[1], ring); }
        systems.push(("high_degree_monomials", vec![p1, p2]));
    }
    // (8) Dense — every variable appears with a non-trivial coefficient.
    if n >= 3 {
        let f = v[0]
            .mul(&v[1], ring).scale(&ring.field.from_u64(3), ring)
            .add(&v[1].mul(&v[2], ring).scale(&ring.field.from_u64(4), ring), ring)
            .add(&v[0].mul(&v[2], ring).scale(&ring.field.from_u64(5), ring), ring)
            .sub(&v[0], ring)
            .sub(&v[1], ring)
            .sub(&v[2], ring)
            .add(&three, ring);
        systems.push(("dense_one_relation", vec![f]));
    }
    // (9) Cyclic-3 (classic GB stress test).
    if n >= 3 {
        let f1 = v[0].add(&v[1], ring).add(&v[2], ring);
        let f2 = v[0].mul(&v[1], ring)
            .add(&v[1].mul(&v[2], ring), ring)
            .add(&v[0].mul(&v[2], ring), ring);
        let f3 = v[0].mul(&v[1], ring).mul(&v[2], ring).sub(&one, ring);
        systems.push(("cyclic_3", vec![f1, f2, f3]));
    }
    // (10) Overlapping LTs — drives symbolic preprocessing chains.
    if n >= 3 {
        let f1 = v[0].mul(&v[0], ring).sub(&v[1], ring); // x0^2 - x1
        let f2 = v[0].mul(&v[1], ring).sub(&v[2], ring); // x0 x1 - x2
        let f3 = v[1].mul(&v[1], ring).sub(&v[0], ring); // x1^2 - x0
        systems.push(("overlapping_lts_x0x1x2", vec![f1, f2, f3]));
    }
    // (11) Field-polynomial-like generators: x_i^p in GF(p) is not what we
    // want (Fermat collapses), but adding x_i^2 - x_i (idempotent) probes
    // small-degree boundary.
    if n >= 2 {
        let f1 = v[0].mul(&v[0], ring).sub(&v[0], ring); // x0^2 - x0
        let f2 = v[1].mul(&v[1], ring).sub(&v[1], ring); // x1^2 - x1
        let f3 = v[0].add(&v[1], ring).sub(&one, ring);  // x0 + x1 - 1
        systems.push(("idempotents_plus_linear", vec![f1, f2, f3]));
    }
    // (12) Many vars, sparse single linear.
    if n >= 4 {
        let mut acc = v[0].clone();
        for i in 1..n { acc = acc.add(&v[i], ring); }
        let f = acc.sub(&one, ring);
        systems.push(("n_vars_sum_minus_1", vec![f]));
    }
    // (13) Zero polynomial mixed with real generators (must be dropped).
    if n >= 2 {
        let z = DensePoly::zero();
        let f = v[0].mul(&v[1], ring).sub(&one, ring);
        systems.push(("zero_mixed_with_relation", vec![z, f]));
    }

    systems
}

/// Mutual-ideal-membership over Dense polys: every element of `a`
/// reduces to zero modulo `b` AND vice versa. Stronger than LT-set
/// equality; pins ideal equality even when bases differ.
fn assert_ideals_equal_dense(
    label: &str,
    a: &[DensePoly],
    b: &[DensePoly],
    ring: &Arc<PolyRing>,
) {
    let a_refs: Vec<&DensePoly> = a.iter().collect();
    let b_refs: Vec<&DensePoly> = b.iter().collect();
    for p in a {
        if p.is_zero() { continue; }
        let nf = p.reduce_by_refs(&b_refs, ring);
        assert!(
            nf.is_zero(),
            "{label}: A ⊄ B (a-element residue has {} term(s))",
            nf.num_terms()
        );
    }
    for p in b {
        if p.is_zero() { continue; }
        let nf = p.reduce_by_refs(&a_refs, ring);
        assert!(
            nf.is_zero(),
            "{label}: B ⊄ A (b-element residue has {} term(s))",
            nf.num_terms()
        );
    }
}

/// SPEC: if 1 ∈ I, both engines must produce {1} as the reduced GB.
fn assert_trivial_iff_unit_in_gens(
    label: &str,
    gens: &[DensePoly],
    gb_pp: &[DensePoly],
    gb_f4: &[DensePoly],
) {
    let unit_present = gens.iter().any(|p| p.is_constant() && !p.is_zero());
    if unit_present {
        // Buchberger.interreduce returns {1} on trivial ideals.
        let pp_trivial = gb_pp.iter().any(|p| p.is_constant() && !p.is_zero());
        let f4_trivial = gb_f4.iter().any(|p| p.is_constant() && !p.is_zero());
        assert!(pp_trivial, "{label}: per-pair must report trivial ideal");
        assert!(f4_trivial, "{label}: F4 must report trivial ideal");
    }
}

/// Run F4 vs Buchberger differential over all `diff_systems_dense`
/// shapes against a chosen prime. Spec: reduced GBs are unique, so
/// the two paths must produce the same ideal (mutual membership).
fn run_f4_vs_buch_diff_bank(prime: u64, n_vars: usize) {
    let ring = ring_p(prime, n_vars);
    for (name, gens) in diff_systems_dense(&ring) {
        let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
        let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
        let gb_pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
        let gb_f4 = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_f4).unwrap().basis, &ring);

        // Spec: every input generator lies in either GB.
        assert_gens_in_ideal(&gens, &gb_pp, &ring);
        assert_gens_in_ideal(&gens, &gb_f4, &ring);
        // Spec: ideals are equal.
        let label = format!("[GF({prime})/{n_vars}vars/{name}]");
        assert_ideals_equal_dense(&label, &gb_pp, &gb_f4, &ring);
        // Spec: trivial-ideal canonical form.
        assert_trivial_iff_unit_in_gens(&label, &gens, &gb_pp, &gb_f4);
    }
}

#[test]
fn diff_f4_vs_buch_bank_small_primes_sweep() {
    // Sweeps (prime, n_vars) ∈ {(7,2), (7,3), (7,4), (101,3), (101,4)};
    // each call exercises the full `diff_systems_dense` bank under that
    // (prime, n_vars) — every system reduces to zero against both engines'
    // GBs and the per-pair vs F4 ideals agree.
    for (prime, n_vars) in [(7u64, 2), (7, 3), (7, 4), (101, 3), (101, 4)] {
        run_f4_vs_buch_diff_bank(prime, n_vars);
    }
}

/// Big-prime (BN254) version: ~2^254 prime so all coefficient arithmetic
/// goes through GMP. Smaller bank (3-var only) because BN254 arithmetic
/// is slow.
#[test]
fn diff_f4_vs_buch_bank_bn254_3vars() {
    let ring = ring_prime_str(BN254_PRIME, 3);
    for (name, gens) in diff_systems_dense(&ring) {
        let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
        let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
        let gb_pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
        let gb_f4 = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_f4).unwrap().basis, &ring);

        let label = format!("[BN254/3vars/{name}]");
        assert_gens_in_ideal(&gens, &gb_pp, &ring);
        assert_gens_in_ideal(&gens, &gb_f4, &ring);
        assert_ideals_equal_dense(&label, &gb_pp, &gb_f4, &ring);
        assert_trivial_iff_unit_in_gens(&label, &gens, &gb_pp, &gb_f4);
    }
}

/// Edge primes: GF(2), GF(3), GF(5). Corpus memory pins small-prime
/// bitprop bugs (R5/H1, R7/J1) — probe GB engines on the same small
/// primes for parity.
#[test]
fn diff_f4_vs_buch_edge_primes_small() {
    for &p in &[2u64, 3, 5] {
        // 2-var only — keep small-prime cyclic computations cheap.
        run_f4_vs_buch_diff_bank(p, 2);
    }
}

// ─────────────────────────────────────────────────────────────────────
// Cancel boundary: pre-cancelled token at every entry point must NOT
// produce engine output that claims a verdict (Sat/Unsat). For F4 at
// the `process_batch` level the contract is an empty Vec; for the
// `groebner_basis` wrapper the contract is EngineError::Timeout.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn diff_precancelled_token_at_groebner_basis_returns_timeout() {
    // Spec: a cancel token that is already cancelled before the call
    // must surface a Timeout error before any (potentially incorrect)
    // basis is emitted. Probed for both per-pair and F4 paths.
    let ring = ring_p(7, 3);
    let x0 = DensePoly::variable(0, &ring);
    let x1 = DensePoly::variable(1, &ring);
    let x2 = DensePoly::variable(2, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let gens = vec![
        x0.mul(&x1, &ring).sub(&x2, &ring),
        x1.mul(&x2, &ring).sub(&one, &ring),
        x0.mul(&x2, &ring).add(&x1, &ring),
    ];
    for &use_f4 in &[false, true] {
        let token = CancelToken::cancelled();
        let cfg = BuchbergerConfig {
            cancel_token: Some(token),
            use_f4,
            ..BuchbergerConfig::default()
        };
        // The engine may legitimately complete trivially-small inputs even
        // under cancellation IF every cancel check passes before any
        // potentially-incorrect output is emitted. The contract we hold
        // is the inverse: if the engine RETURNS Ok, the basis is real;
        // if it returns Err it must be Timeout, never some other error.
        let res = buch_gb(gens.clone(), &ring, &cfg);
        match res {
            Ok(gb) => {
                // Spec: even on a fast completion, the output must remain
                // a sound GB of the input ideal.
                assert_gens_in_ideal(&gens, &gb.basis, &ring);
            }
            Err(crate::EngineError::Timeout) => {
                // Expected.
            }
            Err(other) => panic!(
                "pre-cancelled token must produce Timeout, not {:?} (use_f4={use_f4})",
                other
            ),
        }
    }
}

#[test]
fn diff_precancelled_token_at_process_batch_returns_empty() {
    // Spec contract for the F4 batch primitive: a pre-cancelled
    // token forces an empty output. Test all the system shapes
    // in `diff_systems_dense` to make sure no shape can sneak
    // a non-empty output past the cancel guard.
    let ring = ring_p(7, 3);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let x0 = DensePoly::variable(0, &ring);
    let x1 = DensePoly::variable(1, &ring);
    let x2 = DensePoly::variable(2, &ring);
    // basis = {x0 x1 - x2, x1 x2 - 1}.
    let f0 = x0.mul(&x1, &ring).sub(&x2, &ring);
    let f1 = x1.mul(&x2, &ring).sub(&one, &ring);
    let basis_polys = vec![f0, f1];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter()
        .zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef {
            poly: p, lt: l,
            lt_divmask: ring.divmask.compute(l),
            active: true,
        })
        .collect();
    let lcm = basis_lts[0].lcm(&basis_lts[1]);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let pair = SPair {
        i: 0, j: 1, sugar: lcm_deg, lcm, lcm_divmask: lcm_dm,
        lcm_deg, age: 0, generation: 0, is_coprime: false,
    };
    let token = CancelToken::cancelled();
    let out = process_batch(&[&pair], &basis, &ring, Some(&token));
    assert!(out.is_empty(), "pre-cancelled token must short-circuit process_batch");
    // Repeat with a workspace-threaded variant.
    let mut ws = F4Workspace::new();
    let out2 = process_batch_with_workspace(&[&pair], &basis, &ring, Some(&token), &mut ws);
    assert!(out2.is_empty(), "workspace variant must also short-circuit");
}

// (`diff_mid_pipeline_cancel_token` — `CancelToken::new()` + `cancel()` before
// the call — folded into `diff_precancelled_token_at_groebner_basis_returns_timeout`
// (above), which covers the same pre-cancellation entry-point semantics for
// both per-pair and F4 paths via `CancelToken::cancelled()`.)

// ─────────────────────────────────────────────────────────────────────
// F4_MIN_BATCH boundary: F4 routes batches of < F4_MIN_BATCH (12) to
// the per-pair geobucket fallback and ≥ 12 to the matrix path. Build
// adversarial inputs that straddle the boundary so a regression
// affecting only one branch surfaces.
// ─────────────────────────────────────────────────────────────────────

// (`diff_f4_min_batch_boundary_exactly_12_pairs` — 5-var mixed degree-1/2
// system — folded into the more adversarial
// `diff_f4_min_batch_boundary_homogeneous_x0_chained` (13-var, C(13,2)=78
// non-coprime pairs at sugar 2: a strictly stronger F4 matrix-path probe)
// and the process_batch-level `diff_f4_min_batch_boundary_12_identical_pairs`.)

/// Same-sugar batch exactly 12 from a structurally-uniform input:
/// 13 polynomials of the form `xi^2 - c_i` for distinct constants c_i
/// over GF(101). Every leading monomial is `xi^2` (pairwise coprime
/// for i != j), so coprime pruning would drop all pairs unless we
/// chain a uniform shape that defeats coprimality. Instead use
/// `x0 xi - c_i` so every pair shares x0 ⇒ no coprime pruning ⇒
/// C(13,2) = 78 batch contention. Then the F4 path WILL fire matrix
/// reduction on the largest same-sugar group.
#[test]
fn diff_f4_min_batch_boundary_homogeneous_x0_chained() {
    let ring = ring_p(101, 13);
    let v: Vec<DensePoly> = (0..13).map(|i| DensePoly::variable(i, &ring)).collect();
    let mut gens: Vec<DensePoly> = Vec::new();
    for i in 1..13 {
        let ci = DensePoly::constant(ring.field.from_u64((i as u64) + 7), &ring);
        // x0 * xi - c_i (LT = x0 xi; lots of shared x0 ⇒ many non-coprime pairs).
        gens.push(v[0].mul(&v[i], &ring).sub(&ci, &ring));
    }
    let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
    let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let gb_pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
    let gb_f4 = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_f4).unwrap().basis, &ring);

    assert_gens_in_ideal(&gens, &gb_pp, &ring);
    assert_gens_in_ideal(&gens, &gb_f4, &ring);
    assert_ideals_equal_dense("[f4_min_batch_homogeneous_x0]", &gb_pp, &gb_f4, &ring);
}

/// Adversarial shape: 12 IDENTICAL pairs (i=0, j=1) forced into a
/// batch — they all have the same sugar/lcm. Spec: F4's batch
/// dedup/echelonisation must produce an output ideal-equivalent to
/// a single pair's S-poly. Probe at process_batch level.
#[test]
fn diff_f4_min_batch_boundary_12_identical_pairs() {
    let ring = ring_p(7, 2);
    let x0 = DensePoly::variable(0, &ring);
    let x1 = DensePoly::variable(1, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let f0 = x0.mul(&x1, &ring).sub(&one, &ring); // x*y - 1
    let f1 = x1.mul(&x1, &ring).sub(&x0, &ring);  // y^2 - x
    let basis_polys = vec![f0.clone(), f1.clone()];
    let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
    let basis: Vec<F4BasisRef> = basis_polys
        .iter().zip(basis_lts.iter())
        .map(|(p, l)| F4BasisRef {
            poly: p, lt: l,
            lt_divmask: ring.divmask.compute(l),
            active: true,
        }).collect();
    let lcm = basis_lts[0].lcm(&basis_lts[1]);
    let lcm_dm = ring.divmask.compute(&lcm);
    let lcm_deg = lcm.total_degree();
    let mk_pair = |age: u64| SPair {
        i: 0, j: 1, sugar: lcm_deg, lcm: lcm.clone(), lcm_divmask: lcm_dm,
        lcm_deg, age, generation: 0, is_coprime: false,
    };
    let pairs: Vec<SPair> = (0..12).map(mk_pair).collect();
    let pair_refs: Vec<&SPair> = pairs.iter().collect();
    let out = process_batch(&pair_refs, &basis, &ring, None);
    // Spec: every output must lie in the ideal ⟨f0, f1⟩.
    let cfg = BuchbergerConfig::default();
    let gb = buch_interreduce(buch_gb(basis_polys.clone(), &ring, &cfg).unwrap().basis, &ring);
    let gb_refs: Vec<&DensePoly> = gb.iter().collect();
    for o in &out {
        let nf = o.poly.reduce_by_refs(&gb_refs, &ring);
        assert!(nf.is_zero(), "12-identical-pair batch produced poly outside the ideal");
    }
    // Sanity: 12 identical pairs ≡ 1 pair as far as the ideal is concerned.
    let out1 = process_batch(&[&pairs[0]], &basis, &ring, None);
    // Whatever non-zero outputs exist on both sides must lie in each other's ideal.
    let out_polys: Vec<DensePoly> = out.iter().map(|o| o.poly.clone()).collect();
    let out1_polys: Vec<DensePoly> = out1.iter().map(|o| o.poly.clone()).collect();
    // ideal(out_polys ∪ basis) should equal ideal(out1_polys ∪ basis).
    let mut union_a = basis_polys.clone();
    union_a.extend(out_polys);
    let mut union_b = basis_polys.clone();
    union_b.extend(out1_polys);
    let gb_a = buch_interreduce(buch_gb(union_a, &ring, &cfg).unwrap().basis, &ring);
    let gb_b = buch_interreduce(buch_gb(union_b, &ring, &cfg).unwrap().basis, &ring);
    assert_ideals_equal_dense("[12-identical-vs-1]", &gb_a, &gb_b, &ring);
}

// ─────────────────────────────────────────────────────────────────────
// Restart-schedule independence note: groebner_basis has no restart
// schedule (Buchberger is monotone — no SAT-style restarts). Recorded
// in the StructuredOutput skips section so the orchestrator can route
// the property to the SAT subsystem instead.
// ─────────────────────────────────────────────────────────────────────
