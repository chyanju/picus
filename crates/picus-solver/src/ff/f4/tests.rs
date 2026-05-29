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
fn f4_multipair_3vars_cyclic() {
    // Cyclic-3-style ideal: classic test.
    // f1 = x0 + x1 + x2
    // f2 = x0*x1 + x1*x2 + x2*x0
    // f3 = x0*x1*x2 - 1
    let ring = ring_mod7(3);
    let one = ring.field.one();
    let neg_one = ring.field.neg(&one);
    let x0 = x(0, &ring);
    let x1 = x(1, &ring);
    let x2 = x(2, &ring);
    let f1 = x0.add(&x1.add(&x2, &ring), &ring);
    let f2 = x0.mul(&x1, &ring)
        .add(&x1.mul(&x2, &ring), &ring)
        .add(&x2.mul(&x0, &ring), &ring);
    let f3_part1 = x0.mul(&x1, &ring).mul(&x2, &ring);
    let f3 = f3_part1.add(&DensePoly::constant(neg_one, &ring), &ring);
    cross_check_all_pairs(vec![f1, f2, f3], &ring);
}

#[test]
fn f4_multipair_3vars_overlapping_lts() {
    // Three polys with overlapping LTs to exercise reducer-chain
    // propagation in symbolic preprocessing.
    // f1 = x0^2 - x1
    // f2 = x0*x1 - x2
    // f3 = x1^2 - x0  (LT(f3) = x1^2 may need reducer chain)
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

/// Randomized cross-check: for a handful of small ideals, the
/// F4-driven and per-pair-geobucket-driven incremental GB must
/// produce bases whose leading-term sets agree.
#[test]
fn f4_vs_per_pair_random_cross_check() {
    use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use std::collections::HashSet;

    // Deterministic LCG for reproducibility; produces small
    // bivariate polynomials over F_7.
    fn lcg(seed: u64) -> impl FnMut() -> u64 {
        let mut s = seed;
        move || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        }
    }

    for seed in 1u64..=12 {
        let ring = ring_mod7(2);
        let mut rng = lcg(seed);
        // Build 3 random bivariate polynomials, each of degree ≤ 2.
        let mut polys: Vec<DensePoly> = Vec::new();
        for _ in 0..3 {
            let one = ring.field.one();
            let x0 = x(0, &ring);
            let x1 = x(1, &ring);
            let xx = x0.mul(&x0, &ring);
            let yy = x1.mul(&x1, &ring);
            let xy = x0.mul(&x1, &ring);
            let const_one = DensePoly::constant(one.clone(), &ring);
            let mut acc = DensePoly::zero();
            for atom in [&xx, &xy, &yy, &x0, &x1, &const_one] {
                let coeff = (rng() % 7) as u32;
                if coeff == 0 { continue; }
                let c = ring.field.from_int(coeff as i64);
                let scaled = atom.mul(&DensePoly::constant(c, &ring), &ring);
                acc = acc.add(&scaled, &ring);
            }
            if !acc.is_zero() {
                polys.push(acc);
            }
        }
        if polys.len() < 2 {
            continue;
        }

        // Per-pair path. `abort_on_trivial: false` runs the
        // algorithm to quiescence even after a unit is found so
        // the comparison is against a fully-reduced GB.
        let cfg_pp = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: false,
            use_f4: false,
        };
        let mut igb_pp = IncrementalGB::new(Arc::clone(&ring), cfg_pp);
        let pp_trivial = igb_pp.add_generators(polys.clone()).expect("pp add");

        // F4 path.
        let cfg_f4 = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: false,
            use_f4: true,
        };
        let mut igb_f4 = IncrementalGB::new(Arc::clone(&ring), cfg_f4);
        let f4_trivial = igb_f4.add_generators(polys.clone()).expect("f4 add");

        // Both engines must agree on whether the ideal is the
        // whole ring (the only soundness-critical bit). If both
        // report trivial, the basis content is irrelevant — both
        // describe `R` regardless of which surviving polys
        // remain. If both report non-trivial, the LT sets must
        // match.
        assert_eq!(
            pp_trivial, f4_trivial,
            "F4 and per-pair disagree on triviality for seed={}: \
             pp_trivial={} f4_trivial={}",
            seed, pp_trivial, f4_trivial
        );
        if !pp_trivial {
            let pp_lts: HashSet<Vec<u16>> = igb_pp
                .basis()
                .iter()
                .map(|p| lt(p, &ring).exponents().to_vec())
                .collect();
            let f4_lts: HashSet<Vec<u16>> = igb_f4
                .basis()
                .iter()
                .map(|p| lt(p, &ring).exponents().to_vec())
                .collect();
            assert_eq!(
                pp_lts, f4_lts,
                "F4 and per-pair LT sets differ for seed={}: \
                 pp={:?} f4={:?}",
                seed, pp_lts, f4_lts
            );
        }
    }
}

/// Like [`f4_vs_per_pair_random_cross_check`], but over the BN254 scalar
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

/// Spec: ideal equality — each element of A reduces to 0 mod B and vice versa.
fn assert_ideals_equal(a: &[DensePoly], b: &[DensePoly], ring: &Arc<PolyRing>) {
    let a_refs: Vec<&DensePoly> = a.iter().collect();
    let b_refs: Vec<&DensePoly> = b.iter().collect();
    for p in a {
        let nf = p.reduce_by_refs(&b_refs, ring);
        assert!(nf.is_zero(), "A ⊄ B");
    }
    for p in b {
        let nf = p.reduce_by_refs(&a_refs, ring);
        assert!(nf.is_zero(), "B ⊄ A");
    }
}

// ── (4) post-op invariant: generators reduce to zero modulo F4's GB ──

/// Spec: a Gröbner basis G of ⟨f1,…,fk⟩ must contain ⟨f1,…,fk⟩ as
/// an ideal, so each fi has zero normal form modulo G. Test the F4
/// path directly via the Buchberger driver with `use_f4 = true`.
#[test]
fn f4_path_generators_reduce_to_zero_handbuilt_gf7() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let z = DensePoly::variable(2, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    // Non-trivial non-monomial system: x*y - z, y*z - x, z*x - y + 1.
    let g1 = x.mul(&y, &ring).sub(&z, &ring);
    let g2 = y.mul(&z, &ring).sub(&x, &ring);
    let g3 = z.mul(&x, &ring).sub(&y, &ring).add(&one, &ring);
    let gens = vec![g1, g2, g3];
    let cfg = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let gb = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg).unwrap().basis, &ring);
    assert_gens_in_ideal(&gens, &gb, &ring);
}

// ── (9) engine equivalence: F4 ≡ per-pair on hand-built systems ──

/// Spec: the reduced GB under a fixed monomial order is unique
/// (Cox-Little-O'Shea Thm 2.7.5). Per-pair and F4 paths process
/// different S-pair groupings but must converge on the SAME
/// reduced GB.
#[test]
fn f4_vs_per_pair_reduced_gb_equal_handbuilt_gf7() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let z = DensePoly::variable(2, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let g1 = x.mul(&y, &ring).sub(&z, &ring);
    let g2 = y.mul(&z, &ring).sub(&one, &ring);
    let g3 = x.mul(&z, &ring).add(&y, &ring);
    let gens = vec![g1, g2, g3];

    let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
    let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };

    let pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
    let f4 = buch_interreduce(buch_gb(gens, &ring, &cfg_f4).unwrap().basis, &ring);

    assert_eq!(canon_dense(pp, &ring), canon_dense(f4, &ring));
}

// ── (7) edge primes: GF(2), GF(3), GF(5), GF(7), large prime ──

/// Spec: F4 is a generic-characteristic algorithm; the reduced GB
/// of the same generator set must agree with the per-pair path over
/// any prime. Small primes (2, 3, 5, 7) and a large prime — corpus
/// memory says small primes have bitten the bit-prop subsystem
/// twice, so probe them hard here too.
#[test]
fn f4_vs_per_pair_edge_primes() {
    for &p in &[2u64, 3, 5, 7, 2_147_483_647] {
        let ring = ring_p(p, 2);
        let x = DensePoly::variable(0, &ring);
        let y = DensePoly::variable(1, &ring);
        let one = DensePoly::constant(ring.field.one(), &ring);
        let two = DensePoly::constant(ring.field.from_u64(2), &ring);
        // f1 = x*y - 1, f2 = x + y - 2.
        let f1 = x.mul(&y, &ring).sub(&one, &ring);
        let f2 = x.add(&y, &ring).sub(&two, &ring);
        let gens = vec![f1, f2];

        let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
        let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };

        let pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
        let f4 = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_f4).unwrap().basis, &ring);

        // Reduced GBs are equal (uniqueness theorem).
        assert_eq!(
            canon_dense(pp.clone(), &ring),
            canon_dense(f4.clone(), &ring),
            "F4 vs per-pair reduced-GB mismatch over GF({p})"
        );
        // And ideal-membership: each input reduces to 0 modulo F4's GB.
        assert_gens_in_ideal(&gens, &f4, &ring);
        // And cross-membership: F4's GB ≡ per-pair's GB as ideals.
        assert_ideals_equal(&pp, &f4, &ring);
    }
}

// ── (9) engine equivalence on a non-monomial system with overlapping LTs ──

/// Spec: F4 must handle overlapping leading terms (the case that
/// drives S-pair generation and symbolic-preprocessing) the same as
/// per-pair. Pick a non-monomial multivariate system in GF(7) where
/// every pair has a non-trivial S-polynomial.
#[test]
fn f4_vs_per_pair_overlapping_lts_gf7() {
    let ring = ring_p(7, 4);
    let x0 = DensePoly::variable(0, &ring);
    let x1 = DensePoly::variable(1, &ring);
    let x2 = DensePoly::variable(2, &ring);
    let x3 = DensePoly::variable(3, &ring);
    // All four leading monomials share x1.
    let g1 = x0.mul(&x1, &ring).sub(&x2, &ring);
    let g2 = x1.mul(&x2, &ring).sub(&x3, &ring);
    let g3 = x1.mul(&x3, &ring).sub(&x0, &ring);
    let gens = vec![g1, g2, g3];

    let cfg_pp = BuchbergerConfig { use_f4: false, ..BuchbergerConfig::default() };
    let cfg_f4 = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };

    let pp = buch_interreduce(buch_gb(gens.clone(), &ring, &cfg_pp).unwrap().basis, &ring);
    let f4 = buch_interreduce(buch_gb(gens, &ring, &cfg_f4).unwrap().basis, &ring);

    assert_eq!(canon_dense(pp, &ring), canon_dense(f4, &ring));
}

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

// ── (4) trivial-ideal property: 1 ∈ I ⟺ GB = {1} ──

/// Spec: if a generator is the unit, the ideal is the whole ring and
/// the reduced GB is {1}. The F4 path must enforce this.
#[test]
fn f4_with_unit_generator_collapses_to_one() {
    let ring = ring_p(7, 3);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let g = x.mul(&y, &ring); // non-unit
    let gens = vec![g, one];
    let cfg = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let gb = buch_interreduce(buch_gb(gens, &ring, &cfg).unwrap().basis, &ring);
    assert_eq!(gb.len(), 1, "GB of unit-containing ideal must be {{1}}");
    assert!(gb[0].is_constant() && !gb[0].is_zero(), "GB must be a nonzero constant");
}

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

// ── (7) tiny shape: single non-constant generator ──

/// Spec: GB({p}) for non-constant monic p is {p} — there are no
/// S-pairs to process, so the basis equals the input (made monic).
/// Verify for the F4-flagged path.
#[test]
fn f4_single_generator_returns_input_monic() {
    let ring = ring_p(7, 2);
    let x = DensePoly::variable(0, &ring);
    let y = DensePoly::variable(1, &ring);
    let one = DensePoly::constant(ring.field.one(), &ring);
    let p = x.mul(&y, &ring).sub(&one, &ring); // already monic
    let cfg = BuchbergerConfig { use_f4: true, ..BuchbergerConfig::default() };
    let gb = buch_interreduce(buch_gb(vec![p.clone()], &ring, &cfg).unwrap().basis, &ring);
    assert_eq!(gb.len(), 1, "single-generator GB must have one element");
    // Canonical form equality with the input's monic.
    let p_monic = p.make_monic(&ring);
    assert_eq!(canon_dense(vec![gb[0].clone()], &ring), canon_dense(vec![p_monic], &ring));
}
