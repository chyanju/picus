use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn pr_one_var() -> FfPolyRing {
    FfPolyRing::new(PrimeField::new(BigUint::from(7u32)), vec!["x".into()])
}

fn pr_two_vars() -> FfPolyRing {
    FfPolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
    )
}

// ─────── split_gb (fallback wrapper around split_gb_cancel) ───────

#[test]
fn split_gb_with_empty_generators_yields_per_partition_empty_basis() {
    let pr = pr_one_var();
    let generator_sets: Vec<Vec<Poly>> = vec![vec![], vec![]];
    let mut bp = BitProp::new(&pr);
    let split = split_gb(&pr, generator_sets, &mut bp);
    assert_eq!(split.len(), 2);
    for ideal in &split {
        assert!(ideal.basis.is_empty(), "partition basis should be empty");
    }
}

// ─────── split_gb_cancel ───────

#[test]
fn split_gb_cancel_pre_cancelled_returns_err() {
    let pr = pr_one_var();
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_gb_cancel(&pr, vec![vec![]], &mut bp, &cancel);
    assert!(matches!(out, Err(Cancelled)));
}

#[test]
fn split_gb_cancel_with_consistent_input_keeps_generator_in_basis() {
    // [x - 3] is already a singleton GB; fixpoint should converge
    // without growth and the partition basis should contain it.
    let pr = pr_one_var();
    let f = pr.field();
    let p = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::none();
    let split = split_gb_cancel(&pr, vec![vec![p]], &mut bp, &cancel).expect("not cancelled");
    assert_eq!(split.len(), 1);
    assert!(!split[0].basis.is_empty());
    assert!(
        !split[0].is_whole_ring(),
        "consistent system is not whole ring"
    );
}

#[test]
fn split_gb_cancel_inconsistent_input_yields_whole_ring() {
    // [x - 1, x - 2] → S-poly = 1, ideal = whole ring.
    let pr = pr_one_var();
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::none();
    let split = split_gb_cancel(&pr, vec![vec![p1, p2]], &mut bp, &cancel).expect("not cancelled");
    assert!(split[0].is_whole_ring());
}

// ─────── split_gb_extend_cancel ───────

#[test]
fn split_gb_extend_cancel_from_empty_matches_from_scratch_via_split_gb_cancel() {
    // Both entry points should produce the same final basis when
    // `starting` is empty and `new_polys` is the original input.
    let pr = pr_one_var();
    let f = pr.field();
    let make_input = || vec![vec![pr.sub(pr.var(0), pr.constant(f.from_int(4)))]];

    let mut bp1 = BitProp::new(&pr);
    let from_scratch =
        split_gb_cancel(&pr, make_input(), &mut bp1, &CancelToken::none()).expect("not cancelled");

    let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
    let mut bp2 = BitProp::new(&pr);
    let extended =
        split_gb_extend_cancel(&pr, starting, make_input(), &mut bp2, &CancelToken::none())
            .expect("not cancelled");

    assert_eq!(from_scratch.len(), extended.len());
    assert_eq!(from_scratch[0].basis.len(), extended[0].basis.len());
}

#[test]
fn split_gb_extend_cancel_with_empty_new_polys_is_noop() {
    let pr = pr_one_var();
    let f = pr.field();
    let seed = pr.sub(pr.var(0), pr.constant(f.from_int(5)));
    let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![seed])];
    let starting_len = starting[0].basis.len();
    let mut bp = BitProp::new(&pr);
    let out = split_gb_extend_cancel(&pr, starting, vec![vec![]], &mut bp, &CancelToken::none())
        .expect("not cancelled");
    assert_eq!(out[0].basis.len(), starting_len);
}

#[test]
fn split_gb_extend_cancel_pre_cancelled_returns_err() {
    let pr = pr_one_var();
    let starting: SplitGb = vec![Ideal::from_gb(&pr, vec![])];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_gb_extend_cancel(&pr, starting, vec![vec![]], &mut bp, &cancel);
    assert!(matches!(out, Err(Cancelled)));
}

// ─────── split_gb_cancel_traced ───────

#[test]
fn split_gb_cancel_traced_consistent_returns_no_core() {
    let pr = pr_two_vars();
    let f = pr.field();
    // x - 3, y - 4: independent assignments, consistent.
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(3)));
    let p2 = pr.sub(pr.var(1), pr.constant(f.from_int(4)));
    let gens = vec![vec![p1, p2]];
    let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![
        [0].iter().copied().collect(),
        [1].iter().copied().collect(),
    ]];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::none();
    let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel).expect("not cancelled");
    assert!(out.unsat_core.is_none(), "consistent system → no core");
    assert!(!out.split_basis[0].is_whole_ring());
}

#[test]
fn split_gb_cancel_traced_inconsistent_with_deps_returns_core() {
    // [x - 1, x - 2] → whole ring; deps name original input indices.
    let pr = pr_one_var();
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let gens = vec![vec![p1, p2]];
    let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![
        [0].iter().copied().collect(),
        [1].iter().copied().collect(),
    ]];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::none();
    let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel).expect("not cancelled");
    let core = out.unsat_core.expect("inconsistent → core extracted");
    // Conservative super-set: must mention both contributing inputs.
    assert!(core.contains(&0));
    assert!(core.contains(&1));
}

#[test]
fn split_gb_cancel_traced_inconsistent_empty_deps_returns_none_core() {
    // Inconsistent system but every input is dep-free (encoder-internal):
    // `all_input_deps` is empty → tracer returns `unsat_core = None`.
    let pr = pr_one_var();
    let f = pr.field();
    let p1 = pr.sub(pr.var(0), pr.constant(f.from_int(1)));
    let p2 = pr.sub(pr.var(0), pr.constant(f.from_int(2)));
    let gens = vec![vec![p1, p2]];
    let deps: Vec<Vec<BTreeSet<usize>>> = vec![vec![BTreeSet::new(), BTreeSet::new()]];
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::none();
    let out = split_gb_cancel_traced(&pr, gens, deps, &mut bp, &cancel).expect("not cancelled");
    assert!(out.split_basis[0].is_whole_ring());
    assert!(
        out.unsat_core.is_none(),
        "empty-dep inputs leave the core unattributable"
    );
}

#[test]
fn split_gb_cancel_traced_pre_cancelled_returns_err() {
    let pr = pr_one_var();
    let mut bp = BitProp::new(&pr);
    let cancel = CancelToken::cancelled();
    let out = split_gb_cancel_traced(&pr, vec![vec![]], vec![vec![]], &mut bp, &cancel);
    assert!(matches!(out, Err(Cancelled)));
}
