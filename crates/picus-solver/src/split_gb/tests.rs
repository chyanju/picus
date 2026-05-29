use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

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
