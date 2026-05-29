use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn no_linear_is_identity() {
    // Single nonlinear poly: x*y - 1. No linear polys → pass-through.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let p = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let elim = eliminate_linear(&pr, &[p], &CancelToken::none()).unwrap();
    assert!(!elim.applied);
    assert_eq!(elim.reduced.len(), 1);
    assert_eq!(elim.n_eliminated, 0);
}

#[test]
fn inconsistent_linear_is_unsat() {
    // x = 0 ∧ x = 1 over GF(7): linear subsystem alone is UNSAT.
    // A nonlinear generator (x*y) is included so the pass actually
    // runs (it is skipped for all-linear systems).
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let p1 = pr.var(0);
    let p2 = pr.sub(pr.var(0), pr.one());
    let p3 = pr.mul(pr.var(0), pr.var(1));
    let elim = eliminate_linear(&pr, &[p1, p2, p3], &CancelToken::none()).unwrap();
    assert!(elim.unsat);
}

#[test]
fn linear_relation_substituted_into_nonlinear() {
    // GF(7): x - 3 = 0 (linear, pins x=3) and x*y - 1 = 0 (nonlinear).
    // After elimination the nonlinear poly must no longer mention x:
    // x*y - 1 reduces to 3*y - 1.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let three = pr.field().from_int(3);
    let lin = pr.sub(pr.var(0), pr.constant(three));
    let nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let elim = eliminate_linear(&pr, &[lin, nl], &CancelToken::none()).unwrap();
    assert!(elim.applied);
    assert_eq!(elim.n_eliminated, 1);
    // Substitution happened: besides the pivot definition (x - 3,
    // which necessarily mentions x), at least one reduced poly is a
    // non-constant in y alone — the substituted x*y - 1 → 3*y - 1.
    let substituted = elim.reduced.iter().any(|p| {
        let vars = pr.ring.appearing_indeterminates(p);
        !vars.is_empty() && vars.iter().all(|v| v != 0)
    });
    assert!(
        substituted,
        "x must be substituted out of the nonlinear poly"
    );
    // The variety is preserved: x=3, y=5 satisfies both original
    // polys (3*5=15≡1 mod 7), and must satisfy every reduced poly.
    let assign = |v: usize| -> BigUint {
        match v {
            0 => BigUint::from(3u32),
            _ => BigUint::from(5u32),
        }
    };
    for p in &elim.reduced {
        let mut acc = pr.field().zero();
        for (c, m) in pr.ring.terms(p) {
            let mut term = pr.field().clone_el(c);
            for v in 0..pr.n_vars() {
                let e = pr.ring.exponent_at(&m, v);
                if e > 0 {
                    let val = pr.field().from_biguint(&assign(v));
                    term = pr.field().mul(&term, &pr.field().pow_u64(&val, e as u64));
                }
            }
            acc = pr.field().add(&acc, &term);
        }
        assert!(
            pr.field().is_zero(&acc),
            "reduced poly must vanish at the witness"
        );
    }
}

#[test]
fn zero_polynomials_are_skipped() {
    // GF(7): a zero poly mixed with one linear (x - 3) and one nonlinear
    // (x*y - 1). The zero poly is dropped during partitioning, so it
    // contributes neither to the linear nor the nonlinear set:
    // n_eliminated counts only the single real linear pivot.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let zero = pr.zero();
    let lin = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3)));
    let nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let elim = eliminate_linear(&pr, &[zero, lin, nl], &CancelToken::none()).unwrap();
    assert!(elim.applied);
    assert_eq!(elim.n_eliminated, 1);
    // The reduced set carries no zero polynomial.
    assert!(elim.reduced.iter().all(|p| !pr.is_zero(p)));
}

#[test]
fn cancellation_propagates_as_err() {
    // A linear + nonlinear system so the elimination pass actually runs,
    // with a pre-cancelled token. Cancellation must surface as
    // Err(Cancelled), never as a silently-applied elimination.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let lin = pr.sub(pr.var(0), pr.constant(pr.field().from_int(3)));
    let nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
    let cancel = CancelToken::cancelled();
    assert!(matches!(
        eliminate_linear(&pr, &[lin, nl], &cancel),
        Err(Cancelled)
    ));
}
