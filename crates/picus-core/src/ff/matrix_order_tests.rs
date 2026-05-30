//! Spec lock: the matrix-order kernel must reproduce the classical
//! `Lex` / `DegRevLex` orders bit-for-bit before any wiring depends on it.

use super::*;

const N_VARS: usize = 6;
const MAX_EXP: u16 = 4;
const ITERS: usize = 50_000;

/// Deterministic xorshift PRNG so the fuzz corpus is reproducible.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn exps(&mut self) -> Vec<u16> {
        (0..N_VARS)
            .map(|_| (self.next() % (MAX_EXP as u64 + 1)) as u16)
            .collect()
    }
}

fn ref_total_deg(a: &[u16]) -> u32 {
    a.iter().map(|&e| e as u32).sum()
}

fn ref_cmp_lex(a: &[u16], b: &[u16]) -> Ordering {
    for i in 0..a.len() {
        match a[i].cmp(&b[i]) {
            Ordering::Equal => {}
            o => return o,
        }
    }
    Ordering::Equal
}

fn ref_cmp_degrevlex(a: &[u16], b: &[u16]) -> Ordering {
    match ref_total_deg(a).cmp(&ref_total_deg(b)) {
        Ordering::Equal => {
            for i in (0..a.len()).rev() {
                match a[i].cmp(&b[i]) {
                    Ordering::Equal => {}
                    Ordering::Less => return Ordering::Greater,
                    Ordering::Greater => return Ordering::Less,
                }
            }
            Ordering::Equal
        }
        o => o,
    }
}

#[test]
fn matrix_lex_matches_reference() {
    let m = MatrixOrder::lex(N_VARS);
    let mut rng = Rng(0xC0FFEE_u64);
    for _ in 0..ITERS {
        let a = rng.exps();
        let b = rng.exps();
        assert_eq!(
            m.cmp_dense(&a, &b),
            ref_cmp_lex(&a, &b),
            "lex mismatch a={:?} b={:?}",
            a,
            b
        );
    }
}

#[test]
fn matrix_degrevlex_matches_reference() {
    let m = MatrixOrder::degrevlex(N_VARS);
    let mut rng = Rng(0xDEADBEEF_u64);
    for _ in 0..ITERS {
        let a = rng.exps();
        let b = rng.exps();
        assert_eq!(
            m.cmp_dense(&a, &b),
            ref_cmp_degrevlex(&a, &b),
            "degrevlex mismatch a={:?} b={:?}",
            a,
            b
        );
    }
}

#[test]
fn builtin_orders_are_admissible() {
    assert!(MatrixOrder::lex(N_VARS).is_admissible());
    assert!(MatrixOrder::degrevlex(N_VARS).is_admissible());
    assert!(MatrixOrder::elim(&[0, 1], N_VARS).is_admissible());
}

#[test]
fn elim_order_eliminates_first() {
    // A monomial touching an eliminated var (x0) must order above one that
    // does not, regardless of total degree.
    let m = MatrixOrder::elim(&[0], N_VARS);
    let mut with_elim = vec![0u16; N_VARS];
    with_elim[0] = 1; // x0
    let mut without = vec![0u16; N_VARS];
    without[N_VARS - 1] = MAX_EXP; // x5^4, much higher total degree
    assert_eq!(m.cmp_dense(&with_elim, &without), Ordering::Greater);
}

#[test]
fn registry_intern_resolve_roundtrip() {
    let idx = intern(MatrixOrder::degrevlex(N_VARS));
    let resolved = resolve(idx);
    assert_eq!(*resolved, MatrixOrder::degrevlex(N_VARS));
    // A second intern yields a distinct, independently-resolvable index.
    let idx2 = intern(MatrixOrder::lex(N_VARS));
    assert_ne!(idx, idx2);
    assert_eq!(*resolve(idx2), MatrixOrder::lex(N_VARS));
}
