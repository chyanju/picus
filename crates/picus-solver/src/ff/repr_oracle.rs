//! Differential-test oracle for the polynomial representation.
//!
//! Pins the *specification* of every monomial / polynomial operation the
//! Gröbner-basis engine relies on, by checking the production
//! implementation against an independent textbook reference computed
//! directly from raw exponent vectors and coefficient maps. Run against
//! the current (dense) representation, these tests lock the spec. A
//! second representation is then validated by the same checks plus
//! direct equality against this one (the dense impl is the oracle).
//!
//! No external RNG dependency: a deterministic xorshift PRNG keeps the
//! fuzzing reproducible.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::BigUint;

use super::field::PrimeField;
use super::monomial::{Monomial, MonomialOrder};
use super::polynomial::{PolyRing, Polynomial};
use super::repr::MonomialRepr;
use super::sparse_monomial::SparseMonomial;

/// Deterministic xorshift64* PRNG — reproducible, no dependency.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const N_VARS: usize = 6;
const MAX_EXP: u16 = 4;
const PRIME: u64 = 101;

fn ring() -> std::sync::Arc<PolyRing> {
    let names: Vec<String> = (0..N_VARS).map(|i| format!("x{i}")).collect();
    PolyRing::new(PrimeField::new(BigUint::from(PRIME)), names, MonomialOrder::DegRevLex)
}

fn rand_exps(rng: &mut Rng) -> Vec<u16> {
    (0..N_VARS).map(|_| rng.below((MAX_EXP + 1) as u64) as u16).collect()
}

// ── textbook references over raw exponent vectors ───────────────────
fn ref_total_deg(e: &[u16]) -> u32 {
    e.iter().map(|&x| x as u32).sum()
}
fn ref_mul(a: &[u16], b: &[u16]) -> Vec<u16> {
    a.iter().zip(b).map(|(&x, &y)| x + y).collect()
}
fn ref_div(a: &[u16], b: &[u16]) -> Vec<u16> {
    a.iter().zip(b).map(|(&x, &y)| x - y).collect()
}
fn ref_lcm(a: &[u16], b: &[u16]) -> Vec<u16> {
    a.iter().zip(b).map(|(&x, &y)| x.max(y)).collect()
}
fn ref_gcd(a: &[u16], b: &[u16]) -> Vec<u16> {
    a.iter().zip(b).map(|(&x, &y)| x.min(y)).collect()
}
fn ref_divides(divisor: &[u16], of: &[u16]) -> bool {
    divisor.iter().zip(of).all(|(&x, &y)| x <= y)
}
fn ref_coprime(a: &[u16], b: &[u16]) -> bool {
    a.iter().zip(b).all(|(&x, &y)| x == 0 || y == 0)
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
            // reverse-lex tiebreak: the monomial with the SMALLER
            // highest-indexed differing exponent is the LARGER.
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

fn check_monomial_ops<M: MonomialRepr>(seed: u64, iters: usize) {
    let mut rng = Rng::new(seed);
    for _ in 0..iters {
        let ea = rand_exps(&mut rng);
        let eb = rand_exps(&mut rng);
        let a = M::from_exponents(ea.clone());
        let b = M::from_exponents(eb.clone());

        assert_eq!(a.total_degree(), ref_total_deg(&ea));
        assert_eq!(a.is_one(), ref_total_deg(&ea) == 0);
        assert_eq!(a.to_dense(), ea);
        for v in 0..N_VARS {
            assert_eq!(a.exponent(v), ea[v]);
        }
        let mut nz = vec![0u16; N_VARS];
        a.for_each_nonzero(|v, e| nz[v] = e);
        assert_eq!(nz, ea);

        assert_eq!(a.mul(&b).to_dense(), ref_mul(&ea, &eb));
        assert_eq!(a.lcm(&b).to_dense(), ref_lcm(&ea, &eb));
        assert_eq!(a.gcd(&b).to_dense(), ref_gcd(&ea, &eb));
        assert_eq!(a.divides(&b), ref_divides(&ea, &eb));
        assert_eq!(a.is_coprime(&b), ref_coprime(&ea, &eb));
        assert_eq!(a.cmp_with_order(&b, MonomialOrder::Lex), ref_cmp_lex(&ea, &eb));
        assert_eq!(
            a.cmp_with_order(&b, MonomialOrder::DegRevLex),
            ref_cmp_degrevlex(&ea, &eb)
        );
        // `a.div(&b)` is defined only when `b` divides `a`.
        if ref_divides(&eb, &ea) {
            assert_eq!(a.div(&b).to_dense(), ref_div(&ea, &eb));
        }
    }
}

#[test]
fn monomial_ops_dense() {
    check_monomial_ops::<Monomial>(1, 50_000);
}

#[test]
fn monomial_ops_sparse() {
    check_monomial_ops::<SparseMonomial>(1, 50_000);
}

/// Direct dense-vs-sparse agreement — the dense impl is the oracle.
#[test]
fn monomial_dense_vs_sparse_agree() {
    let mut rng = Rng::new(99);
    for _ in 0..50_000 {
        let ea = rand_exps(&mut rng);
        let eb = rand_exps(&mut rng);
        let da = Monomial::from_exponents(ea.clone());
        let db = Monomial::from_exponents(eb.clone());
        let sa = SparseMonomial::from_exponents(ea);
        let sb = SparseMonomial::from_exponents(eb);
        assert_eq!(
            MonomialRepr::mul(&da, &db).to_dense(),
            MonomialRepr::mul(&sa, &sb).to_dense()
        );
        assert_eq!(
            MonomialRepr::lcm(&da, &db).to_dense(),
            MonomialRepr::lcm(&sa, &sb).to_dense()
        );
        assert_eq!(
            MonomialRepr::gcd(&da, &db).to_dense(),
            MonomialRepr::gcd(&sa, &sb).to_dense()
        );
        assert_eq!(
            MonomialRepr::divides(&da, &db),
            MonomialRepr::divides(&sa, &sb)
        );
        assert_eq!(
            MonomialRepr::cmp_with_order(&da, &db, MonomialOrder::Lex),
            MonomialRepr::cmp_with_order(&sa, &sb, MonomialOrder::Lex)
        );
        assert_eq!(
            MonomialRepr::cmp_with_order(&da, &db, MonomialOrder::DegRevLex),
            MonomialRepr::cmp_with_order(&sa, &sb, MonomialOrder::DegRevLex)
        );
    }
}

/// DegRevLex must be an admissible monomial order: antisymmetric and
/// compatible with multiplication (`a < b ⟹ a·c < b·c`) — the
/// properties Buchberger's correctness relies on. Both reps must hold.
fn check_admissible<M: MonomialRepr>(seed: u64, iters: usize) {
    let mut rng = Rng::new(seed);
    let cmp = |x: &[u16], y: &[u16]| {
        M::from_exponents(x.to_vec())
            .cmp_with_order(&M::from_exponents(y.to_vec()), MonomialOrder::DegRevLex)
    };
    for _ in 0..iters {
        let a = rand_exps(&mut rng);
        let b = rand_exps(&mut rng);
        let c = rand_exps(&mut rng);
        assert_eq!(cmp(&a, &b), cmp(&b, &a).reverse());
        assert_eq!(cmp(&a, &a), Ordering::Equal);
        let ac = ref_mul(&a, &c);
        let bc = ref_mul(&b, &c);
        assert_eq!(cmp(&a, &b), cmp(&ac, &bc));
    }
}

#[test]
fn degrevlex_admissible_dense() {
    check_admissible::<Monomial>(7, 50_000);
}

#[test]
fn degrevlex_admissible_sparse() {
    check_admissible::<SparseMonomial>(7, 50_000);
}

// ── polynomial references over (exponent-vector → coeff) maps ────────
type PolyMap = BTreeMap<Vec<u16>, u64>;

fn rand_poly(rng: &mut Rng, r: &PolyRing, max_terms: usize) -> (Polynomial, PolyMap) {
    let n_terms = 1 + rng.below(max_terms as u64) as usize;
    let mut terms: Vec<(Monomial, _)> = Vec::new();
    let mut map: PolyMap = BTreeMap::new();
    for _ in 0..n_terms {
        let e = rand_exps(rng);
        let c = 1 + rng.below(PRIME - 1); // nonzero in [1, PRIME)
        terms.push((Monomial::from_exponents(e.clone()), r.field.from_u64(c)));
        let slot = map.entry(e).or_insert(0);
        *slot = (*slot + c) % PRIME;
    }
    map.retain(|_, c| *c != 0);
    (Polynomial::from_terms(terms, r), map)
}

fn poly_to_map(p: &Polynomial, r: &PolyRing) -> PolyMap {
    let mut m = PolyMap::new();
    for t in p.terms(r) {
        let c: BigUint = r.field.to_biguint(t.coefficient());
        let c = u64::try_from(c).expect("coeff fits u64 over GF(101)");
        if c != 0 {
            m.insert(t.exponents().to_vec(), c);
        }
    }
    m
}

fn map_add(a: &PolyMap, b: &PolyMap, neg_b: bool) -> PolyMap {
    let mut m = a.clone();
    for (e, &c) in b {
        let slot = m.entry(e.clone()).or_insert(0);
        *slot = if neg_b {
            (*slot + (PRIME - c % PRIME)) % PRIME
        } else {
            (*slot + c) % PRIME
        };
    }
    m.retain(|_, c| *c != 0);
    m
}

#[test]
fn poly_add_sub_mul_match_textbook() {
    let r = ring();
    let mut rng = Rng::new(13);
    for _ in 0..5_000 {
        let (pa, ma) = rand_poly(&mut rng, &r, 8);
        let (pb, mb) = rand_poly(&mut rng, &r, 8);

        assert_eq!(poly_to_map(&pa.add(&pb, &r), &r), map_add(&ma, &mb, false));
        assert_eq!(poly_to_map(&pa.sub(&pb, &r), &r), map_add(&ma, &mb, true));

        // schoolbook multiply reference
        let mut mm: PolyMap = BTreeMap::new();
        for (ea, &ca) in &ma {
            for (eb, &cb) in &mb {
                let e = ref_mul(ea, eb);
                let slot = mm.entry(e).or_insert(0);
                *slot = (*slot + ca * cb) % PRIME;
            }
        }
        mm.retain(|_, c| *c != 0);
        assert_eq!(poly_to_map(&pa.mul(&pb, &r), &r), mm);
    }
}

#[test]
fn poly_evaluate_matches_textbook() {
    let r = ring();
    let mut rng = Rng::new(29);
    for _ in 0..5_000 {
        let (p, m) = rand_poly(&mut rng, &r, 8);
        let vals: Vec<u64> = (0..N_VARS).map(|_| rng.below(PRIME)).collect();
        // reference: Σ c · Π vals[v]^e[v]  (mod PRIME)
        let mut acc = 0u64;
        for (e, &c) in &m {
            let mut term = c % PRIME;
            for (v, &exp) in e.iter().enumerate() {
                for _ in 0..exp {
                    term = (term * vals[v]) % PRIME;
                }
            }
            acc = (acc + term) % PRIME;
        }
        let val_els: Vec<_> = vals.iter().map(|&v| r.field.from_u64(v)).collect();
        let got: BigUint = r.field.to_biguint(&p.evaluate(&val_els, &r));
        assert_eq!(got, BigUint::from(acc));
    }
}

/// The geobucket reduction (production) must agree term-for-term with
/// the naive single-vector reduction (the in-tree reference impl) on
/// random subjects and divisor sets — the reduction oracle.
#[test]
fn reduce_geobucket_matches_naive_random() {
    let r = ring();
    let mut rng = Rng::new(31);
    for _ in 0..2_000 {
        let (subject, _) = rand_poly(&mut rng, &r, 10);
        let n_div = 1 + rng.below(3) as usize;
        let divisors: Vec<Polynomial> = (0..n_div)
            .map(|_| rand_poly(&mut rng, &r, 5).0)
            .filter(|d| !d.is_zero())
            .collect();
        if divisors.is_empty() {
            continue;
        }
        let refs: Vec<&Polynomial> = divisors.iter().collect();
        let geo = subject.reduce_by_refs_geobucket(&refs, &r, None, None);
        let naive = subject.reduce_by_refs_naive(&refs, &r);
        assert_eq!(poly_to_map(&geo, &r), poly_to_map(&naive, &r));
    }
}
