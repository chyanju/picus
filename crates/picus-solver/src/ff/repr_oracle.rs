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
use super::polynomial::{PolyRing, DensePoly};
use super::repr::{MonomialRepr, PolyRepr};
use super::sparse_monomial::SparseMonomial;
use super::sparse_polynomial::SparsePolynomial;

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

/// Random terms shared by both representations, so dense and sparse are
/// built from identical input and can be compared directly.
fn rand_terms(rng: &mut Rng, max_terms: usize) -> Vec<(Vec<u16>, u64)> {
    let n = 1 + rng.below(max_terms as u64) as usize;
    (0..n).map(|_| (rand_exps(rng), 1 + rng.below(PRIME - 1))).collect()
}

fn build_dense(terms: &[(Vec<u16>, u64)], r: &PolyRing) -> DensePoly {
    let ts = terms
        .iter()
        .map(|(e, c)| (Monomial::from_exponents(e.clone()), r.field.from_u64(*c)))
        .collect();
    DensePoly::from_terms(ts, r)
}

fn build_sparse(terms: &[(Vec<u16>, u64)], r: &PolyRing) -> SparsePolynomial {
    let ts = terms
        .iter()
        .map(|(e, c)| (SparseMonomial::from_exponents(e.clone()), r.field.from_u64(*c)))
        .collect();
    SparsePolynomial::from_terms(ts, r)
}

/// Reference coefficient map: fold the raw terms (sum duplicates, drop
/// zeros) mod PRIME.
fn terms_ref_map(terms: &[(Vec<u16>, u64)]) -> PolyMap {
    let mut m = PolyMap::new();
    for (e, c) in terms {
        let slot = m.entry(e.clone()).or_insert(0);
        *slot = (*slot + c) % PRIME;
    }
    m.retain(|_, c| *c != 0);
    m
}

fn dense_to_map(p: &DensePoly, r: &PolyRing) -> PolyMap {
    let mut m = PolyMap::new();
    for t in p.terms(r) {
        let c = u64::try_from(r.field.to_biguint(t.coefficient())).unwrap();
        if c != 0 {
            m.insert(t.exponents().to_vec(), c);
        }
    }
    m
}

fn sparse_to_map(p: &SparsePolynomial, r: &PolyRing) -> PolyMap {
    let mut m = PolyMap::new();
    for (mono, c) in p.iter_terms() {
        let c = u64::try_from(r.field.to_biguint(c)).unwrap();
        if c != 0 {
            m.insert(mono.to_dense(), c);
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
fn poly_add_sub_mul_both_reps() {
    let r = ring();
    let mut rng = Rng::new(13);
    for _ in 0..5_000 {
        let ta = rand_terms(&mut rng, 8);
        let tb = rand_terms(&mut rng, 8);
        let (da, db) = (build_dense(&ta, &r), build_dense(&tb, &r));
        let (sa, sb) = (build_sparse(&ta, &r), build_sparse(&tb, &r));
        let (ma, mb) = (terms_ref_map(&ta), terms_ref_map(&tb));

        let add_ref = map_add(&ma, &mb, false);
        let sub_ref = map_add(&ma, &mb, true);
        let mul_ref = {
            let mut mm = PolyMap::new();
            for (ea, &ca) in &ma {
                for (eb, &cb) in &mb {
                    let slot = mm.entry(ref_mul(ea, eb)).or_insert(0);
                    *slot = (*slot + ca * cb) % PRIME;
                }
            }
            mm.retain(|_, c| *c != 0);
            mm
        };

        assert_eq!(dense_to_map(&da.add(&db, &r), &r), add_ref);
        assert_eq!(sparse_to_map(&sa.add(&sb, &r), &r), add_ref);
        assert_eq!(dense_to_map(&da.sub(&db, &r), &r), sub_ref);
        assert_eq!(sparse_to_map(&sa.sub(&sb, &r), &r), sub_ref);
        assert_eq!(dense_to_map(&da.mul(&db, &r), &r), mul_ref);
        assert_eq!(sparse_to_map(&sa.mul(&sb, &r), &r), mul_ref);
    }
}

#[test]
fn poly_evaluate_both_reps() {
    let r = ring();
    let mut rng = Rng::new(29);
    for _ in 0..5_000 {
        let t = rand_terms(&mut rng, 8);
        let m = terms_ref_map(&t);
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
        let dense_got =
            u64::try_from(r.field.to_biguint(&build_dense(&t, &r).evaluate(&val_els, &r))).unwrap();
        let sparse_got =
            u64::try_from(r.field.to_biguint(&build_sparse(&t, &r).evaluate(&val_els, &r))).unwrap();
        assert_eq!(dense_got, acc);
        assert_eq!(sparse_got, acc);
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
        let subject = build_dense(&rand_terms(&mut rng, 10), &r);
        let n_div = 1 + rng.below(3) as usize;
        let divisors: Vec<DensePoly> = (0..n_div)
            .map(|_| build_dense(&rand_terms(&mut rng, 5), &r))
            .filter(|d| !d.is_zero())
            .collect();
        if divisors.is_empty() {
            continue;
        }
        let refs: Vec<&DensePoly> = divisors.iter().collect();
        let geo = subject.reduce_by_refs_geobucket(&refs, &r, None, None, None);
        let naive = subject.reduce_by_refs_naive(&refs, &r);
        assert_eq!(dense_to_map(&geo, &r), dense_to_map(&naive, &r));
    }
}

/// Sparse multivariate reduction (`SparsePolynomial::reduce_by_refs`)
/// must produce the same normal form as the dense naive reduction (the
/// reference) on random subjects and divisor sets, using the SAME
/// divisor order — the sparse reduction oracle. (Reduction is
/// order-dependent, so the same order is required for term-for-term
/// agreement.)
#[test]
fn sparse_reduce_matches_dense_naive_random() {
    let r = ring();
    let mut rng = Rng::new(57);
    for _ in 0..2_000 {
        let subj_terms = rand_terms(&mut rng, 10);
        let n_div = 1 + rng.below(3) as usize;
        let div_terms: Vec<Vec<(Vec<u16>, u64)>> =
            (0..n_div).map(|_| rand_terms(&mut rng, 5)).collect();

        // Dense reference (filter zero divisors, preserve order).
        let subject_d = build_dense(&subj_terms, &r);
        let divisors_d: Vec<DensePoly> = div_terms
            .iter()
            .map(|t| build_dense(t, &r))
            .filter(|d| !d.is_zero())
            .collect();
        if divisors_d.is_empty() {
            continue;
        }
        let refs_d: Vec<&DensePoly> = divisors_d.iter().collect();
        let dense_nf = subject_d.reduce_by_refs_naive(&refs_d, &r);

        // Sparse: same term lists, same filter, same order.
        let subject_s = build_sparse(&subj_terms, &r);
        let divisors_s: Vec<SparsePolynomial> = div_terms
            .iter()
            .map(|t| build_sparse(t, &r))
            .filter(|d| !d.is_zero())
            .collect();
        let refs_s: Vec<&SparsePolynomial> = divisors_s.iter().collect();
        let sparse_nf = subject_s.reduce_by_refs(&refs_s, &r);

        assert_eq!(dense_to_map(&dense_nf, &r), sparse_to_map(&sparse_nf, &r));
    }
}

/// The sparse Gröbner basis (`sparse_gb::groebner_basis` + `interreduce`)
/// must equal the dense engine's reduced Gröbner basis on random
/// generator sets. The reduced GB under a fixed order is unique, so the
/// two representations must agree exactly (compared as monic,
/// canonically-sorted term maps). The sparse engine's product / M / B
/// criteria and sugar selection change only which S-pairs are processed,
/// never the final ideal, so this agreement holds regardless.
#[test]
fn sparse_groebner_basis_matches_dense_random() {
    use super::buchberger::{groebner_basis, interreduce, BuchbergerConfig};
    const GV: usize = 4;
    const GMAX: u64 = 2;
    let arc_r = PolyRing::new(
        PrimeField::new(BigUint::from(PRIME)),
        (0..GV).map(|i| format!("v{i}")).collect(),
        MonomialOrder::DegRevLex,
    );
    let r: &PolyRing = &arc_r;
    let mut rng = Rng::new(91);

    for _ in 0..300 {
        let n_gen = 2 + rng.below(3) as usize; // 2–4 generators
        let gen_terms: Vec<Vec<(Vec<u16>, u64)>> = (0..n_gen)
            .map(|_| {
                let n = 1 + rng.below(3) as usize;
                (0..n)
                    .map(|_| {
                        let e: Vec<u16> = (0..GV).map(|_| rng.below(GMAX + 1) as u16).collect();
                        (e, 1 + rng.below(PRIME - 1))
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        // Dense reduced GB.
        let gens_d: Vec<DensePoly> = gen_terms
            .iter()
            .map(|t| build_dense(t, r))
            .filter(|p| !p.is_zero())
            .collect();
        if gens_d.is_empty() {
            continue;
        }
        let gb_d = groebner_basis(gens_d, &arc_r, &BuchbergerConfig::default()).expect("dense gb");
        let red_d = interreduce(gb_d.basis, &arc_r);
        let mut canon_d: Vec<PolyMap> = red_d.iter().map(|p| dense_to_map(p, r)).collect();
        canon_d.sort();

        // Sparse reduced GB from the same generators.
        let gens_s: Vec<SparsePolynomial> = gen_terms
            .iter()
            .map(|t| build_sparse(t, r))
            .filter(|p| !p.is_zero())
            .collect();
        let gb_s = super::sparse_gb::groebner_basis(gens_s, r, None);
        let red_s = super::sparse_gb::interreduce(gb_s, r, None);
        let mut canon_s: Vec<PolyMap> = red_s.iter().map(|p| sparse_to_map(p, r)).collect();
        canon_s.sort();

        assert_eq!(canon_d, canon_s, "reduced GB mismatch for generators {:?}", gen_terms);
    }
}

/// Incremental sparse GB (seed the reduced GB of A, extend with B) must
/// equal the from-scratch reduced GB of A ∪ B — the incremental-seeding
/// soundness oracle. Both are GBs of the same ideal, and the reduced GB
/// under a fixed order is unique.
#[test]
fn sparse_groebner_incremental_matches_from_scratch_random() {
    const GV: usize = 4;
    const GMAX: u64 = 2;
    let arc_r = PolyRing::new(
        PrimeField::new(BigUint::from(PRIME)),
        (0..GV).map(|i| format!("v{i}")).collect(),
        MonomialOrder::DegRevLex,
    );
    let r: &PolyRing = &arc_r;
    let mut rng = Rng::new(73);

    let mut rand_gens = |rng: &mut Rng| -> Vec<SparsePolynomial> {
        let count = 1 + rng.below(2) as usize;
        (0..count)
            .map(|_| {
                let n = 1 + rng.below(3) as usize;
                let terms: Vec<(Vec<u16>, u64)> = (0..n)
                    .map(|_| {
                        let e: Vec<u16> = (0..GV).map(|_| rng.below(GMAX + 1) as u16).collect();
                        (e, 1 + rng.below(PRIME - 1))
                    })
                    .collect();
                build_sparse(&terms, r)
            })
            .filter(|p| !p.is_zero())
            .collect()
    };

    for _ in 0..300 {
        let gens_a = rand_gens(&mut rng);
        let gens_b = rand_gens(&mut rng);
        if gens_a.is_empty() {
            continue;
        }

        // From scratch: reduced GB of A ∪ B.
        let mut all = gens_a.clone();
        all.extend(gens_b.clone());
        let gb_full = super::sparse_gb::groebner_basis(all, r, None);
        let red_full = super::sparse_gb::interreduce(gb_full, r, None);
        let mut canon_full: Vec<PolyMap> = red_full.iter().map(|p| sparse_to_map(p, r)).collect();
        canon_full.sort();

        // Incremental: reduced GB of A, then seeded extension with B.
        let gb_a = super::sparse_gb::groebner_basis(gens_a, r, None);
        let known = super::sparse_gb::interreduce(gb_a, r, None);
        let gb_inc = super::sparse_gb::groebner_basis_incremental(known, gens_b, r, None);
        let red_inc = super::sparse_gb::interreduce(gb_inc, r, None);
        let mut canon_inc: Vec<PolyMap> = red_inc.iter().map(|p| sparse_to_map(p, r)).collect();
        canon_inc.sort();

        assert_eq!(canon_full, canon_inc, "incremental vs from-scratch GB mismatch");
    }
}

/// The sparse geobucket reduction (`reduce_by_refs`, production) must
/// produce the same normal form as the sparse naive reduction
/// (`reduce_by_refs_naive`, reference) on random subjects and divisor
/// sets, using the same divisor order — the sparse reduction oracle.
#[test]
fn sparse_reduce_geobucket_matches_naive_random() {
    let r = ring();
    let mut rng = Rng::new(58);
    for _ in 0..2_000 {
        let subject = build_sparse(&rand_terms(&mut rng, 10), &r);
        let n_div = 1 + rng.below(3) as usize;
        let divisors: Vec<SparsePolynomial> = (0..n_div)
            .map(|_| build_sparse(&rand_terms(&mut rng, 5), &r))
            .filter(|d| !d.is_zero())
            .collect();
        if divisors.is_empty() {
            continue;
        }
        let refs: Vec<&SparsePolynomial> = divisors.iter().collect();
        let geo = subject.reduce_by_refs(&refs, &r);
        let naive = subject.reduce_by_refs_naive(&refs, &r);
        assert_eq!(sparse_to_map(&geo, &r), sparse_to_map(&naive, &r));
    }
}

/// `DensePoly`↔`SparsePolynomial` conversions (the boundary the native
/// GB dispatch uses) must be exact: a polynomial built directly in each
/// representation equals the one converted from the other.
#[test]
fn dense_sparse_roundtrip_random() {
    let r = ring();
    let mut rng = Rng::new(123);
    for _ in 0..2_000 {
        let terms = rand_terms(&mut rng, 10);
        let d = build_dense(&terms, &r);
        let s = build_sparse(&terms, &r);
        assert_eq!(
            sparse_to_map(&SparsePolynomial::from_dense(&d, &r), &r),
            sparse_to_map(&s, &r)
        );
        assert_eq!(dense_to_map(&s.to_dense(&r), &r), dense_to_map(&d, &r));
    }
}

/// Exercise the `PolyRepr` trait generically: build via the trait,
/// run add/mul through it, and check `collect_terms_idx` against the
/// coefficient-map reference — for both representations.
fn idx_to_map(terms: &[(BigUint, Vec<(usize, u16)>)]) -> PolyMap {
    let mut m = PolyMap::new();
    for (c, vars) in terms {
        let cc = u64::try_from(c.clone()).unwrap();
        if cc == 0 {
            continue;
        }
        let mut e = vec![0u16; N_VARS];
        for &(v, ex) in vars {
            e[v] = ex;
        }
        m.insert(e, cc);
    }
    m
}

fn check_polyrepr<P: PolyRepr>(seed: u64, iters: usize) {
    let r = ring();
    let mut rng = Rng::new(seed);
    for _ in 0..iters {
        let ta = rand_terms(&mut rng, 8);
        let tb = rand_terms(&mut rng, 8);
        let build = |t: &[(Vec<u16>, u64)]| {
            P::from_terms(
                t.iter()
                    .map(|(e, c)| (P::Mono::from_exponents(e.clone()), r.field.from_u64(*c)))
                    .collect(),
                &r,
            )
        };
        let (pa, pb) = (build(&ta), build(&tb));
        let (ma, mb) = (terms_ref_map(&ta), terms_ref_map(&tb));

        assert_eq!(idx_to_map(&pa.collect_terms_idx(&r)), ma);
        assert_eq!(idx_to_map(&pa.add(&pb, &r).collect_terms_idx(&r)), map_add(&ma, &mb, false));
        assert_eq!(idx_to_map(&pa.sub(&pb, &r).collect_terms_idx(&r)), map_add(&ma, &mb, true));

        let mut mul_ref = PolyMap::new();
        for (ea, &ca) in &ma {
            for (eb, &cb) in &mb {
                let slot = mul_ref.entry(ref_mul(ea, eb)).or_insert(0);
                *slot = (*slot + ca * cb) % PRIME;
            }
        }
        mul_ref.retain(|_, c| *c != 0);
        assert_eq!(idx_to_map(&pa.mul(&pb, &r).collect_terms_idx(&r)), mul_ref);
    }
}

#[test]
fn polyrepr_trait_dense() {
    check_polyrepr::<DensePoly>(41, 2_000);
}

#[test]
fn polyrepr_trait_sparse() {
    check_polyrepr::<SparsePolynomial>(41, 2_000);
}
