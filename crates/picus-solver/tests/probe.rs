//! Probe the 215s issue10937 case.

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::{ConstraintSystem, PolyTerm, encode};
use picus_solver::bitprop::BitProp;
use picus_solver::split_gb::{split_gb, admit};
use feanor_math::ring::RingStore;
use num_bigint::BigUint;
use num_traits::One;
use std::time::Instant;

fn vt(v: &str) -> PolyTerm { PolyTerm { coeff: BigUint::one(), vars: vec![v.into()] } }
fn svt(c: u64, v: &str) -> PolyTerm { PolyTerm { coeff: BigUint::from(c), vars: vec![v.into()] } }
fn pt(c: u64, vars: &[&str]) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(c), vars: vars.iter().map(|s| s.to_string()).collect() }
}

#[test]
#[ignore]
fn probe_issue10937() {
    let p = BigUint::from(7u32);
    let p_minus_1: BigUint = &p - BigUint::one();
    let mut system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![vt("mac1"), svt(6, "k1"), pt(6, &["d", "m1"])],
            vec![vt("mac2"), svt(6, "k2"), pt(6, &["d", "m2"])],
            vec![vt("dm"), pt(6, &["d", "m1"]), pt(6, &["d", "m2"])],
            vec![vt("s"), svt(6, "k1"), svt(6, "k2"), svt(6, "dm")],
        ],
        disequalities: vec![("mac_sum".into(), "s".into())],
        assignments: vec![],
        add_field_polys: false,
    };
    system.equalities.push(vec![vt("mac_sum"), svt(p_minus_1.to_u64_digits()[0], "mac1"), svt(p_minus_1.to_u64_digits()[0], "mac2")]);

    let t0 = Instant::now();
    let _f = picus_solver::field::FfField::new(&system.prime);
    println!("  field: {:?}", t0.elapsed());
    let t0a = Instant::now();
    let pr_test = picus_solver::poly::FfPolyRing::new(_f, vec!["a".into(); 11]);
    println!("  ring(11 vars): {:?}", t0a.elapsed());
    drop(pr_test);
    let t0 = Instant::now();
    let encoded = encode(&system).unwrap();
    println!("encode: {:?}, n_vars={}, n_polys={}", t0.elapsed(), encoded.poly_ring.n_vars, encoded.polynomials.len());
    println!("var names: {:?}", encoded.poly_ring.var_names);

    // Split GB phase
    let pr = &encoded.poly_ring;
    let nl_gens: Vec<_> = encoded.polynomials.iter().map(|p| pr.ring.clone_el(p)).collect();
    let mut l_gens: Vec<_> = Vec::new();
    for p in &encoded.polynomials {
        if admit(pr, 1, p) {
            l_gens.push(pr.ring.clone_el(p));
        }
    }
    println!("nl_gens: {}, l_gens: {}", nl_gens.len(), l_gens.len());

    let t1 = Instant::now();
    let mut bp = BitProp::new(pr);
    let basis = split_gb(pr, vec![l_gens, nl_gens], &mut bp);
    println!("split_gb: {:?}", t1.elapsed());
    for (i, b) in basis.iter().enumerate() {
        println!("  basis[{}]: {} polys, whole_ring={}, zero_dim={}", i, b.basis.len(), b.is_whole_ring(), b.is_zero_dim());
    }

    let t2 = Instant::now();
    let result = solve_encoded(&encoded);
    println!("full solve: {:?}", t2.elapsed());
    match result {
        SolveOutcome::Sat(_) => println!("SAT"),
        SolveOutcome::Unsat(_) => println!("UNSAT"),
        SolveOutcome::Unknown => println!("UNKNOWN"),
    }
}
