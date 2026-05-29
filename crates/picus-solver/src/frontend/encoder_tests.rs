//! Encoder canonical-form + bitsum-extraction tests.
use super::*;
use num_bigint::BigUint;

fn empty_builder(prime: u32) -> ConstraintSystemBuilder {
    ConstraintSystemBuilder::new(BigUint::from(prime))
}

fn idx_term(coeff: u64, vars: &[(VarIdx, u16)]) -> PolyTerm {
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: vars.to_vec(),
    }
}

// ── Polynomial canonical-form tests ─────────────────────────

/// `c1*x + c2*x` (within one equality) should encode to a single
/// `(c1+c2)*x` polynomial term.
#[test]
fn merge_repeated_monomial_within_equality() {
    // 2*x + 3*x = 0 over GF(101) → single term 5*x.
    let mut b = empty_builder(101);
    let x = b.var("x");
    b.add_equality(vec![idx_term(2, &[(x, 1)]), idx_term(3, &[(x, 1)])]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let p = &enc.polynomials[0];
    assert_eq!(p.num_terms(), 1);
}

/// `c1 + c2` constant terms should merge to one constant.
#[test]
fn merge_constant_terms_within_equality() {
    // 2 + 3 + 7 = 12 mod 11 = 1.
    let mut b = empty_builder(11);
    b.add_equality(vec![idx_term(2, &[]), idx_term(3, &[]), idx_term(7, &[])]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.polynomials.len(), 1);
    assert_eq!(enc.polynomials[0].num_terms(), 1);
}

/// `(2 + 3) + 4*x` → 2 terms (constant + linear).
#[test]
fn merge_constants_with_variable_term() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    b.add_equality(vec![
        idx_term(2, &[]),
        idx_term(3, &[]),
        idx_term(4, &[(x, 1)]),
    ]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let p = &enc.polynomials[0];
    assert_eq!(p.num_terms(), 2);
}

/// `c*x + (-c)*x` cancels; encoder drops the equality.
#[test]
fn merge_cancellation_drops_equality() {
    // 7*x + 94*x = 101*x = 0 mod 101.
    let mut b = empty_builder(101);
    let x = b.var("x");
    b.add_equality(vec![idx_term(7, &[(x, 1)]), idx_term(94, &[(x, 1)])]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert!(enc.polynomials.is_empty());
}

/// `c1*x*y + c2*y*x` (commutative same monomial) merges.
#[test]
fn merge_commutative_product() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![
        idx_term(2, &[(x, 1), (y, 1)]),
        idx_term(3, &[(x, 1), (y, 1)]),
    ]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.polynomials[0].num_terms(), 1);
}

// ── auto_extract_bitsums tests ────────────────────────────────────

/// Builds `k` bit constraints `b_i·(b_i − 1) = 0` plus one equality
/// `s − (b_0 + 2·b_1 + ... + 2^{k-1}·b_{k-1}) = 0` over GF(`prime`).
/// Returns the system plus the s/b0/.../b{k-1} indices.
fn bitdecomp_system(prime: u32, k: usize) -> (ConstraintSystem, VarIdx, Vec<VarIdx>) {
    let p = BigUint::from(prime);
    let pm1 = &p - BigUint::from(1u32);
    let mut b = empty_builder(prime);
    let s = b.var("s");
    let bs: Vec<VarIdx> = (0..k).map(|i| b.var(&format!("b{}", i))).collect();
    for &bi in &bs {
        b.add_equality(vec![
            idx_term(1, &[(bi, 2)]),
            PolyTerm {
                coeff: pm1.clone(),
                vars: vec![(bi, 1)],
            },
        ]);
    }
    let mut terms = vec![idx_term(1, &[(s, 1)])];
    let mut coeff = BigUint::from(1u32);
    let two = BigUint::from(2u32);
    for &bi in &bs {
        terms.push(PolyTerm {
            coeff: &p - &coeff,
            vars: vec![(bi, 1)],
        });
        coeff = (&coeff * &two) % &p;
    }
    b.add_equality(terms);
    (b.build(), s, bs)
}

#[test]
fn auto_bitsum_extracts_simple_chain() {
    let (sys, _s, bs) = bitdecomp_system(101, 3);
    let n_eq_before = sys.equalities.len();
    let rewritten = auto_extract_bitsums(&sys);
    assert_eq!(rewritten.bitsums.len(), 1);
    assert_eq!(rewritten.bitsums[0], bs);
    assert_eq!(rewritten.equalities.len(), n_eq_before);
}

#[test]
fn auto_bitsum_skips_when_no_bit_constraints() {
    let mut b = empty_builder(101);
    let s = b.var("s");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    b.add_equality(vec![
        idx_term(1, &[(s, 1)]),
        idx_term(100, &[(b0, 1)]),
        idx_term(99, &[(b1, 1)]),
        idx_term(97, &[(b2, 1)]),
    ]);
    let sys = b.build();
    let rewritten = auto_extract_bitsums(&sys);
    assert!(rewritten.bitsums.is_empty());
    assert_eq!(rewritten.equalities[0].len(), 4);
}

/// Chain length 1 is below `MIN_AUTO_BITSUM_LEN`.
#[test]
fn auto_bitsum_skips_single_bit() {
    let (sys, _s, _bs) = bitdecomp_system(101, 1);
    let rewritten = auto_extract_bitsums(&sys);
    assert!(rewritten.bitsums.is_empty());
}

/// User-provided `bitsums` entries retain their indices; auto-detected
/// entries are appended.
#[test]
fn auto_bitsum_preserves_user_provided() {
    let (mut sys, _s, bs) = bitdecomp_system(101, 3);
    sys.bitsums.push(vec![bs[0], bs[1]]);
    let rewritten = auto_extract_bitsums(&sys);
    assert_eq!(rewritten.bitsums[0], vec![bs[0], bs[1]]);
    assert!(rewritten.bitsums.len() >= 2);
}

/// Auto-extract round-trip preserves SAT semantics on a small
/// bit-decomposition system over GF(11): with target=5 and
/// 3 bits, the unique solution is b0=1, b1=0, b2=1.
#[test]
fn auto_bitsum_solve_extracts_unique_decomp_gf11() {
    use crate::core::{SolveOutcome, solve_encoded};
    let prime: u32 = 11;
    let p = BigUint::from(prime);
    let pm1 = &p - BigUint::from(1u32);
    let target: u32 = 5;
    let mut b = empty_builder(prime);
    let bs: Vec<VarIdx> = (0..3).map(|i| b.var(&format!("b{}", i))).collect();
    for &bi in &bs {
        b.add_equality(vec![
            idx_term(1, &[(bi, 2)]),
            PolyTerm {
                coeff: pm1.clone(),
                vars: vec![(bi, 1)],
            },
        ]);
    }
    let mut sum = vec![];
    let mut c = BigUint::from(1u32);
    let two = BigUint::from(2u32);
    for &bi in &bs {
        sum.push(PolyTerm {
            coeff: c.clone(),
            vars: vec![(bi, 1)],
        });
        c = (&c * &two) % &p;
    }
    sum.push(PolyTerm {
        coeff: &p - BigUint::from(target),
        vars: vec![],
    });
    b.add_equality(sum);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    match solve_encoded(&enc) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)));
            assert_eq!(m.get("b1"), Some(&BigUint::from(0u32)));
            assert_eq!(m.get("b2"), Some(&BigUint::from(1u32)));
        }
        other => panic!("expected Sat with unique decomp, got {:?}", other),
    }
}

// ── encode smoke tests ─────────────────────────────────

#[test]
fn encode_basic_equality_count() {
    // x + y - 1 = 0 over GF(101).
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![
        idx_term(1, &[(x, 1)]),
        idx_term(1, &[(y, 1)]),
        idx_term(100, &[]),
    ]);
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.polynomials.len(), 1);
}

/// Disequalities produce a Rabinowitsch polynomial; aux
/// witness var is appended to var_map.
#[test]
fn encode_disequality_adds_witness() {
    let mut b = empty_builder(7);
    let x = b.var("x");
    let y = b.var("y");
    b.add_disequality(x, y);
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.polynomials.len(), 1, "one Rabinowitsch poly");
    assert!(enc.var_map.contains_key("__w_diseq_0"));
    assert_eq!(enc.poly_ring.n_vars(), 3); // x, y, __w_diseq_0
}

/// Bitsum routes into the separate bitsum_polys list.
#[test]
fn encode_bitsum_routing() {
    let mut b = empty_builder(13);
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    b.add_bitsum(vec![b0, b1, b2]);
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.polynomials.len(), 0);
    assert_eq!(enc.bitsum_polys.len(), 1);
    assert!(enc.var_map.contains_key("__bitsum_0"));
}

/// End-to-end with both a disequality (n_diseq > 0) and an
/// auto-extracted bitsum. The `__bitsum_N` aux variables are appended
/// after the Rabinowitsch witnesses, so the extractor's predicted aux
/// index and the encoder's allocated slot must agree on the `+ n_diseq`
/// offset for the decomposition to solve. The diseq-only and bitsum-only
/// tests never exercise that offset.
#[test]
fn encode_bitsum_with_diseq_solves_unique_decomp() {
    use crate::core::{solve_encoded, SolveOutcome};
    let prime: u32 = 11;
    let p = BigUint::from(prime);
    let pm1 = &p - BigUint::from(1u32);
    let target: u32 = 5; // 101b -> b0=1, b1=0, b2=1
    let mut b = empty_builder(prime);
    let bs: Vec<VarIdx> = (0..3).map(|i| b.var(&format!("b{}", i))).collect();
    for &bi in &bs {
        b.add_equality(vec![
            idx_term(1, &[(bi, 2)]),
            PolyTerm { coeff: pm1.clone(), vars: vec![(bi, 1)] },
        ]);
    }
    let mut sum = Vec::new();
    let mut c = BigUint::from(1u32);
    let two = BigUint::from(2u32);
    for &bi in &bs {
        sum.push(PolyTerm { coeff: c.clone(), vars: vec![(bi, 1)] });
        c = (&c * &two) % &p;
    }
    sum.push(PolyTerm { coeff: &p - BigUint::from(target), vars: vec![] });
    b.add_equality(sum);
    // n_diseq = 1: the unique decomposition has b0=1, b1=0, so b0 != b1
    // holds — the disequality is satisfiable and does not change the model.
    b.add_disequality(bs[0], bs[1]);
    let sys = b.build();

    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.bitsum_polys.len(), 1, "one auto-extracted bitsum");
    // Bitsum aux follows the single Rabinowitsch witness (the +n_diseq offset).
    assert_eq!(
        enc.var_map["__bitsum_0"],
        enc.var_map["__w_diseq_0"] + 1,
        "bitsum aux must be placed after the diseq witness"
    );
    match solve_encoded(&enc) {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b0"), Some(&BigUint::from(1u32)));
            assert_eq!(m.get("b1"), Some(&BigUint::from(0u32)));
            assert_eq!(m.get("b2"), Some(&BigUint::from(1u32)));
        }
        other => panic!("expected unique decomp Sat, got {:?}", other),
    }
}

/// Same variable referenced twice in a builder collapses to one
/// VarIdx; the encoded ring has only one variable.
#[test]
fn builder_var_dedupes() {
    let mut b = empty_builder(7);
    let x1 = b.var("x");
    let x2 = b.var("x");
    assert_eq!(x1, x2);
    assert_eq!(b.n_vars(), 1);
}

/// Soundness gate fires: 3 bits at p=13, `2^3 = 8 < 13` so the
/// chain extracts. Verified by non-empty `bitsum_polys`.
#[test]
fn auto_extract_indexed_sound_chain() {
    let p = BigUint::from(13u32);
    let mut b = ConstraintSystemBuilder::new(p.clone());
    let target = b.var("target");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    b.add_equality(vec![
        idx_term(1, &[(target, 1)]),
        idx_term(12, &[(b0, 1)]),
        idx_term(11, &[(b1, 1)]),
        idx_term(9, &[(b2, 1)]),
    ]);
    for bit in [b0, b1, b2] {
        b.add_equality(vec![idx_term(1, &[(bit, 2)]), idx_term(12, &[(bit, 1)])]);
    }
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert!(
        !enc.bitsum_polys.is_empty(),
        "sound chain must extract a bitsum"
    );
}

/// Soundness gate caps chain length: with 4 bits at p=11,
/// `2^4 > 11` forbids the full chain. The shorter (length-3)
/// prefix still extracts since `2^3 ≤ 11`.
#[test]
fn auto_extract_indexed_caps_chain_at_soundness_limit() {
    let p = BigUint::from(11u32);
    let mut b = ConstraintSystemBuilder::new(p.clone());
    let target = b.var("target");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    let b3 = b.var("b3");
    b.add_equality(vec![
        idx_term(1, &[(target, 1)]),
        idx_term(10, &[(b0, 1)]),
        idx_term(9, &[(b1, 1)]),
        idx_term(7, &[(b2, 1)]),
        idx_term(3, &[(b3, 1)]),
    ]);
    for bit in [b0, b1, b2, b3] {
        b.add_equality(vec![idx_term(1, &[(bit, 2)]), idx_term(10, &[(bit, 1)])]);
    }
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert!(
        !enc.bitsum_polys.is_empty(),
        "length-3 prefix must still extract under 2^n ≤ p cap"
    );
}
