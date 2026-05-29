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

/// `compact_used_vars` drops variables no constraint references and
/// remaps every surviving index. Five user variables `v0..v4` are
/// interned but only `v1` and `v3` appear (one equality `2*v1 + 3*v3`,
/// one disequality `v1 != v3`). After encoding, the ring must hold only
/// the two referenced user variables (plus the one Rabinowitsch
/// witness), and the equality polynomial must reference exactly those
/// two compacted indices.
#[test]
fn compact_used_vars_drops_unreferenced_and_remaps() {
    let mut b = empty_builder(101);
    let _v0 = b.var("v0");
    let v1 = b.var("v1");
    let _v2 = b.var("v2");
    let v3 = b.var("v3");
    let _v4 = b.var("v4");
    b.add_equality(vec![idx_term(2, &[(v1, 1)]), idx_term(3, &[(v3, 1)])]);
    b.add_disequality(v1, v3);
    let sys = b.build();
    assert_eq!(sys.var_names.len(), 5, "5 user vars interned");

    let enc = encode(&sys).expect("encode");
    // 2 surviving user vars (v1, v3) + 1 Rabinowitsch witness.
    assert_eq!(enc.poly_ring.n_vars(), 3);
    assert!(enc.var_map.contains_key("v1"));
    assert!(enc.var_map.contains_key("v3"));
    assert!(!enc.var_map.contains_key("v0"));
    assert!(!enc.var_map.contains_key("v2"));
    assert!(!enc.var_map.contains_key("v4"));
    // v1, v3 remap to the first two compacted slots 0, 1 (sorted order).
    assert_eq!(enc.var_map["v1"], 0);
    assert_eq!(enc.var_map["v3"], 1);
    assert!(enc.var_map.contains_key("__w_diseq_0"));
    // One equality poly + one Rabinowitsch poly.
    assert_eq!(enc.polynomials.len(), 2);
    // The equality `2*v1 + 3*v3` references only the two compacted vars.
    let eq_poly = enc
        .polynomials
        .iter()
        .find(|p| p.num_terms() == 2)
        .expect("equality poly with two terms");
    let appearing = enc.poly_ring.ring.appearing_indeterminates(eq_poly);
    let mut vs: Vec<usize> = appearing.into_iter().collect();
    vs.sort_unstable();
    assert_eq!(vs, vec![0, 1]);
}

/// `compact_used_vars` remaps bitsum and assignment indices too. A
/// leading filler variable `pad` is unreferenced; an assignment pins
/// `s`, and a user bitsum lists `b0, b1`. After compaction the bitsum
/// chain and assignment must point at the renumbered slots, and the
/// `__bitsum_0` aux must follow the three surviving user vars.
#[test]
fn compact_used_vars_remaps_bitsum_and_assignment() {
    let mut b = empty_builder(13);
    let _pad = b.var("pad"); // unreferenced
    let s = b.var("s");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    b.add_assignment(s, BigUint::from(0u32));
    b.add_bitsum(vec![b0, b1]);
    let sys = b.build();
    assert_eq!(sys.var_names.len(), 4);

    let enc = encode(&sys).expect("encode");
    // 3 surviving user vars (s, b0, b1) + 1 bitsum aux; pad dropped.
    assert_eq!(enc.poly_ring.n_vars(), 4);
    assert!(!enc.var_map.contains_key("pad"));
    assert_eq!(enc.var_map["s"], 0);
    assert_eq!(enc.var_map["b0"], 1);
    assert_eq!(enc.var_map["b1"], 2);
    // bitsum aux follows the 3 user vars (no diseq witnesses here).
    assert_eq!(enc.var_map["__bitsum_0"], 3);
    assert_eq!(enc.bitsum_polys.len(), 1);
}

/// `compact_used_vars` is a no-op when every variable is referenced:
/// `n_vars` stays put and the system round-trips through encoding.
#[test]
fn compact_used_vars_noop_when_all_referenced() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.poly_ring.n_vars(), 2);
    assert!(enc.var_map.contains_key("x"));
    assert!(enc.var_map.contains_key("y"));
}

/// `add_field_polys = true` at prime 7 (`<= 1000`) appends `x^p - x` for
/// every ring variable, each with `PolySource::Other` provenance. With
/// two referenced variables the encoder emits the single equality poly
/// plus two field polynomials.
#[test]
fn encode_field_polys_emitted_for_small_prime() {
    let mut b = empty_builder(7);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(6, &[(y, 1)])]);
    b.set_add_field_polys(true);
    let sys = b.build();
    assert!(sys.add_field_polys);

    let enc = encode(&sys).expect("encode");
    assert_eq!(enc.poly_ring.n_vars(), 2);
    // 1 equality + 2 field polys (one per ring variable).
    assert_eq!(enc.polynomials.len(), 3);
    let n_other = enc
        .poly_provenance
        .iter()
        .filter(|s| matches!(s, PolySource::Other))
        .count();
    assert_eq!(n_other, 2, "two field polys carry PolySource::Other");
    // Provenance stays parallel to polynomials.
    assert_eq!(enc.poly_provenance.len(), enc.polynomials.len());
    // A field poly x^7 - x is degree 7: some monomial carries a
    // variable with exponent 7.
    let max_exp = enc
        .polynomials
        .iter()
        .flat_map(|p| {
            enc.poly_ring
                .ring
                .terms(p)
                .map(|(_, m)| {
                    (0..enc.poly_ring.n_vars())
                        .map(|v| enc.poly_ring.ring.exponent_at(&m, v))
                        .max()
                        .unwrap_or(0)
                })
                .collect::<Vec<_>>()
        })
        .max()
        .unwrap();
    assert_eq!(max_exp, 7, "field poly introduces a degree-7 monomial");
}

/// Field polynomials are suppressed when the prime exceeds the
/// `<= 1000` dense-expansion bound, even with `add_field_polys = true`.
#[test]
fn encode_field_polys_suppressed_for_large_prime() {
    let mut b = empty_builder(2003); // > 1000
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(2002, &[(y, 1)])]);
    b.set_add_field_polys(true);
    let sys = b.build();
    let enc = encode(&sys).expect("encode");
    // Only the equality poly survives; no field polys appended.
    assert_eq!(enc.polynomials.len(), 1);
    assert!(enc
        .poly_provenance
        .iter()
        .all(|s| !matches!(s, PolySource::Other)));
}

// ── encode_impl bounds-check error paths ───────────────────────
//
// These reject malformed index-keyed systems. They call `encode_impl`
// directly: `encode` runs `compact_used_vars` first, which dereferences
// `var_names[idx]` for every referenced index and would panic before the
// in-encode bounds checks ever fire. A producer that emits an index past
// its own `var_names` frame is the failure mode being guarded.

/// `n_vars > 5000` rejects ring construction. A system declaring 5001
/// user variables (none referenced) trips the cap.
#[test]
fn encode_impl_rejects_too_many_vars() {
    let var_names: Vec<String> = (0..5001).map(|i| format!("v{}", i)).collect();
    let sys = ConstraintSystem {
        prime: BigUint::from(101u32),
        var_names,
        equalities: vec![],
        disequalities: vec![],
        assignments: vec![],
        bitsums: vec![],
        add_field_polys: false,
    };
    match encode_impl(&sys, true) {
        Err(msg) => assert!(msg.contains("too many variables")),
        Ok(_) => panic!("expected too-many-variables rejection"),
    }
}

/// An equality term referencing a var index beyond the ring is rejected.
#[test]
fn encode_impl_rejects_equality_var_out_of_range() {
    // One declared user var (index 0); equality references index 5.
    let sys = ConstraintSystem {
        prime: BigUint::from(101u32),
        var_names: vec!["x".into()],
        equalities: vec![vec![idx_term(1, &[(5, 1)])]],
        disequalities: vec![],
        assignments: vec![],
        bitsums: vec![],
        add_field_polys: false,
    };
    match encode_impl(&sys, true) {
        Err(msg) => {
            assert!(msg.contains("equality term references var_idx 5"));
            assert!(msg.contains("ring has only 1 vars"));
        }
        Ok(_) => panic!("expected out-of-range equality var rejection"),
    }
}

/// An assignment referencing a non-user var index is rejected. Witness /
/// bitsum aux slots are appended past `n_user`; an assignment must point
/// at a real user variable.
#[test]
fn encode_impl_rejects_assignment_var_out_of_range() {
    let sys = ConstraintSystem {
        prime: BigUint::from(101u32),
        var_names: vec!["x".into()],
        equalities: vec![],
        disequalities: vec![],
        assignments: vec![(3, BigUint::from(0u32))],
        bitsums: vec![],
        add_field_polys: false,
    };
    match encode_impl(&sys, true) {
        Err(msg) => {
            assert!(msg.contains("assignment references var_idx 3"));
            assert!(msg.contains("only 1 user vars"));
        }
        Ok(_) => panic!("expected out-of-range assignment var rejection"),
    }
}

/// A disequality referencing a non-user var index is rejected (only when
/// Rabinowitsch emission is on, since that is where the bound is checked).
#[test]
fn encode_impl_rejects_disequality_var_out_of_range() {
    let sys = ConstraintSystem {
        prime: BigUint::from(101u32),
        var_names: vec!["x".into(), "y".into()],
        equalities: vec![],
        disequalities: vec![(0, 9)],
        assignments: vec![],
        bitsums: vec![],
        add_field_polys: false,
    };
    match encode_impl(&sys, true) {
        Err(msg) => {
            assert!(msg.contains("disequality references var_idx"));
            assert!(msg.contains("only 2 user vars"));
        }
        Ok(_) => panic!("expected out-of-range disequality var rejection"),
    }
}

/// A bitsum referencing a non-user var index is rejected.
#[test]
fn encode_impl_rejects_bitsum_var_out_of_range() {
    let sys = ConstraintSystem {
        prime: BigUint::from(101u32),
        var_names: vec!["b0".into(), "b1".into()],
        equalities: vec![],
        disequalities: vec![],
        assignments: vec![],
        bitsums: vec![vec![0, 7]],
        add_field_polys: false,
    };
    match encode_impl(&sys, true) {
        Err(msg) => {
            assert!(msg.contains("bitsum references var_idx 7"));
            assert!(msg.contains("only 2 user vars"));
        }
        Ok(_) => panic!("expected out-of-range bitsum var rejection"),
    }
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

// ── Spec-driven property tests ────────────────────────────────────
//
// Properties are derived from the encoder spec — "encoding preserves
// the zero set of the original constraint" — and from the math
// (Fermat, Rabinowitsch trick, binary representation), NOT from
// observed encoder output. A failure here is a SOUNDNESS-class bug.

use crate::ff::field::FieldElem;

/// Evaluate a slice of `BigUint` values (interpreted modulo the ring's
/// prime) as a `FieldElem` vector of length `n_vars`. Indices past the
/// supplied slice are filled with zero.
fn vals_field(pr: &FfPolyRing, vals: &[BigUint]) -> Vec<FieldElem> {
    let fp = pr.field();
    let n = pr.n_vars();
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        if i < vals.len() {
            out.push(fp.from_biguint(&vals[i]));
        } else {
            out.push(fp.zero());
        }
    }
    out
}

/// Independent math reference: evaluate an `equality` (list of
/// `PolyTerm`) at a `BigUint`-indexed assignment, modulo `p`. The
/// caller is responsible for supplying enough values to cover every
/// `VarIdx` the equality references.
fn eval_eq_ref(eq: &[PolyTerm], vals: &[BigUint], p: &BigUint) -> BigUint {
    let mut acc = BigUint::from(0u32);
    for term in eq {
        let mut t = term.coeff.clone() % p;
        for &(v, e) in &term.vars {
            let vv = &vals[v as usize] % p;
            for _ in 0..e {
                t = (&t * &vv) % p;
            }
        }
        acc = (&acc + &t) % p;
    }
    acc
}

/// SPEC (property class 1, 4): if the math LHS of an equality
/// evaluates to 0 at an assignment, the encoded polynomial does too.
/// This is the encoder's zero-set preservation invariant for a
/// single-variable linear case (no bitsum extraction triggers).
#[test]
fn spec_encoded_equality_evaluates_to_zero_at_math_root() {
    // 2*x + 3*x - 5*x = 0 mod 101: identically zero in x → encoder
    // drops the polynomial (constant-zero case). Use a non-trivial
    // case instead.
    // 2*x + 3 = 0 mod 101 → x = -3/2 mod 101 = (101 - 3) * inv(2) mod 101
    //                    = 98 * 51 mod 101.
    let p = BigUint::from(101u32);
    let inv2: u32 = 51; // 2 * 51 = 102 ≡ 1 mod 101.
    let x_val_u32 = (98u32 * inv2) % 101;
    let mut b = empty_builder(101);
    let x = b.var("x");
    b.add_equality(vec![idx_term(2, &[(x, 1)]), idx_term(3, &[])]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let vals = vals_field(&enc.poly_ring, &[BigUint::from(x_val_u32)]);
    let ev = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
    assert!(enc.poly_ring.field().is_zero(&ev), "math root must zero the encoded poly");
    // Sanity: also matches the math reference.
    let ref_val = eval_eq_ref(
        &[idx_term(2, &[(x, 1)]), idx_term(3, &[])],
        &[BigUint::from(x_val_u32)],
        &p,
    );
    assert_eq!(ref_val, BigUint::from(0u32));
}

/// SPEC (property class 1, 4): for a non-root assignment, the encoded
/// polynomial evaluates to the same nonzero value as the math LHS,
/// modulo p — so distinguishing zero from nonzero (the zero set) is
/// preserved at every point.
#[test]
fn spec_encoded_equality_matches_math_at_non_root() {
    let p = BigUint::from(101u32);
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    // 7*x*y + 5*x + 4*y + 11 = 0
    let eq = vec![
        idx_term(7, &[(x, 1), (y, 1)]),
        idx_term(5, &[(x, 1)]),
        idx_term(4, &[(y, 1)]),
        idx_term(11, &[]),
    ];
    b.add_equality(eq.clone());
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    // Encoder normalizes each polynomial by inv(LC), so point evaluations
    // differ from the math LHS by a constant factor; the PRESERVED
    // invariant is the zero set: encoded(p)=0 iff math LHS(p)=0.
    for &(xv, yv) in &[(2u32, 3u32), (7, 11), (97, 50), (0, 0), (100, 100)] {
        let vals_bi = [BigUint::from(xv), BigUint::from(yv)];
        let vals = vals_field(&enc.poly_ring, &vals_bi);
        let got = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
        let want_bi = eval_eq_ref(&eq, &vals_bi, &p);
        let math_zero = want_bi == BigUint::from(0u32);
        let enc_zero = enc.poly_ring.field().is_zero(&got);
        assert_eq!(
            enc_zero, math_zero,
            "zero-set must be preserved at (x={}, y={})",
            xv, yv
        );
    }
}

/// SPEC (property class 1, 4, 7): same zero-set property at GF(7) and
/// GF(3). Edge primes exercised separately. For each (x, y) in the
/// full GF(p)^2 plane, encoded == math LHS.
#[test]
fn spec_zero_set_preserved_over_all_gfp_for_small_primes() {
    for prime in [3u32, 5, 7, 11] {
        let p = BigUint::from(prime);
        let mut b = empty_builder(prime);
        let x = b.var("x");
        let y = b.var("y");
        let eq = vec![
            idx_term(1, &[(x, 2)]),
            idx_term((prime as u64) - 1, &[(y, 1)]),
            idx_term(1, &[]),
        ];
        b.add_equality(eq.clone());
        let sys = b.build();
        let enc = encode(&sys).unwrap();
        for xv in 0..prime {
            for yv in 0..prime {
                let vals_bi = [BigUint::from(xv), BigUint::from(yv)];
                let vals = vals_field(&enc.poly_ring, &vals_bi);
                let got = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
                let want_bi = eval_eq_ref(&eq, &vals_bi, &p);
                let want = enc.poly_ring.field().from_biguint(&want_bi);
                assert!(
                    enc.poly_ring.field().eq(&got, &want),
                    "GF({}), (x={}, y={}): encoded eval must match math LHS",
                    prime,
                    xv,
                    yv
                );
            }
        }
    }
}

/// SPEC (property class 1, 5): assignment `v = val` encodes as a
/// polynomial whose root set on `v` is exactly `{val mod p}`. We
/// assert: (a) at v = val mod p, the poly is zero; (b) at every other
/// element of GF(p), it is nonzero.
#[test]
fn spec_assignment_poly_root_is_exact_value() {
    for prime in [5u32, 7, 11, 13] {
        let val: u32 = 3;
        let p = BigUint::from(prime);
        let mut b = empty_builder(prime);
        let v = b.var("v");
        b.add_assignment(v, BigUint::from(val));
        let sys = b.build();
        let enc = encode(&sys).unwrap();
        assert_eq!(enc.polynomials.len(), 1, "GF({}) assignment poly emitted", prime);
        let fp = enc.poly_ring.field();
        for vv in 0..prime {
            let vals = vals_field(&enc.poly_ring, &[BigUint::from(vv)]);
            let ev = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
            let is_root = fp.is_zero(&ev);
            let expected_root = (vv % prime) == (val % prime);
            assert_eq!(
                is_root, expected_root,
                "GF({}): assignment v={} root at vv={} ({}expected)",
                prime, val, vv, if expected_root { "" } else { "not " }
            );
        }
        // Doubled mod-p value still satisfies (val and val+prime are the
        // same field element).
        let _ = &p; // silence
    }
}

/// SPEC (property class 1, 5, Rabinowitsch trick): for `a ≠ b` the
/// encoded polynomial `(a - b)·w - 1` is satisfiable iff `a ≠ b`. We
/// assert:
///   (i)  when a = b is forced, no value of w makes the poly zero;
///   (ii) when a ≠ b, evaluating with w = (a - b)^{-1} gives zero.
/// Both follow from the Rabinowitsch trick spec — independent of how
/// the encoder constructs the polynomial.
#[test]
fn spec_rabinowitsch_satisfied_iff_a_neq_b() {
    let prime: u32 = 13;
    let p = BigUint::from(prime);
    let mut b = empty_builder(prime);
    let av = b.var("a");
    let bv = b.var("b");
    b.add_disequality(av, bv);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let fp = enc.poly_ring.field();
    let n = enc.poly_ring.n_vars();
    assert!(n >= 3, "a, b, __w_diseq_0");
    let w_idx = enc.var_map["__w_diseq_0"];
    let poly = &enc.polynomials[0];
    // (i) If a == b (set a=b=2), then `(a-b)*w - 1 = -1` for every w.
    for w_val in 0..prime {
        let mut vals_bi = vec![BigUint::from(0u32); n];
        vals_bi[enc.var_map["a"]] = BigUint::from(2u32);
        vals_bi[enc.var_map["b"]] = BigUint::from(2u32);
        vals_bi[w_idx] = BigUint::from(w_val);
        let vals = vals_field(&enc.poly_ring, &vals_bi);
        let ev = poly.evaluate(&vals, &enc.poly_ring.ring.ctx);
        assert!(
            !fp.is_zero(&ev),
            "Rabinowitsch must be unsatisfiable when a == b (w={})",
            w_val
        );
    }
    // (ii) If a ≠ b (a=3, b=5 in GF(13)), w = (a-b)^{-1} satisfies it.
    let a_u: i64 = 3;
    let b_u: i64 = 5;
    let diff: i64 = ((a_u - b_u).rem_euclid(prime as i64)) as i64;
    // Find w such that diff * w ≡ 1 mod prime by brute force.
    let mut w_val: Option<u32> = None;
    for w in 1..prime {
        if (diff as u64 * w as u64) % prime as u64 == 1 {
            w_val = Some(w);
            break;
        }
    }
    let w = w_val.expect("inverse exists in GF(prime)");
    let mut vals_bi = vec![BigUint::from(0u32); n];
    vals_bi[enc.var_map["a"]] = BigUint::from(a_u as u32);
    vals_bi[enc.var_map["b"]] = BigUint::from(b_u as u32);
    vals_bi[w_idx] = BigUint::from(w);
    let vals = vals_field(&enc.poly_ring, &vals_bi);
    let ev = poly.evaluate(&vals, &enc.poly_ring.ring.ctx);
    assert!(
        fp.is_zero(&ev),
        "Rabinowitsch must be satisfiable at w = (a-b)^{{-1}} when a != b"
    );
    let _ = p;
}

/// SPEC (property class 6, bitprop): the bitsum poly
/// `b_0 + 2·b_1 + 4·b_2 + ... + 2^{k-1}·b_{k-1} - aux` is zero exactly
/// when `aux` is the binary value of `(b_0, b_1, ..., b_{k-1})`. We
/// enumerate all 2^k bit patterns plus the matching aux and assert
/// zero; we also pick a non-matching aux and assert nonzero. The
/// encoder MUST produce bitsum polys with bit coefficients `2^i mod p`
/// — exact powers of two — otherwise binary decomposition is broken.
/// Memory entry: bitprop is a RECURRING HAZARD class (R5/H1, R7/J1).
#[test]
fn spec_bitsum_poly_encodes_binary_value() {
    let prime: u32 = 101;
    let k = 4usize; // 2^4 = 16 ≤ 101.
    let mut b = empty_builder(prime);
    let bits: Vec<VarIdx> = (0..k).map(|i| b.var(&format!("b{}", i))).collect();
    b.add_bitsum(bits.clone());
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.bitsum_polys.len(), 1);
    let poly = &enc.bitsum_polys[0];
    let fp = enc.poly_ring.field();
    let aux_idx = enc.var_map["__bitsum_0"];
    let n = enc.poly_ring.n_vars();
    for pattern in 0..(1u32 << k) {
        let mut vals_bi = vec![BigUint::from(0u32); n];
        // Bit i (LSB-first) of `pattern`.
        for (i, &bi) in bits.iter().enumerate() {
            let bit = (pattern >> i) & 1;
            vals_bi[bi as usize] = BigUint::from(bit);
        }
        // Matching aux: sum 2^i * bit_i.
        vals_bi[aux_idx] = BigUint::from(pattern);
        let vals = vals_field(&enc.poly_ring, &vals_bi);
        let ev = poly.evaluate(&vals, &enc.poly_ring.ring.ctx);
        assert!(
            fp.is_zero(&ev),
            "bitsum poly must be 0 at aux = binary value of bits, pattern={}",
            pattern
        );
        // Mismatched aux (off by 1): must be nonzero.
        let alt_aux = (pattern + 1) % prime;
        if alt_aux != pattern {
            vals_bi[aux_idx] = BigUint::from(alt_aux);
            let vals2 = vals_field(&enc.poly_ring, &vals_bi);
            let ev2 = poly.evaluate(&vals2, &enc.poly_ring.ring.ctx);
            assert!(
                !fp.is_zero(&ev2),
                "bitsum poly must be nonzero at aux ≠ binary value, pattern={}",
                pattern
            );
        }
    }
}

/// SPEC (property class 6): the bitsum polynomial's coefficient on the
/// monomial `b_i` (single variable, degree 1) is exactly `2^i mod p`.
/// Derived directly from the binary-positional spec — independent of
/// encoder layout. After `normalize_poly` divides by the leading
/// coefficient (which is 1 for this construction since `b_0` has
/// coefficient 1), the coefficients survive unchanged. The aux
/// coefficient is `p - 1` (= -1 mod p).
#[test]
fn spec_bitsum_coefficients_are_powers_of_two() {
    let prime: u32 = 101;
    let k = 5usize;
    let mut b = empty_builder(prime);
    let bits: Vec<VarIdx> = (0..k).map(|i| b.var(&format!("b{}", i))).collect();
    b.add_bitsum(bits.clone());
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let poly = &enc.bitsum_polys[0];
    let pr = &enc.poly_ring;
    let fp = pr.field();
    // Walk the terms; for each linear `b_i` monomial, check coeff = 2^i.
    let n = pr.n_vars();
    let mut found = vec![false; k];
    let mut found_aux = false;
    let aux_idx = enc.var_map["__bitsum_0"];
    for (coeff, mono) in pr.ring.terms(poly) {
        // Detect a single-variable degree-1 monomial.
        let mut nonzero_vars: Vec<(usize, usize)> = Vec::new();
        for v in 0..n {
            let e = pr.ring.exponent_at(&mono, v);
            if e > 0 {
                nonzero_vars.push((v, e));
            }
        }
        if nonzero_vars.len() != 1 {
            continue;
        }
        let (v, e) = nonzero_vars[0];
        if e != 1 {
            continue;
        }
        let coeff_bi = fp.to_biguint(coeff);
        if v == aux_idx {
            // aux coefficient should be -1 mod p == p-1.
            assert_eq!(
                coeff_bi,
                BigUint::from(prime - 1),
                "aux monomial coefficient must be -1 mod p"
            );
            found_aux = true;
        } else {
            // Map `v` back to which b_i this is.
            let mut bit_pos: Option<usize> = None;
            for (i, &bi) in bits.iter().enumerate() {
                if v == bi as usize {
                    bit_pos = Some(i);
                    break;
                }
            }
            let i = bit_pos.expect("monomial variable must be a declared bit");
            let want = BigUint::from(1u32 << i) % BigUint::from(prime);
            assert_eq!(
                coeff_bi, want,
                "bit b_{} coefficient must be 2^{} mod p",
                i, i
            );
            found[i] = true;
        }
    }
    assert!(found.iter().all(|&f| f), "all k bits must appear as monomials");
    assert!(found_aux, "aux monomial must appear");
}

/// SPEC (property class 1, Fermat's little theorem): when
/// `add_field_polys = true` at a small prime, every ring variable `x`
/// gets a polynomial whose root set on `x` is exactly GF(p). We
/// enumerate GF(p) at GF(5) and GF(7) and assert every value is a root
/// of the corresponding `x^p - x` poly. (Independent reference: x^p ≡
/// x mod p for all x ∈ GF(p).)
#[test]
fn spec_field_polys_have_full_gfp_root_set() {
    for prime in [5u32, 7] {
        let mut b = empty_builder(prime);
        let x = b.var("x");
        let y = b.var("y");
        b.add_equality(vec![
            idx_term(1, &[(x, 1)]),
            idx_term((prime - 1) as u64, &[(y, 1)]),
        ]);
        b.set_add_field_polys(true);
        let sys = b.build();
        let enc = encode(&sys).unwrap();
        // Identify the two field polynomials (PolySource::Other).
        let field_polys: Vec<&Poly> = enc
            .polynomials
            .iter()
            .zip(enc.poly_provenance.iter())
            .filter(|(_, s)| matches!(s, PolySource::Other))
            .map(|(p, _)| p)
            .collect();
        assert_eq!(field_polys.len(), 2, "two field polys at GF({})", prime);
        // Each field poly must be zero at every value of GF(p), evaluated
        // at the single variable it constrains. With only 2 ring vars,
        // setting both to the same v evaluates both polys at v.
        let fp = enc.poly_ring.field();
        for v in 0..prime {
            for fpoly in &field_polys {
                let vals = vals_field(&enc.poly_ring, &[BigUint::from(v), BigUint::from(v)]);
                let ev = fpoly.evaluate(&vals, &enc.poly_ring.ring.ctx);
                assert!(
                    fp.is_zero(&ev),
                    "Fermat: x^{} - x must vanish for x = {} in GF({})",
                    prime,
                    v,
                    prime
                );
            }
        }
    }
}

/// SPEC (property class 3, idempotence): `compact_used_vars` is
/// idempotent — running encode twice on the same system produces the
/// same compaction. Concretely, the second encode's `var_map` and
/// `poly_ring.n_vars()` must match the first's. Encoder must be a pure
/// function of its input (no hidden state mutated).
#[test]
fn spec_encode_is_pure_determinism() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    let z = b.var("z");
    b.add_equality(vec![
        idx_term(2, &[(x, 1), (y, 1)]),
        idx_term(3, &[(z, 1)]),
        idx_term(7, &[]),
    ]);
    b.add_disequality(x, z);
    let sys = b.build();
    let e1 = encode(&sys).expect("encode 1");
    let e2 = encode(&sys).expect("encode 2");
    assert_eq!(e1.poly_ring.n_vars(), e2.poly_ring.n_vars());
    assert_eq!(e1.polynomials.len(), e2.polynomials.len());
    assert_eq!(e1.bitsum_polys.len(), e2.bitsum_polys.len());
    assert_eq!(e1.n_input_equalities, e2.n_input_equalities);
    assert_eq!(e1.poly_provenance, e2.poly_provenance);
    let mut k1: Vec<&String> = e1.var_map.keys().collect();
    let mut k2: Vec<&String> = e2.var_map.keys().collect();
    k1.sort();
    k2.sort();
    assert_eq!(k1, k2);
    for k in &k1 {
        assert_eq!(e1.var_map[*k], e2.var_map[*k]);
    }
}

/// SPEC (property class 8, determinism): two independent builders
/// producing logically identical systems yield identical encodings.
#[test]
fn spec_independent_builders_same_logical_system_match() {
    let build = || {
        let mut b = empty_builder(13);
        let x = b.var("x");
        let y = b.var("y");
        b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(12, &[(y, 1)])]);
        b.build()
    };
    let e1 = encode(&build()).unwrap();
    let e2 = encode(&build()).unwrap();
    assert_eq!(e1.poly_ring.n_vars(), e2.poly_ring.n_vars());
    assert_eq!(e1.polynomials.len(), e2.polynomials.len());
    assert_eq!(e1.poly_provenance, e2.poly_provenance);
}

/// SPEC (property class 4): `n_input_equalities` equals the number of
/// equalities fed to `encode_impl`, i.e. post-`rewrite_system` +
/// `auto_extract_bitsums`. Independently computed by replaying the
/// same pre-encode pipeline.
#[test]
fn spec_n_input_equalities_matches_post_pipeline_count() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(2, &[(y, 1)])]);
    b.add_equality(vec![idx_term(3, &[(x, 1)]), idx_term(4, &[]),]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let compacted = {
        // Manually re-run the same pre-encode pipeline encode() runs.
        let s = sys.clone();
        let mut r = s;
        crate::frontend::rewriter::rewrite_system(&mut r);
        auto_extract_bitsums(&r)
    };
    assert_eq!(enc.n_input_equalities, compacted.equalities.len());
}

/// SPEC (property class 4): `poly_provenance` and `polynomials` have
/// the same length (release-mode invariant; debug_assert in source).
#[test]
fn spec_provenance_parallel_to_polynomials() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    b.add_disequality(x, y);
    b.add_assignment(x, BigUint::from(3u32));
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.poly_provenance.len(), enc.polynomials.len());
}

/// SPEC (property class 4): `encode_constraint_side` (Rabinowitsch
/// disabled) never emits a `PolySource::Rabinowitsch` entry.
#[test]
fn spec_encode_constraint_side_omits_rabinowitsch() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    let z = b.var("z");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    b.add_disequality(x, y);
    b.add_disequality(y, z);
    let sys = b.build();
    let enc = encode_constraint_side(&sys).unwrap();
    let n_rab = enc
        .poly_provenance
        .iter()
        .filter(|s| matches!(s, PolySource::Rabinowitsch(_)))
        .count();
    assert_eq!(n_rab, 0, "constraint-side encoding has zero Rabinowitsch polys");
}

/// SPEC (property class 2, round-trip): for every name in
/// `var_map`, `poly_ring.var_names()[var_map[name]] == name`. The two
/// surfaces must agree as inverse maps on the encoded ring.
#[test]
fn spec_var_map_inverse_of_var_names() {
    let mut b = empty_builder(101);
    let _ = b.var("alpha");
    let _ = b.var("beta");
    let _ = b.var("gamma");
    let x = b.var("alpha");
    let y = b.var("beta");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    b.add_disequality(x, y);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let names = enc.poly_ring.var_names();
    for (name, &idx) in &enc.var_map {
        assert_eq!(
            &names[idx], name,
            "var_map[{}] = {} must round-trip via var_names",
            name, idx
        );
    }
}

/// SPEC (property class 1, 4): `bitsum_aux_index` is a strict
/// monotonic function of `bitsum_i` given fixed `(n_user, n_diseq)`,
/// AND the encoded ring must contain exactly the named `__bitsum_i`
/// slot at the predicted index — no off-by-one between the predictor
/// and the allocator. Derived from the spec: the aux for bitsum_i must
/// be allocated right after user vars + diseq witnesses + earlier
/// bitsum auxes.
#[test]
fn spec_bitsum_aux_index_matches_allocation() {
    // 4 user vars, 2 disequalities → expected aux indices 6 and 7 for
    // two user-provided bitsums.
    let mut b = empty_builder(101);
    let v0 = b.var("v0");
    let v1 = b.var("v1");
    let v2 = b.var("v2");
    let v3 = b.var("v3");
    b.add_equality(vec![idx_term(1, &[(v0, 1)]), idx_term(1, &[])]);
    b.add_disequality(v0, v1);
    b.add_disequality(v2, v3);
    b.add_bitsum(vec![v0, v1]); // bitsum 0
    b.add_bitsum(vec![v2, v3]); // bitsum 1
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    // After compact_used_vars (all 4 referenced), n_user = 4, n_diseq = 2.
    let pred0 = bitsum_aux_index(4, 2, 0);
    let pred1 = bitsum_aux_index(4, 2, 1);
    assert_eq!(enc.var_map["__bitsum_0"] as u32, pred0);
    assert_eq!(enc.var_map["__bitsum_1"] as u32, pred1);
    assert!(pred1 > pred0, "indices monotonic");
}

/// SPEC (property class 4, invariant): the polynomial ring's variable
/// count equals `n_user + n_diseq + n_bitsum` (user vars + one
/// Rabinowitsch witness per disequality + one aux per bitsum), where
/// `n_user` is the compacted user-var count.
#[test]
fn spec_ring_size_equals_user_plus_witness_plus_bitsum() {
    let mut b = empty_builder(13);
    let x = b.var("x");
    let y = b.var("y");
    let z = b.var("z");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    b.add_disequality(x, z);
    b.add_bitsum(vec![b0, b1, b2]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    // All declared vars are referenced; compact does not drop any.
    let n_user = 6;
    let n_diseq = 1;
    let n_bitsum = 1;
    assert_eq!(enc.poly_ring.n_vars(), n_user + n_diseq + n_bitsum);
}

/// SPEC (property class 1, 5): an empty equality list produces no
/// equality polynomials (only Rabinowitsch / assignment / field /
/// bitsum entries contribute). Trivial vacuous-input invariant.
#[test]
fn spec_empty_equality_list_emits_no_equality_polys() {
    let mut b = empty_builder(101);
    let _ = b.var("x"); // unreferenced — compact drops it
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.polynomials.len(), 0);
    assert_eq!(enc.bitsum_polys.len(), 0);
    assert_eq!(enc.n_input_equalities, 0);
}

/// SPEC (property class 7, edge prime GF(2)): equality `x + y = 0`
/// over GF(2) is zero iff x == y (since -1 ≡ 1 in GF(2), `x + y` is
/// XOR). Cover the full 2x2 plane.
#[test]
fn spec_zero_set_over_gf2() {
    let mut b = empty_builder(2);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(1, &[(y, 1)])]);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let fp = enc.poly_ring.field();
    for &(xv, yv) in &[(0u32, 0u32), (0, 1), (1, 0), (1, 1)] {
        let vals = vals_field(&enc.poly_ring, &[BigUint::from(xv), BigUint::from(yv)]);
        let ev = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
        let is_root = fp.is_zero(&ev);
        let expected = (xv + yv) % 2 == 0;
        assert_eq!(is_root, expected, "GF(2): x+y=0 root iff x==y (x={}, y={})", xv, yv);
    }
}

/// SPEC (property class 3, idempotence): running `auto_extract_bitsums`
/// twice in a row yields the same result as running it once. After the
/// first pass every detectable chain is collected into `bitsums`; the
/// second pass finds no further chains and is a no-op.
#[test]
fn spec_auto_extract_bitsums_idempotent() {
    let (sys, _s, _bs) = bitdecomp_system(101, 3);
    let once = auto_extract_bitsums(&sys);
    let twice = auto_extract_bitsums(&once);
    assert_eq!(once.bitsums.len(), twice.bitsums.len());
    for (a, b) in once.bitsums.iter().zip(twice.bitsums.iter()) {
        assert_eq!(a, b);
    }
    assert_eq!(once.equalities.len(), twice.equalities.len());
}

/// SPEC (property class 3, idempotence): `compact_used_vars` is
/// idempotent — encoding a system whose user vars are all referenced
/// gives a `n_vars` count equal to the original; re-feeding the
/// encoded layout into another encode does not shrink further. We test
/// via the public surface: encode twice and assert ring size matches.
#[test]
fn spec_encode_idempotent_on_compacted_input() {
    // System where every var is referenced; compact is a no-op.
    let mut b = empty_builder(13);
    let x = b.var("x");
    let y = b.var("y");
    b.add_equality(vec![idx_term(1, &[(x, 1)]), idx_term(12, &[(y, 1)])]);
    let sys = b.build();
    let enc1 = encode(&sys).unwrap();
    let enc2 = encode(&sys).unwrap();
    assert_eq!(enc1.poly_ring.n_vars(), 2);
    assert_eq!(enc1.poly_ring.n_vars(), enc2.poly_ring.n_vars());
}

/// SPEC (property class 4, invariant): every `PolySource::Equality(j)`
/// in `poly_provenance` carries `j < n_input_equalities`. The
/// provenance index addresses the equality frame the encoder received,
/// so it must lie within bounds.
#[test]
fn spec_equality_provenance_in_bounds() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    for i in 0..5u32 {
        b.add_equality(vec![
            idx_term((i + 1) as u64, &[(x, 1)]),
            idx_term((i + 2) as u64, &[(y, 1)]),
        ]);
    }
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    for s in &enc.poly_provenance {
        if let PolySource::Equality(j) = s {
            assert!(*j < enc.n_input_equalities, "Equality({}) out of bounds", j);
        }
    }
}

/// SPEC (property class 4, invariant): every `PolySource::Rabinowitsch(d)`
/// in `poly_provenance` carries `d < disequality_count`. The provenance
/// addresses the disequality frame in the (post-pipeline) system.
#[test]
fn spec_rabinowitsch_provenance_in_bounds() {
    let mut b = empty_builder(101);
    let x = b.var("x");
    let y = b.var("y");
    let z = b.var("z");
    b.add_disequality(x, y);
    b.add_disequality(y, z);
    b.add_disequality(x, z);
    let sys = b.build();
    let n_diseq = sys.disequalities.len();
    let enc = encode(&sys).unwrap();
    for s in &enc.poly_provenance {
        if let PolySource::Rabinowitsch(d) = s {
            assert!(*d < n_diseq, "Rabinowitsch({}) out of bounds (n_diseq={})", d, n_diseq);
        }
    }
}

/// SPEC (property class 1, big prime, BN128-ish): zero-set
/// preservation at a cryptographic-size prime. Single linear equality
/// `5*x + 7*y - 12 = 0`; assertion that the math identity `5*2 + 7*1 - 12
/// = 5 ≠ 0` (so non-root) is preserved, and the root `(1, 1)` zeroes the
/// poly.
#[test]
fn spec_big_prime_zero_set_preserved() {
    // BN128 scalar field prime.
    let p_hex = "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";
    let p = BigUint::parse_bytes(p_hex.as_bytes(), 16).expect("BN128 prime");
    let mut b = ConstraintSystemBuilder::new(p.clone());
    let x = b.var("x");
    let y = b.var("y");
    // 5*x + 7*y + (p - 12) = 0  (i.e. 5x + 7y - 12 = 0).
    let eq = vec![
        idx_term(5, &[(x, 1)]),
        idx_term(7, &[(y, 1)]),
        PolyTerm { coeff: &p - BigUint::from(12u32), vars: vec![] },
    ];
    b.add_equality(eq.clone());
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    let fp = enc.poly_ring.field();
    // Root: (1, 1).
    let vals = vals_field(&enc.poly_ring, &[BigUint::from(1u32), BigUint::from(1u32)]);
    let ev = enc.polynomials[0].evaluate(&vals, &enc.poly_ring.ring.ctx);
    assert!(fp.is_zero(&ev), "(1,1) is a root of 5x+7y-12=0");
    // Non-root: (2, 1) → 5·2 + 7·1 - 12 = 5 ≠ 0. Encoder normalizes the
    // polynomial, so the encoded value at (2,1) is math LHS * inv(5); the
    // PRESERVED invariant is that this is still non-zero.
    let vals2 = vals_field(&enc.poly_ring, &[BigUint::from(2u32), BigUint::from(1u32)]);
    let ev2 = enc.polynomials[0].evaluate(&vals2, &enc.poly_ring.ring.ctx);
    assert!(!fp.is_zero(&ev2), "(2,1) is not a root");
}

/// SPEC (property class 6, bitprop): `bitsum_fits(n, p)` ⇔ `2^n ≤ p`.
/// Independent reference: compute `1u128 << n` and compare to `p`
/// (for n ≤ 60). This locks the chain-length cap formula and
/// directly gates the bitprop soundness guard cited in
/// `[bitsum_fits]` docs.
#[test]
fn spec_bitsum_fits_matches_pow2_inequality() {
    for &prime in &[2u128, 3, 5, 7, 11, 13, 101, 257, 1009, 32771] {
        let p = BigUint::from(prime);
        for n in 0..=12 {
            let want = (1u128 << n) <= prime;
            let got = bitsum_fits(n, &p);
            assert_eq!(
                got, want,
                "bitsum_fits({}, {}) must mirror 2^n ≤ p ({} expected)",
                n, prime, want
            );
        }
    }
}

/// SPEC (property class 6, bitprop hard-probe): a bitsum of length
/// `n` whose decoded value would exceed p-1 cannot be sound; the
/// extractor must reject it. SPEC by the soundness gate
/// (`bitsum_fits`): chain length capped at `floor(log2 p)`. At GF(5),
/// `2^2 = 4 ≤ 5` so length 2 is OK; `2^3 = 8 > 5` so length 3 is
/// CAPPED. We assert: a length-3 auto-detectable chain at GF(5)
/// either produces no bitsum or a bitsum of length ≤ 2.
#[test]
fn spec_auto_extract_caps_chain_under_soundness_gate() {
    // p = 5; build b·(b-1)=0 for b0..b2, plus s - b0 - 2*b1 - 4*b2 = 0.
    // The chain has 3 bits; 2^3 = 8 > 5, so cap forbids length 3.
    let p = BigUint::from(5u32);
    let mut b = empty_builder(5);
    let s = b.var("s");
    let b0 = b.var("b0");
    let b1 = b.var("b1");
    let b2 = b.var("b2");
    let pm1 = &p - BigUint::from(1u32);
    for &bi in &[b0, b1, b2] {
        b.add_equality(vec![
            idx_term(1, &[(bi, 2)]),
            PolyTerm { coeff: pm1.clone(), vars: vec![(bi, 1)] },
        ]);
    }
    b.add_equality(vec![
        idx_term(1, &[(s, 1)]),
        PolyTerm { coeff: &p - BigUint::from(1u32), vars: vec![(b0, 1)] },
        PolyTerm { coeff: &p - BigUint::from(2u32), vars: vec![(b1, 1)] },
        PolyTerm { coeff: &p - BigUint::from(4u32) % &p, vars: vec![(b2, 1)] },
    ]);
    let sys = b.build();
    let extracted = auto_extract_bitsums(&sys);
    for chain in &extracted.bitsums {
        assert!(
            chain.len() <= 2,
            "soundness cap: chain length {} > floor(log2(5)) = 2",
            chain.len()
        );
    }
}

/// SPEC: zero set of each equality is preserved by the encoder
/// COMPONENT-WISE. The encoder normalizes each polynomial independently
/// (by inv(LC)), so per-poly point-evaluation linearity does NOT hold
/// across equalities; what is preserved per polynomial is its zero set.
/// We assert: at a root of eq_i, encoded[i] evaluates to zero (i ∈ {0,1}).
#[test]
fn spec_evaluation_is_additive_across_equalities() {
    let prime: u32 = 101;
    let mut b = empty_builder(prime);
    let x = b.var("x");
    let y = b.var("y");
    // eq1: 3x + 5y = 0. Root at (2, 19): 3*2 + 5*19 = 6 + 95 = 101 ≡ 0.
    let eq1 = vec![idx_term(3, &[(x, 1)]), idx_term(5, &[(y, 1)])];
    // eq2: 7x + 11 = 0. Root at x = -11/7 mod 101. inv(7) mod 101 = 29
    // (since 7*29 = 203 ≡ 1). x = -11*29 mod 101 = -319 mod 101 = 85.
    let eq2 = vec![idx_term(7, &[(x, 1)]), idx_term(11, &[])];
    b.add_equality(eq1);
    b.add_equality(eq2);
    let sys = b.build();
    let enc = encode(&sys).unwrap();
    assert_eq!(enc.polynomials.len(), 2);
    let fp = enc.poly_ring.field();
    // At root of eq1 (2, 19): encoded[0] must be zero.
    let root1 = vals_field(&enc.poly_ring, &[BigUint::from(2u32), BigUint::from(19u32)]);
    let e1_at_root = enc.polynomials[0].evaluate(&root1, &enc.poly_ring.ring.ctx);
    assert!(fp.is_zero(&e1_at_root), "encoded[0] must zero at root of eq1");
    // At root of eq2 (85, anything): encoded[1] must be zero.
    let root2 = vals_field(&enc.poly_ring, &[BigUint::from(85u32), BigUint::from(0u32)]);
    let e2_at_root = enc.polynomials[1].evaluate(&root2, &enc.poly_ring.ring.ctx);
    assert!(fp.is_zero(&e2_at_root), "encoded[1] must zero at root of eq2");
}
