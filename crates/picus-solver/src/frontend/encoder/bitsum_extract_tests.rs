use super::super::ConstraintSystemBuilder;
use super::*;

// ────────── bitsum_fits ──────────

#[test]
fn bitsum_fits_holds_when_2_pow_len_le_prime() {
    // GF(7): len 2 → 4 ≤ 7 ✓; len 3 → 8 > 7 ✗.
    let p = BigUint::from(7u32);
    assert!(bitsum_fits(0, &p));
    assert!(bitsum_fits(1, &p));
    assert!(bitsum_fits(2, &p));
    assert!(!bitsum_fits(3, &p));
    assert!(!bitsum_fits(4, &p));
}

#[test]
fn bitsum_fits_bn128_supports_long_chains() {
    // BN128 is 254-bit but p < 2^254, so the cap is at len 253.
    let p = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    assert!(bitsum_fits(253, &p));
    assert!(!bitsum_fits(254, &p));
    assert!(!bitsum_fits(255, &p));
}

// ────────── auto_extract_bitsums ──────────

fn cs_with(prime: u64, build: impl FnOnce(&mut ConstraintSystemBuilder)) -> ConstraintSystem {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(prime));
    build(&mut b);
    b.build()
}

#[test]
fn auto_extract_no_bit_constrained_vars_is_passthrough() {
    // No bit constraints + no explicit bitsums → returns clone unchanged.
    let cs = cs_with(7, |b| {
        let x = b.var("x");
        let y = b.var("y");
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(x, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(2u32),
                vars: vec![(y, 1)],
            },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    // Same number of equalities, same number of bitsums (none).
    assert_eq!(out.equalities.len(), cs.equalities.len());
    assert_eq!(out.bitsums.len(), 0);
}

#[test]
fn auto_extract_finds_chain_when_bits_declared() {
    // Variables b0, b1 marked as bits via b·(b-1)=0 constraints, plus
    // an equality of the form `b0 + 2·b1 + 3 = 0` (matches bitsum
    // base coeff 1 with k=1). Should extract `[b0, b1]` as a bitsum.
    let cs = cs_with(7, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        // b0·(b0-1) = b0^2 - b0 = 0
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b0, 2)],
            },
            PolyTerm {
                coeff: BigUint::from(6u32),
                vars: vec![(b0, 1)],
            }, // -1 mod 7 = 6
        ]);
        // b1·(b1-1) = 0
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b1, 2)],
            },
            PolyTerm {
                coeff: BigUint::from(6u32),
                vars: vec![(b1, 1)],
            },
        ]);
        // The bitsum-shaped equality: 1·b0 + 2·b1 + 3 = 0
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b0, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(2u32),
                vars: vec![(b1, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(3u32),
                vars: vec![],
            },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    // Should detect [b0, b1] as a bitsum.
    assert_eq!(out.bitsums.len(), 1);
    assert_eq!(out.bitsums[0].len(), 2);
}

#[test]
fn auto_extract_respects_bitsum_fits_cap() {
    // Over GF(7), bitsum_fits caps chain length at 2 (since 2^3 > 7).
    // Even if 3 bit-constrained vars are present with c, 2c, 4c
    // coefficients, the extractor must NOT extract a chain longer
    // than the cap.
    let cs = cs_with(7, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        for bv in [b0, b1, b2] {
            b.add_equality(vec![
                PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(bv, 2)],
                },
                PolyTerm {
                    coeff: BigUint::from(6u32),
                    vars: vec![(bv, 1)],
                },
            ]);
        }
        // c·b0 + 2c·b1 + 4c·b2 with c=1 (would-be 3-chain). 4 mod 7 = 4.
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b0, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(2u32),
                vars: vec![(b1, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(4u32),
                vars: vec![(b2, 1)],
            },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    // No bitsum of length > 2 may be extracted under GF(7).
    for bs in &out.bitsums {
        assert!(
            bs.len() <= 2,
            "chain length {} exceeds GF(7) cap of 2",
            bs.len()
        );
    }
}

// ────────── detect_bit_constraint rejection paths ──────────

#[test]
fn detect_bit_constraint_rejects_mismatched_vars() {
    // b^2 - c = 0: quad on var 0, lin on var 1 — different vars, so it is
    // NOT a `b·(b-1)` constraint. Exercises the `quad.var != lin.var` reject.
    let p = BigUint::from(7u32);
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32), // -1 mod 7
            vars: vec![(1u32, 1)],
        },
    ];
    assert_eq!(detect_bit_constraint(&eq, &p), None);
}

#[test]
fn detect_bit_constraint_rejects_nonzero_coeff_sum() {
    // x^2 + x = 0: quad coeff 1, lin coeff 1, sum = 2 ≠ 0 mod 7. This is
    // x·(x+1), not a bit constraint. Exercises the `sum != 0` reject.
    let p = BigUint::from(7u32);
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 1)],
        },
    ];
    assert_eq!(detect_bit_constraint(&eq, &p), None);
}

#[test]
fn detect_bit_constraint_accepts_canonical() {
    // x^2 - x = 0 over GF(7): canonical bit constraint, var 0.
    let p = BigUint::from(7u32);
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![(0u32, 1)],
        },
    ];
    assert_eq!(detect_bit_constraint(&eq, &p), Some(0));
}

#[test]
fn auto_extract_mismatched_bit_constraint_is_passthrough() {
    // Two bogus "bit constraints" with mismatched vars / nonzero sum mean
    // no bit is registered, so auto_extract returns the system unchanged.
    let cs = cs_with(7, |b| {
        let b0 = b.var("b0");
        let c0 = b.var("c0");
        // b0^2 - c0 (mismatched vars): not a bit constraint.
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b0, 2)],
            },
            PolyTerm {
                coeff: BigUint::from(6u32),
                vars: vec![(c0, 1)],
            },
        ]);
        // c0^2 + c0 (nonzero sum): not a bit constraint.
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(c0, 2)],
            },
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(c0, 1)],
            },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    assert!(out.bitsums.is_empty());
    assert_eq!(out.equalities.len(), cs.equalities.len());
}

// ────────── find_bitsum_chain term handling ──────────

#[test]
fn find_bitsum_chain_skips_zero_coeff_terms() {
    // GF(13): chain b0 + 2·b1 with a stray 0·b2 term interleaved. The
    // zero-coeff term must be skipped, leaving the chain [b0, b1] intact.
    let p = BigUint::from(13u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(0u32), // skipped
            vars: vec![(2u32, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(2u32),
            vars: vec![(1u32, 1)],
        },
    ];
    let (chain, base, consumed) =
        find_bitsum_chain(&eq, &bits, &p, 2).expect("chain of length 2");
    assert_eq!(chain, vec![0u32, 1u32]);
    assert_eq!(base, BigUint::from(1u32));
    // The two non-zero chain terms (indices 0 and 2) are consumed; the
    // skipped zero term (index 1) is not.
    assert!(consumed.contains(&0));
    assert!(consumed.contains(&2));
    assert!(!consumed.contains(&1));
}

#[test]
fn find_bitsum_chain_breaks_on_gap() {
    // GF(13): c·b0 + 2c·b1 present but 4c·b2 missing (gap). The chain
    // stops at length 2; b2 (coeff 8) does not extend it.
    let p = BigUint::from(13u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(2u32),
            vars: vec![(1u32, 1)],
        },
        // coeff 8 = 8·c would be the 4th bit's slot (8c, not 4c) — there is
        // no 4·b term, so the chain breaks after b1.
        PolyTerm {
            coeff: BigUint::from(8u32),
            vars: vec![(2u32, 1)],
        },
    ];
    let (chain, _base, _consumed) =
        find_bitsum_chain(&eq, &bits, &p, 2).expect("chain of length 2");
    assert_eq!(chain.len(), 2);
    assert_eq!(chain, vec![0u32, 1u32]);
}

#[test]
fn auto_extract_gap_caps_chain_length_gf13() {
    // End-to-end: c·b0 + 2c·b1 with 4c·b2 missing yields a length-2 bitsum.
    let cs = cs_with(13, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        for bv in [b0, b1, b2] {
            b.add_equality(vec![
                PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(bv, 2)],
                },
                PolyTerm {
                    coeff: BigUint::from(12u32), // -1 mod 13
                    vars: vec![(bv, 1)],
                },
            ]);
        }
        // b0 + 2·b1 + 8·b2 — gap at 4, so b2 is not part of the chain.
        b.add_equality(vec![
            PolyTerm {
                coeff: BigUint::from(1u32),
                vars: vec![(b0, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(2u32),
                vars: vec![(b1, 1)],
            },
            PolyTerm {
                coeff: BigUint::from(8u32),
                vars: vec![(b2, 1)],
            },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    assert_eq!(out.bitsums.len(), 1);
    assert_eq!(out.bitsums[0].len(), 2, "gap caps the chain at b0, b1");
}

#[test]
fn auto_extract_preserves_existing_bitsums() {
    // Pre-existing bitsum entries must still appear in the output.
    let cs = cs_with(11, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        b.add_bitsum(vec![b0, b1]); // explicit
    });
    let out = auto_extract_bitsums(&cs);
    assert!(out.bitsums.len() >= 1);
    assert_eq!(out.bitsums[0], vec![0, 1]);
}

// ────────── find_bitsum_chain: by_coeff.get(&cur) None path ──────────

#[test]
fn find_bitsum_chain_break_when_next_coeff_missing() {
    // GF(13): max_chain_bits = 3 (since 2^3=8 <= 13 < 16). Eq holds only
    // the (coeff=1, b0) and (coeff=2, b1) bit terms plus a stray non-bit
    // var term that is filtered out of `by_coeff` (vars not in `bits`).
    // Chain: base=1 → consume b0, cur=2 → consume b1, cur=4 →
    // `by_coeff.get(&4)` returns None → break. chain_vars.len() = 2 is
    // strictly below the length cap of 3, so the cap branch is not what
    // ended the loop; the missing-coefficient None branch did.
    let p = BigUint::from(13u32);
    // Only b0 and b1 are declared as bit-constrained; var index 2 is a
    // generic FF var, so its term is dropped from `by_coeff` during
    // bucket construction.
    let bits: HashSet<VarIdx> = [0u32, 1u32].into_iter().collect();
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(2u32),
            vars: vec![(1u32, 1)],
        },
        // 5·v2 — v2 is not a declared bit, so this term is ignored when
        // building the by_coeff buckets and cannot extend the chain.
        PolyTerm {
            coeff: BigUint::from(5u32),
            vars: vec![(2u32, 1)],
        },
    ];
    let (chain, base, _consumed) =
        find_bitsum_chain(&eq, &bits, &p, 2).expect("chain of length 2");
    assert_eq!(chain, vec![0u32, 1u32]);
    assert_eq!(base, BigUint::from(1u32));
}
