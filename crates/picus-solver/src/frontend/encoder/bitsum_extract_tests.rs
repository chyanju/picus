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

// ────────── SPEC-DRIVEN PROPERTY TESTS ──────────
//
// Expected values below are derived from MATH/SPEC, not from reading the
// source's control flow.
//   * bitsum_fits(n, p) ⇔ (2^n ≤ p)   [pure math identity]
//   * Chain-length cap is floor(log2(p)) = largest n with 2^n ≤ p.
//   * find_bitsum_chain accepts only the coefficient sequence
//     c, 2c, 4c, ..., 2^(k-1)·c  (mod p). Any other coefficient must
//     not extend the chain (rejection of 3, 5, 6, 1+p, etc.).
//   * detect_bit_constraint accepts c·x^2 + d·x iff `(c+d) ≡ 0 (mod p)`
//     AND both terms reference the SAME variable.

// PROPERTY (1) math identity for bitsum_fits: equivalent to 2^n ≤ p.
// Independent check: compute 2^n via BigUint shift and compare to p.
#[test]
fn prop_bitsum_fits_equivalent_to_2pow_le_p() {
    for &prime in &[2u32, 3, 5, 7, 11, 13, 17, 31, 257, 65537] {
        let p = BigUint::from(prime);
        for n in 0usize..40 {
            let two_n = BigUint::from(1u32) << n;
            let expected = two_n <= p;
            assert_eq!(
                bitsum_fits(n, &p),
                expected,
                "bitsum_fits({}, {}) disagrees with (2^n ≤ p)",
                n,
                prime
            );
        }
    }
}

// PROPERTY (1) bitsum_fits monotone in `n` for any fixed `p`:
// if bitsum_fits(n, p) is false, then bitsum_fits(n+1, p) is false.
// Math: 2^n > p ⇒ 2^(n+1) > p.
#[test]
fn prop_bitsum_fits_monotone_in_len() {
    for &prime in &[2u32, 3, 5, 7, 11, 13, 17, 257] {
        let p = BigUint::from(prime);
        let mut once_false = false;
        for n in 0usize..30 {
            let fits = bitsum_fits(n, &p);
            if once_false {
                assert!(
                    !fits,
                    "bitsum_fits non-monotone at p={}, n={}",
                    prime, n
                );
            }
            if !fits { once_false = true; }
        }
    }
}

// PROPERTY (1) bitsum_fits at boundary: for prime p with 2^k = p (none in
// our test set since all are odd primes), but the relation `2^k ≤ p` is
// strict-inequality-safe — independent math: 2^n = p ⇒ fits true; we
// check the boundary at p=2 (only even prime).
#[test]
fn prop_bitsum_fits_boundary_p_eq_2() {
    let p = BigUint::from(2u32);
    // 2^0=1 ≤ 2 ✓
    assert!(bitsum_fits(0, &p));
    // 2^1=2 ≤ 2 ✓ (boundary equality)
    assert!(bitsum_fits(1, &p));
    // 2^2=4 > 2 ✗
    assert!(!bitsum_fits(2, &p));
}

// PROPERTY (7) edge primes: bitsum_fits for GF(2), GF(3), GF(5).
// Independent: max chain length is floor(log2 p).
#[test]
fn prop_bitsum_fits_max_chain_len_matches_floor_log2() {
    // (prime, expected_max_len) where max_len is the largest n with 2^n ≤ p.
    for &(prime, expected) in &[
        (2u32, 1usize),  // 2^1 = 2 ≤ 2; 2^2 = 4 > 2
        (3, 1),          // 2^1 = 2 ≤ 3; 2^2 = 4 > 3
        (5, 2),          // 2^2 = 4 ≤ 5; 2^3 = 8 > 5
        (7, 2),          // 2^2 = 4 ≤ 7; 2^3 = 8 > 7
        (11, 3),         // 2^3 = 8 ≤ 11; 2^4 = 16 > 11
        (13, 3),
        (17, 4),         // 2^4 = 16 ≤ 17; 2^5 = 32 > 17
        (31, 4),
        (257, 8),        // 2^8 = 256 ≤ 257; 2^9 = 512 > 257
    ] {
        let p = BigUint::from(prime);
        // Independent: compute max_n by enumeration.
        let mut n = 0usize;
        while bitsum_fits(n + 1, &p) { n += 1; }
        assert_eq!(
            n, expected,
            "p={}: bitsum_fits's max chain length = {}, expected {}",
            prime, n, expected
        );
    }
}

// PROPERTY (1) detect_bit_constraint accept ↔ math identity.
// Spec: accepts (c·x^2 + d·x = 0) iff (c + d) ≡ 0 (mod p) AND both
// terms reference the SAME single variable. Sweep many (c, d, prime).
#[test]
fn prop_detect_bit_constraint_matches_math_definition() {
    for &prime in &[7u32, 11, 13, 17, 257] {
        let p = BigUint::from(prime);
        for c in 1u32..prime {
            for d in 0u32..prime {
                let eq = vec![
                    PolyTerm {
                        coeff: BigUint::from(c),
                        vars: vec![(0u32, 2)],
                    },
                    PolyTerm {
                        coeff: BigUint::from(d),
                        vars: vec![(0u32, 1)],
                    },
                ];
                let expected = ((c + d) % prime) == 0;
                let got = detect_bit_constraint(&eq, &p).is_some();
                assert_eq!(
                    got, expected,
                    "p={} c={} d={}: detect_bit_constraint vs (c+d)≡0",
                    prime, c, d
                );
            }
        }
    }
}

// PROPERTY (1) detect_bit_constraint rejects mismatched vars regardless
// of (c+d) ≡ 0. Math spec: must be the SAME variable.
#[test]
fn prop_detect_bit_constraint_rejects_two_vars() {
    let p = BigUint::from(17u32);
    // c=1, d=16 with (1+16) = 17 ≡ 0 (mod 17): sum is zero, but the two
    // terms reference distinct vars (0 vs 1). Must still reject.
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(0u32, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(16u32),
            vars: vec![(1u32, 1)],
        },
    ];
    assert_eq!(detect_bit_constraint(&eq, &p), None);
}

// PROPERTY (8) determinism: detect_bit_constraint is a pure function.
// Same input → same output across calls.
#[test]
fn prop_detect_bit_constraint_pure() {
    let p = BigUint::from(7u32);
    let eq = vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(2u32, 2)],
        },
        PolyTerm {
            coeff: BigUint::from(6u32),
            vars: vec![(2u32, 1)],
        },
    ];
    let r1 = detect_bit_constraint(&eq, &p);
    let r2 = detect_bit_constraint(&eq, &p);
    assert_eq!(r1, r2);
    assert_eq!(r1, Some(2));
}

// PROPERTY (1) find_bitsum_chain rejects non-power-of-two coefficient.
// Spec (b): the coefficient sequence must be c, 2c, 4c, .... Inserting
// a coefficient `3·c` (which is NOT 2^i·c for i ≤ k) between bit 0 and
// bit 1 must not extend the chain past length 1, so a chain that would
// have been length ≥ 2 is gated by the missing 2·c slot.
#[test]
fn prop_find_bitsum_chain_rejects_coeff_three_in_chain() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    // Coeffs: 1·b0, 3·b1 (NOT 2·b1), 4·b2. The 2·* slot is empty so
    // the chain stops after b0 (length 1, below MIN_AUTO_BITSUM_LEN=2).
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(3u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(2u32, 1)] },
    ];
    // min_len=2 → must return None (only base=1 yields length 1; bases 3,4
    // also yield length 1 since 2·3=6 missing and 2·4=8 missing).
    assert!(
        find_bitsum_chain(&eq, &bits, &p, 2).is_none(),
        "coefficient 3 (not 2^i·c) must NOT extend a chain"
    );
}

// PROPERTY (1) find_bitsum_chain rejects coefficient 5 in chain.
#[test]
fn prop_find_bitsum_chain_rejects_coeff_five_in_chain() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    // Coeffs: 1·b0, 5·b1, 4·b2. 2·1=2 absent so base=1 length=1; 2·5=10
    // absent so base=5 length=1; 2·4=8 absent so base=4 length=1.
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(5u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(2u32, 1)] },
    ];
    assert!(
        find_bitsum_chain(&eq, &bits, &p, 2).is_none(),
        "coefficient 5 (not 2^i·c) must NOT extend a chain"
    );
}

// PROPERTY (1) find_bitsum_chain rejects coefficient 6 in chain.
#[test]
fn prop_find_bitsum_chain_rejects_coeff_six_in_chain() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    // Coeffs: 1·b0, 6·b1, 4·b2.
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(2u32, 1)] },
    ];
    assert!(
        find_bitsum_chain(&eq, &bits, &p, 2).is_none(),
        "coefficient 6 (not 2^i·c) must NOT extend a chain"
    );
}

// PROPERTY (1) find_bitsum_chain accepts the EXACT power-of-two sequence
// {1, 2, 4, 8} for a length-4 chain. Independent math: coeffs are
// 2^0·c, 2^1·c, 2^2·c, 2^3·c with c=1. Then for c=3 (base=3) the
// extended sequence {3, 6, 12, 24} should also be accepted under GF(257)
// (large enough prime, no mod-p collision).
#[test]
fn prop_find_bitsum_chain_accepts_power_of_two_sequence() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32, 3u32].into_iter().collect();
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(2u32, 1)] },
        PolyTerm { coeff: BigUint::from(8u32), vars: vec![(3u32, 1)] },
    ];
    let (chain, base, _) =
        find_bitsum_chain(&eq, &bits, &p, 2).expect("length-4 chain");
    assert_eq!(chain.len(), 4);
    assert_eq!(base, BigUint::from(1u32));
}

// PROPERTY (1) find_bitsum_chain accepts a scaled sequence (base = 3
// over GF(257)): {3, 6, 12}. Independent math: 3·2^0, 3·2^1, 3·2^2.
#[test]
fn prop_find_bitsum_chain_accepts_scaled_sequence() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    let eq = vec![
        PolyTerm { coeff: BigUint::from(3u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(6u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(12u32), vars: vec![(2u32, 1)] },
    ];
    let (chain, base, _) =
        find_bitsum_chain(&eq, &bits, &p, 2).expect("length-3 chain");
    assert_eq!(chain.len(), 3);
    assert_eq!(base, BigUint::from(3u32));
}

// PROPERTY (1) find_bitsum_chain length cap: chain length must never
// exceed floor(log2 p). Independent math: compute the cap by enumeration
// and assert.
#[test]
fn prop_find_bitsum_chain_respects_floor_log2_cap() {
    for &prime in &[7u32, 11, 13, 17, 31] {
        let p = BigUint::from(prime);
        // Independent: enumerate floor(log2 p).
        let mut cap = 0usize;
        while bitsum_fits(cap + 1, &p) { cap += 1; }
        // Build a (cap+2)-bit chain. Source must cap at `cap`.
        let n = cap + 2;
        let bits: HashSet<VarIdx> = (0..n as u32).collect();
        let mut eq = Vec::new();
        let mut c = 1u32;
        for i in 0..n {
            eq.push(PolyTerm {
                coeff: BigUint::from(c % prime),
                vars: vec![(i as u32, 1)],
            });
            c = (c * 2) % prime;
        }
        if let Some((chain, _, _)) = find_bitsum_chain(&eq, &bits, &p, 2) {
            assert!(
                chain.len() <= cap,
                "p={}: chain length {} exceeds floor(log2 p) = {}",
                prime, chain.len(), cap
            );
        }
    }
}

// PROPERTY (8) determinism: find_bitsum_chain is a pure function.
#[test]
fn prop_find_bitsum_chain_deterministic() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32].into_iter().collect();
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(1u32, 1)] },
    ];
    let r1 = find_bitsum_chain(&eq, &bits, &p, 2);
    let r2 = find_bitsum_chain(&eq, &bits, &p, 2);
    assert_eq!(r1.is_some(), r2.is_some());
    if let (Some((c1, b1, _)), Some((c2, b2, _))) = (r1, r2) {
        assert_eq!(c1, c2);
        assert_eq!(b1, b2);
    }
}

// PROPERTY (4) min_len contract: find_bitsum_chain MUST NOT return a
// chain shorter than `min_len`. Math: any return is ≥ min_len.
#[test]
fn prop_find_bitsum_chain_respects_min_len() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = [0u32, 1u32, 2u32].into_iter().collect();
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(1u32, 1)] },
        PolyTerm { coeff: BigUint::from(4u32), vars: vec![(2u32, 1)] },
    ];
    // Ask for min_len = 5 (longer than possible).
    assert!(find_bitsum_chain(&eq, &bits, &p, 5).is_none());
    // Ask for min_len = 3 (just possible).
    let (chain, _, _) = find_bitsum_chain(&eq, &bits, &p, 3).expect("len-3 ok");
    assert!(chain.len() >= 3);
}

// PROPERTY (7) edge: empty equality must yield None.
#[test]
fn prop_find_bitsum_chain_empty_eq_is_none() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = HashSet::new();
    let eq: Vec<PolyTerm> = vec![];
    assert!(find_bitsum_chain(&eq, &bits, &p, 2).is_none());
}

// PROPERTY (7) edge: when `bits` is empty (no declared bit variables),
// no chain can be formed. Spec: the bucket-build step filters by bit
// membership, so the result must be None.
#[test]
fn prop_find_bitsum_chain_no_declared_bits_is_none() {
    let p = BigUint::from(257u32);
    let bits: HashSet<VarIdx> = HashSet::new();
    let eq = vec![
        PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0u32, 1)] },
        PolyTerm { coeff: BigUint::from(2u32), vars: vec![(1u32, 1)] },
    ];
    assert!(find_bitsum_chain(&eq, &bits, &p, 2).is_none());
}

// PROPERTY (8) auto_extract_bitsums determinism: same input → same output.
#[test]
fn prop_auto_extract_bitsums_deterministic() {
    let cs = cs_with(17, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        for bv in [b0, b1] {
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(bv, 2)] },
                PolyTerm { coeff: BigUint::from(16u32), vars: vec![(bv, 1)] },
            ]);
        }
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 1)] },
            PolyTerm { coeff: BigUint::from(2u32), vars: vec![(b1, 1)] },
            PolyTerm { coeff: BigUint::from(10u32), vars: vec![] },
        ]);
    });
    let out1 = auto_extract_bitsums(&cs);
    let out2 = auto_extract_bitsums(&cs);
    assert_eq!(out1.bitsums.len(), out2.bitsums.len());
    assert_eq!(out1.bitsums, out2.bitsums);
}

// PROPERTY (3) idempotence: auto_extract_bitsums(auto_extract_bitsums(x))
// must have the same number of bitsums as the first call. Once chains
// have been extracted into `__bitsum_N` aux vars, re-running cannot
// find new chains (the aux vars are not in `bits`).
#[test]
fn prop_auto_extract_bitsums_idempotent_bitsum_count() {
    let cs = cs_with(257, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        for bv in [b0, b1, b2] {
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(bv, 2)] },
                PolyTerm { coeff: BigUint::from(256u32), vars: vec![(bv, 1)] }, // -1 mod 257
            ]);
        }
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 1)] },
            PolyTerm { coeff: BigUint::from(2u32), vars: vec![(b1, 1)] },
            PolyTerm { coeff: BigUint::from(4u32), vars: vec![(b2, 1)] },
            PolyTerm { coeff: BigUint::from(5u32), vars: vec![] },
        ]);
    });
    let out1 = auto_extract_bitsums(&cs);
    let out2 = auto_extract_bitsums(&out1);
    assert_eq!(
        out1.bitsums.len(),
        out2.bitsums.len(),
        "second pass added more bitsums (non-idempotent)"
    );
}

// PROPERTY (7) edge: auto_extract over GF(2). Independent math:
// floor(log2 2) = 1, so cap = 1, so MIN_AUTO_BITSUM_LEN = 2 > cap and
// NO chain of admissible length can ever be extracted.
#[test]
fn prop_auto_extract_gf2_extracts_nothing() {
    let cs = cs_with(2, |b| {
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        // x^2 - x = x^2 + x mod 2: detect_bit_constraint requires
        // c+d ≡ 0 mod 2, so c=d=1 works (1+1 = 2 ≡ 0 mod 2).
        for bv in [b0, b1] {
            b.add_equality(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(bv, 2)] },
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![(bv, 1)] },
            ]);
        }
        // chain-shaped equality b0 + b1 (with 2 ≡ 0 mod 2 so b1's
        // coefficient is effectively 0; we use 1 so both are bit 0).
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b0, 1)] },
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(b1, 1)] },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    // Cap = 1 < MIN_AUTO_BITSUM_LEN = 2 → no chain extractable.
    assert_eq!(
        out.bitsums.len(),
        0,
        "GF(2) cap is 1 < MIN_AUTO_BITSUM_LEN=2; nothing must be extracted"
    );
}

// PROPERTY (7) edge: BN128-class prime. bitsum_fits at 253 holds and
// can support arbitrarily long bitsum chains (independent math: 2^253
// fits in the BN128 prime ~ 2^254).
#[test]
fn prop_bitsum_fits_bn128_long_chain() {
    let p = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    // Independent: enumerate cap; expected 253.
    let mut cap = 0usize;
    while bitsum_fits(cap + 1, &p) { cap += 1; }
    assert_eq!(cap, 253);
}

// PROPERTY (4) "no bit registered" passthrough invariant: if NO eq
// matches a bit constraint AND no explicit bitsum is present, the
// function returns a clone with the SAME number of equalities (cannot
// extract since `bits` is empty).
#[test]
fn prop_auto_extract_passthrough_when_no_bits_registered() {
    let cs = cs_with(17, |b| {
        let x = b.var("x");
        let y = b.var("y");
        // x + 2y + 3 = 0 (not a bit constraint).
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(2u32), vars: vec![(y, 1)] },
            PolyTerm { coeff: BigUint::from(3u32), vars: vec![] },
        ]);
    });
    let out = auto_extract_bitsums(&cs);
    assert_eq!(out.equalities.len(), cs.equalities.len());
    assert_eq!(out.bitsums.len(), 0);
    assert_eq!(out.prime, cs.prime);
    assert_eq!(out.var_names, cs.var_names);
}
