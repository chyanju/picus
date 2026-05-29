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
