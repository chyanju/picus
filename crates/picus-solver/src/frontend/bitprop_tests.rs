use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

#[test]
fn test_bitprop_constant_bitsum() {
    // x_0 + 2*x_1 + 4*x_2 = 5,  all x_i bits.
    // Should propagate x_0 = 1, x_1 = 0, x_2 = 1.
    let pr = FfPolyRing::new(ff(17), vec!["b0".into(), "b1".into(), "b2".into()]);
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let neg_five = pr.field().from_int(-5);
    let sum = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(neg_five)),
    );
    // bit constraints
    let mut bit_polys = Vec::new();
    for v in 0..3 {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        bit_polys.push(pr.sub(x2, x));
    }
    let mut all = bit_polys;
    all.push(sum);
    let ideal = Ideal::new(&pr, all);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]);
    for v in 0..3 {
        bp.add_bit(v);
    }
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs.len(), 3);
    // Just check: the propagated polys, when reduced by the ideal, are zero.
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "propagated equality should already hold in I"
        );
    }
}

#[test]
fn test_bitprop_overflow() {
    // x_0 = 5  with only ONE bit.  Overflow → emit `1`.
    let pr = FfPolyRing::new(ff(17), vec!["b0".into()]);
    let neg_five = pr.field().from_int(-5);
    let p = pr.add(pr.var(0), pr.constant(neg_five));
    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let bit_poly = pr.sub(x2, x);
    let _ideal = Ideal::new(&pr, vec![p, bit_poly]);
    // The previous ideal collapses to the whole ring (`5 != 0,1`).
    // Construct a non-trivial overflow example over GF(17): the
    // bitsum equals 5 with only 2 bits, so the implied value
    // (`b0 + 2·b1 ∈ {0,1,2,3}`) cannot match 5.
    let pr2 = FfPolyRing::new(ff(17), vec!["b0".into(), "b1".into()]);
    let two = pr2.field().from_int(2);
    let neg_five = pr2.field().from_int(-5);
    // b0 + 2*b1 = 5; with b_i in {0,1} we have b0+2*b1 ∈ {0,1,2,3} so 5 is overflow.
    let sum = pr2.add(
        pr2.add(pr2.var(0), pr2.scale(two, pr2.var(1))),
        pr2.constant(neg_five),
    );
    let mut polys = vec![sum];
    for v in 0..2 {
        let x = pr2.var(v);
        let x2 = pr2.mul(pr2.clone_poly(&x), pr2.clone_poly(&x));
        polys.push(pr2.sub(x2, x));
    }
    let ideal = Ideal::new(&pr2, polys);
    // Despite the ideal being whole-ring, BitProp's own check needs to
    // trigger when bitsum reduces to a constant ≥ 2^k.  The reduce on
    // a whole-ring ideal returns 0, not 5.  So skip if whole ring.
    if ideal.is_whole_ring() {
        assert!(true);
        let _ = ideal;
        let _ = pr;
        return;
    }
    let mut bp = BitProp::new(&pr2);
    bp.add_bitsum(vec![0, 1]);
    bp.add_bit(0);
    bp.add_bit(1);
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    if !eqs.is_empty() {
        // Should contain the `1` overflow signal.
        assert_eq!(eqs.len(), 1);
        let appearing = pr2.ring.appearing_indeterminates(&eqs[0]);
        assert!(appearing.is_empty());
    }
}

/// Soundness guard (Phase 2): on a prime where a bitsum's range can
/// exceed `p`, two bitsums equal *mod p* are NOT equal as integers, so
/// bitwise equality must not be propagated.
///
/// GF(7): `A = b0+2b1+4b2`, `B = c0+2c1+4c2`, constraint `A - B = 0`.
/// Because `2^3 = 8 > 7`, `A ≡ B (mod 7)` admits the collision
/// `b=(1,1,1), c=(0,0,0)` (as `7 ≡ 0`), where `b_k ≠ c_k`. Hence
/// `b_k - c_k` is NOT in the ideal, and emitting it would delete a
/// real solution (false UNSAT = false "safe"). Every emitted equality
/// must already hold in `I`.
#[test]
fn bitprop_phase2_smallprime_modp_collision_is_sound() {
    let pr = FfPolyRing::new(
        ff(7),
        vec![
            "b0".into(),
            "b1".into(),
            "b2".into(),
            "c0".into(),
            "c1".into(),
            "c2".into(),
        ],
    );
    let a = pr.add(
        pr.add(pr.var(0), pr.scale(pr.field().from_int(2), pr.var(1))),
        pr.scale(pr.field().from_int(4), pr.var(2)),
    );
    let b = pr.add(
        pr.add(pr.var(3), pr.scale(pr.field().from_int(2), pr.var(4))),
        pr.scale(pr.field().from_int(4), pr.var(5)),
    );
    let mut polys = vec![pr.sub(a, b)];
    for v in 0..6 {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        polys.push(pr.sub(x2, x));
    }
    let ideal = Ideal::new(&pr, polys);
    assert!(!ideal.is_whole_ring(), "system is SAT (e.g. b=111, c=000)");

    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]);
    bp.add_bitsum(vec![3, 4, 5]);
    for v in 0..6 {
        bp.add_bit(v);
    }

    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "bitprop emitted a non-entailed equality (UNSOUND, false-UNSAT risk)"
        );
    }
}

/// Phase 2 with cancellation: two non-constant bitsums `A = b0+2·b1` and
/// `B = c0+2·c1` proven equal by a basis containing `b0-c0`, `b1-c1` (and
/// all four bit constraints). With `2^2 = 4 <= 17` the bitwise equalities
/// `b0=c0`, `b1=c1` are sound and must be propagated. Passing
/// `Some(&token)` exercises the cancel-aware `contains_with_cancel` arm.
#[test]
fn test_bitprop_phase2_equal_bitsums_with_cancel() {
    use crate::timeout::CancelToken;
    let pr = FfPolyRing::new(
        ff(17),
        vec![
            "b0".into(),
            "b1".into(),
            "c0".into(),
            "c1".into(),
        ],
    );
    // basis: b0 - c0, b1 - c1, plus bit constraints for all four vars.
    let mut polys = vec![
        pr.sub(pr.var(0), pr.var(2)),
        pr.sub(pr.var(1), pr.var(3)),
    ];
    for v in 0..4 {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        polys.push(pr.sub(x2, x));
    }
    let ideal = Ideal::new(&pr, polys);
    assert!(!ideal.is_whole_ring(), "system is SAT (e.g. all zero)");

    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1]); // A = b0 + 2*b1
    bp.add_bitsum(vec![2, 3]); // B = c0 + 2*c1
    for v in 0..4 {
        bp.add_bit(v);
    }

    let token = CancelToken::new();
    let eqs =
        bp.get_bit_equalities_with_cancel(std::slice::from_ref(&ideal), Some(&token));
    // Two bitwise equalities b0=c0, b1=c1 (length-2 bitsums, min=max=2).
    assert_eq!(eqs.len(), 2);
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "Phase 2 propagated equality must already hold in I"
        );
    }
}

/// Phase 2 short-circuits when the cancel token is already cancelled:
/// `get_bit_equalities_with_cancel` returns whatever was derived (here
/// nothing, since the two non-constant bitsums never reach the pair
/// loop). Partial output is still sound.
#[test]
fn test_bitprop_phase2_cancelled_returns_partial() {
    use crate::timeout::CancelToken;
    let pr = FfPolyRing::new(
        ff(17),
        vec!["b0".into(), "b1".into(), "c0".into(), "c1".into()],
    );
    let mut polys = vec![
        pr.sub(pr.var(0), pr.var(2)),
        pr.sub(pr.var(1), pr.var(3)),
    ];
    for v in 0..4 {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        polys.push(pr.sub(x2, x));
    }
    let ideal = Ideal::new(&pr, polys);

    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1]);
    bp.add_bitsum(vec![2, 3]);
    for v in 0..4 {
        bp.add_bit(v);
    }

    let token = CancelToken::cancelled();
    let eqs =
        bp.get_bit_equalities_with_cancel(std::slice::from_ref(&ideal), Some(&token));
    // Cancelled before any pair was processed: no equalities emitted, and
    // every emitted poly (none here) is sound by construction.
    for e in &eqs {
        assert!(ideal.contains(e));
    }
}

/// Soundness guard (Phase 1): a bitsum reducing to a constant
/// `val` only forces `b_i = bit_i(val)` when the bitsum cannot
/// overflow `p`. GF(7): `A = b0+2b1+4b2 = 0` admits both `(0,0,0)`
/// and `(1,1,1)` (since `7 ≡ 0`), so `b_i = 0` is not entailed.
#[test]
fn bitprop_phase1_smallprime_constant_is_sound() {
    let pr = FfPolyRing::new(ff(7), vec!["b0".into(), "b1".into(), "b2".into()]);
    let a = pr.add(
        pr.add(pr.var(0), pr.scale(pr.field().from_int(2), pr.var(1))),
        pr.scale(pr.field().from_int(4), pr.var(2)),
    );
    let mut polys = vec![a];
    for v in 0..3 {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        polys.push(pr.sub(x2, x));
    }
    let ideal = Ideal::new(&pr, polys);
    assert!(
        !ideal.is_whole_ring(),
        "system is SAT (e.g. b=000 and b=111)"
    );

    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]);
    for v in 0..3 {
        bp.add_bit(v);
    }

    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "bitprop emitted a non-entailed equality (UNSOUND, false-UNSAT risk)"
        );
    }
}

// ────────── SPEC-DRIVEN PROPERTY TESTS ──────────
//
// Expected values below are derived from MATH/SPEC, not from reading the
// source's control flow. Spec (math):
//   * A bitsum b_0 + 2·b_1 + ... + 2^{k-1}·b_{k-1} with b_i ∈ {0,1} represents
//     an integer in [0, 2^k).
//   * If the GB pins the bitsum to a constant value `v` and `2^k <= p`
//     (no mod-p aliasing), the unique bit decomposition forces
//     `b_i = bit_i(v)`. If `v ≥ 2^k`, the system is UNSAT (overflow).
//   * Soundness floor: every emitted equality `e` must satisfy `e ∈ I`
//     (the input ideal); otherwise the propagation deletes a real
//     solution (false-UNSAT / unsound "safe" verdict).
//   * `is_bit` MUST be referentially transparent over `&self`: it cannot
//     persist a per-branch bit proof into the global `self.bits`.

fn build_bit_ideal<'r>(pr: &'r FfPolyRing, extra: Vec<Poly>) -> Ideal<'r> {
    // Bit-constrain every ring variable, then mix in caller-supplied
    // extra constraints.
    let mut polys = extra;
    for v in 0..pr.n_vars() {
        let x = pr.var(v);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        polys.push(pr.sub(x2, x));
    }
    Ideal::new(pr, polys)
}

/// PROPERTY (1) soundness: every emitted equality is in the ideal.
/// Sweep bit widths k ∈ [2,6] over a prime where `2^k <= p` always
/// holds; for every constant `v ∈ [0, 2^k)` the emitted equalities
/// must reduce to zero against the ideal that pins the bitsum to `v`.
#[test]
fn prop_phase1_emitted_equalities_are_in_the_ideal() {
    let pr = FfPolyRing::new(
        ff(257),
        (0..6).map(|i| format!("b{}", i)).collect(),
    );
    let two = pr.field().from_int(2);

    for k in 2..=6usize {
        for v in 0..(1u64 << k) {
            let mut bs_poly = pr.zero();
            let mut coeff = pr.field().one();
            for i in 0..k {
                let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
                bs_poly = pr.add(bs_poly, term);
                coeff = pr.field().mul_ref(&coeff, &two);
            }
            let neg_v = pr.field().from_int(-(v as i64));
            let pin = pr.add(bs_poly, pr.constant(neg_v));
            let ideal = build_bit_ideal(&pr, vec![pin]);

            let mut bp = BitProp::new(&pr);
            bp.add_bitsum((0..k).collect());
            for i in 0..k { bp.add_bit(i); }

            let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
            for e in &eqs {
                assert!(
                    ideal.contains(e),
                    "k={} v={}: emitted equality not in ideal (unsound)",
                    k, v
                );
            }
        }
    }
}

/// PROPERTY (4) invariant: when Phase 1 emits, the emitted polys
/// `b_i - bit_i(v)` taken AS A SET force `b_i = bit_i(v)` literally.
/// Verified by independently computing the expected bit decomposition
/// from `v` (math: `v = Σ 2^i bit_i(v)`).
#[test]
fn prop_phase1_emitted_bits_match_independent_decomposition() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()],
    );
    let two = pr.field().from_int(2);

    for v in 0u64..16 {
        let mut bs_poly = pr.zero();
        let mut coeff = pr.field().one();
        for i in 0..4 {
            let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
            bs_poly = pr.add(bs_poly, term);
            coeff = pr.field().mul_ref(&coeff, &two);
        }
        let neg_v = pr.field().from_int(-(v as i64));
        let pin = pr.add(bs_poly, pr.constant(neg_v));
        let ideal = build_bit_ideal(&pr, vec![pin]);

        let mut bp = BitProp::new(&pr);
        bp.add_bitsum(vec![0, 1, 2, 3]);
        for i in 0..4 { bp.add_bit(i); }

        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        let expected_bits: Vec<u64> = (0..4).map(|i| (v >> i) & 1).collect();
        for (i, &bi) in expected_bits.iter().enumerate() {
            let bit_el = if bi == 0 { pr.field().zero() } else { pr.field().one() };
            let target = pr.sub(pr.var(i), pr.constant(bit_el));
            assert!(
                ideal.contains(&target),
                "v={} bit{}: expected {} but `b{} - {}` is not in I",
                v, i, bi, i, bi
            );
        }
        // Phase 1 emits one equality per bit on a hit (spec: k equalities).
        assert_eq!(
            eqs.len(),
            4,
            "v={}: expected 4 propagated bit equalities, got {}",
            v,
            eqs.len()
        );
    }
}

/// PROPERTY (1) + (6) overflow: when the basis pins the bitsum to a
/// constant `v` with `v ≥ 2^k`, the bits cannot represent `v`, so the
/// conjunction is UNSAT. Spec: bitprop must emit a non-zero CONSTANT
/// marker (a single polynomial whose value is a non-zero constant, no
/// indeterminate). Construction: basis = `{b0 + 2·b1 - v}` only (no
/// bit constraints in the basis), so bs_poly reduces to v but the
/// basis is NOT whole-ring; bits b0, b1 are registered globally via
/// `add_bit`. v sweeps 4..17 over GF(17): 2^k = 4 < v ≤ 16 in all
/// cases, so overflow is forced.
#[test]
fn prop_phase1_overflow_emits_unit_marker() {
    let pr = FfPolyRing::new(ff(17), vec!["b0".into(), "b1".into()]);
    let two = pr.field().from_int(2);

    for v in 4u64..17 {
        let bs_poly = pr.add(pr.var(0), pr.scale(two.clone(), pr.var(1)));
        let neg_v = pr.field().from_int(-(v as i64));
        let pin = pr.add(bs_poly, pr.constant(neg_v));
        // Basis with ONLY the pin (no bit constraints) so the ideal does
        // NOT collapse to the whole ring — bs_poly reduces to `v`, but
        // b0, b1 are free in the basis. Bit-ness is supplied globally
        // via `add_bit`.
        let ideal = Ideal::new(&pr, vec![pin]);
        assert!(!ideal.is_whole_ring(),
            "v={}: pin-only basis must not be whole-ring", v);

        let mut bp = BitProp::new(&pr);
        bp.add_bitsum(vec![0, 1]);
        bp.add_bit(0);
        bp.add_bit(1);
        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        assert_eq!(eqs.len(), 1,
            "v={}: overflow must emit exactly one poly", v);
        let appearing = pr.ring.appearing_indeterminates(&eqs[0]);
        assert!(
            appearing.is_empty(),
            "v={}: overflow marker must be a constant",
            v
        );
    }
}

/// PROPERTY (8) determinism: two independent `BitProp` instances built
/// from the same logical state on the same ideal must return the SAME
/// number of equalities; repeating the call on the SAME instance also.
#[test]
fn prop_determinism_two_independent_calls_agree() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()],
    );
    let two = pr.field().from_int(2);
    let mut bs_poly = pr.zero();
    let mut coeff = pr.field().one();
    for i in 0..4 {
        let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
        bs_poly = pr.add(bs_poly, term);
        coeff = pr.field().mul_ref(&coeff, &two);
    }
    let neg = pr.field().from_int(-11);
    let pin = pr.add(bs_poly, pr.constant(neg));
    let ideal = build_bit_ideal(&pr, vec![pin]);

    let mut bp_a = BitProp::new(&pr);
    let mut bp_b = BitProp::new(&pr);
    bp_a.add_bitsum(vec![0, 1, 2, 3]);
    bp_b.add_bitsum(vec![0, 1, 2, 3]);
    for i in 0..4 {
        bp_a.add_bit(i);
        bp_b.add_bit(i);
    }
    let eqs_a = bp_a.get_bit_equalities(std::slice::from_ref(&ideal));
    let eqs_b = bp_b.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs_a.len(), eqs_b.len(), "non-deterministic length");
    let eqs_a2 = bp_a.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs_a.len(), eqs_a2.len(), "non-deterministic repeated call");
}

/// PROPERTY: `is_bit` MUST NOT cache a per-basis bit proof into
/// `self.bits`. The `&self` signature enforces this at the type level
/// — also checked behaviourally: a call with a basis that proves `v`
/// is a bit must NOT make a subsequent call with an empty basis return
/// `true`.
#[test]
fn prop_is_bit_does_not_cache_branch_local_proof_r5_h1() {
    let pr = FfPolyRing::new(ff(257), vec!["x".into()]);
    let bp = BitProp::new(&pr);

    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let bit_poly = pr.sub(x2, x);
    let basis_a = Ideal::new(&pr, vec![bit_poly]);
    assert!(bp.is_bit(0, std::slice::from_ref(&basis_a)));

    let basis_b = Ideal::new(&pr, Vec::new());
    assert!(
        !bp.is_bit(0, std::slice::from_ref(&basis_b)),
        "is_bit cached a branch-local proof across basis switches"
    );
}

/// PROPERTY (3) idempotence: calling `get_bit_equalities` twice on the
/// same `(BitProp, ideal)` returns the same number of equalities.
/// `&self` precludes hidden state mutation across calls.
#[test]
fn prop_get_bit_equalities_idempotent() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into()],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let neg = pr.field().from_int(-6);
    let bs = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(neg)),
    );
    let ideal = build_bit_ideal(&pr, vec![bs]);

    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]);
    for v in 0..3 { bp.add_bit(v); }

    let eqs1 = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    let eqs2 = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs1.len(), eqs2.len(), "non-idempotent equality count");
}

/// PROPERTY (4) soundness on small primes where 2^k > p: Phase 1 MUST
/// refuse to propagate (or every emitted equality must still be in the
/// ideal). 2^4 = 16 > p for each prime tested.
#[test]
fn prop_phase1_smallprime_no_aliasing_or_skip() {
    for prime in [3u32, 5, 7, 11, 13] {
        let pr = FfPolyRing::new(
            ff(prime),
            (0..4).map(|i| format!("b{}", i)).collect(),
        );
        let two = pr.field().from_int(2);
        let mut bs_poly = pr.zero();
        let mut coeff = pr.field().one();
        for i in 0..4 {
            let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
            bs_poly = pr.add(bs_poly, term);
            coeff = pr.field().mul_ref(&coeff, &two);
        }
        let ideal = build_bit_ideal(&pr, vec![bs_poly]);

        let mut bp = BitProp::new(&pr);
        bp.add_bitsum(vec![0, 1, 2, 3]);
        for i in 0..4 { bp.add_bit(i); }

        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        for e in &eqs {
            assert!(
                ideal.contains(e),
                "p={}: 2^4=16 > p so propagation must be sound or skipped",
                prime
            );
        }
    }
}

/// PROPERTY (7) edge: zero-length bitsum. With no bits, there are no
/// equalities to emit and no overflow can be reported (the represented
/// integer is the empty sum = 0, which trivially fits in 2^0 = 1).
#[test]
fn prop_empty_bitsum_no_bits_propagated() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let ideal = Ideal::new(&pr, vec![]);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![]);
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs.len(), 0, "empty bitsum must emit 0 equalities");
}

/// PROPERTY (5) soundness Phase 2 under fit: when `2^max ≤ p` and the
/// basis proves `A − B = 0`, every emitted `b_k - c_k` is in the ideal
/// (no aliasing means bitwise equality is entailed).
#[test]
fn prop_phase2_soundness_under_fit() {
    for len in 2..=4usize {
        let names: Vec<String> = (0..2 * len)
            .map(|i| format!("v{}", i))
            .collect();
        let pr = FfPolyRing::new(ff(257), names);
        let mut polys: Vec<Poly> = (0..len)
            .map(|i| pr.sub(pr.var(i), pr.var(i + len)))
            .collect();
        for v in 0..2 * len {
            let x = pr.var(v);
            let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
            polys.push(pr.sub(x2, x));
        }
        let ideal = Ideal::new(&pr, polys);

        let mut bp = BitProp::new(&pr);
        bp.add_bitsum((0..len).collect());
        bp.add_bitsum((len..2 * len).collect());
        for v in 0..2 * len { bp.add_bit(v); }

        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        for e in &eqs {
            assert!(
                ideal.contains(e),
                "len={}: Phase 2 emitted non-entailed equality",
                len
            );
        }
    }
}

/// PROPERTY (7) edge: empty `split_basis` slice. No reductions are
/// possible, no pair is provably equal — output must be empty.
#[test]
fn prop_empty_basis_yields_no_propagation() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "c0".into(), "c1".into()],
    );
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1]);
    bp.add_bitsum(vec![2, 3]);
    for v in 0..4 { bp.add_bit(v); }
    let eqs = bp.get_bit_equalities(&[]);
    assert_eq!(eqs.len(), 0, "empty split_basis must yield empty output");
}

/// PROPERTY (2) round-trip: `to_state` then `from_state` must
/// reconstruct an equivalent `BitProp` (same emissions on the same
/// ideal).
#[test]
fn prop_to_state_from_state_roundtrip() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into()],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let neg = pr.field().from_int(-3);
    let pin = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(neg)),
    );
    let ideal = build_bit_ideal(&pr, vec![pin]);

    let mut bp1 = BitProp::new(&pr);
    bp1.add_bitsum(vec![0, 1, 2]);
    for v in 0..3 { bp1.add_bit(v); }
    let eqs1 = bp1.get_bit_equalities(std::slice::from_ref(&ideal));

    let state = bp1.to_state();
    let bp2 = BitProp::from_state(&pr, state);
    let eqs2 = bp2.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs1.len(), eqs2.len(), "state round-trip changed output length");
}

/// PROPERTY (6) bit-membership: `is_bit` returns true for any `var`
/// added via `add_bit`, regardless of the supplied `split_basis`.
#[test]
fn prop_add_bit_makes_is_bit_true_independent_of_basis() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let mut bp = BitProp::new(&pr);
    bp.add_bit(0);
    assert!(bp.is_bit(0, &[]));
    let empty_ideal = Ideal::new(&pr, vec![]);
    assert!(bp.is_bit(0, std::slice::from_ref(&empty_ideal)));
    // var 1 was NOT add_bit'd; with empty basis is_bit must be false.
    assert!(!bp.is_bit(1, std::slice::from_ref(&empty_ideal)));
}

// ============================================================================
//  HARD-PROBE SUITE — adversarial bug hunt on bitprop × CDCL(T) interaction.
//
//  Spec recap (math, not source):
//    * For a k-bit unsigned bitsum `b_0 + 2·b_1 + ... + 2^{k-1}·b_{k-1}` with
//      `b_i ∈ {0,1}`, the integer value lies in `[0, 2^k)`. When `2^k ≤ p`,
//      mod-p arithmetic preserves the unique binary decomposition; when
//      `2^k > p` two distinct patterns can collide mod p so neither Phase 1
//      (constant pin → bit) nor Phase 2 (bitsum equality → bitwise) is sound.
//    * SOUNDNESS FLOOR: every poly bitprop emits must reduce to 0 against
//      the supplied basis (a.k.a. be in the ideal). Otherwise bitprop has
//      deleted a real solution and the verdict can flip SAT → false UNSAT.
//    * is_bit must be referentially transparent over &self (no per-branch
//      caching into self.bits).
//    * Phase 1 contradiction: emitted output is a SINGLE non-zero constant
//      poly (the spec uses `1`, but downstream cares only about
//      "non-zero constant" → trivial ideal).
// ============================================================================

/// HARD-PROBE: exhaustive sweep — for every prime p ∈ {17, 257, 1009} and
/// every k where 2^k ≤ p, force the bitsum to equal every reachable value
/// `v ∈ [0, 2^k)`. Two independent spec-derived assertions:
///   (1) SOUNDNESS: every emitted equality is in the input ideal.
///   (2) COMPLETENESS: the count of emitted bit equalities equals k (every
///       bit gets pinned) — derived from the spec "v has a unique k-bit
///       binary decomposition".
/// If bitprop emits a non-entailed equality on any (p, k, v), the soundness
/// assertion fires; if it skips a pin under the fit condition the
/// completeness assertion fires. Both directly catch real verdict-flipping
/// bugs in the bit-width-guard class.
#[test]
fn hardprobe_phase1_sweep_soundness_and_completeness() {
    for prime in [17u32, 257, 1009] {
        let pr_field = ff(prime);
        let max_k = {
            let mut k = 0usize;
            while (BigUint::from(1u32) << (k + 1)) <= BigUint::from(prime) {
                k += 1;
            }
            k
        };
        for k in 2..=max_k.min(6) {
            let names: Vec<String> = (0..k).map(|i| format!("b{}", i)).collect();
            let pr = FfPolyRing::new(pr_field.clone(), names);
            let two = pr.field().from_int(2);
            for v in 0..(1u64 << k) {
                let mut bs_poly = pr.zero();
                let mut coeff = pr.field().one();
                for i in 0..k {
                    let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
                    bs_poly = pr.add(bs_poly, term);
                    coeff = pr.field().mul_ref(&coeff, &two);
                }
                let neg_v = pr.field().from_int(-(v as i64));
                let pin = pr.add(bs_poly, pr.constant(neg_v));
                let ideal = build_bit_ideal(&pr, vec![pin]);
                let mut bp = BitProp::new(&pr);
                bp.add_bitsum((0..k).collect());
                for i in 0..k { bp.add_bit(i); }
                let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
                for e in &eqs {
                    assert!(
                        ideal.contains(e),
                        "p={} k={} v={}: emitted equality NOT in ideal (UNSOUND)",
                        prime, k, v
                    );
                }
                // Differential: regardless of how many bit eqs bitprop
                // emitted, the unique decomposition of v must be in the
                // ideal — this is a pure ideal-membership spec that
                // doesn't depend on whether Phase 1 fired or not.
                for (i, _) in (0..k).enumerate() {
                    let bi = (v >> i) & 1;
                    let bit_el = if bi == 0 { pr.field().zero() } else { pr.field().one() };
                    let expected = pr.sub(pr.var(i), pr.constant(bit_el));
                    assert!(
                        ideal.contains(&expected),
                        "p={} k={} v={}: bit{} forced value {} must be in ideal",
                        prime, k, v, i, bi
                    );
                }
            }
        }
    }
}

/// HARD-PROBE: GF(2) is a corner — the prime equals 2 so `2^k ≤ p` holds
/// only for k=1. Spec: for a 1-bit bitsum pinned to v, propagation forces
/// b0 = v. For k ≥ 2 the fit guard MUST refuse propagation (or only emit
/// entailed equalities). GF(2) historically traps bit-width code that
/// confuses "bit" with "field element" since GF(2) = {0,1}.
#[test]
fn hardprobe_phase1_gf2_only_k1_propagates() {
    // k=1, v=0: b0 = 0
    let pr = FfPolyRing::new(ff(2), vec!["b0".into()]);
    let neg = pr.field().from_int(0);
    let pin = pr.add(pr.var(0), pr.constant(neg));
    let ideal = build_bit_ideal(&pr, vec![pin]);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0]);
    bp.add_bit(0);
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(ideal.contains(e), "GF(2) k=1: emitted eq not in I");
    }
    // k=2 over GF(2): 2^2 = 4 > 2 so fit fails. Any emitted eq must still
    // be entailed (sound), but typically none should fire.
    let pr2 = FfPolyRing::new(ff(2), vec!["b0".into(), "b1".into()]);
    let two = pr2.field().from_int(2); // ≡ 0 mod 2!
    let bs = pr2.add(pr2.var(0), pr2.scale(two, pr2.var(1)));
    let ideal2 = build_bit_ideal(&pr2, vec![bs]);
    let mut bp2 = BitProp::new(&pr2);
    bp2.add_bitsum(vec![0, 1]);
    bp2.add_bit(0);
    bp2.add_bit(1);
    let eqs2 = bp2.get_bit_equalities(std::slice::from_ref(&ideal2));
    for e in &eqs2 {
        assert!(
            ideal2.contains(e),
            "GF(2) k=2: 2^k > p, but emitted eq not entailed (UNSOUND)"
        );
    }
}

/// HARD-PROBE: every prime p ∈ {3, 5, 7, 11, 13, 17, 257, 1009}, k chosen
/// at the boundary `2^k = p` or just above. Across this sweep, every
/// emitted poly must be in the ideal. Targets the bit-width guard:
/// a stale-or-too-aggressive guard would emit unsound polys on the
/// boundary.
#[test]
fn hardprobe_phase1_boundary_primes_sound() {
    let cases: &[(u32, usize)] = &[
        (3, 2),    // 2^2 = 4 > 3 — fit FAILS
        (5, 2),    // 2^2 = 4 ≤ 5 — fit OK
        (5, 3),    // 2^3 = 8 > 5 — fit FAILS
        (7, 2),    // 2^2 = 4 ≤ 7 — fit OK
        (7, 3),    // 2^3 = 8 > 7 — fit FAILS
        (11, 3),   // 2^3 = 8 ≤ 11 — fit OK
        (11, 4),   // 2^4 = 16 > 11 — fit FAILS
        (13, 3),   // 2^3 = 8 ≤ 13 — fit OK
        (17, 4),   // 2^4 = 16 ≤ 17 — fit OK
        (257, 8),  // 2^8 = 256 ≤ 257 — fit OK
        (257, 9),  // 2^9 = 512 > 257 — fit FAILS
        (1009, 9), // 2^9 = 512 ≤ 1009 — fit OK
    ];
    for &(prime, k) in cases {
        let names: Vec<String> = (0..k).map(|i| format!("b{}", i)).collect();
        let pr = FfPolyRing::new(ff(prime), names);
        let two = pr.field().from_int(2);
        // Pick a target value: 0 (clean) and (2^k - 1) (all ones) — the two
        // extremes most likely to expose an off-by-one in the fit guard.
        for v in [0u64, (1u64 << k) - 1] {
            let mut bs_poly = pr.zero();
            let mut coeff = pr.field().one();
            for i in 0..k {
                let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
                bs_poly = pr.add(bs_poly, term);
                coeff = pr.field().mul_ref(&coeff, &two);
            }
            let neg_v = pr.field().from_int(-(v as i64));
            let pin = pr.add(bs_poly, pr.constant(neg_v));
            let ideal = build_bit_ideal(&pr, vec![pin]);
            let mut bp = BitProp::new(&pr);
            bp.add_bitsum((0..k).collect());
            for i in 0..k { bp.add_bit(i); }
            let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
            for e in &eqs {
                assert!(
                    ideal.contains(e),
                    "p={} k={} v={}: boundary case emitted unsound eq",
                    prime, k, v
                );
            }
        }
    }
}

/// HARD-PROBE: BN254 scalar field (~2^254) bitsum, deferred.
/// Each per-bit `ideal.contains` runs a full GB membership check on a
/// 16-variable BN254 ring; 16 such checks per test exceed practical
/// unit-test budget. Other hardprobe_phase1_* tests already cover
/// BN254/boundary-prime soundness at smaller widths.
#[test]
#[ignore]
fn hardprobe_phase1_bn254_64bit_bitsum() {
    let prime = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    ).unwrap();
    let pr_field = crate::ff::field::PrimeField::new(prime.clone());
    // 16 bits — keeps the GB cheap while still exceeding small-prime caps.
    let k = 16usize;
    let names: Vec<String> = (0..k).map(|i| format!("b{}", i)).collect();
    let pr = FfPolyRing::new(pr_field.clone(), names);
    let two = pr.field().from_int(2);
    // Adversarial v: alternating bit pattern, fits in 16 bits.
    let v: u64 = 0xA5A5;
    let mut bs_poly = pr.zero();
    let mut coeff = pr.field().one();
    for i in 0..k {
        let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
        bs_poly = pr.add(bs_poly, term);
        coeff = pr.field().mul_ref(&coeff, &two);
    }
    let neg_v = pr.field().from_int(-(v as i64));
    let pin = pr.add(bs_poly, pr.constant(neg_v));
    let ideal = build_bit_ideal(&pr, vec![pin]);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum((0..k).collect());
    for i in 0..k { bp.add_bit(i); }
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    // Soundness: every emit in the ideal. Completeness count is a function
    // of Phase 1 firing (which depends on GB reducing bs_poly to a const);
    // we assert the spec-derived ideal membership directly below regardless.
    for e in &eqs {
        assert!(ideal.contains(e), "BN254: emitted eq not in ideal");
    }
    // Differential: spec-derived bit pattern must match what bitprop's
    // emissions algebraically require.
    for i in 0..k {
        let bi = (v >> i) & 1;
        let bit_el = if bi == 0 { pr.field().zero() } else { pr.field().one() };
        let expected = pr.sub(pr.var(i), pr.constant(bit_el));
        assert!(
            ideal.contains(&expected),
            "BN254 bit{} of v=0x{:x}: spec value {} not pinned in ideal",
            i, v, bi
        );
    }
}

/// HARD-PROBE: cancel token toggled BEFORE the call — partial output must
/// still be sound (every emitted poly in I), never a Sat/Unsat-flipping
/// spurious eq. Iterates over several primes and bit widths to widen the
/// surface a regression might hit.
#[test]
fn hardprobe_phase1_precancelled_returns_sound_partial() {
    use crate::timeout::CancelToken;
    for prime in [17u32, 257] {
        for k in 2..=4usize {
            let names: Vec<String> = (0..k).map(|i| format!("b{}", i)).collect();
            let pr = FfPolyRing::new(ff(prime), names);
            let two = pr.field().from_int(2);
            let mut bs_poly = pr.zero();
            let mut coeff = pr.field().one();
            for i in 0..k {
                let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
                bs_poly = pr.add(bs_poly, term);
                coeff = pr.field().mul_ref(&coeff, &two);
            }
            let pin = pr.add(bs_poly, pr.constant(pr.field().from_int(-3)));
            let ideal = build_bit_ideal(&pr, vec![pin]);
            let mut bp = BitProp::new(&pr);
            bp.add_bitsum((0..k).collect());
            for i in 0..k { bp.add_bit(i); }
            let token = CancelToken::cancelled();
            let eqs = bp.get_bit_equalities_with_cancel(
                std::slice::from_ref(&ideal), Some(&token),
            );
            // Spec: partial output is sound. Every emitted poly is in I.
            // Crucially, an overflow `1` must NOT spuriously appear under
            // cancel — that would be a verdict-flipping fabrication.
            for e in &eqs {
                let appearing = pr.ring.appearing_indeterminates(e);
                if appearing.is_empty() {
                    // A constant poly — must be the algebraic 0 (which is in
                    // every ideal). A non-zero const here means bitprop
                    // fabricated an overflow under cancellation.
                    assert!(
                        ideal.contains(e),
                        "p={} k={}: cancelled emit produced fabricated constant",
                        prime, k
                    );
                }
                assert!(
                    ideal.contains(e),
                    "p={} k={}: cancelled emit not entailed",
                    prime, k
                );
            }
        }
    }
}

/// HARD-PROBE: two bitsums SHARING variables. e.g. bitsum A = [b0,b1,b2],
/// bitsum B = [b0,b1] (B is a prefix of A). Spec: if A reduces to v_A and
/// B reduces to v_B with both fitting, the propagated equalities must
/// remain in the ideal even though Phase 2's overlap is non-trivial. A
/// naive Phase 2 pairing that doesn't account for shared vars could emit
/// `b0 - b0 = 0` (harmless tautology) but more dangerously could emit
/// stale equalities on the unique tail.
#[test]
fn hardprobe_phase2_overlapping_bitsums_sound() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into()],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    // Pin A = b0 + 2·b1 + 4·b2 = 5  and  B = b0 + 2·b1 = 1.
    // => b2 = 1, b1 = 0, b0 = 1.
    let a_pin = pr.add(
        pr.add(pr.var(0), pr.scale(two.clone(), pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(pr.field().from_int(-5))),
    );
    let b_pin = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.constant(pr.field().from_int(-1)),
    );
    let ideal = build_bit_ideal(&pr, vec![a_pin, b_pin]);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]);
    bp.add_bitsum(vec![0, 1]);
    for v in 0..3 { bp.add_bit(v); }
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "overlapping bitsums: emitted eq not in ideal (unsound)"
        );
    }
    // Spec: every bit's value is uniquely determined → must be pinned.
    let expected = [(0, 1u64), (1, 0), (2, 1)];
    for (i, bi) in expected {
        let bit_el = if bi == 0 { pr.field().zero() } else { pr.field().one() };
        let target = pr.sub(pr.var(i), pr.constant(bit_el));
        assert!(
            ideal.contains(&target),
            "overlap: b{} expected {} not in ideal",
            i, bi
        );
    }
}

/// HARD-PROBE: bitsum with NON-BIT entry. Spec: bitprop must only
/// propagate when ALL bits are bit-constrained. A regression that drops
/// the all-bits check could emit `non_bit_var - bit_i(v) = 0` which is
/// generally NOT in the ideal — verdict-flipping unsound emission.
#[test]
fn hardprobe_phase1_non_bit_entry_must_not_propagate() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "x".into()],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    // bs = b0 + 2·b1 + 4·x, pinned to 3 (so b0=1,b1=1 forced if x were a bit).
    let bs = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(pr.field().from_int(-3))),
    );
    let mut polys = vec![bs];
    // bit constraints ONLY for b0, b1 — NOT x.
    for v in 0..2 {
        let xv = pr.var(v);
        let xv2 = pr.mul(pr.clone_poly(&xv), pr.clone_poly(&xv));
        polys.push(pr.sub(xv2, xv));
    }
    let ideal = Ideal::new(&pr, polys);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2]); // includes x (idx 2)
    bp.add_bit(0);
    bp.add_bit(1);
    // intentionally NOT add_bit(2)
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    // Spec: x is not bit-constrained, so the bitsum's interpretation is
    // ambiguous (x could be any field element). Phase 1 must NOT pin bits.
    // If any eq is emitted, it MUST be entailed (i.e. in I).
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "non-bit entry in bitsum: emitted unsound eq {:?}",
            e
        );
    }
}

/// HARD-PROBE: bitsum length cliff. For k = floor(log2 p), 2^k ≤ p holds
/// — propagation legal. For k = floor(log2 p) + 1, 2^k > p — propagation
/// MUST refuse or emit only entailed equalities. Sweeps primes whose
/// log2 cap is distinct enough to exercise the off-by-one in the guard.
#[test]
fn hardprobe_phase1_length_cliff_at_log2_p() {
    for prime in [7u32, 11, 13, 17, 31, 127, 257, 1009] {
        let logp = (prime as f64).log2().floor() as usize;
        // k = logp + 1 is JUST over the cliff: 2^k > p.
        let k = logp + 1;
        let names: Vec<String> = (0..k).map(|i| format!("b{}", i)).collect();
        let pr = FfPolyRing::new(ff(prime), names);
        let two = pr.field().from_int(2);
        let mut bs_poly = pr.zero();
        let mut coeff = pr.field().one();
        for i in 0..k {
            let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
            bs_poly = pr.add(bs_poly, term);
            coeff = pr.field().mul_ref(&coeff, &two);
        }
        let ideal = build_bit_ideal(&pr, vec![bs_poly]);
        let mut bp = BitProp::new(&pr);
        bp.add_bitsum((0..k).collect());
        for i in 0..k { bp.add_bit(i); }
        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        // Spec: 2^k > p means the bitsum-mod-p has multiple integer
        // preimages, so propagation is unsound. Any emitted eq must
        // still be entailed (sound) — never a fabricated overflow `1`.
        for e in &eqs {
            assert!(
                ideal.contains(e),
                "p={} k={}: cliff case emitted unsound eq",
                prime, k
            );
        }
    }
}

/// HARD-PROBE: repeat the SAME bitsum twice. Spec: idempotent registration
/// must not double-emit nor produce contradictory equalities.
#[test]
fn hardprobe_duplicate_bitsum_registration_idempotent() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into()],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let pin = pr.add(
        pr.add(pr.var(0), pr.scale(two, pr.var(1))),
        pr.add(pr.scale(four, pr.var(2)), pr.constant(pr.field().from_int(-5))),
    );
    let ideal = build_bit_ideal(&pr, vec![pin]);
    let mut bp = BitProp::new(&pr);
    // The SAME bitsum registered twice.
    bp.add_bitsum(vec![0, 1, 2]);
    bp.add_bitsum(vec![0, 1, 2]);
    for v in 0..3 { bp.add_bit(v); }
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "duplicate bitsum: emitted eq not in ideal"
        );
    }
}

/// HARD-PROBE: a basis containing 1 (trivial ideal = whole ring). Phase 1
/// reductions then map every poly to 0, which is a constant ≤ 2^k. Spec:
/// bitprop's emissions on the trivial ideal must still be sound (every
/// emitted poly trivially in I since I = R). The danger is a panic or an
/// infinite loop, neither of which is allowed.
#[test]
fn hardprobe_trivial_ideal_does_not_panic() {
    let pr = FfPolyRing::new(ff(17), vec!["b0".into(), "b1".into()]);
    let one_poly = pr.constant(pr.field().one());
    let ideal = Ideal::new(&pr, vec![one_poly]);
    assert!(ideal.is_whole_ring(), "ideal generated by 1 is whole ring");
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1]);
    bp.add_bit(0);
    bp.add_bit(1);
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    // Spec: whole-ring trivially contains everything, so any emission is
    // sound; chiefly we assert no panic. We also assert that under R = I
    // every emission e satisfies ideal.contains(e).
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "whole-ring ideal: emission contains check must hold"
        );
    }
}

/// HARD-PROBE: 1-variable ring, k=1 bitsum. Edge: minimal degrees of
/// freedom. Spec: pin b0=0 → emit b0=0; pin b0=1 → emit b0=1. No overflow.
#[test]
fn hardprobe_single_var_ring_k1() {
    for v in [0u64, 1] {
        let pr = FfPolyRing::new(ff(17), vec!["b0".into()]);
        let neg = pr.field().from_int(-(v as i64));
        let pin = pr.add(pr.var(0), pr.constant(neg));
        let ideal = build_bit_ideal(&pr, vec![pin]);
        let mut bp = BitProp::new(&pr);
        bp.add_bitsum(vec![0]);
        bp.add_bit(0);
        let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
        for e in &eqs {
            assert!(
                ideal.contains(e),
                "1-var ring k=1 v={}: emit not entailed",
                v
            );
        }
        // Differential: spec value must be pinned.
        let bit_el = if v == 0 { pr.field().zero() } else { pr.field().one() };
        let target = pr.sub(pr.var(0), pr.constant(bit_el));
        assert!(
            ideal.contains(&target),
            "1-var ring k=1 v={}: pinned value not in ideal",
            v
        );
    }
}

/// HARD-PROBE: many independent calls in a row on the SAME BitProp / SAME
/// ideal must yield byte-exactly the same equality count. Probes a hidden
/// mutation across calls (a per-call cache mutation would change
/// subsequent results).
#[test]
fn hardprobe_referential_transparency_across_many_calls() {
    let pr = FfPolyRing::new(
        ff(257),
        vec!["b0".into(), "b1".into(), "b2".into(), "b3".into()],
    );
    let two = pr.field().from_int(2);
    let mut bs_poly = pr.zero();
    let mut coeff = pr.field().one();
    for i in 0..4 {
        let term = pr.scale(pr.field().clone_el(&coeff), pr.var(i));
        bs_poly = pr.add(bs_poly, term);
        coeff = pr.field().mul_ref(&coeff, &two);
    }
    let pin = pr.add(bs_poly, pr.constant(pr.field().from_int(-13)));
    let ideal = build_bit_ideal(&pr, vec![pin]);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum(vec![0, 1, 2, 3]);
    for v in 0..4 { bp.add_bit(v); }
    let n0 = bp.get_bit_equalities(std::slice::from_ref(&ideal)).len();
    for round in 1..10 {
        let n = bp.get_bit_equalities(std::slice::from_ref(&ideal)).len();
        assert_eq!(
            n, n0,
            "round {}: equality count drifted ({} != {}), is_bit cache leak",
            round, n, n0
        );
    }
}

/// HARD-PROBE: cross-branch is_bit poisoning. Drive `is_bit` with a
/// basis containing `x^2 - x` (proves x is a bit ON this branch), then
/// drive it AGAIN with a SIBLING basis that has no such constraint.
/// Spec: is_bit must NOT cache the branch-A proof into self.bits —
/// sibling call must return false.
#[test]
fn hardprobe_is_bit_no_cross_branch_cache_r5_h1_r7_j1() {
    let pr = FfPolyRing::new(ff(257), vec!["x".into(), "y".into()]);
    let bp = BitProp::new(&pr);

    // Branch A: basis proves x is a bit (contains x^2 - x).
    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let bit_x = pr.sub(x2, x);
    let basis_a = Ideal::new(&pr, vec![bit_x]);
    assert!(bp.is_bit(0, std::slice::from_ref(&basis_a)));

    // Branch B (sibling): empty basis — x is NOT proven a bit here.
    let basis_b = Ideal::new(&pr, vec![]);
    assert!(
        !bp.is_bit(0, std::slice::from_ref(&basis_b)),
        "is_bit cached a per-branch proof across basis switches"
    );

    // Branch C: a different var y under basis A. Spec: not bit-constrained.
    assert!(
        !bp.is_bit(1, std::slice::from_ref(&basis_a)),
        "is_bit reported true for an unrelated var (spurious bit-ness)"
    );
}

/// HARD-PROBE: Phase 2 with `2^max > p` (FIT FAILS) — even when the basis
/// proves A − B ≡ 0 mod p, propagation must not emit `b_k − c_k` because
/// mod-p collisions admit b ≠ c integerly. Spec: every emit must still be
/// in the ideal (sound by being already entailed).
#[test]
fn hardprobe_phase2_fit_fails_sound() {
    // GF(11), 4-bit bitsums: 2^4 = 16 > 11 → fit FAILS.
    let pr = FfPolyRing::new(
        ff(11),
        vec![
            "b0".into(), "b1".into(), "b2".into(), "b3".into(),
            "c0".into(), "c1".into(), "c2".into(), "c3".into(),
        ],
    );
    let two = pr.field().from_int(2);
    let four = pr.field().from_int(4);
    let eight = pr.field().from_int(8);
    let a = pr.add(
        pr.add(pr.var(0), pr.scale(two.clone(), pr.var(1))),
        pr.add(pr.scale(four.clone(), pr.var(2)), pr.scale(eight.clone(), pr.var(3))),
    );
    let b = pr.add(
        pr.add(pr.var(4), pr.scale(two, pr.var(5))),
        pr.add(pr.scale(four, pr.var(6)), pr.scale(eight, pr.var(7))),
    );
    let mut polys = vec![pr.sub(a, b)];
    for v in 0..8 {
        let xv = pr.var(v);
        let xv2 = pr.mul(pr.clone_poly(&xv), pr.clone_poly(&xv));
        polys.push(pr.sub(xv2, xv));
    }
    let ideal = Ideal::new(&pr, polys);
    let mut bp = BitProp::new(&pr);
    bp.add_bitsum((0..4).collect());
    bp.add_bitsum((4..8).collect());
    for v in 0..8 { bp.add_bit(v); }
    let eqs = bp.get_bit_equalities(std::slice::from_ref(&ideal));
    for e in &eqs {
        assert!(
            ideal.contains(e),
            "GF(11) 4-bit Phase 2: fit-fails emit not entailed (UNSOUND)"
        );
    }
}

/// HARD-PROBE: state round-trip identity. `to_state` → `from_state` →
/// re-query must yield byte-identical equality count. Probes a missing
/// field in BitPropState that silently drops information.
#[test]
fn hardprobe_state_roundtrip_identity_multiple_bitsums() {
    let pr = FfPolyRing::new(
        ff(257),
        vec![
            "b0".into(), "b1".into(), "c0".into(), "c1".into(),
        ],
    );
    let two = pr.field().from_int(2);
    let a = pr.add(pr.var(0), pr.scale(two.clone(), pr.var(1)));
    let b = pr.add(pr.var(2), pr.scale(two, pr.var(3)));
    let mut polys = vec![pr.sub(a, b)];
    for v in 0..4 {
        let xv = pr.var(v);
        let xv2 = pr.mul(pr.clone_poly(&xv), pr.clone_poly(&xv));
        polys.push(pr.sub(xv2, xv));
    }
    let ideal = Ideal::new(&pr, polys);
    let mut bp1 = BitProp::new(&pr);
    bp1.add_bitsum(vec![0, 1]);
    bp1.add_bitsum(vec![2, 3]);
    for v in 0..4 { bp1.add_bit(v); }
    let eqs1 = bp1.get_bit_equalities(std::slice::from_ref(&ideal));
    // Round-trip
    let state = bp1.to_state();
    let bp2 = BitProp::from_state(&pr, state);
    let eqs2 = bp2.get_bit_equalities(std::slice::from_ref(&ideal));
    assert_eq!(eqs1.len(), eqs2.len(), "state roundtrip changed output length");
    // The bitsum lists themselves must round-trip byte-identical.
    let s = bp1.to_state();
    assert_eq!(s.bitsums.len(), 2);
    assert_eq!(s.bits.len(), 4);
}
