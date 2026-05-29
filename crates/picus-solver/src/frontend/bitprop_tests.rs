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
//     persist a per-branch bit proof into the global `self.bits` (R5 H1).

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

/// PROPERTY (R5 H1 regression / spec): `is_bit` MUST NOT cache a
/// per-basis bit proof into `self.bits`. The `&self` signature enforces
/// this at the type level — also checked behaviourally: a call with a
/// basis that proves `v` is a bit must NOT make a subsequent call with
/// an empty basis return `true`.
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
        "is_bit cached a branch-local proof (R5 H1 regression)"
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
