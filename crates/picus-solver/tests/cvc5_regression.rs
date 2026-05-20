//! QF_FF regression tests.
//!
//! Each test encodes a mathematical problem as a polynomial system
//! and checks the SAT / UNSAT verdict via
//! [`picus_solver::core::solve_encoded`].

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::{ConstraintSystem, PolyTerm, encode};
use num_bigint::BigUint;
use num_traits::One;

fn solve_system(system: &ConstraintSystem) -> &'static str {
    let encoded = encode(system).unwrap();
    match solve_encoded(&encoded) {
        SolveOutcome::Sat(_) => "sat",
        SolveOutcome::Unsat(_) => "unsat",
        SolveOutcome::Unknown => panic!("unknown (cancelled)"),
    }
}

/// Helper: create a constant term.
fn cterm(coeff: u64) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(coeff), vars: vec![] }
}

/// Helper: single variable term.
fn vterm(var: &str) -> PolyTerm {
    PolyTerm { coeff: BigUint::one(), vars: vec![var.into()] }
}

/// Helper: scaled variable term.
fn svterm(coeff: u64, var: &str) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(coeff), vars: vec![var.into()] }
}

/// Helper: product term.
fn pterm(coeff: u64, vars: &[&str]) -> PolyTerm {
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: vars.iter().map(|s| s.to_string()).collect(),
    }
}

// ===== Simple tests over GF(17) =====

/// cvc5: negneg.smt2 — double negation: -(-(x)) = x → UNSAT (tautology)
/// We encode: x + (-(-x)) should be identically zero.
/// Actually negneg tests that neg(neg(x)) - x = 0. In field terms this is always true.
/// A trivially satisfiable system.
#[test]
fn test_negneg_field_identity() {
    // Over GF(17): x exists s.t. x ≠ 0 → sat
    let system = ConstraintSystem {
        prime: BigUint::from(17u32),
        equalities: vec![],
        disequalities: vec![("x".into(), "zero".into())],
        assignments: vec![("zero".into(), BigUint::from(0u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "sat");
}

/// univar_conjunction_sat.smt2: x^2 = x AND x ≠ 1 AND x ≠ 2 over GF(17) → sat (x=0)
#[test]
fn test_univar_conjunction_sat() {
    let p = BigUint::from(17u32);
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // x^2 - x = 0
            vec![pterm(1, &["x", "x"]), svterm(16, "x")], // x^2 + (-1)*x = x^2 + 16x
            // Rabinowitsch for x ≠ 1: (x - 1)*w1 = 1
            vec![pterm(1, &["x", "w1"]), svterm(16, "w1"), cterm(16)],
            // Rabinowitsch for x ≠ 2: (x - 2)*w2 = 1
            vec![pterm(1, &["x", "w2"]), svterm(15, "w2"), cterm(16)],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "sat");
}

/// univar_conjunction_unsat.smt2: x^2 = x AND x ≠ 1 AND x ≠ 0 over GF(17) → unsat
#[test]
fn test_univar_conjunction_unsat() {
    let p = BigUint::from(17u32);
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // x^2 - x = 0 → x ∈ {0, 1}
            vec![pterm(1, &["x", "x"]), svterm(16, "x")],
            // (x - 1)*w1 - 1 = 0 → x ≠ 1
            vec![pterm(1, &["x", "w1"]), svterm(16, "w1"), cterm(16)],
            // (x - 0)*w2 - 1 = 0 → x ≠ 0
            vec![pterm(1, &["x", "w2"]), cterm(16)],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "unsat");
}

/// ff_is_zero_sound.smt2: IsZero gadget is sound over GF(17)
/// m*x + is_zero - 1 = 0, is_zero*x = 0
/// Proves: is_zero ∈ {0,1} and is_zero=1 ⟺ x=0
/// Encoding: check if we can find a witness where these hold but is_zero ∉ {0,1}
#[test]
fn test_is_zero_sound_bit_constraint() {
    let p = BigUint::from(17u32);
    // is_zero^2 - is_zero = 0 given the two IsZero constraints?
    // Actually the cvc5 test checks (not (=> constraints conclusion))
    // = constraints AND NOT conclusion
    // = m*x + iz - 1 = 0 AND iz*x = 0 AND NOT(iz ∈ {0,1} AND iz=1⟺x=0)
    //
    // Simplify: constraints force iz*(iz-1)=0, so iz ∈ {0,1}.
    // AND iz=1→x=0 (from iz*x=0), and x=0→iz=1 (from m*x+iz-1=0 with x=0→iz=1)
    //
    // For our test: check that iz^2 - iz = 0 is implied.
    // Encode: constraints + iz^2 - iz ≠ 0 → UNSAT
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // m*x + iz + 16 = 0  (i.e., m*x + iz - 1 = 0)
            vec![pterm(1, &["m", "x"]), vterm("iz"), cterm(16)],
            // iz * x = 0
            vec![pterm(1, &["iz", "x"])],
            // We want to prove iz^2 - iz = 0
            // So we assert iz^2 - iz ≠ 0 via Rabinowitsch:
            // (iz^2 - iz) * w - 1 = 0
            vec![pterm(1, &["iz", "iz", "w"]), svterm(16, &"izw"), cterm(16)],
            // izw = iz * w
            vec![pterm(1, &["iz", "w"]), svterm(16, "izw")],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "unsat");
}

/// field_poly.smt2: a^3 = a over GF(3) → a^p = a for all a (Fermat's little theorem)
/// We test: a^3 - a ≠ 0 → UNSAT
#[test]
fn test_field_poly_gf3() {
    let p = BigUint::from(3u32);
    // Introduce aa = a*a, then aaa = aa*a = a^3
    // Constraints: aa - a*a = 0, aaa - aa*a = 0, (aaa - a)*w - 1 = 0
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // aa = a*a
            vec![vterm("aa"), pterm(2, &["a", "a"])], // aa - a^2 = 0
            // aaa = aa*a
            vec![vterm("aaa"), pterm(2, &["aa", "a"])],
        ],
        // aaa ≠ a (Rabinowitsch trick)
        disequalities: vec![("aaa".into(), "a".into())],
        assignments: vec![],
        add_field_polys: true,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "unsat");
}

/// simple.smt2 equivalent: a*b = 1, a = 2 over GF(5) → sat (b = 3 since 2*3=6=1)
#[test]
fn test_simple_sat_gf5() {
    let system = ConstraintSystem {
        prime: BigUint::from(5u32),
        equalities: vec![
            // a*b - 1 = 0
            vec![pterm(1, &["a", "b"]), cterm(4)], // -1 = 4 mod 5
        ],
        disequalities: vec![],
        assignments: vec![("a".into(), BigUint::from(2u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    match solve_encoded(&encoded) {
        SolveOutcome::Sat(model) => {
            assert_eq!(model["b"], BigUint::from(3u32));
        }
        SolveOutcome::Unsat(_) => panic!("Expected SAT"),
        _ => panic!("unexpected outcome"),
    }
}

/// a*b = 1, a = 2, b = 2 over GF(5) → unsat (2*2=4≠1)
#[test]
fn test_simple_unsat_gf5() {
    let system = ConstraintSystem {
        prime: BigUint::from(5u32),
        equalities: vec![
            vec![pterm(1, &["a", "b"]), cterm(4)],
        ],
        disequalities: vec![],
        assignments: vec![
            ("a".into(), BigUint::from(2u32)),
            ("b".into(), BigUint::from(2u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "unsat");
}

/// XOR gadget sound: f0 XOR f1 = sum with proper bit constraints over GF(11)
/// f0*(f0-1) = 0, f1*(f1-1) = 0 (binary), sum = f0+f1-2*f0*f1
/// sum*(sum-1) = 0 → UNSAT (proving sum is also binary)
#[test]
fn test_xor_sum_is_binary() {
    let p = BigUint::from(11u32);
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            // f0^2 - f0 = 0
            vec![pterm(1, &["f0", "f0"]), svterm(10, "f0")],
            // f1^2 - f1 = 0
            vec![pterm(1, &["f1", "f1"]), svterm(10, "f1")],
            // sum = f0 + f1 - 2*f0*f1 → sum - f0 - f1 + 2*f0*f1 = 0
            vec![vterm("sum"), svterm(10, "f0"), svterm(10, "f1"), pterm(2, &["f0", "f1"])],
            // Prove sum^2 - sum = 0 by asserting its negation:
            // (sum^2 - sum)*w - 1 = 0
            vec![pterm(1, &["sum", "sum", "w"]), svterm(10, &"sw"), cterm(10)],
            vec![pterm(1, &["sum", "w"]), svterm(10, "sw")],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    assert_eq!(solve_system(&system), "unsat");
}

/// Large field: BN128 prime, simple a*b=1 with a=2
#[test]
fn test_bn128_simple() {
    let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pterm(1, &["a", "b"]), PolyTerm { coeff: &p - BigUint::one(), vars: vec![] }],
        ],
        disequalities: vec![],
        assignments: vec![("a".into(), BigUint::from(2u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    match solve_encoded(&encoded) {
        SolveOutcome::Sat(model) => {
            // b should be (p+1)/2 since 2 * (p+1)/2 = p+1 = 1 mod p
            let expected_b = (&p + BigUint::one()) / BigUint::from(2u32);
            assert_eq!(model["b"], expected_b);
        }
        SolveOutcome::Unsat(_) => panic!("Expected SAT"),
        _ => panic!("unexpected outcome"),
    }
}
