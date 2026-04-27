//! Pattern detection on polynomials.
//!
//! Mirrors cvc5's `theory/ff/parse.{h,cpp}` but operates on the **semantic**
//! polynomial form (i.e. on a `Poly` already encoded in our `FfPolyRing`)
//! rather than on SMT AST nodes.  This is sufficient for our pipeline, which
//! has already encoded all input constraints into polynomials.
//!
//! The functions here are pure: they inspect a polynomial and try to
//! recognise specific structural patterns commonly emitted by Circom and
//! other ZK frontends:
//!
//!   * `bit_constraint(p)`           : detects   `x*(x-1) == 0`     (any sign)
//!   * `zero_constraint(p)`          : detects   `x == 0`
//!   * `one_constraint(p)`           : detects   `x == 1`
//!   * `linear_monomial(p)`          : detects   `c*x`              (single mono)
//!   * `extract_linear_monomials(p)` : splits a polynomial into linear and
//!                                     non-linear terms
//!   * `bit_sums(p, bits)`           : detects sub-sums of the form
//!                                     `k*(b_0 + 2*b_1 + ... + 2^k*b_k)`
//!                                     where the `b_i` are (preferentially)
//!                                     known bit-constrained variables.
//!   * `disjunctive_bit_constraint`  : intentionally not implemented at the
//!                                     polynomial level (it is a *boolean*
//!                                     pattern, handled before encoding).

use std::collections::{HashMap, HashSet};

use crate::field::FfEl;
use crate::poly::{FfPolyRing, Poly};

/// Information about a detected bit constraint:  `var * (var - 1) == 0`
/// (i.e. `var` is constrained to {0,1}).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitConstraint {
    pub var: usize,
}

/// A linear monomial `coeff * var`.
#[derive(Debug, Clone)]
pub struct LinearMonomial {
    pub var: usize,
    pub coeff: FfEl,
}

/// A bitsum `coeff * (2^0 * b_0 + 2^1 * b_1 + ... + 2^k * b_k)`.
///
/// `bits[i]` is the variable index whose coefficient in the underlying sum
/// is `coeff * 2^i`.
#[derive(Debug, Clone)]
pub struct BitSum {
    pub coeff: FfEl,
    pub bits: Vec<usize>,
}

/// Returns `Some(var_idx)` if `p` is `c*x` for some single variable `x`
/// and a non-zero constant `c`.  Otherwise `None`.
pub fn linear_monomial(pr: &FfPolyRing, p: &Poly) -> Option<LinearMonomial> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let n_vars = pr.n_vars;

    let mut found: Option<(usize, FfEl)> = None;
    for (c, m) in ring.terms(p) {
        if fp.is_zero(c) {
            continue;
        }
        // Determine which (if any) single variable appears with degree 1.
        let mut var: Option<usize> = None;
        let mut total_deg = 0usize;
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            if e > 0 {
                if var.is_some() || e > 1 {
                    return None;
                }
                var = Some(v);
                total_deg += e;
            }
        }
        if total_deg != 1 || var.is_none() {
            return None;
        }
        if found.is_some() {
            return None; // more than one term
        }
        found = Some((var.unwrap(), fp.clone_el(c)));
    }
    found.map(|(var, coeff)| LinearMonomial { var, coeff })
}

/// `p == 0` represents `x == 0` for some variable `x`?
/// Detects polynomials of the form `c*x` with `c != 0`.
pub fn zero_constraint(pr: &FfPolyRing, p: &Poly) -> Option<usize> {
    linear_monomial(pr, p).map(|lm| lm.var)
}

/// `p == 0` represents `x == 1` for some variable `x`?
/// Detects polynomials of the form `c*x + d` with `c, d != 0` and `d/c = -1`.
pub fn one_constraint(pr: &FfPolyRing, p: &Poly) -> Option<usize> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let n_vars = pr.n_vars;

    let mut linear_term: Option<(usize, FfEl)> = None;
    let mut const_term: Option<FfEl> = None;

    for (c, m) in ring.terms(p) {
        if fp.is_zero(c) { continue; }
        // Compute total degree
        let mut total_deg = 0usize;
        let mut var: Option<usize> = None;
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            if e > 0 {
                if var.is_some() || e > 1 {
                    return None;
                }
                var = Some(v);
                total_deg += e;
            }
        }
        match total_deg {
            0 => {
                if const_term.is_some() { return None; }
                const_term = Some(fp.clone_el(c));
            }
            1 => {
                if linear_term.is_some() { return None; }
                linear_term = Some((var.unwrap(), fp.clone_el(c)));
            }
            _ => return None,
        }
    }
    let (var, coeff) = linear_term?;
    let cst = const_term?;
    // We need cst == -coeff  (so that p = coeff*x + cst = coeff*(x - 1))
    let neg_coeff = fp.negate(coeff);
    if fp.eq_el(&cst, &neg_coeff) {
        Some(var)
    } else {
        None
    }
}

/// `p == 0` represents `x*(x-1) == 0`?  Detects bit constraints in
/// any sign / scalar form: `c*(x^2 - x) == 0` for some non-zero `c`.
pub fn bit_constraint(pr: &FfPolyRing, p: &Poly) -> Option<BitConstraint> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let n_vars = pr.n_vars;

    // Collect the (degree, var, coeff) triples.
    // Expect exactly two terms: c*x^2 and -c*x for the same var.
    let mut quad: Option<(usize, FfEl)> = None;
    let mut lin: Option<(usize, FfEl)> = None;

    for (c, m) in ring.terms(p) {
        if fp.is_zero(c) { continue; }
        let mut total_deg = 0usize;
        let mut var: Option<usize> = None;
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            if e > 0 {
                if var.is_some() {
                    return None;
                }
                var = Some(v);
                total_deg = e;
            }
        }
        let var = var?;
        match total_deg {
            2 => {
                if quad.is_some() { return None; }
                quad = Some((var, fp.clone_el(c)));
            }
            1 => {
                if lin.is_some() { return None; }
                lin = Some((var, fp.clone_el(c)));
            }
            _ => return None,
        }
    }
    let (qv, qc) = quad?;
    let (lv, lc) = lin?;
    if qv != lv { return None; }
    // Check qc + lc == 0  (i.e. lc = -qc)
    let neg_qc = fp.negate(qc);
    if fp.eq_el(&lc, &neg_qc) {
        Some(BitConstraint { var: qv })
    } else {
        None
    }
}

/// Decompose a polynomial into a list of linear monomials and a list of
/// "rest" (constant + non-linear) terms (each rest term as a single-term
/// polynomial).  Returns `None` if the polynomial is zero.
pub fn extract_linear_monomials(
    pr: &FfPolyRing,
    p: &Poly,
) -> Option<(Vec<LinearMonomial>, Vec<Poly>)> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let n_vars = pr.n_vars;

    if ring.is_zero(p) {
        return None;
    }

    let mut linears: Vec<LinearMonomial> = Vec::new();
    let mut rest: Vec<Poly> = Vec::new();

    for (c, m) in ring.terms(p) {
        if fp.is_zero(c) { continue; }
        let mut total_deg = 0usize;
        let mut single_var: Option<usize> = None;
        let mut multi = false;
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            if e > 0 {
                if e > 1 || single_var.is_some() {
                    multi = true;
                }
                single_var.get_or_insert(v);
                total_deg += e;
            }
        }
        if total_deg == 1 && !multi {
            linears.push(LinearMonomial { var: single_var.unwrap(), coeff: fp.clone_el(c) });
        } else {
            // Build a single-term polynomial: c * monomial
            let term = ring.create_term(fp.clone_el(c), ring.clone_monomial(&m));
            rest.push(term);
        }
    }
    Some((linears, rest))
}

/// Detect bitsums in a polynomial.  Given `p`, look for a sub-sum of the
/// form  `coeff * (b_0 + 2*b_1 + ... + 2^k * b_k)` where the `b_i` are
/// distinct linear monomials, preferring variables in `bits_hint` (which
/// are known to be bit-constrained).
///
/// Returns the list of detected bitsums and the *remaining* polynomial
/// (i.e. `p` minus the recognised bitsums, kept as a single polynomial).
///
/// Algorithm (faithfully ported from cvc5's `parse::bitSums`):
///   1. Extract linear monomials from `p`.
///   2. Group them by the **lowest bit** of their coefficient (i.e. by the
///      candidate `coeff` after dividing out the power of 2).  For each
///      candidate `coeff = c`, we try to greedily build the longest chain
///      `c, 2c, 4c, ..., 2^k c` whose linear monomials are present.
///   3. Among multiple candidate coeffs, prefer the one whose first bit is
///      a variable from `bits_hint` (priority queue, as cvc5 does).
///   4. Remove the consumed linear monomials, repeat until no more bitsums.
pub fn bit_sums(
    pr: &FfPolyRing,
    p: &Poly,
    bits_hint: &HashSet<usize>,
) -> Option<(Vec<BitSum>, Poly)> {
    let ring = &pr.ring;
    let fp = pr.field.field();
    let two = fp.int_hom().map(2);

    let (mut linears, rest) = extract_linear_monomials(pr, p)?;
    let mut bitsums: Vec<BitSum> = Vec::new();

    // Helper: index linear monomials by var -> position in `linears`.
    loop {
        if linears.is_empty() {
            break;
        }

        // Build var -> coeff lookup, and var -> Vec<position> (vars distinct).
        let mut var_pos: HashMap<usize, usize> = HashMap::new();
        for (i, lm) in linears.iter().enumerate() {
            var_pos.insert(lm.var, i);
        }

        // Try each linear monomial as the candidate "least significant bit"
        // (i.e. with coefficient = base coeff `c`).
        // Sort candidate ordering: hinted bits first.
        let mut order: Vec<usize> = (0..linears.len()).collect();
        order.sort_by_key(|&i| !bits_hint.contains(&linears[i].var));

        let mut chosen: Option<(BitSum, Vec<usize>)> = None;
        let mut best_len = 0usize;

        for &start in &order {
            let base_var = linears[start].var;
            let base_coeff = fp.clone_el(&linears[start].coeff);

            let mut chain: Vec<usize> = vec![base_var];
            let mut consumed_positions: Vec<usize> = vec![start];
            let mut next_coeff = fp.mul_ref(&base_coeff, &two);

            // Greedy extension: look for a linear monomial with coeff = next_coeff,
            // var not yet in chain.
            loop {
                let mut found_pos: Option<usize> = None;
                for (i, lm) in linears.iter().enumerate() {
                    if consumed_positions.contains(&i) { continue; }
                    if chain.contains(&lm.var) { continue; }
                    if fp.eq_el(&lm.coeff, &next_coeff) {
                        found_pos = Some(i);
                        break;
                    }
                }
                match found_pos {
                    Some(i) => {
                        chain.push(linears[i].var);
                        consumed_positions.push(i);
                        next_coeff = fp.mul_ref(&next_coeff, &two);
                    }
                    None => break,
                }
            }

            if chain.len() >= 2 && chain.len() > best_len {
                best_len = chain.len();
                let bs = BitSum { coeff: fp.clone_el(&base_coeff), bits: chain };
                chosen = Some((bs, consumed_positions));
            }
            // Otherwise: continue to next candidate base.
        }

        match chosen {
            Some((bs, mut positions)) => {
                positions.sort_unstable();
                positions.reverse();
                for pos in positions {
                    linears.swap_remove(pos);
                }
                bitsums.push(bs);
            }
            None => break,
        }

        // Avoid runaway in pathological inputs.
        if bitsums.len() > pr.n_vars + 4 {
            break;
        }
    }

    // Reassemble residual polynomial: leftover linears + rest.
    let mut residual = pr.zero();
    for lm in &linears {
        let term = ring.create_term(
            fp.clone_el(&lm.coeff),
            ring.clone_monomial(&ring.indeterminate(lm.var)),
        );
        residual = ring.add(residual, term);
    }
    for r in rest {
        residual = ring.add(residual, r);
    }

    if bitsums.is_empty() {
        Some((Vec::new(), residual))
    } else {
        Some((bitsums, residual))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FfField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> FfField {
        FfField::new(&BigUint::from(p))
    }

    #[test]
    fn test_zero_constraint() {
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
        let x = pr.var(0);
        assert_eq!(zero_constraint(&pr, &x), Some(0));

        let three = pr.field.from_int(3);
        let three_x = pr.scale(three, pr.var(0));
        assert_eq!(zero_constraint(&pr, &three_x), Some(0));

        let xy = pr.mul(pr.var(0), pr.var(1));
        assert_eq!(zero_constraint(&pr, &xy), None);
    }

    #[test]
    fn test_one_constraint() {
        // x - 1 = 0  →  x = 1
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let x_minus_1 = pr.sub(pr.var(0), pr.one());
        assert_eq!(one_constraint(&pr, &x_minus_1), Some(0));

        // 3x - 3 = 0  →  x = 1
        let three = pr.field.from_int(3);
        let neg_three = pr.field.from_int(-3);
        let term = pr.scale(three, pr.var(0));
        let p = pr.add(term, pr.constant(neg_three));
        assert_eq!(one_constraint(&pr, &p), Some(0));

        // x - 2 ≠ x = 1
        let neg_two = pr.field.from_int(-2);
        let p2 = pr.add(pr.var(0), pr.constant(neg_two));
        assert_eq!(one_constraint(&pr, &p2), None);
    }

    #[test]
    fn test_bit_constraint() {
        // x^2 - x = 0
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let x = pr.var(0);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let p = pr.sub(x2, pr.clone_poly(&x));
        assert_eq!(bit_constraint(&pr, &p), Some(BitConstraint { var: 0 }));

        // 5*x^2 - 5*x = 0  (also a bit constraint after scaling)
        let five = pr.field.from_int(5);
        let neg_five = pr.field.from_int(-5);
        let x2_b = pr.mul(pr.var(0), pr.var(0));
        let lin = pr.scale(neg_five, pr.var(0));
        let quad = pr.scale(five, x2_b);
        let p2 = pr.add(quad, lin);
        assert_eq!(bit_constraint(&pr, &p2), Some(BitConstraint { var: 0 }));

        // x^2 + x = 0  (NOT a bit constraint -- this is x*(x+1))
        let x2c = pr.mul(pr.var(0), pr.var(0));
        let p3 = pr.add(x2c, pr.var(0));
        assert_eq!(bit_constraint(&pr, &p3), None);
    }

    #[test]
    fn test_extract_linear_monomials() {
        // p = 2x + 3y + xy + 5
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
        let two = pr.field.from_int(2);
        let three = pr.field.from_int(3);
        let five = pr.field.from_int(5);
        let p = pr.add(
            pr.add(
                pr.add(pr.scale(two, pr.var(0)), pr.scale(three, pr.var(1))),
                pr.mul(pr.var(0), pr.var(1)),
            ),
            pr.constant(five),
        );
        let (lins, rest) = extract_linear_monomials(&pr, &p).unwrap();
        assert_eq!(lins.len(), 2);
        assert_eq!(rest.len(), 2);
    }

    #[test]
    fn test_bit_sums_simple() {
        // p = x_0 + 2*x_1 + 4*x_2  →  bitsum with coeff=1, bits=[0,1,2]
        let pr = FfPolyRing::new(ff(17), vec!["x0".into(), "x1".into(), "x2".into()]);
        let two = pr.field.from_int(2);
        let four = pr.field.from_int(4);
        let p = pr.add(
            pr.add(pr.var(0), pr.scale(two, pr.var(1))),
            pr.scale(four, pr.var(2)),
        );
        let hint: HashSet<usize> = HashSet::new();
        let (sums, residual) = bit_sums(&pr, &p, &hint).unwrap();
        assert_eq!(sums.len(), 1);
        assert_eq!(sums[0].bits.len(), 3);
        assert!(pr.is_zero(&residual));
    }

    #[test]
    fn test_bit_sums_with_residual() {
        // p = x + 2*y + z*z  →  bitsum [x,y] with coeff=1, residual=z*z
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into(), "z".into()]);
        let two = pr.field.from_int(2);
        let z2 = pr.mul(pr.var(2), pr.var(2));
        let p = pr.add(pr.add(pr.var(0), pr.scale(two, pr.var(1))), z2);
        let (sums, residual) = bit_sums(&pr, &p, &HashSet::new()).unwrap();
        assert_eq!(sums.len(), 1);
        assert_eq!(sums[0].bits, vec![0, 1]);
        assert!(!pr.is_zero(&residual));
    }
}
