//! circomlib `CompConstant` (254-bit range-check comparator) recognition
//! for the `basis2` lemma. Recognises `CompConstant(ct) + (out === 0)`
//! over a bit decomposition, certifying `Σ 2^j b_j ≤ ct < p` so the
//! decomposition is injective even when `2^n > p`. Conservative: any
//! unmatched structural link returns `false`. Sole entry point:
//! [`companion_proves_below_prime`].

use std::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use num_traits::{One, Zero};

use picus_core::poly::IrPoly as Poly;
use picus_smt::poly_ir::PolyIR;

use super::match_decomp;
use crate::propagation::range::RangeValue;

/// Number of bits in the recognised comparator (circomlib `CompConstant`
/// is fixed at 254).
const COMPCONSTANT_BITS: usize = 254;
/// Number of base-4 digit `parts` (`COMPCONSTANT_BITS / 2`).
const COMPCONSTANT_PARTS: usize = 127;
/// Weight of the comparator output bit inside the parts-sum (the
/// gadget's `num2bits.out[127]`).
const COMPCONSTANT_OUT_BIT: usize = 127;

/// Returns `true` only if the IR contains a complete 254-bit
/// `CompConstant` comparator over the given decomposition `bits`
/// (weight-aligned) whose output is forced to zero and whose decoded
/// constant `ct` satisfies `ct < p`. A `true` result certifies
/// `Σ 2^j bits[j] < p`, so the decomposition is injective and basis2
/// may propagate even when `2^n > p`. Conservative: any unmatched link
/// returns `false`.
pub(super) fn companion_proves_below_prime(
    ir: &PolyIR,
    bits: &[usize],
    ranges: &HashMap<usize, RangeValue>,
) -> bool {
    if bits.len() != COMPCONSTANT_BITS {
        return false;
    }
    let p = ir.ring.field().prime();

    let canon = build_canon(ir);
    let part_map = build_part_map(ir, &canon);

    // 1. Match the 127 parts over weight-aligned bit pairs, decode the
    //    base-4 digits into `ct`, and collect the part output wires.
    let two_128 = BigUint::one() << 128usize;
    let mut ct = BigUint::zero();
    let mut part_outs: Vec<usize> = Vec::with_capacity(COMPCONSTANT_PARTS);
    for i in 0..COMPCONSTANT_PARTS {
        let a_i = BigUint::one() << i; // a_i = 2^i
        let b_i = (&two_128 - &a_i) % p; // b_i = 2^128 - 2^i
        let sl = canon[bits[2 * i]]; // digit's low bit  (weight 2^{2i})
        let sm = canon[bits[2 * i + 1]]; // digit's high bit (weight 2^{2i+1})
        let Some(polys) = part_map.get(&pair_key(sl, sm)) else {
            return false;
        };
        let mut matched = None;
        for poly in polys {
            if let Some(found) = match_part(ir, &canon, poly, sl, sm, &a_i, &b_i) {
                matched = Some(found);
                break;
            }
        }
        let Some((digit, out_var)) = matched else {
            return false;
        };
        // ct += digit · 4^i  (4^i = 2^{2i}).
        ct += BigUint::from(digit as u32) * (BigUint::one() << (2 * i));
        part_outs.push(canon[out_var]);
    }

    // 2. `ct < p` is what makes `X ≤ ct` imply `X < p`.
    if &ct >= p {
        return false;
    }

    // 3. The parts sum into a single signal `S`.
    let Some(s_var) = find_sum_var(ir, &canon, &part_outs) else {
        return false;
    };

    // 4. `S` is faithfully bit-decomposed; locate its weight-127 bit.
    let Some(out_bit_var) = find_inner_bit(ir, &canon, s_var, COMPCONSTANT_OUT_BIT, ranges) else {
        return false;
    };

    // 5. That output bit (= `[X > ct]`) is forced to zero.
    find_pinned_zero(ir, &canon, canon[out_bit_var])
}

/// Canonical-variable map: union-find over pure two-term linear
/// identities `c1·x_i + c2·x_j = 0` with `c1 + c2 ≡ 0` (i.e.
/// `x_i = x_j`). `canon[v]` is the representative of `v`'s class. These
/// identities are ordinary PolyIR equalities (the same facts the
/// `linear` lemma propagates); following them lets the matcher relate
/// the decomposition bits to the comparator inputs regardless of how
/// the compiler renumbered wires.
fn build_canon(ir: &PolyIR) -> Vec<usize> {
    let p = ir.ring.field().prime();
    let n = ir.ring.n_vars();
    let mut parent: Vec<usize> = (0..n).collect();
    for poly in &ir.equalities {
        let mut lin: Vec<(BigUint, usize)> = Vec::with_capacity(2);
        let mut ok = true;
        for (c, vars) in ir.poly_terms_idx(poly) {
            if vars.is_empty() {
                if !c.is_zero() {
                    ok = false;
                    break;
                }
                continue;
            }
            if vars.len() != 1 || vars[0].1 != 1 || lin.len() == 2 {
                ok = false;
                break;
            }
            lin.push((c, vars[0].0));
        }
        if !ok || lin.len() != 2 {
            continue;
        }
        if (&lin[0].0 + &lin[1].0) % p == BigUint::zero() {
            let ra = uf_find(&mut parent, lin[0].1);
            let rb = uf_find(&mut parent, lin[1].1);
            if ra != rb {
                parent[ra] = rb;
            }
        }
    }
    (0..n).map(|v| uf_find(&mut parent, v)).collect()
}

fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Index every "part-shaped" equality (exactly one degree-2 monomial
/// over two distinct variables, no higher degree, no square) by the
/// canonical pair of its product variables.
fn build_part_map<'a>(
    ir: &'a PolyIR,
    canon: &[usize],
) -> HashMap<(usize, usize), Vec<&'a Poly>> {
    let mut map: HashMap<(usize, usize), Vec<&Poly>> = HashMap::new();
    for poly in &ir.equalities {
        if let Some((va, vb)) = product_pair(ir, poly) {
            map.entry(pair_key(canon[va], canon[vb]))
                .or_default()
                .push(poly);
        }
    }
    map
}

/// If `poly` has exactly one product monomial and it is a product of
/// two distinct degree-1 variables (no squares, no higher degree),
/// return that variable pair; otherwise `None`.
fn product_pair(ir: &PolyIR, poly: &Poly) -> Option<(usize, usize)> {
    let mut found = None;
    for (_c, vars) in ir.poly_terms_idx(poly) {
        match vars.len() {
            0 | 1 if vars.first().map(|t| t.1).unwrap_or(1) == 1 => {}
            2 if vars[0].1 == 1 && vars[1].1 == 1 => {
                if found.is_some() {
                    return None;
                }
                found = Some((vars[0].0, vars[1].0));
            }
            _ => return None, // square (x^2) or higher degree
        }
    }
    found
}

/// Match one CompConstant `parts_i` equality over the bit pair
/// `(sl, sm)` (canonical low/high digit bits). On success returns the
/// base-4 digit `c_i ∈ {0,1,2,3}` and the part's output variable.
///
/// The lowered equality, normalised so the output wire has coefficient
/// `+1`, must exactly match one of the four `−parts_i` coefficient
/// signatures for `a = 2^i`, `b = 2^128 − 2^i`:
///   c=0: prod=b,   sl=−b, sm=−b, const=0
///   c=1: prod=−a,  sl=a,  sm=a−b, const=−a
///   c=2: prod=−b,  sl=0,  sm=a,  const=−a
///   c=3: prod=a,   sl=0,  sm=0,  const=−a
fn match_part(
    ir: &PolyIR,
    canon: &[usize],
    poly: &Poly,
    sl: usize,
    sm: usize,
    a: &BigUint,
    b: &BigUint,
) -> Option<(u8, usize)> {
    let p = ir.ring.field().prime();
    let mut prod: Option<BigUint> = None;
    let mut konst = BigUint::zero();
    let mut sl_c = BigUint::zero();
    let mut sm_c = BigUint::zero();
    let mut sl_seen = false;
    let mut sm_seen = false;
    let mut wire: Option<(BigUint, usize)> = None;

    for (c, vars) in ir.poly_terms_idx(poly) {
        match vars.len() {
            0 => konst = c,
            1 => {
                if vars[0].1 != 1 {
                    return None;
                }
                let cv = canon[vars[0].0];
                if cv == sl {
                    if sl_seen {
                        return None;
                    }
                    sl_c = c;
                    sl_seen = true;
                } else if cv == sm {
                    if sm_seen {
                        return None;
                    }
                    sm_c = c;
                    sm_seen = true;
                } else {
                    if wire.is_some() {
                        return None;
                    }
                    wire = Some((c, vars[0].0));
                }
            }
            2 => {
                if vars[0].1 != 1 || vars[1].1 != 1 {
                    return None;
                }
                if pair_key(canon[vars[0].0], canon[vars[1].0]) != pair_key(sl, sm) {
                    return None;
                }
                if prod.is_some() {
                    return None;
                }
                prod = Some(c);
            }
            _ => return None,
        }
    }

    let prod = prod?;
    let (wc, wvar) = wire?;
    // Normalise the equality so the output wire's coefficient is 1.
    let inv = crate::propagation::mod_inverse(&wc, p)?;
    let norm = |x: &BigUint| (x * &inv) % p;
    let prod = norm(&prod);
    let sl_c = norm(&sl_c);
    let sm_c = norm(&sm_c);
    let konst = norm(&konst);

    let zero = BigUint::zero();
    let nb = (p - b) % p; // −b
    let na = (p - a) % p; // −a
    let amb = ((a + p) - b) % p; // a − b

    if prod == *b && sl_c == nb && sm_c == nb && konst == zero {
        return Some((0, wvar));
    }
    if prod == na && sl_c == *a && sm_c == amb && konst == na {
        return Some((1, wvar));
    }
    if prod == nb && sl_c == zero && sm_c == *a && konst == na {
        return Some((2, wvar));
    }
    if prod == *a && sl_c == zero && sm_c == zero && konst == na {
        return Some((3, wvar));
    }
    None
}

/// Find the signal `S` defined by `S = Σ part_outs` (each part output
/// appears with one shared coefficient `−k`, `S` with `+k`, no other
/// terms). Returns the canonical variable of `S`.
fn find_sum_var(ir: &PolyIR, canon: &[usize], part_outs: &[usize]) -> Option<usize> {
    let p = ir.ring.field().prime();
    let targets: HashSet<usize> = part_outs.iter().copied().collect();
    for poly in &ir.equalities {
        let mut coeffs: HashMap<usize, BigUint> = HashMap::new();
        let mut ok = true;
        for (c, vars) in ir.poly_terms_idx(poly) {
            if vars.is_empty() {
                if !c.is_zero() {
                    ok = false;
                    break;
                }
                continue;
            }
            if vars.len() != 1 || vars[0].1 != 1 {
                ok = false;
                break;
            }
            let e = coeffs.entry(canon[vars[0].0]).or_insert_with(BigUint::zero);
            *e = (&*e + &c) % p;
        }
        if !ok {
            continue;
        }
        // Exactly one variable outside `targets` (the candidate `S`).
        let extras: Vec<usize> = coeffs
            .keys()
            .copied()
            .filter(|v| !targets.contains(v))
            .collect();
        if extras.len() != 1 {
            continue;
        }
        let s = extras[0];
        if !targets.iter().all(|v| coeffs.contains_key(v)) {
            continue;
        }
        let ks = coeffs[&s].clone();
        if ks.is_zero() {
            continue;
        }
        let neg_ks = (p - &ks) % p;
        if targets.iter().all(|v| coeffs[v] == neg_ks) {
            return Some(s);
        }
    }
    None
}

/// Find a faithful binary decomposition whose target is `s_var` and
/// return the variable at weight `bit`. "Faithful" = `2^width ≤ p` and
/// every bit pinned to `{0, 1}`, so the weight-`bit` variable really is
/// bit `bit` of `S`.
fn find_inner_bit(
    ir: &PolyIR,
    canon: &[usize],
    s_var: usize,
    bit: usize,
    ranges: &HashMap<usize, RangeValue>,
) -> Option<usize> {
    let p = ir.ring.field().prime();
    for poly in &ir.equalities {
        let Some(decomp) = match_decomp(ir, poly) else {
            continue;
        };
        if canon[decomp.target_var] != s_var || decomp.bits.len() <= bit {
            continue;
        }
        if &(BigUint::one() << decomp.bits.len()) > p {
            continue; // not faithful
        }
        let all_binary = decomp
            .bits
            .iter()
            .all(|&v| matches!(ranges.get(&ir.var_to_wire(v)), Some(r) if r.is_binary()));
        if all_binary {
            return Some(decomp.bits[bit]);
        }
    }
    None
}

/// True if some equality pins the variable to zero: a single linear
/// term `c·w = 0` (`c ≠ 0`) with `canon[w] == var`.
fn find_pinned_zero(ir: &PolyIR, canon: &[usize], var: usize) -> bool {
    for poly in &ir.equalities {
        let mut lin: Option<(BigUint, usize)> = None;
        let mut ok = true;
        for (c, vars) in ir.poly_terms_idx(poly) {
            if vars.is_empty() {
                if !c.is_zero() {
                    ok = false;
                    break;
                }
                continue;
            }
            if vars.len() != 1 || vars[0].1 != 1 || lin.is_some() {
                ok = false;
                break;
            }
            lin = Some((c, canon[vars[0].0]));
        }
        if !ok {
            continue;
        }
        if let Some((c, v)) = lin {
            if !c.is_zero() && v == var {
                return true;
            }
        }
    }
    false
}

fn pair_key(a: usize, b: usize) -> (usize, usize) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
#[path = "compconstant_tests.rs"]
mod tests;

