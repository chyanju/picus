//! FF term canonicalization on polynomial term lists.
//!
//! Equivalent of cvc5's `theory_ff_rewriter`
//! at the granularity picus-solver works with. cvc5 rewrites on its AST
//! (`FINITE_FIELD_ADD`, `FINITE_FIELD_MULT`, `FINITE_FIELD_NEG`, `EQUAL`);
//! picus-solver receives a flat `Vec<PolyTerm>` per equality, so the
//! corresponding rewrites are:
//!
//! * Sort variables inside each term (analog of cvc5's child-order
//!   canonicalization under associative-commutative kinds).
//! * Sort terms by variable list, merge consecutive like terms summing
//!   coefficients (analog of `postRewriteFfAdd` like-term combining).
//! * Reduce coefficients modulo `prime` (analog of cvc5's constant
//!   folding).
//! * Drop terms whose coefficient is zero modulo `prime` (analog of
//!   cvc5's drop-zero-summand rule).
//! * Drop equalities whose normalized term list is empty (analog of
//!   `postRewriteFfEq` evaluating `0 = 0` to `true`).

use num_bigint::BigUint;
use num_traits::Zero;

use crate::frontend::encoder::{ConstraintSystem, PolyTerm};

/// Normalize an `PolyTerm` list in place. Each term's
/// `vars: Vec<(VarIdx, u16)>` is sorted by index and entries with the
/// same index are merged by adding exponents; terms are sorted by
/// their `vars` slice; like terms (same `vars`) merge coefficients
/// modulo `prime`; terms with zero coefficient are dropped.
pub fn normalize_term_list(terms: &mut Vec<PolyTerm>, prime: &BigUint) {
    for t in terms.iter_mut() {
        // 1. Within-term: sort by var idx and merge same-idx entries
        //    by summing exponents (handles e.g. `x * x` ↔ `[(x, 2)]`
        //    vs accidentally repeated `[(x, 1), (x, 1)]`).
        t.vars.sort_by_key(|&(idx, _)| idx);
        let mut write = 0usize;
        for read in 0..t.vars.len() {
            if write > 0 && t.vars[write - 1].0 == t.vars[read].0 {
                let combined_exp = t.vars[write - 1].1
                    .checked_add(t.vars[read].1)
                    .expect("monomial exponent exceeds u16");
                t.vars[write - 1].1 = combined_exp;
            } else {
                if read != write {
                    t.vars.swap(read, write);
                }
                write += 1;
            }
        }
        t.vars.truncate(write);
        // 2. Coefficient reduction mod prime.
        if !t.coeff.is_zero() && &t.coeff >= prime {
            t.coeff = &t.coeff % prime;
        }
    }
    // 3. Sort terms by var list lexicographically.
    terms.sort_by(|a, b| a.vars.cmp(&b.vars));
    // 4. Merge consecutive like terms by summing coefficients mod p.
    let mut write = 0usize;
    for read in 0..terms.len() {
        if write > 0 && terms[write - 1].vars == terms[read].vars {
            let sum = (&terms[write - 1].coeff + &terms[read].coeff) % prime;
            terms[write - 1].coeff = sum;
        } else {
            if read != write {
                terms.swap(read, write);
            }
            write += 1;
        }
    }
    terms.truncate(write);
    // 5. Drop zero-coefficient terms.
    terms.retain(|t| !t.coeff.is_zero());
}

/// Normalize every equality in a [`ConstraintSystem`].
/// Equalities whose term list collapses to empty are dropped.
pub fn rewrite_system(system: &mut ConstraintSystem) {
    let prime = system.prime.clone();
    let mut new_equalities = Vec::with_capacity(system.equalities.len());
    for mut eq in std::mem::take(&mut system.equalities) {
        normalize_term_list(&mut eq, &prime);
        if eq.is_empty() {
            continue;
        }
        new_equalities.push(eq);
    }
    system.equalities = new_equalities;
}

#[cfg(test)]
#[path = "rewriter_tests.rs"]
mod tests;
