//! The index-keyed `ConstraintSystem` type family — the canonical system
//! shape consumed by the encoder ([`super::encode`]): [`PolyTerm`],
//! [`ConstraintSystem`], and the producer-side [`ConstraintSystemBuilder`].
//! Re-exported from `encoder` so `encoder::ConstraintSystem` etc. resolve here.

use std::collections::HashMap;

use num_bigint::BigUint;

use super::VarIdx;

/// A term in an [`ConstraintSystem`] equality.
///
/// Sparse representation: `vars` lists only variables with non-zero
/// exponent, paired with their exponent. An empty `vars` denotes a
/// constant term.
#[derive(Clone, Debug)]
pub struct PolyTerm {
    pub coeff: BigUint,
    pub vars: Vec<(VarIdx, u16)>,
}

/// Index-keyed constraint system for callers that produce term lists
/// in integer form via [`ConstraintSystemBuilder`].
#[derive(Clone, Debug)]
pub struct ConstraintSystem {
    pub prime: BigUint,
    /// Authoritative variable-name list. `var_names[i as usize]` is
    /// the canonical String name of variable `i`. The encoder uses
    /// this to construct the polynomial ring; downstream model
    /// extraction surfaces the same names back to the caller.
    pub var_names: Vec<String>,
    /// Each equality is `sum(terms) = 0`.
    pub equalities: Vec<Vec<PolyTerm>>,
    /// Each disequality `(a, b)` means `a ≠ b`. The encoder
    /// reserves one Rabinowitsch witness variable per entry,
    /// appended to `var_names` at encoding time.
    pub disequalities: Vec<(VarIdx, VarIdx)>,
    /// Each assignment `(v, val)` means `v = val`.
    pub assignments: Vec<(VarIdx, BigUint)>,
    /// Each bitsum `[b_0, b_1, ..., b_k]` defines an auxiliary
    /// variable `__bitsum_N = sum(2^i · b_i)`. The encoder appends
    /// the aux variable to `var_names`.
    pub bitsums: Vec<Vec<VarIdx>>,
    /// Add `x^p - x = 0` for every ring variable. Honoured by
    /// `encode` only when `prime <= 1000` (matching
    /// `encode_impl`).
    pub add_field_polys: bool,
}

/// Producer-side builder for [`ConstraintSystem`]. Each
/// producer constructs one builder, interns variable names through
/// [`Self::var`] (deduplicating against the running `var_names`),
/// emits terms as `Vec<PolyTerm>` over the returned indices, and
/// finalises with [`Self::build`]. [`Clone`] so callers like
/// `BooleanQuery::to_disjunct_systems` can fan out per-disjunct
/// builders from a query-level scaffold.
#[derive(Clone, Debug)]
pub struct ConstraintSystemBuilder {
    prime: BigUint,
    var_names: Vec<String>,
    name_to_idx: HashMap<String, VarIdx>,
    equalities: Vec<Vec<PolyTerm>>,
    disequalities: Vec<(VarIdx, VarIdx)>,
    assignments: Vec<(VarIdx, BigUint)>,
    bitsums: Vec<Vec<VarIdx>>,
    add_field_polys: bool,
}

impl ConstraintSystemBuilder {
    pub fn new(prime: BigUint) -> Self {
        Self {
            prime,
            var_names: Vec::new(),
            name_to_idx: HashMap::new(),
            equalities: Vec::new(),
            disequalities: Vec::new(),
            assignments: Vec::new(),
            bitsums: Vec::new(),
            add_field_polys: false,
        }
    }

    /// Intern a variable name, returning its index. Repeated calls
    /// with the same name return the same index.
    pub fn var(&mut self, name: &str) -> VarIdx {
        if let Some(&idx) = self.name_to_idx.get(name) {
            return idx;
        }
        let idx = self.var_names.len() as VarIdx;
        self.var_names.push(name.to_string());
        self.name_to_idx.insert(name.to_string(), idx);
        idx
    }

    /// Number of variables interned so far.
    pub fn n_vars(&self) -> usize {
        self.var_names.len()
    }

    /// Variable-name frame interned so far. Used by callers like
    /// `BooleanQuery` to feed the SAT-side `AtomTable` for
    /// reverse-resolving `PolyTerm` indices to canonical names.
    pub fn var_names(&self) -> &[String] {
        &self.var_names
    }

    pub fn prime(&self) -> &BigUint {
        &self.prime
    }

    /// Update the builder's prime in place. Used by long-lived
    /// builders (e.g. `SmtSession::builder`) whose prime is only
    /// known after a `define-sort` or first FF-sorted `declare-fun`.
    pub fn set_prime(&mut self, prime: BigUint) {
        self.prime = prime;
    }

    pub fn add_equality(&mut self, terms: Vec<PolyTerm>) {
        self.equalities.push(terms);
    }

    pub fn add_disequality(&mut self, a: VarIdx, b: VarIdx) {
        self.disequalities.push((a, b));
    }

    /// Introduce the witness pair for encoding `lhs != 0`: a fresh
    /// `__diseq_d_{seq}` variable `d` (the caller then constrains
    /// `d = lhs` via [`Self::add_equality`]) and a shared, lazily-created
    /// `__zero` pinned to `0`. Returns `(d, zero)`; the caller asserts the
    /// disequality with `add_disequality(d, zero)`. Centralises the
    /// synthetic-variable naming and the `__zero` lazy-init shared by the
    /// DNF (`BooleanQuery`) and CDCL(T) (`FfTheory`) disequality encoders
    /// so the two cannot drift. `seq` is the caller's per-system
    /// disequality counter (incremented here).
    pub fn fresh_disequality_vars(
        &mut self,
        seq: &mut usize,
        zero_idx: &mut Option<VarIdx>,
    ) -> (VarIdx, VarIdx) {
        let d_idx = self.var(&format!("__diseq_d_{}", *seq));
        *seq += 1;
        let zero = match *zero_idx {
            Some(z) => z,
            None => {
                let z = self.var("__zero");
                self.add_assignment(z, BigUint::from(0u32));
                *zero_idx = Some(z);
                z
            }
        };
        (d_idx, zero)
    }

    pub fn add_assignment(&mut self, v: VarIdx, val: BigUint) {
        self.assignments.push((v, val));
    }

    pub fn add_bitsum(&mut self, bits: Vec<VarIdx>) {
        self.bitsums.push(bits);
    }

    pub fn set_add_field_polys(&mut self, on: bool) {
        self.add_field_polys = on;
    }

    pub fn build(self) -> ConstraintSystem {
        ConstraintSystem {
            prime: self.prime,
            var_names: self.var_names,
            equalities: self.equalities,
            disequalities: self.disequalities,
            assignments: self.assignments,
            bitsums: self.bitsums,
            add_field_polys: self.add_field_polys,
        }
    }

}
