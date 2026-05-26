//! Encoder: translates a polynomial system into polynomials for GB computation.
//!
//! - Equality `f = 0` → polynomial `f`
//! - Disequality `a ≠ b` → Rabinowitsch trick: `(a - b) * w - 1`
//! - Bitsum subpatterns in equalities are extracted by
//!   [`auto_extract_bitsums`] and routed to `bitsum_polys`
//!   (split-GB basis 0 only).
//!
//! Single index-keyed type family. [`ConstraintSystem`] is the
//! canonical system shape (`var_names: Vec<String>` authoritative
//! for index↔name; equalities carry sparse `Vec<PolyTerm>` with
//! `(VarIdx, u16)` exponent pairs). [`ConstraintSystemBuilder`] is
//! the producer-side intern API; every public GB-query producer
//! (`native_ff` via `PolyIR::encode`, `smt2::parse` /
//! `parse_boolean`, `boolean::to_disjunct_systems`,
//! `cdclt::ff_theory`) constructs its output through a builder so
//! variable names are interned in encounter order with no
//! transient String-keyed struct ever materialised. The cache
//! ([`crate::incremental_context::IncrementalSolverContext`]) and
//! the `dump_smt` formatter both consume `ConstraintSystem`
//! directly.

use num_bigint::BigUint;
use num_traits::Zero;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ff::field::PrimeField;
use crate::poly::{FfPolyRing, Poly};

/// Origin of an entry in [`EncodedSystem::polynomials`], parallel to it
/// 1:1. Lets a UNSAT-core consumer attribute a core polynomial index back
/// to the source constraint without relying on positional layout
/// assumptions. `Equality(j)` carries `j` = the index into the
/// `encode_impl`-input equality list; `Rabinowitsch(d)` carries `d` = the
/// index into the disequality list. `Other` is an encoder-introduced,
/// constraint-independent polynomial (the zero assignment, field
/// polynomials) that does not correspond to a removable source constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolySource {
    Equality(usize),
    Rabinowitsch(usize),
    Other,
}

/// Encoded polynomial system ready for GB computation.
pub struct EncodedSystem {
    pub poly_ring: FfPolyRing,
    pub polynomials: Vec<Poly>,
    /// Provenance of each `polynomials[k]`, same length and order.
    pub poly_provenance: Vec<PolySource>,
    /// Number of equalities `encode_impl` received (post-rewrite /
    /// post-bitsum-extraction). Equals the producer's pre-pipeline
    /// equality count iff `rewrite_system` dropped no equality; a
    /// core consumer uses this to decide whether `Equality(j)` indices
    /// align 1:1 with its own equality frame.
    pub n_input_equalities: usize,
    /// Bitsum definition polynomials: `b0 + 2*b1 + ... - aux = 0`.
    /// These are kept separate from `polynomials` because the split-GB
    /// algorithm seeds them only into the linear basis (basis 0), not
    /// the nonlinear basis (basis 1).
    pub bitsum_polys: Vec<Poly>,
    pub var_map: HashMap<String, usize>,
}


/// Minimum chain length for [`auto_extract_bitsums`] to
/// extract a detected bitsum.
const MIN_AUTO_BITSUM_LEN: usize = 2;

/// Rewrite equalities to extract bitsum subpatterns into
/// `ConstraintSystem::bitsums`. Operates on [`PolyTerm`] lists:
/// `bits: HashSet<VarIdx>`, chain extender indexed by coefficient
/// via `BTreeMap<BigUint, Vec<(VarIdx, idx)>>`. No String allocation.
///
/// Algorithm:
/// 1. Collect `bits`: variables appearing in `system.bitsums`, plus
///    any variable `b` with an equality of the form `b·(b − 1) = 0`
///    (matched by [`detect_bit_constraint`]).
/// 2. For each equality, repeatedly find the longest sub-sum
///    `c·b_0 + 2c·b_1 + ... + 2^k·c·b_k` where each `b_i ∈ bits`
///    appears as a single-variable degree-1 term. Base coefficients
///    are tried in ascending symmetric-residue order
///    (`min(c, p − c)`, ties broken by raw value).
/// 3. On a chain of length ≥ [`MIN_AUTO_BITSUM_LEN`]: drop the
///    chain's terms from the equality, append a `c · __bitsum_N`
///    term, append the bit list to `system.bitsums`. The encoder
///    emits `b_0 + 2·b_1 + ... + 2^k·b_k − __bitsum_N = 0` into
///    `bitsum_polys` (split-GB seeder routes those to basis 0 only).
///
/// Soundness gate: chain length capped at `floor(log2(prime))` so
/// distinct bit patterns never collide modulo `prime`. The same
/// invariant gates the `basis2` propagation lemma in
/// `picus-analysis`. For cryptographic primes the cap is ~254; for
/// small primes used in regression tests (GF(7), GF(11), GF(13))
/// it's 2-3.
pub fn auto_extract_bitsums(
    system: &ConstraintSystem,
) -> ConstraintSystem {
    let p = &system.prime;

    // Bit-constrained variable set: variables with a `b·(b - 1) = 0`
    // equality plus any explicit bitsum entries.
    let mut bits: HashSet<VarIdx> = HashSet::new();
    for bs in &system.bitsums {
        for &v in bs {
            bits.insert(v);
        }
    }
    for eq in &system.equalities {
        if let Some(bit_idx) = detect_bit_constraint(eq, p) {
            bits.insert(bit_idx);
        }
    }
    if bits.is_empty() {
        return system.clone();
    }

    let mut rewritten_equalities: Vec<Vec<PolyTerm>> =
        Vec::with_capacity(system.equalities.len());
    let mut new_bitsums: Vec<Vec<VarIdx>> = system.bitsums.clone();

    // Aux indices align with the encoder's append order:
    //   user vars : 0 .. n_user
    //   witnesses : n_user .. n_user + n_diseq
    //   bitsum aux: n_user + n_diseq .. + n_bitsums
    // Pre-compute the bitsum-aux base so the rewrite-time term
    // emission and `encode_impl`'s own aux append loop agree.
    let n_user = system.var_names.len() as VarIdx;
    let n_diseq = system.disequalities.len() as VarIdx;
    let aux_base: VarIdx = n_user + n_diseq;

    for eq in &system.equalities {
        let mut current_eq: Vec<PolyTerm> = eq.clone();
        let max_iters = current_eq.len() + 1;
        for _ in 0..max_iters {
            match find_bitsum_chain(&current_eq, &bits, p, MIN_AUTO_BITSUM_LEN) {
                Some((bit_list, base_coeff, consumed)) => {
                    let aux_idx = aux_base + (new_bitsums.len() as VarIdx);
                    new_bitsums.push(bit_list);

                    let mut new_terms: Vec<PolyTerm> = current_eq
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !consumed.contains(i))
                        .map(|(_, t)| t.clone())
                        .collect();
                    new_terms.push(PolyTerm {
                        coeff: base_coeff,
                        vars: vec![(aux_idx, 1)],
                    });
                    current_eq = new_terms;
                }
                None => break,
            }
        }
        rewritten_equalities.push(current_eq);
    }

    ConstraintSystem {
        prime: system.prime.clone(),
        var_names: system.var_names.clone(),
        equalities: rewritten_equalities,
        disequalities: system.disequalities.clone(),
        assignments: system.assignments.clone(),
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

/// Match `b·(b - 1) = 0` on an [`PolyTerm`] list. The list is
/// expected to already be normalised by `rewrite_system`, so
/// `b^2` lives as `[(b_idx, 2)]` and `b` lives as `[(b_idx, 1)]`.
/// Returns the `VarIdx` of `b` on match.
fn detect_bit_constraint(eq: &[PolyTerm], p: &BigUint) -> Option<VarIdx> {
    let nonzero: Vec<&PolyTerm> = eq.iter().filter(|t| !t.coeff.is_zero()).collect();
    if nonzero.len() != 2 {
        return None;
    }
    let is_quad = |t: &&PolyTerm| t.vars.len() == 1 && t.vars[0].1 == 2;
    let is_lin = |t: &&PolyTerm| t.vars.len() == 1 && t.vars[0].1 == 1;
    let (quad, lin) = if is_quad(&nonzero[0]) && is_lin(&nonzero[1]) {
        (nonzero[0], nonzero[1])
    } else if is_quad(&nonzero[1]) && is_lin(&nonzero[0]) {
        (nonzero[1], nonzero[0])
    } else {
        return None;
    };
    if quad.vars[0].0 != lin.vars[0].0 {
        return None;
    }
    let sum = (&quad.coeff + &lin.coeff) % p;
    if !sum.is_zero() {
        return None;
    }
    Some(quad.vars[0].0)
}

/// Looks
/// for `c·b_0 + 2c·b_1 + ... + 2^(k-1)·c·b_{k-1}` where each `b_i`
/// is a known bit (degree 1 in a single index, coefficient
/// `(2^i · base) mod p`). Soundness gate: chain length capped at
/// `floor(log2(p))`.
fn find_bitsum_chain(
    eq: &[PolyTerm],
    bits: &HashSet<VarIdx>,
    p: &BigUint,
    min_len: usize,
) -> Option<(Vec<VarIdx>, BigUint, HashSet<usize>)> {
    let mut by_coeff: BTreeMap<BigUint, Vec<(VarIdx, usize)>> = BTreeMap::new();
    for (idx, t) in eq.iter().enumerate() {
        if t.coeff.is_zero() {
            continue;
        }
        if t.vars.len() == 1 && t.vars[0].1 == 1 && bits.contains(&t.vars[0].0) {
            by_coeff
                .entry(&t.coeff % p)
                .or_default()
                .push((t.vars[0].0, idx));
        }
    }
    if by_coeff.is_empty() {
        return None;
    }

    let abs_residue = |c: &BigUint| -> BigUint {
        let neg = p - c;
        if c < &neg {
            c.clone()
        } else {
            neg
        }
    };
    let mut candidates: Vec<BigUint> = by_coeff.keys().cloned().collect();
    candidates.sort_by(|a, b| {
        let ra = abs_residue(a);
        let rb = abs_residue(b);
        ra.cmp(&rb).then(a.cmp(b))
    });

    let two = BigUint::from(2u32);

    let max_chain_bits: usize = {
        let mut n = 0usize;
        let mut pow = BigUint::from(1u32);
        while &pow * &two <= *p {
            pow = pow * &two;
            n += 1;
        }
        n
    };

    let mut best: Option<(Vec<VarIdx>, BigUint, HashSet<usize>)> = None;

    for base in &candidates {
        let mut chain_vars: Vec<VarIdx> = Vec::new();
        let mut chain_idxs: HashSet<usize> = HashSet::new();
        let mut used_vars: HashSet<VarIdx> = HashSet::new();

        let mut cur = base.clone();
        loop {
            if chain_vars.len() >= max_chain_bits {
                break;
            }
            let bucket = match by_coeff.get(&cur) {
                Some(b) => b,
                None => break,
            };
            let next = bucket
                .iter()
                .filter(|(v, _)| !used_vars.contains(v))
                .min_by_key(|(_, idx)| *idx);
            match next {
                Some(&(var, idx)) => {
                    used_vars.insert(var);
                    chain_vars.push(var);
                    chain_idxs.insert(idx);
                    cur = (&cur * &two) % p;
                }
                None => break,
            }
        }

        if chain_vars.len() >= min_len {
            let pick = match &best {
                None => true,
                Some((b_vars, _, _)) => chain_vars.len() > b_vars.len(),
            };
            if pick {
                best = Some((chain_vars, base.clone(), chain_idxs));
            }
        }
    }

    best
}

/// Divide a polynomial by its leading coefficient (in DegRevLex order).
fn normalize_poly(pr: &FfPolyRing, p: Poly) -> Poly {
    let ring = &pr.ring;
    let fp = &pr.field();
    if ring.is_zero(&p) || p.num_terms() == 0 { return p; }
    // Leading term is at index 0 (polynomials are stored sorted descending).
    let lc = fp.clone_el(p.leading_coefficient().expect("nonzero polynomial has a leading term"));
    if fp.is_zero(&lc) || fp.is_one(&lc) { return p; }
    let inv = fp.div(&fp.one(), &lc).expect("non-zero leading coefficient");
    let inv_poly = pr.constant(inv);
    ring.mul(inv_poly, p)
}

// ─────────────────────────────────────────────────────────────────────
//   Index-based constraint system
// ─────────────────────────────────────────────────────────────────────
//
// `ConstraintSystem` references variables by integer index into an
// owned `var_names` list, eliminating per-monomial String allocation
// and HashMap lookups in the encoder hot path. Producers build one via
// `ConstraintSystemBuilder`; `encode` is the entry point that turns it
// into polynomials.

/// Variable index into [`ConstraintSystem::var_names`]. `u32`
/// holds 4 G variables — well beyond any practical constraint
/// system.
pub type VarIdx = u32;

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

/// Encode a [`ConstraintSystem`] into polynomials.
///
/// Pre-encode pipeline:
///   1. `compact_used_vars`: drop variables from `var_names` that
///      no equality / disequality / assignment / bitsum references
///      — keeps the polynomial ring tight. Without this,
///      `PolyIR`'s `2 * n_wires` ring exposes every `y_i` even
///      when most are never referenced, inflating the GB engine's
///      monomial table and causing pathological slowdowns on big
///      circuits.
///   2. `rewriter::rewrite_system`: canonicalise terms.
///   3. `auto_extract_bitsums`: extract bitsum chains into
///      `bitsum_polys`.
pub fn encode(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::frontend::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, true)
}

/// Like [`encode`], but passes `emit_rabinowitsch = false` to
/// `encode_impl` so no Rabinowitsch witnesses are emitted for
/// disequalities.
pub fn encode_constraint_side(
    system: &ConstraintSystem,
) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::frontend::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, false)
}

/// Compact `system.var_names` to only the variables actually
/// referenced by some equality, disequality, assignment, or
/// bitsum. Returns a new `ConstraintSystem` with renumbered
/// indices.
///
/// The ring must contain only variables that actually appear in the
/// constraint side; otherwise it gains spurious extra variables that
/// the GB engine has to factor in.
fn compact_used_vars(system: &ConstraintSystem) -> ConstraintSystem {
    use std::collections::BTreeSet;
    let mut used: BTreeSet<VarIdx> = BTreeSet::new();
    for eq in &system.equalities {
        for term in eq {
            for &(idx, _) in &term.vars {
                used.insert(idx);
            }
        }
    }
    for &(a, b) in &system.disequalities {
        used.insert(a);
        used.insert(b);
    }
    for (v, _) in &system.assignments {
        used.insert(*v);
    }
    for chain in &system.bitsums {
        for &v in chain {
            used.insert(v);
        }
    }
    if used.len() == system.var_names.len() {
        return system.clone();
    }
    let used_sorted: Vec<VarIdx> = used.into_iter().collect();
    let mut input_to_compact: HashMap<VarIdx, VarIdx> = HashMap::with_capacity(used_sorted.len());
    for (compact_idx, &input_idx) in used_sorted.iter().enumerate() {
        input_to_compact.insert(input_idx, compact_idx as VarIdx);
    }
    let new_var_names: Vec<String> = used_sorted
        .iter()
        .map(|&idx| system.var_names[idx as usize].clone())
        .collect();
    let new_equalities: Vec<Vec<PolyTerm>> = system
        .equalities
        .iter()
        .map(|eq| {
            eq.iter()
                .map(|t| PolyTerm {
                    coeff: t.coeff.clone(),
                    vars: t
                        .vars
                        .iter()
                        .map(|&(idx, exp)| (input_to_compact[&idx], exp))
                        .collect(),
                })
                .collect()
        })
        .collect();
    let new_disequalities: Vec<(VarIdx, VarIdx)> = system
        .disequalities
        .iter()
        .map(|&(a, b)| (input_to_compact[&a], input_to_compact[&b]))
        .collect();
    let new_assignments: Vec<(VarIdx, BigUint)> = system
        .assignments
        .iter()
        .map(|(v, val)| (input_to_compact[v], val.clone()))
        .collect();
    let new_bitsums: Vec<Vec<VarIdx>> = system
        .bitsums
        .iter()
        .map(|chain| chain.iter().map(|v| input_to_compact[v]).collect())
        .collect();
    ConstraintSystem {
        prime: system.prime.clone(),
        var_names: new_var_names,
        equalities: new_equalities,
        disequalities: new_disequalities,
        assignments: new_assignments,
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

fn encode_impl(
    system: &ConstraintSystem,
    emit_rabinowitsch: bool,
) -> Result<EncodedSystem, String> {
    // Ring is `var_names` from the system, then aux witness vars for
    // disequalities and bitsums (one each, appended in order).
    let mut var_names: Vec<String> = system.var_names.clone();
    let n_user = var_names.len();

    let n_diseq = system.disequalities.len();
    let mut witness_idxs: Vec<VarIdx> = Vec::with_capacity(n_diseq);
    for i in 0..n_diseq {
        let name = format!("__w_diseq_{}", i);
        witness_idxs.push(var_names.len() as VarIdx);
        var_names.push(name);
    }

    let n_bitsum = system.bitsums.len();
    let mut bitsum_aux_idxs: Vec<VarIdx> = Vec::with_capacity(n_bitsum);
    for i in 0..n_bitsum {
        let name = format!("__bitsum_{}", i);
        bitsum_aux_idxs.push(var_names.len() as VarIdx);
        var_names.push(name);
    }

    let n_vars = var_names.len();
    if n_vars > 5000 {
        return Err(format!(
            "too many variables ({}) for polynomial ring construction",
            n_vars
        ));
    }

    let field = PrimeField::new(system.prime.clone());
    let poly_ring = FfPolyRing::new(field, var_names.clone());

    // Build var_map for downstream callers that still consult it
    // (e.g. SUBP_CONSTANT_NAMES filtering in the picus crate).
    let mut var_map: HashMap<String, usize> = HashMap::with_capacity(n_vars);
    for (i, name) in var_names.iter().enumerate() {
        var_map.insert(name.clone(), i);
    }

    let mut polynomials: Vec<Poly> = Vec::new();
    // Parallel to `polynomials`: source constraint of each entry.
    let mut provenance: Vec<PolySource> = Vec::new();

    // Equalities: sum(coeff · prod_vars) = 0. Equality terms may
    // reference aux variables introduced by
    // `auto_extract_bitsums` (indices in the bitsum-aux
    // range); the bounds check is against the full ring size.
    let n_ring = var_names.len();
    for (eq_idx, eq) in system.equalities.iter().enumerate() {
        let mut poly = poly_ring.zero();
        for term in eq {
            let c = poly_ring.field().from_biguint(&term.coeff);
            let mut t = poly_ring.constant(c);
            for &(vidx, exp) in &term.vars {
                if (vidx as usize) >= n_ring {
                    return Err(format!(
                        "equality term references var_idx {} but ring has only {} vars",
                        vidx, n_ring
                    ));
                }
                let v_poly = poly_ring.var(vidx as usize);
                for _ in 0..exp {
                    t = poly_ring.mul(t, poly_ring.clone_poly(&v_poly));
                }
            }
            poly = poly_ring.add(poly, t);
        }
        if !poly_ring.is_zero(&poly) {
            polynomials.push(poly);
            provenance.push(PolySource::Equality(eq_idx));
        }
    }

    // Assignments: v - val = 0.
    for (v_idx, val) in &system.assignments {
        if (*v_idx as usize) >= n_user {
            return Err(format!(
                "assignment references var_idx {} but only {} user vars exist",
                v_idx, n_user
            ));
        }
        let v = poly_ring.var(*v_idx as usize);
        let c = poly_ring.constant(poly_ring.field().from_biguint(val));
        let diff = poly_ring.sub(v, c);
        if !poly_ring.is_zero(&diff) {
            polynomials.push(diff);
            provenance.push(PolySource::Other);
        }
    }

    // Rabinowitsch trick: (a - b) · w_i - 1 = 0 for each disequality.
    if emit_rabinowitsch {
        for (d_idx, ((a, b), &w_idx)) in
            system.disequalities.iter().zip(witness_idxs.iter()).enumerate()
        {
            if (*a as usize) >= n_user || (*b as usize) >= n_user {
                return Err(format!(
                    "disequality references var_idx >= {} but only {} user vars exist",
                    a.max(b),
                    n_user
                ));
            }
            let diff = poly_ring.sub(
                poly_ring.var(*a as usize),
                poly_ring.var(*b as usize),
            );
            let prod = poly_ring.mul(diff, poly_ring.var(w_idx as usize));
            let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
            polynomials.push(rabinowitsch);
            provenance.push(PolySource::Rabinowitsch(d_idx));
        }
    }

    // Bitsum definitions: b0 + 2·b1 + 4·b2 + ... - aux = 0.
    let mut bitsum_polys: Vec<Poly> = Vec::new();
    for (bs, &aux_idx) in system.bitsums.iter().zip(bitsum_aux_idxs.iter()) {
        let fp = &poly_ring.field();
        let two = fp.int_hom().map(2);
        let mut sum = poly_ring.zero();
        let mut coeff = poly_ring.field().one();
        for &bit_idx in bs {
            if (bit_idx as usize) >= n_user {
                return Err(format!(
                    "bitsum references var_idx {} but only {} user vars exist",
                    bit_idx, n_user
                ));
            }
            let term = poly_ring.scale(fp.clone_el(&coeff), poly_ring.var(bit_idx as usize));
            sum = poly_ring.add(sum, term);
            coeff = fp.mul_ref(&coeff, &two);
        }
        let aux = poly_ring.var(aux_idx as usize);
        let def_poly = poly_ring.sub(sum, aux);
        if !poly_ring.is_zero(&def_poly) {
            bitsum_polys.push(normalize_poly(&poly_ring, def_poly));
        }
    }

    // Field polynomials: x^p - x = 0 for every ring variable when
    // `prime <= 1000`. Matches the gate in `encode_impl`.
    if system.add_field_polys {
        let p_usize = system.prime.to_u64_digits();
        if p_usize.len() == 1 && p_usize[0] <= 1000 {
            let p_val = p_usize[0] as usize;
            for i in 0..poly_ring.n_vars() {
                let x = poly_ring.var(i);
                let mut x_p = poly_ring.one();
                let mut base = poly_ring.clone_poly(&x);
                let mut exp = p_val;
                while exp > 0 {
                    if exp & 1 == 1 {
                        x_p = poly_ring.mul(x_p, poly_ring.clone_poly(&base));
                    }
                    base = poly_ring.mul(
                        poly_ring.clone_poly(&base),
                        poly_ring.clone_poly(&base),
                    );
                    exp >>= 1;
                }
                let field_poly = poly_ring.sub(x_p, x);
                if !poly_ring.is_zero(&field_poly) {
                    polynomials.push(field_poly);
                    provenance.push(PolySource::Other);
                }
            }
        }
    }

    debug_assert_eq!(
        provenance.len(),
        polynomials.len(),
        "poly_provenance must stay parallel to polynomials"
    );
    let polynomials = polynomials
        .into_iter()
        .map(|p| normalize_poly(&poly_ring, p))
        .collect();

    Ok(EncodedSystem {
        poly_ring,
        polynomials,
        poly_provenance: provenance,
        n_input_equalities: system.equalities.len(),
        bitsum_polys,
        var_map,
    })
}

#[cfg(test)]
mod tests;
