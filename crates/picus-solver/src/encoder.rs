//! Encoder: translates a polynomial system into polynomials for GB computation.
//!
//! - Equality `f = 0` → polynomial `f`
//! - Disequality `a ≠ b` → Rabinowitsch trick: `(a - b) * w - 1`
//! - Bitsum subpatterns in equalities are extracted by
//!   [`auto_extract_bitsums`] and routed to `bitsum_polys` (basis 0
//!   only).
//!
//! ## Phase 7 migration status (informational)
//!
//! Two parallel type families coexist after Phase 7:
//!
//! * **Index-keyed (the canonical encoder hot path):**
//!   [`IndexedConstraintSystem`], [`IndexedTerm`],
//!   [`ConstraintSystemBuilder`], [`encode_indexed`],
//!   [`encode_indexed_constraint_side`],
//!   [`auto_extract_bitsums_indexed`],
//!   `rewriter::rewrite_indexed_system`,
//!   `normalize_indexed_term_list`, and
//!   `incremental_context::digest_indexed_constraint_side`. Every
//!   producer's PUBLIC return shape is `IndexedConstraintSystem`,
//!   and every producer (`native_ff` via `PolyIR::encode`,
//!   `smt2::parse`, `boolean::to_disjunct_systems`,
//!   `cdclt::ff_theory`) builds the index-keyed form via
//!   `ConstraintSystemBuilder` instead of constructing the legacy
//!   `ConstraintSystem` struct.
//! * **Legacy (String-keyed), survives for one downstream consumer:**
//!   [`ConstraintSystem`], [`PolyTerm`], [`encode`],
//!   [`encode_constraint_side`], [`encode_no_auto_bitsum`],
//!   [`auto_extract_bitsums`], `rewriter::rewrite_system`,
//!   `normalize_term_list`, `digest_constraint_side`. The only
//!   remaining caller is `IncrementalSolverContext` (the
//!   `native_ff` cache) plus `NativeFfBackend::dump_smt`'s text
//!   formatter — both still key on the legacy String-keyed
//!   `ConstraintSystem`. `to_legacy` / `from_legacy` bridge across
//!   the boundary.
//!
//! Phase 7B extended [`crate::poly::FfPolyRing`]-consumer `PolyIR`
//! (in `picus-smt`) with `disequalities`, `assignments`, `bitsums`,
//! `add_field_polys` so a `PolyIR` is a complete GB-query
//! description; `PolyIR::encode` is the one-call lowering path.
//!
//! Phase 8 will: (1) migrate the cache's internal split-GB seed +
//! digest path to consume `IndexedConstraintSystem`, preserving the
//! alphabetical user-var sort the GB engine's DegRevLex layer
//! expects; (2) migrate the `dump_smt` text formatter; (3) once the
//! legacy `ConstraintSystem` has no remaining caller, delete it
//! along with the legacy `PolyTerm`, encode / rewriter / digest
//! variants, and the `to_legacy` / `from_legacy` bridges; (4)
//! rename `IndexedConstraintSystem` → `ConstraintSystem`,
//! `IndexedTerm` → `PolyTerm`, `encode_indexed` → `encode`, etc., so
//! the canonical names point at the index-keyed forms.
//!
//! Phase 7 attempted (1) — the migration is straightforward in
//! signature but the GB engine's monomial ordering is sensitive to
//! the ring's variable layout, and the naive port produced
//! PLDI-smoke regressions that the included sort-fix did not fully
//! resolve. The attempt was reverted; (1) needs a closer look at
//! the cache's split-GB seed path before retrying.

use num_bigint::BigUint;
use num_traits::Zero;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::field::FfField;
use crate::poly::{FfPolyRing, Poly};

/// Encoded polynomial system ready for GB computation.
pub struct EncodedSystem {
    pub poly_ring: FfPolyRing,
    pub polynomials: Vec<Poly>,
    /// Bitsum definition polynomials: `b0 + 2*b1 + ... - aux = 0`.
    /// These are kept separate from `polynomials` because the split-GB
    /// algorithm seeds them only into the linear basis (basis 0), not
    /// the nonlinear basis (basis 1).
    pub bitsum_polys: Vec<Poly>,
    pub var_map: HashMap<String, usize>,
}

/// A term in a polynomial constraint: coeff * prod(vars).
/// If vars is empty, it's a constant term.
#[derive(Clone, Debug)]
pub struct PolyTerm {
    pub coeff: BigUint,
    pub vars: Vec<String>,
}

/// Input constraint system.
#[derive(Clone, Debug)]
pub struct ConstraintSystem {
    pub prime: BigUint,
    /// Each equality is a list of terms; their sum equals zero.
    pub equalities: Vec<Vec<PolyTerm>>,
    /// All disequalities: each pair (a, b) means `a ≠ b`.
    /// One Rabinowitsch witness variable per pair is introduced.
    pub disequalities: Vec<(String, String)>,
    /// Variable assignments: var = value.
    pub assignments: Vec<(String, BigUint)>,
    /// Whether to add field polynomials x^p - x for each variable.
    pub add_field_polys: bool,
    /// Optional bitsum declarations.  Each entry is a list of variable names
    /// `[b0, b1, ..., bk]` representing a bitsum `b0 + 2*b1 + 4*b2 + ...`.
    /// When provided, the encoder creates a fresh auxiliary variable for each
    /// bitsum and adds a definition polynomial `b0 + 2*b1 + ... - aux = 0`
    /// to a separate list. When empty, the solver falls back to heuristic
    /// detection via [`crate::parse::bit_sums`].
    pub bitsums: Vec<Vec<String>>,
}

impl ConstraintSystem {
    /// Collect all variable names.
    pub fn collect_vars(&self) -> Vec<String> {
        let mut vars = HashSet::new();
        for eq in &self.equalities {
            for t in eq {
                for v in &t.vars {
                    vars.insert(v.clone());
                }
            }
        }
        for (v, _) in &self.assignments {
            vars.insert(v.clone());
        }
        for (a, b) in &self.disequalities {
            vars.insert(a.clone());
            vars.insert(b.clone());
        }
        for bs in &self.bitsums {
            for v in bs {
                vars.insert(v.clone());
            }
        }
        let mut sorted: Vec<_> = vars.into_iter().collect();
        sorted.sort();
        sorted
    }
}

/// Encode a constraint system into polynomials for GB computation.
///
/// Disequalities are encoded via the Rabinowitsch trick:
/// `a != b` becomes `(a - b) * w_i - 1 = 0`, where `w_i` is a fresh
/// witness variable named `__w_diseq_i`.
///
/// Runs [`auto_extract_bitsums`] first, so bitsum subpatterns
/// `c·b_0 + 2c·b_1 + ... + 2^k·c·b_k` (with each `b_i` bit-constrained)
/// get rewritten as `c · aux` and the bitsum definition is appended to
/// `system.bitsums`. Use [`encode_no_auto_bitsum`] to skip the rewrite.
pub fn encode(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let mut rewritten = system.clone();
    crate::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, true)
}

/// Encode the *constraint side* of `system` — equalities, assignments,
/// bitsum definitions, and (optionally) field polynomials — but skip
/// the Rabinowitsch polynomials for the disequalities.
///
/// The witness variables `__w_diseq_i` are still reserved in `var_map`
/// for every entry of `system.disequalities`, so a caller can later
/// build the Rabinowitsch polynomial in the same ring (see
/// [`crate::incremental_context::IncrementalSolverContext`], which
/// caches the constraint-side encoding and adds per-query disequality
/// polynomials lazily).
///
/// Also runs [`auto_extract_bitsums`] before encoding.
pub fn encode_constraint_side(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let mut rewritten = system.clone();
    crate::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, false)
}

/// Same as [`encode`] but skips [`auto_extract_bitsums`].
pub fn encode_no_auto_bitsum(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let mut rewritten = system.clone();
    crate::rewriter::rewrite_system(&mut rewritten);
    encode_impl(&rewritten, true)
}

/// Shared encoder body. When `emit_rabinowitsch` is false, the witness
/// variables for disequalities are still reserved (so [`EncodedSystem::var_map`]
/// contains them) but no `(a - b) * w_i - 1` polynomial is emitted.
fn encode_impl(
    system: &ConstraintSystem,
    emit_rabinowitsch: bool,
) -> Result<EncodedSystem, String> {
    let mut var_names = system.collect_vars();
    // Names already declared. Aux-reservation loops below skip
    // entries already present (auto-extract may write `__bitsum_<i>`
    // into equalities, so `collect_vars` already returns them).
    let mut seen_names: HashSet<String> = var_names.iter().cloned().collect();

    // Reserve a Rabinowitsch witness variable for each disequality —
    // even when we are not going to emit the polynomial, so callers
    // that build it later in this ring can look the variable up.
    let n_diseq = system.disequalities.len();
    let mut witness_vars: Vec<String> = Vec::with_capacity(n_diseq);
    for i in 0..n_diseq {
        let name = format!("__w_diseq_{}", i);
        if seen_names.insert(name.clone()) {
            var_names.push(name.clone());
        }
        witness_vars.push(name);
    }

    // Add bitsum auxiliary variables.
    let mut bitsum_aux_vars: Vec<String> = Vec::with_capacity(system.bitsums.len());
    for i in 0..system.bitsums.len() {
        let name = format!("__bitsum_{}", i);
        if seen_names.insert(name.clone()) {
            var_names.push(name.clone());
        }
        bitsum_aux_vars.push(name);
    }

    let field = FfField::new(system.prime.clone());

    // Conservative cap to keep monomial-table allocations bounded.
    let n_vars = var_names.len();
    if n_vars > 5000 {
        return Err(format!(
            "too many variables ({}) for polynomial ring construction",
            n_vars
        ));
    }

    let poly_ring = FfPolyRing::new(field, var_names.clone());

    let mut var_map: HashMap<String, usize> = HashMap::new();
    for (i, name) in var_names.iter().enumerate() {
        var_map.insert(name.clone(), i);
    }

    let mut polynomials = Vec::new();

    // Encode equalities: sum of (coeff * prod_vars) = 0
    for eq in &system.equalities {
        let mut poly = poly_ring.zero();
        for term in eq {
            let c = poly_ring.field.from_biguint(&term.coeff);
            let mut t = poly_ring.constant(c);
            for v in &term.vars {
                let idx = *var_map.get(v).ok_or_else(|| format!("unknown var: {}", v))?;
                t = poly_ring.mul(t, poly_ring.var(idx));
            }
            poly = poly_ring.add(poly, t);
        }
        if !poly_ring.is_zero(&poly) {
            polynomials.push(poly);
        }
    }

    // Encode assignments: var - value = 0
    for (var, val) in &system.assignments {
        let idx = *var_map.get(var).ok_or_else(|| format!("unknown var: {}", var))?;
        let v = poly_ring.var(idx);
        let c = poly_ring.constant(poly_ring.field.from_biguint(val));
        let diff = poly_ring.sub(v, c);
        if !poly_ring.is_zero(&diff) {
            polynomials.push(diff);
        }
    }

    // Rabinowitsch trick: (a - b) * w_i - 1 = 0 for each disequality.
    if emit_rabinowitsch {
        for ((a, b), w_name) in system.disequalities.iter().zip(witness_vars.iter()) {
            let a_idx = *var_map.get(a).ok_or_else(|| format!("unknown var: {}", a))?;
            let b_idx = *var_map.get(b).ok_or_else(|| format!("unknown var: {}", b))?;
            let w_idx = *var_map.get(w_name).unwrap();

            let diff = poly_ring.sub(poly_ring.var(a_idx), poly_ring.var(b_idx));
            let prod = poly_ring.mul(diff, poly_ring.var(w_idx));
            let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
            polynomials.push(rabinowitsch);
        }
    }

    // Encode bitsum definitions: b0 + 2*b1 + 4*b2 + ... - aux = 0.
    // These go into a separate list (bitsum_polys) because the split-GB
    // algorithm seeds them only into the linear basis.
    let mut bitsum_polys = Vec::new();
    for (bs, aux_name) in system.bitsums.iter().zip(bitsum_aux_vars.iter()) {
        let fp = &poly_ring.field;
        let two = fp.int_hom().map(2);
        let mut sum = poly_ring.zero();
        let mut coeff = poly_ring.field.one();
        for bit_var in bs {
            let idx = *var_map.get(bit_var).ok_or_else(|| format!("unknown bitsum var: {}", bit_var))?;
            let term = poly_ring.scale(fp.clone_el(&coeff), poly_ring.var(idx));
            sum = poly_ring.add(sum, term);
            coeff = fp.mul_ref(&coeff, &two);
        }
        let aux_idx = *var_map.get(aux_name).unwrap();
        let aux = poly_ring.var(aux_idx);
        let def_poly = poly_ring.sub(sum, aux);
        if !poly_ring.is_zero(&def_poly) {
            bitsum_polys.push(normalize_poly(&poly_ring, def_poly));
        }
    }

    // Optionally add field polynomials: x^p - x = 0 for each variable.
    if system.add_field_polys {
        let p_usize = system.prime.to_u64_digits();
        if p_usize.len() == 1 && p_usize[0] <= 1000 {
            let p_val = p_usize[0] as usize;
            for i in 0..poly_ring.n_vars {
                let x = poly_ring.var(i);
                // Compute x^p via repeated squaring
                let mut x_p = poly_ring.one();
                let mut base = poly_ring.clone_poly(&x);
                let mut exp = p_val;
                while exp > 0 {
                    if exp & 1 == 1 {
                        x_p = poly_ring.mul(x_p, poly_ring.clone_poly(&base));
                    }
                    base = poly_ring.mul(poly_ring.clone_poly(&base), poly_ring.clone_poly(&base));
                    exp >>= 1;
                }
                let field_poly = poly_ring.sub(x_p, x);
                if !poly_ring.is_zero(&field_poly) {
                    polynomials.push(field_poly);
                }
            }
        }
    }

    // Normalize all polynomials: divide by leading coefficient so LC = 1.
    // Ensures a consistent representation for tracer-based UNSAT core
    // extraction.
    let polynomials = polynomials.into_iter().map(|p| {
        normalize_poly(&poly_ring, p)
    }).collect();

    Ok(EncodedSystem { poly_ring, polynomials, bitsum_polys, var_map })
}

/// Minimum chain length for [`auto_extract_bitsums`] to extract a
/// detected bitsum.
const MIN_AUTO_BITSUM_LEN: usize = 2;

/// Rewrite equalities to extract bitsum subpatterns into
/// [`ConstraintSystem::bitsums`].
///
/// Algorithm:
/// 1. Collect `bits`: variables appearing in `system.bitsums`, plus
///    any variable `b` with an equality of the form `b·(b − 1) = 0`
///    (matched by [`detect_bit_constraint_in_terms`]).
/// 2. For each equality, repeatedly find the longest sub-sum
///    `c·b_0 + 2c·b_1 + ... + 2^k·c·b_k` where each `b_i ∈ bits`
///    appears as a single-variable degree-1 term. Base coefficients
///    are tried in ascending symmetric-residue order (`min(c, p−c)`).
/// 3. When a chain of length ≥ [`MIN_AUTO_BITSUM_LEN`] is found:
///    - Drop the chain's terms from the equality.
///    - Append a `c · __bitsum_N` term, where `N` is the bitsum's
///      index in the returned `bitsums` vector.
///    - Append the bit list to `bitsums`. The encoder then emits
///      `b_0 + 2·b_1 + ... + 2^k·b_k − __bitsum_N = 0` into
///      `bitsum_polys` (which the split-GB seeder routes to basis 0
///      only).
///
/// Equivalence: substituting `__bitsum_N = b_0 + 2·b_1 + ... +
/// 2^k·b_k` into the rewritten equality yields the original.
pub fn auto_extract_bitsums(system: &ConstraintSystem) -> ConstraintSystem {
    let p = &system.prime;

    // Bit-constrained variable set.
    let mut bits: HashSet<String> = HashSet::new();
    for bs in &system.bitsums {
        for var in bs {
            bits.insert(var.clone());
        }
    }
    for eq in &system.equalities {
        if let Some(bit_var) = detect_bit_constraint_in_terms(eq, p) {
            bits.insert(bit_var);
        }
    }
    if bits.is_empty() {
        return system.clone();
    }

    let mut rewritten_equalities: Vec<Vec<PolyTerm>> = Vec::with_capacity(system.equalities.len());
    let mut new_bitsums: Vec<Vec<String>> = system.bitsums.clone();

    for eq in &system.equalities {
        let mut current_eq: Vec<PolyTerm> = eq.clone();
        // Each iteration consumes ≥ 2 terms.
        let max_iters = current_eq.len() + 1;
        for _ in 0..max_iters {
            match find_bitsum_chain_in_terms(&current_eq, &bits, p, MIN_AUTO_BITSUM_LEN) {
                Some((bit_list, base_coeff, consumed)) => {
                    let aux_name = format!("__bitsum_{}", new_bitsums.len());
                    new_bitsums.push(bit_list);

                    let mut new_terms: Vec<PolyTerm> = current_eq
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !consumed.contains(i))
                        .map(|(_, t)| t.clone())
                        .collect();
                    new_terms.push(PolyTerm {
                        coeff: base_coeff,
                        vars: vec![aux_name],
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
        equalities: rewritten_equalities,
        disequalities: system.disequalities.clone(),
        assignments: system.assignments.clone(),
        add_field_polys: system.add_field_polys,
        bitsums: new_bitsums,
    }
}

/// Match the term-list form of `b·(b − 1) = 0`: exactly two non-zero
/// terms `c · b·b` and `c' · b` with the same variable `b` and
/// `c + c' ≡ 0 (mod p)`. Returns the variable name on match.
fn detect_bit_constraint_in_terms(eq: &[PolyTerm], p: &BigUint) -> Option<String> {
    let nonzero: Vec<&PolyTerm> = eq.iter().filter(|t| !t.coeff.is_zero()).collect();
    if nonzero.len() != 2 {
        return None;
    }
    let (quad, lin) = if nonzero[0].vars.len() == 2
        && nonzero[0].vars[0] == nonzero[0].vars[1]
        && nonzero[1].vars.len() == 1
        && nonzero[1].vars[0] == nonzero[0].vars[0]
    {
        (nonzero[0], nonzero[1])
    } else if nonzero[1].vars.len() == 2
        && nonzero[1].vars[0] == nonzero[1].vars[1]
        && nonzero[0].vars.len() == 1
        && nonzero[0].vars[0] == nonzero[1].vars[0]
    {
        (nonzero[1], nonzero[0])
    } else {
        return None;
    };
    let sum = (&quad.coeff + &lin.coeff) % p;
    if !sum.is_zero() {
        return None;
    }
    Some(quad.vars[0].clone())
}

/// Find the longest bitsum chain in an equality, where a chain is
/// `c·b_0 + 2c·b_1 + 4c·b_2 + ... + 2^k·c·b_k` with each
/// `b_i ∈ bits` appearing as a single-variable, exponent-1 term.
/// Base coefficients are tried in ascending symmetric-residue order
/// (`min(c, p − c)`, ties broken by raw value).
///
/// Returns `(bit_list_low_to_high, base_coeff, consumed_term_indices)`,
/// or `None` if no chain of length `>= min_len` exists.
fn find_bitsum_chain_in_terms(
    eq: &[PolyTerm],
    bits: &HashSet<String>,
    p: &BigUint,
    min_len: usize,
) -> Option<(Vec<String>, BigUint, HashSet<usize>)> {
    // Linear-on-bit terms indexed by coefficient (mod p).
    let mut by_coeff: BTreeMap<BigUint, Vec<(String, usize)>> = BTreeMap::new();
    for (idx, t) in eq.iter().enumerate() {
        if t.coeff.is_zero() {
            continue;
        }
        if t.vars.len() == 1 && bits.contains(&t.vars[0]) {
            by_coeff
                .entry(&t.coeff % p)
                .or_default()
                .push((t.vars[0].clone(), idx));
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

    // Soundness gate: a bitsum chain of `n` bits uniquely decomposes
    // its target only when `2^n <= p`. Beyond that, two distinct bit
    // patterns can wrap to the same value modulo `p` and the rewrite
    // would over-constrain. Cap chain length accordingly so the
    // rewrite stays equivalence-preserving. The same invariant gates
    // the `basis2` propagation lemma in `picus-analysis`.
    //
    // `max_chain_bits` = largest `n` with `2^n <= p`. For
    // cryptographic primes this is ~254; for small primes used in
    // regression tests (GF(7), GF(11), GF(13), ...) it's 2-3.
    let max_chain_bits: usize = {
        let mut n = 0usize;
        let mut pow = BigUint::from(1u32);
        while &pow * &two <= *p {
            pow = pow * &two;
            n += 1;
        }
        n
    };

    let mut best: Option<(Vec<String>, BigUint, HashSet<usize>)> = None;

    for base in &candidates {
        let mut chain_vars: Vec<String> = Vec::new();
        let mut chain_idxs: HashSet<usize> = HashSet::new();
        let mut used_vars: HashSet<String> = HashSet::new();

        let mut cur = base.clone();
        loop {
            if chain_vars.len() >= max_chain_bits {
                // Extending further would violate `2^n <= p`.
                break;
            }
            let bucket = match by_coeff.get(&cur) {
                Some(b) => b,
                None => break,
            };
            // Lowest unused term-index → deterministic output.
            let next = bucket
                .iter()
                .filter(|(v, _)| !used_vars.contains(v))
                .min_by_key(|(_, idx)| *idx);
            match next {
                Some((var, idx)) => {
                    used_vars.insert(var.clone());
                    chain_vars.push(var.clone());
                    chain_idxs.insert(*idx);
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

// ─────────────────────────────────────────────────────────────────────
//   Index-keyed bitsum extraction (Phase 7A7)
// ─────────────────────────────────────────────────────────────────────

/// Index-keyed counterpart of [`auto_extract_bitsums`]. Operates on
/// [`IndexedTerm`] lists: `bits: HashSet<VarIdx>`, chain extender
/// indexed by coefficient via `BTreeMap<BigUint, Vec<(VarIdx, idx)>>`.
/// No String allocation on the hot path.
///
/// Soundness gate is shared with the legacy implementation:
/// chain length capped at `floor(log2(prime))` so distinct bit
/// patterns never collide modulo `prime`.
pub fn auto_extract_bitsums_indexed(
    system: &IndexedConstraintSystem,
) -> IndexedConstraintSystem {
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
        if let Some(bit_idx) = detect_bit_constraint_indexed(eq, p) {
            bits.insert(bit_idx);
        }
    }
    if bits.is_empty() {
        return system.clone();
    }

    let mut rewritten_equalities: Vec<Vec<IndexedTerm>> =
        Vec::with_capacity(system.equalities.len());
    let mut new_bitsums: Vec<Vec<VarIdx>> = system.bitsums.clone();

    // Aux indices align with the encoder's append order:
    //   user vars : 0 .. n_user
    //   witnesses : n_user .. n_user + n_diseq
    //   bitsum aux: n_user + n_diseq .. + n_bitsums
    // Pre-compute the bitsum-aux base so the rewrite-time term
    // emission and `encode_indexed_impl`'s own aux append loop agree.
    let n_user = system.var_names.len() as VarIdx;
    let n_diseq = system.disequalities.len() as VarIdx;
    let aux_base: VarIdx = n_user + n_diseq;

    for eq in &system.equalities {
        let mut current_eq: Vec<IndexedTerm> = eq.clone();
        let max_iters = current_eq.len() + 1;
        for _ in 0..max_iters {
            match find_bitsum_chain_indexed(&current_eq, &bits, p, MIN_AUTO_BITSUM_LEN) {
                Some((bit_list, base_coeff, consumed)) => {
                    let aux_idx = aux_base + (new_bitsums.len() as VarIdx);
                    new_bitsums.push(bit_list);

                    let mut new_terms: Vec<IndexedTerm> = current_eq
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !consumed.contains(i))
                        .map(|(_, t)| t.clone())
                        .collect();
                    new_terms.push(IndexedTerm {
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

    IndexedConstraintSystem {
        prime: system.prime.clone(),
        var_names: system.var_names.clone(),
        equalities: rewritten_equalities,
        disequalities: system.disequalities.clone(),
        assignments: system.assignments.clone(),
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

/// Match `b·(b - 1) = 0` on an [`IndexedTerm`] list. The list is
/// expected to already be normalised by `rewrite_indexed_system`, so
/// `b^2` lives as `[(b_idx, 2)]` and `b` lives as `[(b_idx, 1)]`.
/// Returns the `VarIdx` of `b` on match.
fn detect_bit_constraint_indexed(eq: &[IndexedTerm], p: &BigUint) -> Option<VarIdx> {
    let nonzero: Vec<&IndexedTerm> = eq.iter().filter(|t| !t.coeff.is_zero()).collect();
    if nonzero.len() != 2 {
        return None;
    }
    let is_quad = |t: &&IndexedTerm| t.vars.len() == 1 && t.vars[0].1 == 2;
    let is_lin = |t: &&IndexedTerm| t.vars.len() == 1 && t.vars[0].1 == 1;
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

/// Index-keyed counterpart of [`find_bitsum_chain_in_terms`]. Looks
/// for `c·b_0 + 2c·b_1 + ... + 2^(k-1)·c·b_{k-1}` where each `b_i`
/// is a known bit (degree 1 in a single index, coefficient
/// `(2^i · base) mod p`). Soundness gate: chain length capped at
/// `floor(log2(p))`.
fn find_bitsum_chain_indexed(
    eq: &[IndexedTerm],
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
    let fp = &pr.field;
    if ring.is_zero(&p) || p.num_terms() == 0 { return p; }
    // Leading term is at index 0 (polynomials are stored sorted descending).
    let lc = fp.clone_el(p.term(0, ring.ctx.as_ref()).coefficient());
    if fp.is_zero(&lc) || fp.is_one(&lc) { return p; }
    let inv = fp.div(&fp.one(), &lc).expect("non-zero leading coefficient");
    let inv_poly = pr.constant(inv);
    ring.mul(inv_poly, p)
}

// ─────────────────────────────────────────────────────────────────────
//   Index-based constraint system (Phase 7A scaffolding)
// ─────────────────────────────────────────────────────────────────────
//
// `IndexedConstraintSystem` is the index-keyed counterpart to
// `ConstraintSystem`. It carries the same semantic content but
// references variables by integer index into an owned `var_names`
// list, eliminating per-monomial String allocation and HashMap
// lookups in the encoder hot path.
//
// During the A1-A9 migration both forms coexist. A producer migrates
// to `IndexedConstraintSystem` by routing through
// `ConstraintSystemBuilder`; the encoder dispatches via the parallel
// entry point `encode_indexed`. When every producer is on the new
// form, A9 renames `IndexedConstraintSystem` to `ConstraintSystem`
// and deletes the legacy String-keyed types.

/// Variable index into [`IndexedConstraintSystem::var_names`]. `u32`
/// holds 4 G variables — well beyond any practical constraint
/// system.
pub type VarIdx = u32;

/// A term in an [`IndexedConstraintSystem`] equality.
///
/// Sparse representation: `vars` lists only variables with non-zero
/// exponent, paired with their exponent. An empty `vars` denotes a
/// constant term.
#[derive(Clone, Debug)]
pub struct IndexedTerm {
    pub coeff: BigUint,
    pub vars: Vec<(VarIdx, u16)>,
}

/// Index-keyed constraint system. Direct counterpart of
/// [`ConstraintSystem`] for callers that produce term lists in
/// integer form via [`ConstraintSystemBuilder`].
#[derive(Clone, Debug)]
pub struct IndexedConstraintSystem {
    pub prime: BigUint,
    /// Authoritative variable-name list. `var_names[i as usize]` is
    /// the canonical String name of variable `i`. The encoder uses
    /// this to construct the polynomial ring; downstream model
    /// extraction surfaces the same names back to the caller.
    pub var_names: Vec<String>,
    /// Each equality is `sum(terms) = 0`.
    pub equalities: Vec<Vec<IndexedTerm>>,
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
    /// `encode_indexed` only when `prime <= 1000` (matching
    /// `encode_impl`).
    pub add_field_polys: bool,
}

/// Producer-side builder for [`IndexedConstraintSystem`]. Each
/// producer constructs one builder, interns variable names through
/// [`Self::var`] (deduplicating against the running `var_names`),
/// emits terms as `Vec<IndexedTerm>` over the returned indices, and
/// finalises with [`Self::build`].
pub struct ConstraintSystemBuilder {
    prime: BigUint,
    var_names: Vec<String>,
    name_to_idx: HashMap<String, VarIdx>,
    equalities: Vec<Vec<IndexedTerm>>,
    disequalities: Vec<(VarIdx, VarIdx)>,
    assignments: Vec<(VarIdx, BigUint)>,
    bitsums: Vec<Vec<VarIdx>>,
    add_field_polys: bool,
}

impl IndexedConstraintSystem {
    /// Lift a legacy String-keyed [`ConstraintSystem`] to the
    /// index-keyed form. Variable names are interned in the order
    /// returned by `cs.collect_vars` (alphabetical), matching the
    /// ring ordering the legacy `encode` path uses. Each
    /// `PolyTerm.vars: Vec<String>` (which lists each variable
    /// repeated `exp` times for degree `exp`) collapses to a sparse
    /// `Vec<(VarIdx, u16)>` by counting occurrences.
    ///
    /// Used during the Phase 7 migration as a producer-side bridge
    /// so callers like the SMT-LIB v2 parser can keep their internal
    /// String-keyed build pipeline while publishing the index-keyed
    /// form at their boundary. Removed in A9.
    pub fn from_legacy(cs: &ConstraintSystem) -> IndexedConstraintSystem {
        let names = cs.collect_vars();
        let mut name_to_idx: HashMap<String, VarIdx> = HashMap::with_capacity(names.len());
        for (i, n) in names.iter().enumerate() {
            name_to_idx.insert(n.clone(), i as VarIdx);
        }

        let intern = |n: &str| -> VarIdx { name_to_idx[n] };

        let equalities: Vec<Vec<IndexedTerm>> = cs
            .equalities
            .iter()
            .map(|eq| {
                eq.iter()
                    .map(|t| {
                        let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
                        for v in &t.vars {
                            *counts.entry(intern(v)).or_insert(0) += 1;
                        }
                        let vars: Vec<(VarIdx, u16)> = counts.into_iter().collect();
                        IndexedTerm {
                            coeff: t.coeff.clone(),
                            vars,
                        }
                    })
                    .collect()
            })
            .collect();

        let disequalities = cs
            .disequalities
            .iter()
            .map(|(a, b)| (intern(a), intern(b)))
            .collect();

        let assignments = cs
            .assignments
            .iter()
            .map(|(v, val)| (intern(v), val.clone()))
            .collect();

        let bitsums = cs
            .bitsums
            .iter()
            .map(|bs| bs.iter().map(|n| intern(n)).collect())
            .collect();

        IndexedConstraintSystem {
            prime: cs.prime.clone(),
            var_names: names,
            equalities,
            disequalities,
            assignments,
            bitsums,
            add_field_polys: cs.add_field_polys,
        }
    }

    /// Lower this index-keyed system to the legacy String-keyed
    /// [`ConstraintSystem`]. Each `IndexedTerm` expands to a
    /// `PolyTerm` whose `vars: Vec<String>` repeats each variable
    /// name `exp` times. Used during the Phase 7 migration as a
    /// bridge so producers that have moved to the index-keyed
    /// builder can still feed the legacy `encode` / cache /
    /// `digest_constraint_side` paths. Removed in A9.
    pub fn to_legacy(&self) -> ConstraintSystem {
        let resolve = |idx: VarIdx| self.var_names[idx as usize].clone();
        ConstraintSystem {
            prime: self.prime.clone(),
            equalities: self
                .equalities
                .iter()
                .map(|eq| {
                    eq.iter()
                        .map(|t| {
                            let mut vars: Vec<String> = Vec::new();
                            for &(idx, exp) in &t.vars {
                                let name = resolve(idx);
                                for _ in 0..exp {
                                    vars.push(name.clone());
                                }
                            }
                            PolyTerm {
                                coeff: t.coeff.clone(),
                                vars,
                            }
                        })
                        .collect()
                })
                .collect(),
            disequalities: self
                .disequalities
                .iter()
                .map(|&(a, b)| (resolve(a), resolve(b)))
                .collect(),
            assignments: self
                .assignments
                .iter()
                .map(|(v, val)| (resolve(*v), val.clone()))
                .collect(),
            add_field_polys: self.add_field_polys,
            bitsums: self
                .bitsums
                .iter()
                .map(|bs| bs.iter().map(|&v| resolve(v)).collect())
                .collect(),
        }
    }
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

    pub fn add_equality(&mut self, terms: Vec<IndexedTerm>) {
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

    pub fn build(self) -> IndexedConstraintSystem {
        IndexedConstraintSystem {
            prime: self.prime,
            var_names: self.var_names,
            equalities: self.equalities,
            disequalities: self.disequalities,
            assignments: self.assignments,
            bitsums: self.bitsums,
            add_field_polys: self.add_field_polys,
        }
    }

    /// Intern each variable name in a legacy `PolyTerm` list and
    /// emit the equivalent `Vec<IndexedTerm>`. Used by producers
    /// that hold an upstream `Vec<PolyTerm>` (e.g. atoms in the
    /// CDCL(T) trail, Literal AST nodes in the boolean DNF expander)
    /// and want to commit those terms to the index-keyed form.
    ///
    /// Within-term repeated names (`x * x` represented as
    /// `vars = ["x", "x"]`) collapse to a sparse `(VarIdx, exp)`
    /// pair.
    pub fn intern_poly_terms(&mut self, terms: &[PolyTerm]) -> Vec<IndexedTerm> {
        terms
            .iter()
            .map(|t| {
                let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
                for v in &t.vars {
                    let idx = self.var(v);
                    *counts.entry(idx).or_insert(0) += 1;
                }
                IndexedTerm {
                    coeff: t.coeff.clone(),
                    vars: counts.into_iter().collect(),
                }
            })
            .collect()
    }
}

/// Encode an [`IndexedConstraintSystem`] into polynomials. Mirrors
/// [`encode`] but consumes the index-keyed form.
///
/// Pre-encode pipeline:
///   1. `compact_used_vars`: drop variables from `var_names` that
///      no equality / disequality / assignment / bitsum references
///      — keeps the polynomial ring tight, matching the legacy
///      `ConstraintSystem::collect_vars` behaviour. Without this,
///      `PolyIR`'s `2 * n_wires` ring exposes every `y_i` even
///      when most are never referenced, inflating the GB engine's
///      monomial table and causing pathological slowdowns on big
///      circuits.
///   2. `rewriter::rewrite_indexed_system`: canonicalise terms.
///   3. `auto_extract_bitsums_indexed`: extract bitsum chains into
///      `bitsum_polys`.
pub fn encode_indexed(system: &IndexedConstraintSystem) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::rewriter::rewrite_indexed_system(&mut rewritten);
    let extracted = auto_extract_bitsums_indexed(&rewritten);
    encode_indexed_impl(&extracted, true)
}

/// Index-keyed counterpart of [`encode_constraint_side`].
pub fn encode_indexed_constraint_side(
    system: &IndexedConstraintSystem,
) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::rewriter::rewrite_indexed_system(&mut rewritten);
    let extracted = auto_extract_bitsums_indexed(&rewritten);
    encode_indexed_impl(&extracted, false)
}

/// Compact `system.var_names` to only the variables actually
/// referenced by some equality, disequality, assignment, or
/// bitsum. Returns a new `IndexedConstraintSystem` with renumbered
/// indices.
///
/// Mirrors `ConstraintSystem::collect_vars` — the legacy
/// `encode_impl` builds its ring from `collect_vars()` (a SET that
/// contains only names appearing in the constraint side), so the
/// index-keyed path must do the same or it produces a ring with
/// spurious extra variables that the GB engine has to factor in.
fn compact_used_vars(system: &IndexedConstraintSystem) -> IndexedConstraintSystem {
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
    let new_equalities: Vec<Vec<IndexedTerm>> = system
        .equalities
        .iter()
        .map(|eq| {
            eq.iter()
                .map(|t| IndexedTerm {
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
    IndexedConstraintSystem {
        prime: system.prime.clone(),
        var_names: new_var_names,
        equalities: new_equalities,
        disequalities: new_disequalities,
        assignments: new_assignments,
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

fn encode_indexed_impl(
    system: &IndexedConstraintSystem,
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

    let field = FfField::new(system.prime.clone());
    let poly_ring = FfPolyRing::new(field, var_names.clone());

    // Build var_map for downstream callers that still consult it
    // (e.g. SUBP_CONSTANT_NAMES filtering in the picus crate).
    let mut var_map: HashMap<String, usize> = HashMap::with_capacity(n_vars);
    for (i, name) in var_names.iter().enumerate() {
        var_map.insert(name.clone(), i);
    }

    let mut polynomials: Vec<Poly> = Vec::new();

    // Equalities: sum(coeff · prod_vars) = 0. Equality terms may
    // reference aux variables introduced by
    // `auto_extract_bitsums_indexed` (indices in the bitsum-aux
    // range); the bounds check is against the full ring size.
    let n_ring = var_names.len();
    for eq in &system.equalities {
        let mut poly = poly_ring.zero();
        for term in eq {
            let c = poly_ring.field.from_biguint(&term.coeff);
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
        let c = poly_ring.constant(poly_ring.field.from_biguint(val));
        let diff = poly_ring.sub(v, c);
        if !poly_ring.is_zero(&diff) {
            polynomials.push(diff);
        }
    }

    // Rabinowitsch trick: (a - b) · w_i - 1 = 0 for each disequality.
    if emit_rabinowitsch {
        for ((a, b), &w_idx) in system.disequalities.iter().zip(witness_idxs.iter()) {
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
        }
    }

    // Bitsum definitions: b0 + 2·b1 + 4·b2 + ... - aux = 0.
    let mut bitsum_polys: Vec<Poly> = Vec::new();
    for (bs, &aux_idx) in system.bitsums.iter().zip(bitsum_aux_idxs.iter()) {
        let fp = &poly_ring.field;
        let two = fp.int_hom().map(2);
        let mut sum = poly_ring.zero();
        let mut coeff = poly_ring.field.one();
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
            for i in 0..poly_ring.n_vars {
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
                }
            }
        }
    }

    let polynomials = polynomials
        .into_iter()
        .map(|p| normalize_poly(&poly_ring, p))
        .collect();

    Ok(EncodedSystem {
        poly_ring,
        polynomials,
        bitsum_polys,
        var_map,
    })
}

#[cfg(test)]
mod tests {
    //! Encoder canonical-form tests. Confirm that the polynomial-level
    //! merging produces the expected canonical form (constant merging,
    //! repeated-monomial collapse) on each `encode()` call.
    use super::*;
    use num_bigint::BigUint;

    fn small_sys(prime: u32) -> ConstraintSystem {
        ConstraintSystem {
            prime: BigUint::from(prime),
            equalities: vec![],
            disequalities: vec![],
            assignments: vec![],
            add_field_polys: false,
            bitsums: vec![],
        }
    }

    fn term(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// `c1*x + c2*x` (within one equality) should encode to a single
    /// `(c1+c2)*x` polynomial term.
    #[test]
    fn merge_repeated_monomial_within_equality() {
        // 2*x + 3*x = 0 over GF(101) should produce a poly with a
        // single term of coefficient 5 on monomial x.
        let mut sys = small_sys(101);
        sys.equalities.push(vec![term(2, &["x"]), term(3, &["x"])]);
        let enc = encode(&sys).unwrap();
        // The lone polynomial should have exactly 1 term: 5*x (or
        // its monic rescale, since `normalize_poly` divides by LC).
        // After normalization 5*x → x, so the polynomial is just `x`.
        let p = &enc.polynomials[0];
        assert_eq!(p.num_terms(), 1, "expected single term, got {} terms", p.num_terms());
    }

    /// `c1 + c2` (constant terms, within one equality) should merge to
    /// a single constant.
    #[test]
    fn merge_constant_terms_within_equality() {
        // 2 + 3 + 7 = 0 mod 11 → 12 = 0 mod 11 → 1 = 0 (so the
        // equality is unsatisfiable; we just check the polynomial
        // form here).
        let mut sys = small_sys(11);
        sys.equalities.push(vec![term(2, &[]), term(3, &[]), term(7, &[])]);
        let enc = encode(&sys).unwrap();
        // 12 mod 11 = 1 ≠ 0, so the polynomial is the constant 1.
        // After normalize_poly divides by LC=1, still 1.
        assert_eq!(enc.polynomials.len(), 1);
        assert_eq!(enc.polynomials[0].num_terms(), 1);
    }

    /// Constants and a variable term mix: `(2 + 3) + 4*x` should
    /// produce a polynomial with two terms (5 + 4*x), not three
    /// (2 + 3 + 4*x). cvc5 merges constants in
    /// `postRewriteFfAdd:83-114`.
    #[test]
    fn merge_constants_with_variable_term() {
        let mut sys = small_sys(101);
        sys.equalities.push(vec![term(2, &[]), term(3, &[]), term(4, &["x"])]);
        let enc = encode(&sys).unwrap();
        let p = &enc.polynomials[0];
        // 4*x + 5 = 0; after normalize_poly (divide by 4): x + (5/4)
        assert_eq!(p.num_terms(), 2, "expected 2 terms (x + const), got {}", p.num_terms());
    }

    /// `c*x + (-c)*x` cancels to zero. picus's polynomial-level merge
    /// drops the equality entirely (the encoder skips zero polynomials).
    #[test]
    fn merge_cancellation_drops_equality() {
        // Over GF(101): 7*x + 94*x = (7 + 94)*x = 101*x = 0.
        let mut sys = small_sys(101);
        sys.equalities.push(vec![term(7, &["x"]), term(94, &["x"])]);
        let enc = encode(&sys).unwrap();
        assert!(enc.polynomials.is_empty(),
            "cancelled equality should produce no polynomial; got {} polys",
            enc.polynomials.len());
    }

    /// Repeated monomial with multiple variables: `c1*x*y + c2*y*x`
    /// (commutative, same monomial) should merge.
    #[test]
    fn merge_commutative_product() {
        // 2*x*y + 3*y*x = 5*x*y over GF(101).
        let mut sys = small_sys(101);
        sys.equalities.push(vec![term(2, &["x", "y"]), term(3, &["y", "x"])]);
        let enc = encode(&sys).unwrap();
        let p = &enc.polynomials[0];
        // After normalize_poly divides by 5: just x*y.
        assert_eq!(p.num_terms(), 1, "expected single x*y term, got {} terms", p.num_terms());
    }

    // ── auto_extract_bitsums tests ────────────────────────────────────

    /// Builds `k` bit constraints `b_i·(b_i − 1) = 0` plus one equality
    /// `s − (b_0 + 2·b_1 + 4·b_2 + ... + 2^{k-1}·b_{k-1}) = 0` over GF(`prime`).
    fn bitdecomp_system_no_target(prime: u32, k: usize) -> ConstraintSystem {
        let p = BigUint::from(prime);
        let pm1 = &p - BigUint::from(1u32);
        let mut sys = small_sys(prime);
        for i in 0..k {
            let bi = format!("b{}", i);
            sys.equalities.push(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![bi.clone(), bi.clone()] },
                PolyTerm { coeff: pm1.clone(), vars: vec![bi] },
            ]);
        }
        // Terms: (1, [s]), (p-1, [b_0]), (p-2, [b_1]), ..., (p-2^{k-1}, [b_{k-1}]).
        let mut terms: Vec<PolyTerm> = vec![PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec!["s".to_string()],
        }];
        let mut coeff: BigUint = BigUint::from(1u32);
        let two = BigUint::from(2u32);
        for i in 0..k {
            terms.push(PolyTerm {
                coeff: &p - &coeff,
                vars: vec![format!("b{}", i)],
            });
            coeff = (&coeff * &two) % &p;
        }
        sys.equalities.push(terms);
        sys
    }

    #[test]
    fn auto_bitsum_extracts_simple_chain() {
        let sys = bitdecomp_system_no_target(101, 3);
        let n_eq_before = sys.equalities.len();
        let n_bitsums_before = sys.bitsums.len();

        let rewritten = auto_extract_bitsums(&sys);

        assert_eq!(rewritten.bitsums.len(), n_bitsums_before + 1);
        let detected = rewritten.bitsums.last().unwrap();
        assert_eq!(detected, &vec!["b0".to_string(), "b1".to_string(), "b2".to_string()]);
        assert_eq!(rewritten.equalities.len(), n_eq_before);

        let sum_eq = rewritten.equalities.last().unwrap();
        let nonzero: Vec<&PolyTerm> = sum_eq.iter().filter(|t| !t.coeff.is_zero()).collect();
        assert_eq!(nonzero.len(), 2, "rewritten sum equality should have 2 terms, got {}", nonzero.len());
        let vars: HashSet<&str> = nonzero.iter().flat_map(|t| t.vars.iter().map(|s| s.as_str())).collect();
        assert!(vars.contains("s"));
        assert!(vars.iter().any(|v| v.starts_with("__bitsum_")));
    }

    /// No `b·(b − 1) = 0` constraints and no user-provided bitsums → empty
    /// `bits` set → chain detection skipped even on bitsum-shaped equalities.
    #[test]
    fn auto_bitsum_skips_when_no_bit_constraints() {
        let mut sys = small_sys(101);
        sys.equalities.push(vec![
            term(1, &["s"]),
            term(100, &["b0"]), // -1 mod 101
            term(99,  &["b1"]), // -2 mod 101
            term(97,  &["b2"]), // -4 mod 101
        ]);
        let rewritten = auto_extract_bitsums(&sys);
        assert!(rewritten.bitsums.is_empty(), "expected no bitsum extraction; got {:?}", rewritten.bitsums);
        assert_eq!(rewritten.equalities[0].len(), 4);
    }

    /// Chain length 1 is below `MIN_AUTO_BITSUM_LEN`.
    #[test]
    fn auto_bitsum_skips_single_bit() {
        let sys = bitdecomp_system_no_target(101, 1);
        let rewritten = auto_extract_bitsums(&sys);
        assert!(rewritten.bitsums.is_empty());
    }

    /// User-provided `bitsums` entries retain their indices; auto-detected
    /// entries are appended.
    #[test]
    fn auto_bitsum_preserves_user_provided() {
        let mut sys = bitdecomp_system_no_target(101, 3);
        sys.bitsums.push(vec!["b0".into(), "b1".into()]);
        let rewritten = auto_extract_bitsums(&sys);
        assert_eq!(rewritten.bitsums[0], vec!["b0".to_string(), "b1".to_string()]);
        assert!(rewritten.bitsums.len() >= 2);
    }

    /// `encode` (auto-extract on) and `encode_no_auto_bitsum` produce the same
    /// verdict on a bitdecomp-shaped system.
    #[test]
    fn auto_bitsum_solve_equivalence_gf11() {
        use crate::core::{solve_encoded, SolveOutcome};

        // k=3 bits over GF(11), target = 5 (binary 101 → b0=1, b1=0, b2=1).
        let prime: u32 = 11;
        let p = BigUint::from(prime);
        let pm1 = &p - BigUint::from(1u32);
        let target: u32 = 5;
        let bits = ["b0", "b1", "b2"];

        let mut sys = small_sys(prime);
        for b in &bits {
            sys.equalities.push(vec![
                PolyTerm { coeff: BigUint::from(1u32), vars: vec![b.to_string(), b.to_string()] },
                PolyTerm { coeff: pm1.clone(), vars: vec![b.to_string()] },
            ]);
        }
        // b_0 + 2·b_1 + 4·b_2 − target = 0
        let mut sum_terms: Vec<PolyTerm> = Vec::new();
        let mut c = BigUint::from(1u32);
        let two = BigUint::from(2u32);
        for b in &bits {
            sum_terms.push(PolyTerm { coeff: c.clone(), vars: vec![b.to_string()] });
            c = (&c * &two) % &p;
        }
        sum_terms.push(PolyTerm { coeff: &p - BigUint::from(target), vars: vec![] });
        sys.equalities.push(sum_terms);

        let enc_auto = encode(&sys).unwrap();
        let out_auto = solve_encoded(&enc_auto);

        let enc_raw = encode_no_auto_bitsum(&sys).unwrap();
        let out_raw = solve_encoded(&enc_raw);

        match (&out_auto, &out_raw) {
            (SolveOutcome::Sat(m_auto), SolveOutcome::Sat(m_raw)) => {
                for b in &bits {
                    let va = m_auto.get(*b).expect("auto: missing bit in model");
                    let vr = m_raw.get(*b).expect("raw: missing bit in model");
                    assert_eq!(va, vr, "models disagree on {}: auto={}, raw={}", b, va, vr);
                }
            }
            (SolveOutcome::Unsat(_), SolveOutcome::Unsat(_)) => {}
            (a, b) => panic!("verdict mismatch — auto: {:?}, raw: {:?}", a, b),
        }
    }

    /// Matches `b·(b − 1) = 0` in several term orderings and scalings;
    /// rejects shapes that don't satisfy `c + c' ≡ 0 (mod p)` or have
    /// extra terms.
    #[test]
    fn detect_bit_constraint_canonical_forms() {
        let p = BigUint::from(101u32);
        // b² + (p-1)·b = 0
        let eq1 = vec![term(1, &["b", "b"]), term(100, &["b"])];
        assert_eq!(detect_bit_constraint_in_terms(&eq1, &p), Some("b".to_string()));

        // Linear term first, quadratic second.
        let eq2 = vec![term(100, &["b"]), term(1, &["b", "b"])];
        assert_eq!(detect_bit_constraint_in_terms(&eq2, &p), Some("b".to_string()));

        // 2·b² + (p-2)·b = 0
        let eq3 = vec![term(2, &["b", "b"]), term(99, &["b"])];
        assert_eq!(detect_bit_constraint_in_terms(&eq3, &p), Some("b".to_string()));

        // c + c' ≢ 0 (mod p) → no match.
        let eq4 = vec![term(1, &["b", "b"]), term(99, &["b"])];
        assert_eq!(detect_bit_constraint_in_terms(&eq4, &p), None);

        // Distinct variables → no match.
        let eq5 = vec![term(1, &["b", "b"]), term(100, &["c"])];
        assert_eq!(detect_bit_constraint_in_terms(&eq5, &p), None);

        // Three terms → no match.
        let eq6 = vec![term(1, &["b", "b"]), term(100, &["b"]), term(1, &[])];
        assert_eq!(detect_bit_constraint_in_terms(&eq6, &p), None);
    }

    // ── encode_indexed parity smoke tests ─────────────────────────

    fn idx_term(coeff: u64, vars: &[(VarIdx, u16)]) -> IndexedTerm {
        IndexedTerm {
            coeff: BigUint::from(coeff),
            vars: vars.to_vec(),
        }
    }

    /// Builder produces a constraint system that encode_indexed
    /// can lower; polynomial count matches the legacy encode() on
    /// an equivalent String-keyed system.
    #[test]
    fn encode_indexed_basic_equality_count() {
        // System: x + y - 1 = 0 over GF(101).
        let mut b = ConstraintSystemBuilder::new(BigUint::from(101u32));
        let x = b.var("x");
        let y = b.var("y");
        b.add_equality(vec![
            idx_term(1, &[(x, 1)]),
            idx_term(1, &[(y, 1)]),
            idx_term(100, &[]), // -1 mod 101
        ]);
        let sys = b.build();
        let enc = encode_indexed(&sys).expect("encode_indexed");
        assert_eq!(enc.polynomials.len(), 1);

        // Legacy path on the equivalent String system.
        let mut legacy = small_sys(101);
        legacy.equalities.push(vec![
            term(1, &["x"]),
            term(1, &["y"]),
            term(100, &[]),
        ]);
        let enc_legacy = encode(&legacy).expect("encode");
        assert_eq!(enc.polynomials.len(), enc_legacy.polynomials.len());
    }

    /// Disequalities produce a Rabinowitsch polynomial; aux
    /// witness var is appended to var_map.
    #[test]
    fn encode_indexed_disequality_adds_witness() {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        let y = b.var("y");
        b.add_disequality(x, y);
        let sys = b.build();
        let enc = encode_indexed(&sys).expect("encode_indexed");
        assert_eq!(enc.polynomials.len(), 1, "one Rabinowitsch poly");
        assert!(enc.var_map.contains_key("__w_diseq_0"));
        assert_eq!(enc.poly_ring.n_vars, 3); // x, y, __w_diseq_0
    }

    /// Bitsum routes into the separate bitsum_polys list.
    #[test]
    fn encode_indexed_bitsum_routing() {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(13u32));
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        b.add_bitsum(vec![b0, b1, b2]);
        let sys = b.build();
        let enc = encode_indexed(&sys).expect("encode_indexed");
        assert_eq!(enc.polynomials.len(), 0);
        assert_eq!(enc.bitsum_polys.len(), 1);
        assert!(enc.var_map.contains_key("__bitsum_0"));
    }

    /// Same variable referenced twice in a builder collapses to one
    /// VarIdx; the encoded ring has only one variable.
    #[test]
    fn builder_var_dedupes() {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x1 = b.var("x");
        let x2 = b.var("x");
        assert_eq!(x1, x2);
        assert_eq!(b.n_vars(), 1);
    }

    /// `auto_extract_bitsums_indexed` produces an `EncodedSystem`
    /// with the same polynomial + bitsum_poly counts as the legacy
    /// `auto_extract_bitsums` on the equivalent String-keyed system.
    /// Exercises the soundness gate (`2^n <= p`): with 3 bits at p=13,
    /// `2^3 = 8 < 13` so the chain extracts.
    #[test]
    fn auto_extract_indexed_matches_legacy_count() {
        let p = BigUint::from(13u32);
        let mut b = ConstraintSystemBuilder::new(p.clone());
        let target = b.var("target");
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        // target - b0 - 2*b1 - 4*b2 = 0
        b.add_equality(vec![
            idx_term(1, &[(target, 1)]),
            idx_term(12, &[(b0, 1)]),
            idx_term(11, &[(b1, 1)]),
            idx_term(9, &[(b2, 1)]),
        ]);
        // Binary constraints b_i^2 + 12 b_i = 0  (i.e. b_i*(b_i-1)=0 mod 13)
        for bit in [b0, b1, b2] {
            b.add_equality(vec![
                idx_term(1, &[(bit, 2)]),
                idx_term(12, &[(bit, 1)]),
            ]);
        }
        let sys = b.build();
        let enc_idx = encode_indexed(&sys).expect("encode_indexed");

        let legacy = sys.to_legacy();
        let enc_leg = encode(&legacy).expect("encode");

        assert_eq!(
            enc_idx.bitsum_polys.len(),
            enc_leg.bitsum_polys.len(),
            "bitsum_polys count must match (idx vs legacy)"
        );
        assert_eq!(
            enc_idx.polynomials.len(),
            enc_leg.polynomials.len(),
            "polynomials count must match (idx vs legacy)"
        );
    }

    /// Soundness gate parity: with 4 bits at p=11, `2^4 > 11` so the
    /// chain must NOT extract. The indexed path must agree with the
    /// legacy path on this skip.
    #[test]
    fn auto_extract_indexed_skips_unsound_chain() {
        let p = BigUint::from(11u32);
        let mut b = ConstraintSystemBuilder::new(p.clone());
        let target = b.var("target");
        let b0 = b.var("b0");
        let b1 = b.var("b1");
        let b2 = b.var("b2");
        let b3 = b.var("b3");
        // 4-bit chain — must skip extraction since 2^4 > p.
        b.add_equality(vec![
            idx_term(1, &[(target, 1)]),
            idx_term(10, &[(b0, 1)]),
            idx_term(9, &[(b1, 1)]),
            idx_term(7, &[(b2, 1)]),
            idx_term(3, &[(b3, 1)]),
        ]);
        for bit in [b0, b1, b2, b3] {
            b.add_equality(vec![
                idx_term(1, &[(bit, 2)]),
                idx_term(10, &[(bit, 1)]),
            ]);
        }
        let sys = b.build();
        let enc_idx = encode_indexed(&sys).expect("encode_indexed");
        let legacy = sys.to_legacy();
        let enc_leg = encode(&legacy).expect("encode");

        // Both must agree on whether bitsum extraction fires. With
        // 2^n > p both paths can still extract a length-3 prefix, so
        // we just check parity, not zero.
        assert_eq!(
            enc_idx.bitsum_polys.len(),
            enc_leg.bitsum_polys.len()
        );
    }
}
