# Propagation Lemmas

The DPVL outer loop interleaves cheap propagation with calls into the
configured solver backend. The propagation pass applies a registered
set of lemmas that deduce wire uniqueness from polynomial structure
without invoking the solver. Every lemma is sound: a wire is only
marked known when polynomial structure forces it.

## Plugin interface

Lemmas implement
[`picus_analysis::propagation::lemma::PropagationLemma`]:

```rust
pub trait PropagationLemma: Send {
    fn name(&self) -> &'static str;
    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool;
}
```

Each lemma's source file ends with an `inventory::submit!` block:

```rust
inventory::submit! {
    LemmaDescriptor {
        name: "linear",
        factory: || Box::new(LinearLemma::default()),
    }
}
```

The DPVL driver discovers descriptors at link time via
`inventory::iter::<LemmaDescriptor>`. `LemmaSet::parse` validates the
`--lemmas` flag against the live registry, so adding a new lemma is
two edits: one new file under `crates/picus-analysis/src/propagation/`
plus a one-line `pub mod` declaration in `propagation/mod.rs`. A
range-aware lemma additionally uses the `RangeValue` type from
`propagation::range`; no other lemma needs to be touched.

`PropagationCtx` exposes five mutable channels:

| Field | Use |
|---|---|
| `known: &mut HashSet<usize>` | Wires the lemma has proved unique. |
| `unknown: &mut HashSet<usize>` | Wires still to be checked. |
| `ranges: &mut HashMap<usize, RangeValue>` | Per-wire value-set constraints (`Bottom` / `Values(set)`). |
| `learned: &mut Vec<Poly>` | New polynomial equalities the lemma wants the framework to fold into the IR for the next iteration. |
| `learned_disjunctions: &mut Vec<Vec<Poly>>` | New `(p_1 = 0 ∨ p_2 = 0 ∨ ...)` clauses; the driver appends them to `ir.disjunctions` at iteration end. |

`run` returns `true` iff the call made progress. The outer DPVL
loop runs every lemma once per iteration; at the end of each
iteration `ctx.learned` is appended to `ir.equalities` and
`ctx.learned_disjunctions` to `ir.disjunctions`, then the iteration
repeats. The fixed-point detector counts four kinds of progress
(`known` growth, `run() == true`, a new learned equality, a new
learned disjunction), so a lemma whose only output is a tightened
range or a new constraint still triggers another iteration.

Inter-lemma ordering within an iteration is irrelevant: every lemma
in an iteration reads the same IR snapshot, and the next iteration
starts with everyone's facts merged. Per-lemma contribution counts
(`ks` / `ranges` / `learned` / `disjunctions` deltas) are emitted at
`log::debug!` for ablation work.

## Built-in lemmas

All five built-ins operate on `PolyIR` directly; they pattern-match
on polynomial structure (via `appearing_indeterminates`,
`poly_terms`, and direct monomial inspection) rather than on an AST.

### `linear`

For each polynomial constraint `p = 0`, partition the variables that
actually appear into linear-only (every term containing them has
total degree 1) and nonlinear (appear in some term of total degree
≥ 2). A purely-linear variable `v` is uniquely determined as soon as
every other variable in `p` is known, so the lemma records the
implication `deps(p, v) → wire(v)`. A fixed-point pass over the
implications grows `ctx.known` while any deps-set becomes fully
known.

### `binary01`

Detects polynomial equalities `c1 * x^2 + c2 * x = 0` with
`c1 + c2 ≡ 0 mod p` — i.e. `c1 * (x² - x) = 0`. The constraint pins
`x ∈ {0, 1}`; the lemma intersects the wire's range with `{0, 1}` in
`ctx.ranges`. Any wire whose range collapses to a singleton joins
`ctx.known`.

### `basis2`

Recognises binary-decomposition shapes
`target + Σ_i (−2^i) · bit_i = 0` (equivalently
`target = Σ 2^i · bit_i`) where each `bit_i` has already been pinned
to `{0, 1}` by `binary01`. When the target is known, the bits are
recoverable bit-by-bit and so move to `ctx.known`. Coefficients are
checked against the power-of-2 set after both sign normalisations
(coefficient or its field negation must be a power of 2).

**Soundness gate**: when `2^n ≤ p` (where `n` is the chain length)
the decomposition is injective and the lemma fires directly. When
`2^n > p`, two distinct bit patterns can sum to the same value modulo
`p` (e.g. `0` and `(1,1,...,1)` with `2^n - 1 ≡ 0 mod p`), so target
uniqueness no longer implies bit uniqueness — the lemma fires only if
a range-check companion proves the bit-vector value `< p`.

**Companion recognition (`2^n > p`)**: the lemma matches circomlib's
254-bit `CompConstant` comparator whose output is constrained to `0`
(the `AliasCheck` gadget) over the decomposition bits — the 127
quadratic `parts` (weight-aligned to the bit pairs by following the
IR's linear identities), their sum, the inner bit-decomposition of
that sum, and the forced-zero output bit — and decodes the
comparator's constant `ct` from the `parts` coefficients, requiring
`ct < p`. A complete match certifies `Σ 2^i · bit_i ≤ ct < p`, so the
decomposition is injective and the gate is relaxed. The match is
purely structural on the polynomial IR; any unmatched link leaves the
conservative gate in place (a miss is slow, never unsound).

### `aboz`

All-But-One-Zero: detects selector-shaped triples
`x · y_0 = 0`, `x · y_1 = 0`, `x + y_0 + y_1 + c = 0` (the first two
are bilinear monomials sharing wire `x`; the third is a linear sum
touching the same wires plus at least one additional known partner).
From `x · y_i = 0` and `x ≠ 0` it follows that `y_i = 0`.

**Soundness gate**: only fires when `ctx.ranges[x].excludes_zero()`
is true. Without that gate, two witnesses with `x = 0` could
disagree on `y_0` / `y_1` (the bilinear products vanish, and the
linear sum admits a one-parameter family of solutions), so marking
them uniquely-determined would be unsound.

### `bim`

Big Integer Multiply: collects every polynomial equality whose terms
are all linear monomials with non-zero coefficient (constant terms
must be exactly zero). If the participating wires form a square
system over GF(p) and the coefficient matrix has non-zero
determinant, every wire in the system is uniquely determined and
joins `ctx.known`. Determinant computation uses Gaussian elimination
over the finite field with extended-Euclidean modular inverse.
