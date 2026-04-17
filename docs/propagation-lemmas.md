# Propagation Lemmas

The DPVL algorithm alternates between cheap propagation and expensive SMT solving. Propagation applies a set of lemmas that deduce signal uniqueness from the current known-set without invoking the solver. All lemmas are sound: they never incorrectly mark a signal as unique.

The lemmas run in sequence until a fixed point (no new signals added).

## L0: Linear Lemma

**Idea:** If a variable appears linearly in a constraint (not multiplied by another variable), and all other variables in that constraint are known, then it is uniquely determined.

**Implementation:**
1. Build a *constraint dependency map* (cdmap): for each linearly-deducible variable `v`, record the set of other variables that must be known to deduce `v`.
2. Invert into a *reverse cdmap* (rcdmap): dependency set → deducible variables.
3. Fixed-point iteration: if a dependency set is a subset of the known-set, add all its deducible variables to the known-set.

This is the workhorse lemma — it resolves the majority of signals in typical circuits.

## L1: Binary01 Lemma

**Idea:** Detect constraints of the form `x · (x - 1) = 0`, which force `x ∈ {0, 1}`.

**Implementation:** Pattern-matches several expanded forms:
- `x² + (p-1)·x = 0` (before optimization)
- `or(x = 0, x - 1 = 0)` (after AB0 optimization)

When matched, the signal's range is narrowed to `{0, 1}`. If any signal's range becomes a singleton, it is added to the known-set.

Adapted from ECNE Rule 2a.

## L2: Basis2 Lemma

**Idea:** If `z = 2⁰·x₀ + 2¹·x₁ + ⋯ + 2ⁿ·xₙ` where all `xᵢ ∈ {0,1}`, and `z` is known, then each `xᵢ` is uniquely determined (binary decomposition is unique).

**Implementation:** Matches constraints where the coefficient set is a prefix of `{1, 2, 4, 8, ...}` and all non-target variables have binary range (from L1). If the target (sum) variable is in the known-set, all bit variables are added.

Adapted from ECNE Rules 3/5.

## L3: ABOZ (All-But-One-Zero) Lemma

**Idea:** Detects selector-style constraint triples:
```
y₀ · (x - 0) = 0
y₁ · (x - 1) = 0
y₀ + y₁ = c
```

If `x` and `c` are known, then `y₀` and `y₁` are uniquely determined.

**Implementation:** Slides a 3-constraint window over the constraint list and pattern-matches the triple. Both finite-field and integer-arithmetic forms are handled.

## L4: BIM (Big Integer Multiply) Lemma

**Idea:** If a set of linear homogeneous constraints forms a system `Ax = 0` where `A` is a square matrix with non-zero determinant (mod p), then all variables in `x` are zero — hence uniquely determined.

**Implementation:**
1. Collect all constraints matching `0 = a₁·x₁ + a₂·x₂ + ⋯`.
2. Build the coefficient matrix.
3. Compute the determinant via Gaussian elimination over the finite field.
4. If `det ≠ 0`, add all involved signals to the known-set.

## BabyJubJub Lemma (domain-specific)

**Idea:** Detects the Edwards curve point addition pattern used in BabyJubJub (constants `a = 168700`, `d = 168696`) and propagates uniqueness through the curve arithmetic.

**Status:** Stub (no-op). The original Racket implementation had this lemma commented out. Can be activated when BabyJubJub circuits need analysis.
