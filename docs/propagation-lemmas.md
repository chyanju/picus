# Propagation Lemmas

The DPVL algorithm alternates between cheap propagation and expensive SMT solving. Propagation applies a set of lemmas that deduce signal uniqueness from the current known-set without invoking the solver. All lemmas are sound: they never incorrectly mark a signal as unique.

The lemmas run in sequence until a fixed point (no new signals added).

## Linear Lemma

**Idea:** If a variable appears linearly in a constraint (not multiplied by another variable), and all other variables in that constraint are known, then it is uniquely determined.

**Implementation:**
1. Build a *constraint dependency map* (cdmap): for each linearly-deducible variable `v`, record the set of other variables that must be known to deduce `v`.
2. Invert into a *reverse cdmap* (rcdmap): dependency set -> deducible variables.
3. Fixed-point iteration: if a dependency set is a subset of the known-set, add all its deducible variables to the known-set.

## Binary01 Lemma

**Idea:** Detect constraints of the form `x * (x - 1) = 0`, which force `x in {0, 1}`.

**Implementation:** Pattern-matches several expanded forms:
- `x^2 + (p-1)*x = 0` (quadratic form)
- `or(x = 0, x - 1 = 0)` (after AB0 optimization, z3 only)
- Handles both numeric (`Int`) and named (`Var("ps1")`) coefficients from the SubP optimizer.

When matched, the signal's range is narrowed to `{0, 1}`. If any signal's range becomes a singleton, it is added to the known-set.

## Basis2 Lemma

**Idea:** If `z = 2^0*x_0 + 2^1*x_1 + ... + 2^n*x_n` where all `x_i in {0,1}`, and `z` is known, then each `x_i` is uniquely determined (binary decomposition is unique).

**Implementation:** Matches constraints where the coefficient set (or their field negations) equals `{1, 2, 4, ..., 2^n}` and all non-target variables have binary range (from Binary01). Handles both `Int` and named constant coefficients, and correctly normalizes coefficients near the field boundary (where `2^k > p/2`).

## ABOZ (All-But-One-Zero) Lemma

**Idea:** Detects selector-style constraint triples:
```
y_0 * (x - 0) = 0
y_1 * (x - 1) = 0
y_0 + y_1 = c
```

If `x` and `c` are known, then `y_0` and `y_1` are uniquely determined.

**Implementation:** Slides a 3-constraint window over the constraint list and pattern-matches the triple.

## BIM (Big Integer Multiply) Lemma

**Idea:** If a set of linear homogeneous constraints forms a system `Ax = 0` where `A` is a square matrix with non-zero determinant (mod p), then all variables in `x` are zero -- hence uniquely determined.

**Implementation:**
1. Collect all constraints matching `0 = a_1*x_1 + a_2*x_2 + ...`.
2. Build the coefficient matrix.
3. Compute the determinant via Gaussian elimination over the finite field.
4. If `det != 0`, add all involved signals to the known-set.
