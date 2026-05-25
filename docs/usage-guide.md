# Usage Guide

## Interpreting Results

Picus outputs one of three results:

| Result | Meaning |
|--------|---------|
| **safe** | The solver has proven that all output signals are uniquely determined by the inputs. There are no under-constrained outputs. This result has no false positives — if Picus says safe, the circuit's outputs are safe. |
| **unsafe** | The solver has found a concrete counter-example: two distinct valid witnesses that share the same public inputs but produce different outputs. The counter-example is displayed as two witnesses. |
| **unknown** | The solver could not determine the result within the given timeout. This does not mean the circuit is safe or unsafe — it means analysis was inconclusive. Increasing `--timeout` or trying a different solver may help. |

## Solver Differences

Picus supports four solver backends:

| Backend | Theory | How it works |
|---------|--------|-------------|
| cvc5 + QF_FF | Finite field | Native field arithmetic via cvc5's CoCoA/Groebner basis solver |
| native + QF_FF | Finite field | Pure-Rust solver (`picus-solver`) with an in-tree Groebner basis engine; no C++ dependencies |
| z3 + QF_NIA | Integer mod p | Integer arithmetic with explicit `mod p` |
| none | — | Propagation only; no SMT solver invoked |

The QF_FF and QF_NIA encodings are semantically equivalent. If two solvers terminate, they should agree on safe/unsafe:

- **cvc5 safe, z3 safe** — consistent, circuit is safe.
- **cvc5 unsafe, z3 unsafe** — consistent, circuit is unsafe.
- **One safe, one unknown** — normal. The unknown solver timed out. Trust the one that terminated.
- **One safe, one unsafe** — this should not happen with correct encodings. If it does, verify the counter-example manually by checking that both witnesses satisfy all R1CS constraints. The solver reporting unsafe may have a soundness issue, or there may be an encoding discrepancy.

> **Known issue**: cvc5 1.2.0–1.3.3 has a bug where `or` disjunctions in QF_FF can produce spurious SAT results with inconsistent models. The PolyIR lowering avoids emitting `or`-shaped queries entirely, so this does not affect default Picus usage.

## Troubleshooting

### Killed / Out of memory

If the process is killed unexpectedly, it is likely a memory issue. Large circuits (10k+ constraints) can consume significant memory during solver invocation. If running in Docker, increase the container's memory limit.

### Solver hangs / very slow

If the solver does not return within the timeout, Picus reports `unknown`. Common causes:

- The circuit has complex nonlinear constraints that are hard for the solver
- The circuit is very large (thousands of wires)

Options:
- Increase `--timeout` (e.g., `--timeout 60000` for 60 seconds)
- Try a different solver (`--solver z3 --theory nia`, or `--solver cvc5 --theory ff` if built with `--features cvc5`); the default is `--solver native --theory ff`
- Use `--solver none` to see how much propagation alone can resolve
- Try `--gb-by-homog auto` on `native + ff`: routes through a homogenisation-based GB pipeline that wins on bit-decomposition-shaped ideals
- Enable the F4 matrix path with `--use-f4` (research flag; native FF only)

## Analyzing Large Circuits

For circuits that are too large to verify in one pass, a semi-automatic approach can be used:

### Divide and verify

Split the circuit into smaller sub-circuits (e.g., by Circom template) and verify each one independently. If every sub-circuit is safe, the full circuit is also safe. If any sub-circuit reports unsafe or unknown, manual review of that component is needed.

Note: a locally unsafe sub-circuit does not necessarily mean the full circuit is vulnerable — other constraints in the surrounding circuit may fix the issue.

### Template substitution

If a specific template is too complex for the solver (e.g., a cryptographic hash function), but is known to be correct, it can be replaced with a simpler template that has the same output domain. This reduces the verification burden while preserving the circuit's security properties.

For example, if `f(g(h(x)))` is the circuit and `h(x)` is a known-correct hash that blocks verification, replace `h(x)` with a fresh variable `y` constrained to `h`'s output domain. The resulting simplified circuit can then be verified. If it passes, the original circuit is also safe (assuming the substitution is sound).

Caution: the substitution must not under-approximate the original template's behavior — it should cover at least the same output space. An over-approximation is fine (it may produce false `unsafe` results, but will never miss real bugs).
