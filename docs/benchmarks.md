# PLDI circomlib benchmark — baseline

Reference table for the full PLDI 68-fixture circomlib subset
(`benchmarks/circom/circomlib-cff5ab6/*.r1cs`). Recorded per fixture:

1. **ground truth** — the *true* verdict of the circuit (`safe` =
   outputs uniquely determined / `unsafe` = under-constrained), a
   property of the circuit itself, independent of any tool. Best-effort:
   the 8 `unsafe` rows were independently confirmed by substituting both
   witnesses back into the raw R1CS; the `safe` rows are inherited from
   the resolved verdicts (trusted, not each independently re-proven);
   `unknown` = true verdict not yet established (no build below resolves
   it).
2. **recorded verdict** — what a given build actually *output*. This can
   differ from ground truth when the solver hits a bug or the time budget
   is too small.

Two builds are recorded, both kept as regression references:

- **cvc5 `7cb6d45`** — the original baseline. Backend cvc5
  (`--solver cvc5 --theory ff`); that commit had no native solver.
  Captured 2026-05-23 on a 16-core Linux box, release build.
- **native `124c7d2`** — the current baseline (default in-tree native FF
  solver, no `--solver` flag). Captured 2026-05-30, release build; each
  solve runs in its own process under a 6 GB `RLIMIT_AS` cap, strictly
  sequential.

Both used the same limits: `--timeout 10000` (per-SMT-query, 10 s); outer
wall-clock hard-capped at 30 s. A `timeout` verdict means the 30 s cap
fired before a result; `unknown` means the solver returned without a
verdict (a per-query 10 s budget expired). Times in ms.

A future build whose verdict contradicts a *known* ground truth (or flips
a settled verdict) needs investigation.

| fixture | ground truth | cvc5 `7cb6d45` verdict | cvc5 time (ms) | native `124c7d2` verdict | native time (ms) |
|---|---|---|---:|---|---:|
| AliasCheck@aliascheck | safe | safe | 18 | safe | 16 |
| AND@gates | safe | safe | 7 | safe | 3 |
| BabyAdd@babyjub | unknown | timeout | 30007 | unknown | 10005 |
| BabyCheck@babyjub | safe | safe | 7 | safe | 2 |
| BabyDbl@babyjub | safe | safe | 20 | safe | 6 |
| BabyPbk@babyjub | unknown | timeout | 30615 | timeout | 30018 |
| BinSub@binsub | safe | safe | 17 | safe | 4 |
| BinSum@binsum | safe | safe | 16 | safe | 4 |
| BitElementMulAny@escalarmulany | unknown | timeout | 30038 | timeout | 30030 |
| Bits2Num@bitify | safe | safe | 7 | safe | 3 |
| Bits2Num_strict@bitify | safe | safe | 36 | safe | 34 |
| Bits2Point@pointbits | unsafe | unsafe | 10 | unsafe | 3 |
| Bits2Point_Strict@pointbits | unknown | timeout | 30173 | timeout | 30034 |
| CompConstant@compconstant | safe | safe | 17 | safe | 13 |
| Decoder@multiplexer | unsafe | unsafe | 14 | unsafe | 4 |
| EdDSAMiMCSpongeVerifier@eddsamimcsponge | safe | safe | 2257 | safe | 7002 |
| EdDSAMiMCVerifier@eddsamimc | safe | safe | 1169 | safe | 3750 |
| EdDSAPoseidonVerifier@eddsaposeidon | safe | safe | 569 | safe | 1563 |
| EdDSAVerifier@eddsa | safe | safe | 828 | safe | 2653 |
| Edwards2Montgomery@montgomery | unsafe | unsafe | 12 | unsafe | 4 |
| EscalarMulAny@escalarmulany | unknown | timeout | 30034 | timeout | 30039 |
| EscalarProduct@multiplexer | safe | safe | 8 | safe | 3 |
| ForceEqualIfEnabled@comparators | safe | safe | 7 | safe | 3 |
| GreaterEqThan@comparators | safe | safe | 8 | safe | 3 |
| GreaterThan@comparators | safe | safe | 7 | safe | 3 |
| IsEqual@comparators | safe | safe | 14 | safe | 3 |
| IsZero@comparators | safe | safe | 13 | safe | 3 |
| LessEqThan@comparators | safe | safe | 8 | safe | 3 |
| LessThan@comparators | safe | safe | 8 | safe | 3 |
| MiMC7@mimc | safe | safe | 8 | safe | 3 |
| MiMCFeistel@mimcsponge | safe | safe | 8 | safe | 3 |
| MiMCSponge@mimcsponge | safe | safe | 8 | safe | 4 |
| Montgomery2Edwards@montgomery | unsafe | unsafe | 12 | unsafe | 3 |
| MontgomeryAdd@montgomery | unsafe | unsafe | 32 | unsafe | 15 |
| MontgomeryDouble@montgomery | unsafe | unsafe | 56 | unsafe | 16 |
| MultiAND@gates | safe | safe | 10 | safe | 3 |
| MultiMiMC7@mimc | safe | safe | 8 | safe | 3 |
| MultiMux1@mux1 | safe | safe | 7 | safe | 4 |
| MultiMux2@mux2 | safe | safe | 7 | safe | 3 |
| MultiMux3@mux3 | safe | safe | 7 | safe | 3 |
| MultiMux4@mux4 | safe | safe | 11 | safe | 4 |
| Multiplexer@multiplexer | safe | safe | 23 | safe | 5 |
| Multiplexor2@escalarmulany | safe | safe | 9 | safe | 3 |
| Mux1@mux1 | safe | safe | 8 | safe | 3 |
| Mux2@mux2 | safe | safe | 7 | safe | 4 |
| Mux3@mux3 | safe | safe | 8 | safe | 3 |
| Mux4@mux4 | safe | safe | 8 | safe | 4 |
| NAND@gates | safe | safe | 7 | safe | 2 |
| NOR@gates | safe | safe | 7 | safe | 2 |
| NOT@gates | safe | safe | 8 | safe | 9 |
| Num2Bits@bitify | safe | safe | 7 | safe | 3 |
| Num2BitsNeg@bitify | safe | safe | 16 | safe | 4 |
| Num2Bits_strict@bitify | safe | safe | 38 | safe | 55 |
| OR@gates | safe | safe | 7 | safe | 2 |
| Pedersen@pedersen_old | safe | safe | 56 | safe | 103 |
| Pedersen@pedersen | unsafe | timeout | 30030 | unsafe | 6371 |
| Point2Bits@pointbits | unsafe | unsafe | 13 | unsafe | 3 |
| Point2Bits_Strict@pointbits | safe | safe | 80 | safe | 166 |
| Poseidon@poseidon | safe | safe | 23 | safe | 16 |
| SegmentMulAny@escalarmulany | unknown | timeout | 30032 | timeout | 30027 |
| SegmentMulFix@escalarmulfix | unknown | timeout | 30032 | timeout | 30037 |
| Segment@pedersen | unknown | timeout | 30030 | timeout | 30026 |
| Sigma@poseidon | safe | safe | 11 | safe | 3 |
| Sign@sign | safe | safe | 22 | safe | 15 |
| Switcher@switcher | safe | safe | 8 | safe | 3 |
| Window4@pedersen | unknown | timeout | 30026 | timeout | 30036 |
| WindowMulFix@escalarmulfix | unknown | timeout | 30029 | timeout | 30036 |
| XOR@gates | safe | safe | 8 | safe | 3 |

**Tally**
- ground truth: 50 safe / 8 unsafe / 10 unknown
- cvc5 `7cb6d45`: 50 safe / 7 unsafe / 11 timeout
- native `124c7d2`: 50 safe / 8 unsafe / 9 timeout / 1 unknown

Verdict differences, native `124c7d2` vs cvc5 `7cb6d45` (verdicts otherwise
identical):
- `Pedersen@pedersen` — cvc5 `timeout` → native `unsafe` (6371 ms). Native
  resolves the true verdict cvc5 timed out on; this was the only row where
  the cvc5 baseline disagreed with a known ground truth.
- `BabyAdd@babyjub` — cvc5 `timeout` → native `unknown` (per-query budget
  expired at 10 s). Both non-resolution; ground truth still `unknown`.

Native is faster on the small fixtures and slower on the four resolved EdDSA
circuits (cvc5 538–2257 ms vs native 1563–7002 ms), all still `safe`.
