# PLDI circomlib benchmark — baseline

Reference table for the full PLDI 68-fixture circomlib subset
(`benchmarks/circom/circomlib-cff5ab6/*.r1cs`). Two distinct things are
recorded per fixture:

1. **ground truth** — the *true* verdict of the circuit (`safe` =
   outputs uniquely determined / `unsafe` = under-constrained), a
   property of the circuit itself, independent of any tool. Best-effort:
   the 8 `unsafe` rows were independently confirmed by substituting both
   witnesses back into the raw R1CS;
   the `safe` rows are inherited from the baseline's resolved verdicts
   (trusted, not each independently re-proven); `unknown` = true verdict
   not yet established (no version below resolves it).
2. **baseline verdict** — what the baseline build actually *output*. This
   can differ from ground truth when the solver hits a bug or the time
   budget is too small (e.g. `Pedersen@pedersen` is truly `unsafe` but
   the baseline times out before deciding).

The baseline build is the regression reference; a future build whose
verdict contradicts a *known* ground truth (or flips a settled baseline
verdict) needs investigation.

- **Baseline version**: commit `7cb6d45` on `main`.
- **Baseline backend**: cvc5 (`--solver cvc5 --theory ff`). This commit
  has no native solver.
- **Limits**: `--timeout 10000` (per-SMT-query, 10 s); outer wall-clock
  hard-capped at 30 s via GNU `timeout(1)`. A `timeout` verdict means the
  30 s cap fired before a result. Times in ms.
- Captured 2026-05-23 on a 16-core Linux box, release build.

| fixture | ground truth | baseline verdict | baseline time (ms) |
|---|---|---|---:|
| AliasCheck@aliascheck | safe | safe | 18 |
| AND@gates | safe | safe | 7 |
| BabyAdd@babyjub | unknown | timeout | 30007 |
| BabyCheck@babyjub | safe | safe | 7 |
| BabyDbl@babyjub | safe | safe | 20 |
| BabyPbk@babyjub | unknown | timeout | 30615 |
| BinSub@binsub | safe | safe | 17 |
| BinSum@binsum | safe | safe | 16 |
| BitElementMulAny@escalarmulany | unknown | timeout | 30038 |
| Bits2Num@bitify | safe | safe | 7 |
| Bits2Num_strict@bitify | safe | safe | 36 |
| Bits2Point@pointbits | unsafe | unsafe | 10 |
| Bits2Point_Strict@pointbits | unknown | timeout | 30173 |
| CompConstant@compconstant | safe | safe | 17 |
| Decoder@multiplexer | unsafe | unsafe | 14 |
| EdDSAMiMCSpongeVerifier@eddsamimcsponge | safe | safe | 2257 |
| EdDSAMiMCVerifier@eddsamimc | safe | safe | 1169 |
| EdDSAPoseidonVerifier@eddsaposeidon | safe | safe | 569 |
| EdDSAVerifier@eddsa | safe | safe | 828 |
| Edwards2Montgomery@montgomery | unsafe | unsafe | 12 |
| EscalarMulAny@escalarmulany | unknown | timeout | 30034 |
| EscalarProduct@multiplexer | safe | safe | 8 |
| ForceEqualIfEnabled@comparators | safe | safe | 7 |
| GreaterEqThan@comparators | safe | safe | 8 |
| GreaterThan@comparators | safe | safe | 7 |
| IsEqual@comparators | safe | safe | 14 |
| IsZero@comparators | safe | safe | 13 |
| LessEqThan@comparators | safe | safe | 8 |
| LessThan@comparators | safe | safe | 8 |
| MiMC7@mimc | safe | safe | 8 |
| MiMCFeistel@mimcsponge | safe | safe | 8 |
| MiMCSponge@mimcsponge | safe | safe | 8 |
| Montgomery2Edwards@montgomery | unsafe | unsafe | 12 |
| MontgomeryAdd@montgomery | unsafe | unsafe | 32 |
| MontgomeryDouble@montgomery | unsafe | unsafe | 56 |
| MultiAND@gates | safe | safe | 10 |
| MultiMiMC7@mimc | safe | safe | 8 |
| MultiMux1@mux1 | safe | safe | 7 |
| MultiMux2@mux2 | safe | safe | 7 |
| MultiMux3@mux3 | safe | safe | 7 |
| MultiMux4@mux4 | safe | safe | 11 |
| Multiplexer@multiplexer | safe | safe | 23 |
| Multiplexor2@escalarmulany | safe | safe | 9 |
| Mux1@mux1 | safe | safe | 8 |
| Mux2@mux2 | safe | safe | 7 |
| Mux3@mux3 | safe | safe | 8 |
| Mux4@mux4 | safe | safe | 8 |
| NAND@gates | safe | safe | 7 |
| NOR@gates | safe | safe | 7 |
| NOT@gates | safe | safe | 8 |
| Num2Bits@bitify | safe | safe | 7 |
| Num2BitsNeg@bitify | safe | safe | 16 |
| Num2Bits_strict@bitify | safe | safe | 38 |
| OR@gates | safe | safe | 7 |
| Pedersen@pedersen_old | safe | safe | 56 |
| Pedersen@pedersen | unsafe | timeout | 30030 |
| Point2Bits@pointbits | unsafe | unsafe | 13 |
| Point2Bits_Strict@pointbits | safe | safe | 80 |
| Poseidon@poseidon | safe | safe | 23 |
| SegmentMulAny@escalarmulany | unknown | timeout | 30032 |
| SegmentMulFix@escalarmulfix | unknown | timeout | 30032 |
| Segment@pedersen | unknown | timeout | 30030 |
| Sigma@poseidon | safe | safe | 11 |
| Sign@sign | safe | safe | 22 |
| Switcher@switcher | safe | safe | 8 |
| Window4@pedersen | unknown | timeout | 30026 |
| WindowMulFix@escalarmulfix | unknown | timeout | 30029 |
| XOR@gates | safe | safe | 8 |

**Tally**
- ground truth: 50 safe / 8 unsafe / 10 unknown
- baseline verdict: 50 safe / 7 unsafe / 11 timeout

The single row where ground truth and the baseline verdict disagree is
`Pedersen@pedersen` (truly `unsafe`, baseline times out). The 10
`unknown` rows are the fixtures the baseline never resolves, so their
true verdict is not yet established here.
