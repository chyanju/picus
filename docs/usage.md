# Usage

Full command-line and configuration reference. For a quick start see the
[README](../README.md); for building the optional cvc5 / z3 backends see
[building.md](building.md).

## `picus check` — verify circuit uniqueness

```bash
picus check --r1cs circuit.r1cs                              # default: native + ff
picus check --r1cs circuit.r1cs --solver cvc5 --theory ff    # cvc5 (build with --features cvc5)
picus check --r1cs circuit.r1cs --solver z3 --theory nia     # z3 over the integers (--features z3)
picus check --r1cs circuit.r1cs --solver none                # propagation only
picus check --r1cs circuit.r1cs --lemmas all-bim             # all lemmas except bim
picus check --r1cs circuit.r1cs --format json                # JSON output
picus check --r1cs circuit.r1cs --dump-smt /tmp/smt/         # dump SMT queries
```

| Flag | Default | Description |
|------|---------|-------------|
| `--r1cs <path>` | *required* | R1CS binary file |
| `--config <path>` | `./picus.toml` if present | TOML config file (see [Configuration](#configuration)); flags below override it |
| `--solver <name>` | `native` | Backend: `native`, `cvc5`, `z3`, `none` (`cvc5`/`z3` require their Cargo features). Names resolve against the inventory of registered backends |
| `--theory <ff\|nia>` | `ff` | `ff` (finite field) or `nia` (integer mod) |
| `--timeout <ms>` | `5000` | Per-query solver timeout |
| `--selector <first\|counter>` | `counter` | Signal selection heuristic |
| `--lemmas <spec>` | `all` | `all`, `none`, `all-X,Y` (exclude), `none+X,Y` (include). Names: `linear`, `binary01`, `basis2`, `aboz`, `bim` |
| `--format <human\|json>` | `human` | Output format |
| `--dump-smt <dir>` | — | Dump SMT-LIB queries to a directory |
| `--profile <none\|wall>` | `none` | Emit per-site wall-clock profile to stderr |
| `--gb-strategy <direct\|by-homog\|auto>` | `direct` | GB algorithm: direct Buchberger / homogenisation pipeline / auto-pick by homogeneity test (`native` only). Matches the `gb_strategy` config key. (`--gb-by-homog <off\|on\|auto>` is a deprecated alias.) |

### Advanced / research flags

| Flag | Default | Description |
|------|---------|-------------|
| `--poly-repr <sparse\|dense>` | `sparse` | Polynomial representation (`native`): `sparse` scales on wide rings, `dense` is faster on narrow rings |
| `--use-f4` | off | F4 matrix reduction for batched same-sugar S-pairs (`native`) |
| `--dnf` | off | Pick DNF instead of CNF for the boolean layer (`native`) |
| `--dnf-cap <N>` | `100000` | DNF expansion cap; returns `unknown` beyond this disjunct count |
| `--cdclt-iter-cap <N>` | `1000000` | CDCL(T) outer-iteration cap |
| `--gb-stats` | off | Emit per-run GB statistics to stderr (`native`) |
| `--gb-trace` | off | Emit GB trace events to stderr (`native`) |
| `--no-cache` | off | Disable the native FF backend's incremental Buchberger cache between successive `solve()` calls |
| `--no-aboz-disj` | off | Disable the `aboz` lemma's entailed zero-product disjunctions (`native`) |
| `--linear-elim` | off | Linear (Gaussian) pre-elimination before solving (`native`); may help linear-heavy circuits |
| `--split-triangular <on\|off>` | off | Triangular model construction for a zero-dimensional combined system on the split-GB path, in place of the brancher DFS (`native`) |
| `--reducer-index-cache <on\|off>` | off | Cache the reducer's divisor index across reductions with an unchanged active basis (`native`) |
| `--frobenius-cache <on\|off>` | on | Memoize `x^p mod poly` across Cantor–Zassenhaus calls on the same `(prime, poly)` (`native`) |
| `--branching-incremental-gb <on\|off>` | on | Extend the parent GB with the single branching constraint via `compute_gb_incremental_with_order` instead of recomputing the full basis at each DFS branch (`native`) |
| `--cdclt-multi-prime-router <on\|off>` | off | Route CDCL(T) facts through `cdclt::multi_prime::FfTheoryRouter` (single-slot when input is single-prime; multi-slot when fed by `parse_boolean_multi`) (`native`) |
| `--cdclt-equality-engine <on\|off>` | off | Interpose `cdclt::equality_engine::EqualityEngine` before the FF theory; drops canonical-polynomial duplicate facts and surfaces precise 2-literal lemmas on polarity contradictions (`native`) |
| `--cdclt-incremental-theory <on\|off>` | off | Route CDCL(T) through `cdclt::ff_theory_incremental::IncrementalFfTheoryState`; carries an `IncrementalGB` across SAT decisions, with model extraction via a user-namespaced facade ring (`native`) |
| `--f4-hilbert-select <on\|off>` | on | BCR Hilbert-driven F4 batch selection (`HilbertNum::add_generators_incremental` per candidate; inert when `--use-f4` is off) (`native`) |
| `--f4-sparse-reducer-cache <on\|off>` | on | Sparse-row reducer cache inside `F4Workspace`: stores basis index only, rematerialises the reducer at hit time (inert when `--use-f4` is off) (`native`) |

> `z3 + ff` is rejected (z3 has no finite-field theory); `native + nia` is
> rejected (the native backend implements only QF_FF).

## `picus info` — inspect R1CS metadata

```bash
picus info --r1cs circuit.r1cs
picus info --r1cs circuit.r1cs --constraints   # also print every constraint
```

## Configuration

Every knob has a built-in default, so no configuration is required. When you
do want to pin settings, Picus resolves them in three layers, each overriding
only the keys it sets (later wins):

1. **Built-in defaults** — compiled in; what a library import (`Config::default()`) and a flagless CLI run get. No file is read.
2. **Config file** — the TOML passed to `--config <FILE>`, or `./picus.toml` in the working directory when present. A missing *explicit* `--config` file is an error; a missing `./picus.toml` is skipped silently.
3. **CLI flags** — highest precedence.

[`picus.default.toml`](../picus.default.toml) at the repo root documents every
key at its default value — copy it and edit. Keys are split into two tables:

- `[analysis]` — `solver`, `theory`, `timeout_ms`, `selector`, `lemmas`, `dump_smt`. Backend-agnostic.
- `[engine]` — Picus's in-tree engine: the native FF Gröbner solver knobs (`gb_strategy`, `use_f4`, `dnf_enabled`, `dnf_cap`, `cdclt_iter_cap`, `cache_enabled`, `linear_elim`, `split_triangular`, `reducer_index_cache`, `frobenius_cache`, `branching_incremental_gb`, `cdclt_multi_prime_router`, `cdclt_equality_engine`, `cdclt_incremental_theory`, `f4_hilbert_select`, `f4_sparse_reducer_cache`, `track_inter_reduce_deps`) plus the IR/lemma knobs that also shape the cvc5 path (`poly_repr`, `aboz_emit_disjunctions`) and the diagnostics (`gb_stats_enabled`, `gb_trace_enabled`, `profile_enabled`). The native-solver-only keys are unused when delegating to cvc5 / z3.

```toml
[analysis]
solver = "native"
timeout_ms = 10000

[engine]
poly_repr = "sparse"
gb_strategy = "auto"
```

An unknown key is a hard error. As a library, `PicusConfig::from_file("picus.toml")`
applies a file over the defaults, while `PicusConfig::default()` stays zero-I/O.

## Interpreting results

| Result | Meaning |
|--------|---------|
| **safe** | All output signals are proven uniquely determined by the inputs. No false positives — if Picus says safe, the outputs are safe. |
| **unsafe** | A concrete counter-example was found: two distinct valid witnesses sharing the same public inputs but differing on an output. Shown as two witnesses. |
| **unknown** | The solver could not decide within the timeout. Not a safety claim either way — analysis was inconclusive. A larger `--timeout` or a different solver may help. |

## Solver differences

| Backend | Theory | How it works |
|---------|--------|--------------|
| native + QF_FF *(default)* | Finite field | Pure-Rust in-tree Gröbner-basis engine; no external solver or C++ dependency |
| cvc5 + QF_FF | Finite field | cvc5's CoCoA / Gröbner-basis FF solver (`--features cvc5`) |
| z3 + QF_NIA | Integer mod p | Integer arithmetic with explicit `mod p` (`--features z3`) |
| none | — | Propagation only; no SMT solver invoked |

The QF_FF and QF_NIA encodings are semantically equivalent: if two backends
terminate, they should agree on safe/unsafe.

- **Both safe** / **both unsafe** — consistent.
- **One safe, one unknown** — normal; the unknown backend timed out. Trust the one that terminated.
- **One safe, one unsafe** — should not happen with correct encodings. Verify the counter-example manually (check that both witnesses satisfy every R1CS constraint); the backend reporting unsafe may have a soundness issue, or there is an encoding discrepancy.

> **Known cvc5 issue**: cvc5 1.2.0–1.3.3 can produce spurious SAT with
> inconsistent models for `or` disjunctions in QF_FF. The PolyIR lowering
> avoids emitting `or`-shaped queries, so this does not affect normal usage.

## Troubleshooting

**Killed / out of memory.** Large circuits can consume significant memory
during the solve. Under Docker, raise the container memory limit. On the
native backend, `--poly-repr sparse` (the default) keeps wide rings compact.

**Solver hangs / reports `unknown`.** The query was too hard within the
timeout. Options:

- Increase `--timeout` (e.g. `--timeout 60000`).
- Try another backend (`--solver z3 --theory nia`, or `--solver cvc5 --theory ff` if built with `--features cvc5`).
- `--solver none` to see how far propagation alone gets.
- On `native + ff`: `--gb-strategy auto` routes through the homogenisation GB pipeline that wins on bit-decomposition-shaped ideals; `--use-f4` enables the F4 matrix path (research flag).
