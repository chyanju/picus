//! Runtime configuration for the solver.
//!
//! Single thread-local [`RuntimeConfig`] aggregates every runtime
//! knob: GB strategy, F4 toggle, DNF cap, CDCL(T) iteration cap,
//! GB-stats / GB-trace / phase-profile flags. Production code reads
//! values via [`with`] at the point of use so no cached snapshot can
//! drift from the active config. Callers override fields via
//! [`set`] (one-shot) or [`ConfigGuard`] (RAII scope); per-thread
//! storage keeps concurrent solves on different threads independent.
//!
//! The thread-local seed is the compiled [`RuntimeConfig::default`];
//! file and CLI layers are merged on top by the `picus` facade
//! (`resolve_config`) via [`RuntimeConfig::apply_overlay`].

use serde::{Deserialize, Serialize};
use std::cell::RefCell;

/// Strategy for computing a Groebner basis. Set via
/// [`RuntimeConfig::gb_strategy`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GbStrategy {
    /// Plain DegRevLex Buchberger on `P`. Default.
    Direct,
    /// Homogenize → GB on `P[h]` → dehomogenize → interreduce.
    ByHomog,
    /// Pick `Direct` if every input is already homogeneous w.r.t. the
    /// total-degree grading; otherwise pick `ByHomog`.
    Auto,
}

/// Polynomial storage representation, selected at ring construction and
/// carried by `ff::PolyRing.repr`. Applies to the IR (`PolyIR` equalities/
/// disjunctions, lemma `learned` buffers) and the native Gröbner solve.
///
/// `Dense` stores each monomial as a full-length exponent vector
/// (O(n_vars) per term); `Sparse` stores only the nonzero `(var, exp)`
/// pairs (O(nnz) per term). On wide rings (tens of thousands of variables)
/// dense resident memory is O(n_vars · terms), so `Sparse` is the scalable
/// choice. Both are kept permanently: `Dense` is the differential-test
/// oracle and is faster on small/narrow rings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReprKind {
    Dense,
    Sparse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeConfig {
    /// GB algorithm strategy.
    pub gb_strategy: GbStrategy,
    /// Use F4 matrix reduction for batched same-sugar S-pairs.
    pub use_f4: bool,
    /// DNF expansion cap (max disjunct count) before
    /// `solve_boolean_query_dnf` (in picus-solver) returns `Unknown`.
    pub dnf_cap: u64,
    /// Pick DNF instead of CNF for the boolean layer.
    pub dnf_enabled: bool,
    /// CDCL(T) outer-iteration cap. Set `0` to force an immediate
    /// `Unknown` (used by tests); `u64::MAX` for effectively unbounded.
    pub cdclt_iter_cap: u64,
    /// Emit per-run GB statistics (basis size, S-pair counts, F4 batch
    /// distribution) to stderr.
    pub gb_stats_enabled: bool,
    /// Emit GB trace events for the in-flight basis to stderr.
    pub gb_trace_enabled: bool,
    /// Enable the phase profiler (`ScopedTimer`).
    pub profile_enabled: bool,
    /// Reuse the incremental Buchberger cache between successive
    /// `solve()` calls in the same `NativeFfBackend` instance. The cache
    /// amortises split-GB across calls whose constraint set didn't
    /// change. Disabling it forces every call to rebuild the basis from
    /// scratch — useful for benchmarking or for diagnosing cache bugs.
    pub cache_enabled: bool,
    /// Let the `aboz` lemma emit the (entailed) zero-product
    /// disjunctions for selector patterns whose selector cannot be
    /// proved non-zero, feeding the disjunction-aware solver path. On by
    /// default: each clause follows from an `s * o = 0` equality already
    /// in the IR, so it is sound and verdict-neutral; this keeps the
    /// pipeline's disjunction path live. Set `aboz_emit_disjunctions =
    /// false` in config (CLI `--no-aboz-disj`) to disable (e.g. for an
    /// A/B perf comparison).
    pub aboz_emit_disjunctions: bool,
    /// Representation of the IR poly type ([`ReprKind`]). Defaults to
    /// `Sparse` so lowering + the cvc5 path scale on wide rings (the dense
    /// form OOMs there); set `poly_repr = "dense"` in config (CLI
    /// `--poly-repr dense`) to force the dense representation (the
    /// differential-test oracle, faster on small rings).
    pub poly_repr: ReprKind,
    /// Opt-in linear (Gaussian) pre-elimination (cvc5 `gauss.cpp`
    /// analogue): before solving, reduce the nonlinear constraints modulo
    /// a Gröbner basis of the linear subsystem, substituting out pivot
    /// variables. Off by default — split-GB already handles linear
    /// constraints in basis 0, and the substitution can densify the
    /// nonlinear part and add per-`solve` overhead. A PLDI corpus
    /// differential measured +3.3% total wall-clock with regressions
    /// (BinSum/BinSub 80×, EdDSA family 1.3-1.6×, Pedersen +2.9 s) and zero
    /// wins. Exposed as a knob for linear-heavy conjunctive circuits where
    /// it may pay off.
    pub linear_elim: bool,
    /// Track inter-reduction reducer dependencies in the single-GB UNSAT-core
    /// tracer (`GbTracer`), so a trivial core reflects the basis elements that
    /// actually reduced the contradiction — matching cvc5/CoCoA's precise
    /// cores. On by default, and only meaningful on the non-default SingleGb
    /// path: that path tail-reduces the basis and emits `on_inter_reduce`
    /// events (gated by this flag). The default split-GB path never
    /// tail-reduces during its incremental extends, so no inter-reduce events
    /// fire there regardless of this flag; its UNSAT core is instead
    /// attributed by a conservative union (see `split_gb::fixpoint`). Set
    /// false to drop the small per-reduce counting cost on the SingleGb path.
    pub track_inter_reduce_deps: bool,
    /// Triangular model construction (cvc5 `multi_roots` analogue) on the
    /// default split-GB path: decide a zero-dimensional combined system by
    /// univariate-root + back-substitution enumeration instead of the
    /// brancher DFS. Sound — SAT returns a verified witness, UNSAT comes only
    /// from a complete zero-dimensional enumeration, and any other case
    /// (positive-dimensional, inconclusive, cancelled) falls back to the DFS,
    /// so it can change timing and `Unknown` resolution but never a definite
    /// verdict. Off by default: it builds the combined GB the split path
    /// otherwise avoids, so it is opt-in for zero-dimensional workloads the
    /// bounded brancher leaves `Unknown`.
    pub split_triangular: bool,
    /// Ideal-membership Safe fast-path for uniqueness queries on the
    /// cached split-GB path. Before extending the constraint-side basis
    /// with a query disequality's Rabinowitsch polynomial, reduce the
    /// difference `x_a − x_b` against that basis: a zero remainder proves
    /// `x_a − x_b ∈ I`, so the two copies are forced equal on every
    /// solution and the disequality query is UNSAT — returned directly,
    /// skipping the Rabinowitsch extend. Sound: reduction to zero against
    /// the constraint generators proves membership, so the verdict matches
    /// the full solve; a nonzero remainder is inconclusive and falls
    /// through. For primes ≤ 1000 the basis already carries the field
    /// polynomials, so the test is exact radical membership; for large
    /// primes it is a one-sided Safe filter (misses fall through). On by
    /// default: a PLDI same-binary A/B measured −2.9% total wall-clock on
    /// completing circuits (the multi-output EdDSA family −0.03 to −0.37 s
    /// each) with identical verdicts and no fixture-level regression.
    pub membership_fastpath: bool,
    /// Compute the native split-GB under an elimination term order on the
    /// alt-copy (`y`) variables instead of DegRevLex, driving those
    /// variables out of the leading terms first (see
    /// [`crate::ff::matrix_order::MatrixOrder::elim`]). The split-GB engine
    /// reads its order from the ring, so this only changes which (equally
    /// valid) reduced GB of the same ideal is computed; SAT/UNSAT verdicts
    /// are preserved (`verify_model` / whole-ring detection are
    /// order-independent). Off by default: a PLDI same-binary A/B measured
    /// +318% total wall-clock with five regressions to `unknown` / timeout
    /// (MontgomeryAdd, MontgomeryDouble, BinSum, BinSub, Pedersen) and zero
    /// wins — the elimination order's leading-term structure makes the
    /// model search (`find_zero`) exhaust the per-query budget on those
    /// circuits. Soundness held (every regression is an `unknown`, never a
    /// wrong verdict). Kept as a research knob; re-evaluate if the model
    /// search gains an elimination-aware branching strategy.
    pub matrix_elim_order: bool,
    /// Size-adaptive term-order selection for the native split-GB. When
    /// set, the encoder builds the solve ring under the alt-copy
    /// elimination order only for rings of at least
    /// `frontend::encoder::DYNAMIC_ORDER_MIN_VARS` variables, and DegRevLex
    /// below that — the elimination order helps only large systems (EdDSA
    /// family) and regresses tiny ones. The split-GB is
    /// order-agnostic, so this only changes which equally valid GB is
    /// computed; verdicts are guarded independently of the order. On by
    /// default: a PLDI same-binary A/B measured -3.1% total wall-clock — the
    /// EdDSA family -54..-585 ms via the elimination order on its large rings —
    /// with identical verdicts and no regression (the size guard routes
    /// small rings, where the elimination order regressed, to DegRevLex).
    pub dynamic_order: bool,
    /// Signature-based Gröbner basis (GVW with signature-safe reduction) in
    /// place of the per-pair Buchberger run, for rings of at least
    /// `ff::buchberger::GVW_MIN_VARS` variables. GVW carries a Schreyer
    /// module signature on every labeled polynomial and J-pair, reduces
    /// signature-safely, and skips a J-pair a recorded syzygy / rewrite /
    /// singular criterion proves redundant — so the zero-reductions the
    /// product / Gebauer-Möller / Buchberger criteria fail to predict are
    /// never paid for, rather than reduced-then-discarded. Off by default: a
    /// PLDI same-binary A/B measured -0.2% total wall-clock with identical
    /// verdicts (a 300-seed differential oracle pins the GVW basis equal to
    /// the per-pair reduced GB) and no regression, but no clean fixture win —
    /// the timeout circuits are bounded by the intrinsic Gröbner-basis size,
    /// not by the zero-reductions GVW removes, so it does not resolve them.
    /// The size guard routes small rings, where a from-scratch GVW recompute
    /// on each split-GB extend regressed (Pedersen), to the per-pair engine.
    /// Kept as a research knob and the foundation for further signature work.
    pub signature_criterion: bool,
    /// Use Zech (discrete-log) tables for prime fields with
    /// `prime <= ff::field::ZECH_LOG_MAX_PRIME`, turning multiply / inverse /
    /// power into table lookups. Result-identical (the stored element is the
    /// plain residue either way). Off by default, for two reasons: (i) picus's
    /// deployed workload is BN254 — the GMP backend, where the small-prime
    /// path is never taken, so the PLDI corpus cannot gate it; (ii) the
    /// speedup is not uniform. A 5M-op micro-benchmark: `inv` wins everywhere
    /// (GF(101) 103→11 ms, GF(65521) 102→11 ms — a table lookup vs extended
    /// Euclid), but `mul` regresses on mid-size primes (GF(65521) 46→81 ms:
    /// the ~1 MB `exp` table overflows L2, and Gröbner reduction is mul-heavy)
    /// and only marginally wins on tiny ones (GF(101) 46→40 ms). So the net is
    /// workload-dependent; kept as an opt-in knob for inverse-heavy small-prime
    /// arithmetic, with an `O(prime)` table build per field.
    pub zech_log_small_fp: bool,
    /// Cache the geobucket reducer's divisor index (DivMask buckets + degree
    /// order) across S-pair reductions whose active basis is unchanged,
    /// instead of rebuilding it per call. Result-preserving (same normal
    /// form). Off by default: a growing basis changes the active set often,
    /// so the rebuild on a cache miss offsets the saving; opt-in for long
    /// runs of reductions against a stable basis.
    pub reducer_index_cache: bool,
    /// Memoize the Frobenius polynomial `x^p mod f` across calls to
    /// `distinct_linear_part` keyed by `(prime, f.coeffs)`. The result is a
    /// pure function of its key, so cached values are always correct. Helps
    /// model-construction phases that call root-finding on the same `(ring,
    /// f)` across multiple DFS branches. Off by default; flip on if PLDI
    /// total wall-clock drops.
    pub frobenius_cache: bool,
    /// In multivariate model construction (`find_zero_cancel`), use the
    /// incremental Buchberger driver (`compute_gb_incremental_with_order`)
    /// to extend the basis with the new `(var − val)` constraint at every
    /// DFS branch, instead of running a fresh full Buchberger over the
    /// merged generator list. Result-preserving (same reduced GB modulo
    /// canonicalisation) — only the work to reach it is amortized across
    /// branches. Off by default; flip on if PLDI total wall-clock drops.
    pub branching_incremental_gb: bool,
    /// Route the FF theory through `cdclt::multi_prime::FfTheoryRouter`
    /// instead of the single-prime `FfTheory`. Capability flag for
    /// future multi-prime SMT-LIB inputs; the parser today still
    /// rejects multi-prime sessions, so the router runs in single-slot
    /// mode (path-equivalent to `FfTheory` on the same input). Off by
    /// default until corpus differential confirms equivalence and the
    /// parser is widened to emit per-prime atom tables.
    pub cdclt_multi_prime_router: bool,
    /// Interpose `cdclt::equality_engine::EqualityEngine` before the
    /// FF theory at fact-notification time. `Fresh` facts forward,
    /// `Redundant` facts drop, `Contradiction` facts surface a
    /// precise 2-literal lemma `{atom, witness}` via
    /// `EqualityEngine::prior_witness` instead of deferring to the
    /// inner GB collapse. Off by default after a PLDI corpus
    /// differential: −0.38% total wall-clock, 0 verdict regressions,
    /// mixed fixtures (EdDSAMiMCVerifier −21% and Pedersen −3.6%, but a
    /// borderline EdDSAMiMCSpongeVerifier +1.7%), so the default-flag-flip
    /// rule keeps it off pending a noise-vs-systematic recheck.
    pub cdclt_equality_engine: bool,
    /// Reorder F4 S-pair batches by predicted Hilbert-function drop
    /// (Bigatti–Caboara–Robbiano selection oracle with
    /// `HilbertNum::add_generators_incremental` per candidate;
    /// `HILBERT_SELECT_BASIS_CAP=250` ceiling). Default ON when the
    /// F4 path is in use (`use_f4=true`); inert when the per-pair
    /// path runs. PLDI corpus differential (with `--use-f4`): −1.3% total
    /// wall-clock, 0 verdict regressions, EdDSAPoseidonVerifier −55%
    /// (3349 → 1500 ms), EdDSAMiMCVerifier −21%, EdDSAVerifier −24%,
    /// EdDSAMiMCSpongeVerifier −3.9%, no fixture regression > 200 ms.
    /// Cyclic-N is homogeneous so the oracle has nothing to rank;
    /// katsura-N (heterogeneous) is flat to marginally faster.
    pub f4_hilbert_select: bool,
    /// Cross-batch sparse reducer-row cache inside `F4Workspace`:
    /// stores only the basis index per cache entry and rematerialises
    /// the reducer poly via `basis[bi].poly.mul_term(m / LT(basis[bi]),
    /// 1)` at hit time. Default ON when `use_f4=true`; inert
    /// otherwise. PLDI corpus differential is the same run as
    /// `f4_hilbert_select` above (both flags toggled together):
    /// −1.3% total, 4 EdDSA-family clean wins. Per-entry memory drops
    /// from O(n_terms × n_vars) to O(1) word, freeing allocator
    /// pressure on wider-ring F4 workloads.
    pub f4_sparse_reducer_cache: bool,
    /// Route the FF theory through `cdclt::ff_theory_incremental::
    /// IncrementalFfTheoryState`, which carries an `IncrementalGB`
    /// across SAT decisions instead of rebuilding the basis per
    /// `post_check`. Off by default; the wire-up ports the tier1+tier2
    /// propagation from `FfTheory` and falls back to Unknown on
    /// large-prime non-trivial bases (BN254/BabyJubJub) until model
    /// extraction lands in a follow-up round.
    pub cdclt_incremental_theory: bool,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            gb_strategy: GbStrategy::Direct,
            use_f4: false,
            dnf_cap: 100_000,
            dnf_enabled: false,
            cdclt_iter_cap: 1_000_000,
            gb_stats_enabled: false,
            gb_trace_enabled: false,
            profile_enabled: false,
            cache_enabled: true,
            aboz_emit_disjunctions: true,
            poly_repr: ReprKind::Sparse,
            linear_elim: false,
            track_inter_reduce_deps: true,
            split_triangular: false,
            membership_fastpath: true,
            matrix_elim_order: false,
            dynamic_order: true,
            signature_criterion: false,
            zech_log_small_fp: false,
            reducer_index_cache: false,
            frobenius_cache: true,
            branching_incremental_gb: true,
            cdclt_multi_prime_router: false,
            cdclt_equality_engine: false,
            f4_hilbert_select: true,
            f4_sparse_reducer_cache: true,
            cdclt_incremental_theory: false,
        }
    }
}

impl RuntimeConfig {
    /// Merge the `Some` fields of `o` onto `self`; `None` fields are
    /// left untouched. This is the overlay/merge step that layers a
    /// config file, environment, or CLI flags onto a base config.
    pub fn apply_overlay(&mut self, o: &EngineOverlay) {
        if let Some(v) = o.gb_strategy { self.gb_strategy = v; }
        if let Some(v) = o.use_f4 { self.use_f4 = v; }
        if let Some(v) = o.dnf_cap { self.dnf_cap = v; }
        if let Some(v) = o.dnf_enabled { self.dnf_enabled = v; }
        if let Some(v) = o.cdclt_iter_cap { self.cdclt_iter_cap = v; }
        if let Some(v) = o.gb_stats_enabled { self.gb_stats_enabled = v; }
        if let Some(v) = o.gb_trace_enabled { self.gb_trace_enabled = v; }
        if let Some(v) = o.profile_enabled { self.profile_enabled = v; }
        if let Some(v) = o.cache_enabled { self.cache_enabled = v; }
        if let Some(v) = o.aboz_emit_disjunctions { self.aboz_emit_disjunctions = v; }
        if let Some(v) = o.poly_repr { self.poly_repr = v; }
        if let Some(v) = o.linear_elim { self.linear_elim = v; }
        if let Some(v) = o.track_inter_reduce_deps { self.track_inter_reduce_deps = v; }
        if let Some(v) = o.split_triangular { self.split_triangular = v; }
        if let Some(v) = o.membership_fastpath { self.membership_fastpath = v; }
        if let Some(v) = o.matrix_elim_order { self.matrix_elim_order = v; }
        if let Some(v) = o.dynamic_order { self.dynamic_order = v; }
        if let Some(v) = o.signature_criterion { self.signature_criterion = v; }
        if let Some(v) = o.zech_log_small_fp { self.zech_log_small_fp = v; }
        if let Some(v) = o.reducer_index_cache { self.reducer_index_cache = v; }
        if let Some(v) = o.frobenius_cache { self.frobenius_cache = v; }
        if let Some(v) = o.branching_incremental_gb { self.branching_incremental_gb = v; }
        if let Some(v) = o.cdclt_multi_prime_router { self.cdclt_multi_prime_router = v; }
        if let Some(v) = o.cdclt_equality_engine { self.cdclt_equality_engine = v; }
        if let Some(v) = o.f4_hilbert_select { self.f4_hilbert_select = v; }
        if let Some(v) = o.f4_sparse_reducer_cache { self.f4_sparse_reducer_cache = v; }
        if let Some(v) = o.cdclt_incremental_theory { self.cdclt_incremental_theory = v; }
    }
}

/// Partial overlay for [`RuntimeConfig`]: every field is optional, so a
/// single config layer (file, environment, CLI) carries only the knobs
/// it actually sets. Merged onto a base via [`RuntimeConfig::apply_overlay`];
/// later layers win.
///
/// TOML keys mirror the [`RuntimeConfig`] field names exactly, so adding
/// a knob is one field here plus one line in `apply_overlay` — no rename
/// bookkeeping. `deny_unknown_fields` turns a mistyped key into an error
/// rather than a silent no-op.
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct EngineOverlay {
    pub gb_strategy: Option<GbStrategy>,
    pub use_f4: Option<bool>,
    pub dnf_cap: Option<u64>,
    pub dnf_enabled: Option<bool>,
    pub cdclt_iter_cap: Option<u64>,
    pub gb_stats_enabled: Option<bool>,
    pub gb_trace_enabled: Option<bool>,
    pub profile_enabled: Option<bool>,
    pub cache_enabled: Option<bool>,
    pub aboz_emit_disjunctions: Option<bool>,
    pub poly_repr: Option<ReprKind>,
    pub linear_elim: Option<bool>,
    pub track_inter_reduce_deps: Option<bool>,
    pub split_triangular: Option<bool>,
    pub membership_fastpath: Option<bool>,
    pub matrix_elim_order: Option<bool>,
    pub dynamic_order: Option<bool>,
    pub signature_criterion: Option<bool>,
    pub zech_log_small_fp: Option<bool>,
    pub reducer_index_cache: Option<bool>,
    pub frobenius_cache: Option<bool>,
    pub branching_incremental_gb: Option<bool>,
    pub cdclt_multi_prime_router: Option<bool>,
    pub cdclt_equality_engine: Option<bool>,
    pub f4_hilbert_select: Option<bool>,
    pub f4_sparse_reducer_cache: Option<bool>,
    pub cdclt_incremental_theory: Option<bool>,
}

thread_local! {
    static THREAD_CONFIG: RefCell<RuntimeConfig> = RefCell::new(RuntimeConfig::default());
}

/// Read a snapshot of the current thread's config.
pub fn with<R>(f: impl FnOnce(&RuntimeConfig) -> R) -> R {
    THREAD_CONFIG.with(|c| f(&c.borrow()))
}

/// Replace the thread's config. The previous value is discarded; prefer
/// [`ConfigGuard`] for scoped overrides.
pub fn set(new: RuntimeConfig) {
    THREAD_CONFIG.with(|c| *c.borrow_mut() = new);
}

/// RAII override: installs `new` for the lifetime of the guard, then
/// restores the previous config on drop. Tests use this to flip a
/// single knob without leaking the change to sibling tests.
pub struct ConfigGuard {
    prev: RuntimeConfig,
}

impl ConfigGuard {
    pub fn install(new: RuntimeConfig) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        set(new);
        Self { prev }
    }

    /// Replace just one field, keeping the rest of the current config.
    pub fn with_override(f: impl FnOnce(&mut RuntimeConfig)) -> Self {
        let prev = THREAD_CONFIG.with(|c| c.borrow().clone());
        let mut next = prev.clone();
        f(&mut next);
        set(next);
        Self { prev }
    }
}

impl Drop for ConfigGuard {
    fn drop(&mut self) {
        THREAD_CONFIG.with(|c| *c.borrow_mut() = self.prev.clone());
    }
}

#[cfg(test)]
#[path = "config_tests.rs"]
mod tests;
