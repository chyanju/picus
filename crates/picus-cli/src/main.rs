use anstream::println as aprintln;
use clap::{Parser, Subcommand, ValueEnum};
use owo_colors::OwoColorize;
use picus::{
    check_r1cs, dump_gb_stats, dump_profile, read_r1cs_file, resolve_config, AnalysisOverlay,
    BigUint, CheckResult, EngineOverlay, GbStrategy, PicusConfig, PicusConfigOverlay, ReprKind,
    SolverKind, Theory,
};
use serde::Serialize;
use std::collections::HashMap;
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "picus",
    about = "Picus — automated detection of under-constrained signals in ZK circuits",
    version
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(ValueEnum, Clone, Copy)]
enum OutputFormat {
    Human,
    Json,
}

#[derive(Subcommand)]
enum Commands {
    /// Check uniqueness of signals in an R1CS circuit
    Check {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Config file (TOML). Layered under the flags below, over the
        /// built-in defaults. If omitted, `./picus.toml` is used when
        /// present. See `picus.default.toml` for the full schema and
        /// defaults.
        #[arg(long)]
        config: Option<PathBuf>,

        /// Solver backend. Built-in names: native, cvc5, z3, none.
        /// Resolved through `SolverKind::from_str`; the inventory of
        /// registered backends supplies the "known backends" list shown
        /// on an unknown name. [default: native]
        #[arg(long)]
        solver: Option<String>,

        /// SMT theory: ff (finite field) or nia (nonlinear integer
        /// arithmetic). [default: ff]
        #[arg(long)]
        theory: Option<String>,

        /// Per-query solver timeout in milliseconds. [default: 5000]
        #[arg(long)]
        timeout: Option<u64>,

        /// Signal selection strategy. [default: counter]
        #[arg(long, value_parser = ["first", "counter"])]
        selector: Option<String>,

        /// Propagation lemmas to enable.
        /// Formats: all, none, all-X,Y (exclude), none+X,Y (include).
        /// Names: linear, binary01, basis2, aboz, bim. [default: all]
        #[arg(long)]
        lemmas: Option<String>,

        /// Dump SMT queries to a directory for debugging
        #[arg(long, name = "dump-smt")]
        dump_smt: Option<PathBuf>,

        /// Output format
        #[arg(long, default_value = "human", value_enum)]
        format: OutputFormat,

        /// Profile output: none, wall (per-site wall-clock). Stats are
        /// written to stderr. [default: none]
        #[arg(long, value_parser = ["none", "wall"])]
        profile: Option<String>,

        /// GB strategy:
        ///   off  — direct DegRevLex Buchberger on P (default, baseline);
        ///   on   — homogenize → GB on P[h] → dehom → interreduce;
        ///   auto — pick `on` iff at least one input is non-homogeneous (cheap test).
        /// Targets the bit-decomp benchmark family where sugar mis-prediction
        /// causes intermediate expression swell. [default: off]
        #[arg(long, value_parser = ["off", "on", "auto"])]
        gb_by_homog: Option<String>,

        /// Polynomial representation for the native FF backend:
        /// sparse (scales on wide rings) or dense (faster on narrow
        /// rings). [default: sparse]
        #[arg(long, value_parser = ["sparse", "dense"])]
        poly_repr: Option<String>,

        /// Use F4 matrix reduction for batched same-sugar S-pairs
        /// (native FF backend only). Research flag.
        #[arg(long)]
        use_f4: bool,

        /// Pick DNF instead of CNF for the boolean layer (native FF
        /// backend only). Research flag.
        #[arg(long)]
        dnf: bool,

        /// DNF expansion cap; native FF returns Unknown beyond this
        /// disjunct count. [default: 100000]
        #[arg(long)]
        dnf_cap: Option<u64>,

        /// CDCL(T) outer-iteration cap. `0` = immediate Unknown
        /// (test helper); large values = effectively unbounded.
        /// [default: 1000000]
        #[arg(long)]
        cdclt_iter_cap: Option<u64>,

        /// Emit per-run GB statistics (basis size, S-pair counts) to
        /// stderr (native FF backend only).
        #[arg(long)]
        gb_stats: bool,

        /// Emit GB trace events for the in-flight basis to stderr
        /// (native FF backend only).
        #[arg(long)]
        gb_trace: bool,

        /// Disable the native FF backend's incremental Buchberger
        /// cache between successive solve() calls. Useful for
        /// benchmarking or for diagnosing cache bugs.
        #[arg(long)]
        no_cache: bool,

        /// Disable the aboz lemma's entailed zero-product disjunctions
        /// (native FF backend only). Default: enabled.
        #[arg(long)]
        no_aboz_disj: bool,

        /// Enable linear (Gaussian) pre-elimination before solving (native
        /// FF backend only). Off by default; may help linear-heavy
        /// conjunctive circuits, but densifies the nonlinear part on the
        /// general workload.
        #[arg(long)]
        linear_elim: bool,

        /// Triangular model construction (cvc5 multi_roots analogue) on the
        /// default split-GB path: on | off. Decides a zero-dimensional
        /// combined system by univariate-root enumeration instead of the
        /// brancher DFS. Omit to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        split_triangular: Option<String>,

        /// Cache the reducer's divisor index across reductions with an
        /// unchanged active basis (native FF backend only): on | off. Omit
        /// to use the built-in default.
        #[arg(long, value_parser = ["on", "off"])]
        reducer_index_cache: Option<String>,
    },

    /// Print R1CS circuit information
    Info {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Print all constraints in human-readable form
        #[arg(long)]
        constraints: bool,

        /// Output format
        #[arg(long, default_value = "human", value_enum)]
        format: OutputFormat,
    },
}

fn main() {
    env_logger::init();
    install_profile_signal_handler();
    let cli = Cli::parse();

    match cli.command {
        Commands::Check {
            r1cs,
            config,
            solver,
            theory,
            timeout,
            selector,
            lemmas,
            dump_smt,
            format,
            profile,
            gb_by_homog,
            poly_repr,
            use_f4,
            dnf,
            dnf_cap,
            cdclt_iter_cap,
            gb_stats,
            gb_trace,
            no_cache,
            no_aboz_disj,
            linear_elim,
            split_triangular,
            reducer_index_cache,
        } => {
            // CLI overlay — the highest-precedence config layer. Only the
            // flags the user actually passed become `Some`; everything
            // else stays `None` and falls through to the config file,
            // then built-in defaults (see `resolve_config`). On/off bool
            // flags can only turn a knob *on* (or, for the `no_*` flags,
            // off).
            let overlay = PicusConfigOverlay {
                analysis: AnalysisOverlay {
                    solver,
                    theory,
                    selector,
                    timeout_ms: timeout,
                    lemmas,
                    dump_smt,
                },
                engine: EngineOverlay {
                    gb_strategy: gb_by_homog.as_deref().map(|s| match s {
                        "on" => GbStrategy::ByHomog,
                        "auto" => GbStrategy::Auto,
                        _ => GbStrategy::Direct,
                    }),
                    poly_repr: poly_repr.as_deref().map(|s| match s {
                        "dense" => ReprKind::Dense,
                        _ => ReprKind::Sparse,
                    }),
                    use_f4: use_f4.then_some(true),
                    dnf_enabled: dnf.then_some(true),
                    dnf_cap,
                    cdclt_iter_cap,
                    gb_stats_enabled: gb_stats.then_some(true),
                    gb_trace_enabled: gb_trace.then_some(true),
                    cache_enabled: no_cache.then_some(false),
                    aboz_emit_disjunctions: no_aboz_disj.then_some(false),
                    profile_enabled: profile.as_deref().map(|s| s == "wall"),
                    linear_elim: linear_elim.then_some(true),
                    // Config-file only (no CLI flag): precise inter-reduce
                    // core tracking is a niche knob; set it via picus.toml.
                    track_inter_reduce_deps: None,
                    split_triangular: split_triangular.as_deref().map(|s| s == "on"),
                    reducer_index_cache: reducer_index_cache.as_deref().map(|s| s == "on"),
                },
            };
            let resolved = resolve_config(config.as_deref(), &overlay)
                .unwrap_or_else(|e| exit_error(&e.to_string()));
            cmd_check(r1cs, resolved, format);
        }
        Commands::Info {
            r1cs,
            constraints,
            format,
        } => cmd_info(r1cs, constraints, format),
    }
    dump_profile("cli");
    dump_gb_stats();
}

// ============================================================
// JSON schema types
// ============================================================

#[derive(Serialize)]
struct CheckOutput {
    circuit: CircuitInfo,
    config: ConfigInfo,
    result: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    counter_example: Option<CounterExampleJson>,
}

#[derive(Serialize)]
struct CircuitInfo {
    file: String,
    wires: u32,
    constraints: u32,
    pub_out: u32,
    pub_in: u32,
    prv_in: u32,
}

#[derive(Serialize)]
struct ConfigInfo {
    solver: String,
    theory: String,
    lemmas: String,
    timeout_ms: u64,
}

#[derive(Serialize)]
struct CounterExampleJson {
    witness_1: HashMap<String, String>,
    witness_2: HashMap<String, String>,
}

#[derive(Serialize)]
struct InfoOutput {
    file: String,
    version: u32,
    field_size: u32,
    prime: String,
    wires: u32,
    constraints: u32,
    pub_out: u32,
    pub_in: u32,
    prv_in: u32,
    labels: u64,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
}

// ============================================================
// Human output helpers
// ============================================================

const SECTION_WIDTH: usize = 50;

fn print_section(title: &str) {
    let dashes = SECTION_WIDTH.saturating_sub(title.len() + 3);
    aprintln!(
        "{} {} {}",
        "──".dimmed(),
        title.bold(),
        "─".repeat(dashes).dimmed()
    );
}

fn print_field(label: &str, value: &str) {
    aprintln!("  {:<16}{}", format!("{}:", label).dimmed(), value);
}

fn print_field_pair(l1: &str, v1: &str, l2: &str, v2: &str) {
    aprintln!(
        "  {:<16}{:<8}{:<16}{}",
        format!("{}:", l1).dimmed(),
        v1,
        format!("{}:", l2).dimmed(),
        v2
    );
}

fn exit_error(msg: &str) -> ! {
    aprintln!("{} {}", "error:".red().bold(), msg);
    std::process::exit(1);
}

/// On SIGTERM/SIGINT, dump profile counters to stderr before exiting.
/// Lets us profile runs that don't terminate cleanly. The dumps are
/// no-ops when no profile/stats data has been recorded.
fn install_profile_signal_handler() {
    use signal_hook::consts::{SIGINT, SIGTERM};
    use signal_hook::iterator::Signals;
    let mut signals = match Signals::new([SIGTERM, SIGINT]) {
        Ok(s) => s,
        Err(_) => return,
    };
    std::thread::spawn(move || {
        for sig in signals.forever() {
            dump_profile(&format!("signal={}", sig));
            dump_gb_stats();
            // Re-raise default behavior: exit with conventional code.
            std::process::exit(128 + sig);
        }
    });
}

// ============================================================
// check command
// ============================================================

fn cmd_check(r1cs_path: PathBuf, config: PicusConfig, format: OutputFormat) {
    // Pull the display-facing fields out before `config` moves into the
    // solve; the engine knobs travel inside `config`.
    let solver = config.analysis.solver;
    let theory = config.analysis.theory;
    let timeout = config.analysis.timeout_ms;
    let lemmas_display = config.analysis.lemmas.to_string();
    let theory_str = match theory {
        Theory::Ff => "ff",
        Theory::Nia => "nia",
    };

    // Validate up front for a clean message (check_r1cs validates too).
    if let Err(e) = picus::picus_smt::validate_combination(solver, theory) {
        exit_error(&e);
    }

    let r1cs = read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        exit_error(&format!("failed to read R1CS file: {}", e));
    });

    let result = check_r1cs(&r1cs, config).unwrap_or_else(|e| exit_error(&e.to_string()));

    let solver_display = match (solver, theory) {
        (SolverKind::Cvc5, Theory::Ff) => "cvc5 (QF_FF)",
        (SolverKind::Cvc5, Theory::Nia) => "cvc5 (QF_NIA)",
        (SolverKind::Z3, Theory::Nia) => "z3 (QF_NIA)",
        (SolverKind::Native, Theory::Ff) => "native (QF_FF)",
        (SolverKind::None, _) => "none",
        _ => "unknown",
    };

    match format {
        OutputFormat::Human => {
            print_section("Circuit");
            print_field("File", &r1cs_path.display().to_string());
            print_field_pair(
                "Wires",
                &r1cs.header.n_wires.to_string(),
                "Constraints",
                &r1cs.header.m_constraints.to_string(),
            );
            print_field_pair(
                "Pub Out",
                &r1cs.header.n_pub_out.to_string(),
                "Pub In",
                &r1cs.header.n_pub_in.to_string(),
            );
            print_field("Prv In", &r1cs.header.n_prv_in.to_string());
            aprintln!();
            print_section("Analysis");
            print_field("Solver", solver_display);
            print_field("Lemmas", &lemmas_display);
            print_field("Timeout", &format!("{}ms", timeout));
            aprintln!();
            print_section("Result");

            match &result {
                CheckResult::Safe => {
                    aprintln!("  {} {}", "✓".green().bold(), "uniqueness: safe".green().bold());
                }
                CheckResult::Unsafe { witness_1, witness_2 } => {
                    aprintln!("  {} {}", "✗".red().bold(), "uniqueness: unsafe".red().bold());
                    print_counter_example_human(witness_1, witness_2);
                }
                CheckResult::Unknown => {
                    aprintln!("  {} {}", "?".yellow().bold(), "uniqueness: unknown".yellow().bold());
                }
            }
        }
        OutputFormat::Json => {
            let (result_str, cex) = match &result {
                CheckResult::Safe => ("safe".to_string(), None),
                CheckResult::Unsafe { witness_1, witness_2 } => {
                    ("unsafe".to_string(), Some(CounterExampleJson {
                        witness_1: witness_1.iter().map(|(k, v)| (k.clone(), v.to_string())).collect(),
                        witness_2: witness_2.iter().map(|(k, v)| (k.clone(), v.to_string())).collect(),
                    }))
                }
                CheckResult::Unknown => ("unknown".to_string(), None),
            };

            let output = CheckOutput {
                circuit: CircuitInfo {
                    file: r1cs_path.display().to_string(),
                    wires: r1cs.header.n_wires,
                    constraints: r1cs.header.m_constraints,
                    pub_out: r1cs.header.n_pub_out,
                    pub_in: r1cs.header.n_pub_in,
                    prv_in: r1cs.header.n_prv_in,
                },
                config: ConfigInfo {
                    solver: solver.as_str().to_string(),
                    theory: theory_str.to_string(),
                    lemmas: lemmas_display,
                    timeout_ms: timeout,
                },
                result: result_str,
                counter_example: cex,
            };

            println!("{}", serde_json::to_string_pretty(&output).expect("JSON serialization failed"));
        }
    }
}

fn print_counter_example_human(
    witness_1: &HashMap<String, BigUint>,
    witness_2: &HashMap<String, BigUint>,
) {
    let mut x_vals: Vec<_> = witness_1.iter().collect();
    let mut y_vals: Vec<_> = witness_2.iter().collect();

    x_vals.sort_by_key(|(k, _)| picus::picus_r1cs::parse_var_index(k).unwrap_or(usize::MAX));
    y_vals.sort_by_key(|(k, _)| picus::picus_r1cs::parse_var_index(k).unwrap_or(usize::MAX));

    aprintln!();
    aprintln!("  {}:", "Counter-example".dimmed());
    aprintln!("    {}:", "Witness 1 (original)".dimmed());
    for (var, val) in &x_vals {
        aprintln!("      {} {} {}", var.bold(), "=".dimmed(), val);
    }
    aprintln!("    {}:", "Witness 2 (alternative)".dimmed());
    for (var, val) in &y_vals {
        aprintln!("      {} {} {}", var.bold(), "=".dimmed(), val);
    }
}


// ============================================================
// info command
// ============================================================

fn cmd_info(r1cs_path: PathBuf, show_constraints: bool, format: OutputFormat) {
    let r1cs = read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        exit_error(&format!("failed to read R1CS file: {}", e));
    });

    match format {
        OutputFormat::Human => {
            print_section("R1CS Info");
            print_field("File", &r1cs_path.display().to_string());
            print_field("Version", &r1cs.version.to_string());
            print_field("Field Size", &format!("{} bytes", r1cs.header.field_size));
            print_field("Prime", &r1cs.header.prime_number.to_string());
            print_field("Wires", &r1cs.header.n_wires.to_string());
            print_field("Constraints", &r1cs.header.m_constraints.to_string());
            print_field("Pub Outputs", &r1cs.header.n_pub_out.to_string());
            print_field("Pub Inputs", &r1cs.header.n_pub_in.to_string());
            print_field("Prv Inputs", &r1cs.header.n_prv_in.to_string());
            print_field("Labels", &r1cs.header.n_labels.to_string());
            print_field("Inputs", &format!("{:?}", r1cs.inputs));
            print_field("Outputs", &format!("{:?}", r1cs.outputs));

            if show_constraints {
                aprintln!();
                print_section("Constraints");
                for i in 0..r1cs.header.m_constraints as usize {
                    aprintln!(
                        "  {} {}",
                        format!("[{}]", i).dimmed(),
                        r1cs.constraint_to_string(i)
                    );
                }
            }
        }
        OutputFormat::Json => {
            let output = InfoOutput {
                file: r1cs_path.display().to_string(),
                version: r1cs.version,
                field_size: r1cs.header.field_size,
                prime: r1cs.header.prime_number.to_string(),
                wires: r1cs.header.n_wires,
                constraints: r1cs.header.m_constraints,
                pub_out: r1cs.header.n_pub_out,
                pub_in: r1cs.header.n_pub_in,
                prv_in: r1cs.header.n_prv_in,
                labels: r1cs.header.n_labels,
                inputs: r1cs.inputs.clone(),
                outputs: r1cs.outputs.clone(),
            };

            println!("{}", serde_json::to_string_pretty(&output).expect("JSON serialization failed"));
        }
    }
}
