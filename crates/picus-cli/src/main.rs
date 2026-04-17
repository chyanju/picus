use clap::{Parser, Subcommand};
use picus_analysis::dpvl::{DpvlConfig, DpvlResult};
use picus_analysis::selector::SelectorKind;
use picus_r1cs::precondition;
use picus_smt::SolverKind;
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

#[derive(Subcommand)]
enum Commands {
    /// Check uniqueness of signals in an R1CS circuit
    Check {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Solver backend
        #[arg(long, default_value = "cvc5", value_parser = ["z3", "cvc4", "cvc5"])]
        solver: String,

        /// Per-query solver timeout in milliseconds
        #[arg(long, default_value = "5000")]
        timeout: u64,

        /// Signal selection strategy
        #[arg(long, default_value = "counter", value_parser = ["first", "counter"])]
        selector: String,

        /// Path to precondition JSON file
        #[arg(long)]
        precondition: Option<PathBuf>,

        /// Disable propagation lemmas (solver-only mode)
        #[arg(long)]
        noprop: bool,

        /// Disable solver phase (propagation-only mode)
        #[arg(long)]
        nosolve: bool,

        /// Print SMT file paths for debugging
        #[arg(long)]
        smt: bool,

        /// Check weak safety (outputs only) instead of strong (all signals)
        #[arg(long)]
        weak: bool,

        /// Map signal IDs to Circom variable names via .sym file
        #[arg(long)]
        map: bool,
    },

    /// Print R1CS circuit information
    Info {
        /// Path to the .r1cs file
        #[arg(long)]
        r1cs: PathBuf,

        /// Print all constraints in human-readable form
        #[arg(long)]
        constraints: bool,
    },
}

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match cli.command {
        Commands::Check {
            r1cs,
            solver,
            timeout,
            selector,
            precondition: precond_path,
            noprop,
            nosolve,
            smt,
            weak,
            map,
        } => cmd_check(
            r1cs,
            &solver,
            timeout,
            &selector,
            precond_path,
            noprop,
            nosolve,
            smt,
            weak,
            map,
        ),
        Commands::Info { r1cs, constraints } => cmd_info(r1cs, constraints),
    }
}

#[allow(clippy::too_many_arguments)]
fn cmd_check(
    r1cs_path: PathBuf,
    solver_str: &str,
    timeout: u64,
    selector_str: &str,
    precond_path: Option<PathBuf>,
    noprop: bool,
    nosolve: bool,
    smt: bool,
    weak: bool,
    map: bool,
) {
    let solver: SolverKind = solver_str.parse().unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    let selector: SelectorKind = selector_str.parse().unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    let r1cs = picus_r1cs::parser::read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        eprintln!("error: failed to read R1CS file: {}", e);
        std::process::exit(1);
    });

    eprintln!("circuit: {}", r1cs_path.display());
    eprintln!(
        "  wires: {}, constraints: {}, pub_out: {}, pub_in: {}, prv_in: {}",
        r1cs.header.n_wires,
        r1cs.header.m_constraints,
        r1cs.header.n_pub_out,
        r1cs.header.n_pub_in,
        r1cs.header.n_prv_in
    );

    let preconditions = precond_path.as_ref().map(|path| {
        precondition::read_precondition(path).unwrap_or_else(|e| {
            eprintln!("error: failed to read precondition file: {}", e);
            std::process::exit(1);
        })
    });

    let config = DpvlConfig {
        solver,
        selector,
        timeout_ms: timeout,
        enable_propagation: !noprop,
        enable_solving: !nosolve,
        weak,
        show_smt: smt,
    };

    let mode = if weak { "weak" } else { "strong" };
    let result = picus_analysis::dpvl::run_dpvl(&r1cs, &config, preconditions.as_ref());

    match result {
        DpvlResult::Safe => {
            println!("{} uniqueness: safe", mode);
        }
        DpvlResult::Unsafe(model) => {
            println!("{} uniqueness: unsafe", mode);
            if !model.is_empty() {
                println!("counter-example:");
                let sym_map = if map {
                    let sym_path = r1cs_path.with_extension("sym");
                    if sym_path.exists() {
                        picus_r1cs::sym::parse_sym_file(&sym_path, r1cs.header.n_wires as usize)
                            .ok()
                    } else {
                        None
                    }
                } else {
                    None
                };

                let mut entries: Vec<_> = model.iter().collect();
                entries.sort_by_key(|(k, _)| k.to_string());
                for (var, val) in entries {
                    let display = sym_map
                        .as_ref()
                        .and_then(|s| {
                            parse_var_index(var).and_then(|idx| s.signal_names.get(&idx).cloned())
                        })
                        .unwrap_or_else(|| var.clone());
                    println!("  {} = {}", display, val);
                }
            }
        }
        DpvlResult::Unknown => {
            println!("{} uniqueness: unknown", mode);
        }
    }
}

fn cmd_info(r1cs_path: PathBuf, show_constraints: bool) {
    let r1cs = picus_r1cs::parser::read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        eprintln!("error: failed to read R1CS file: {}", e);
        std::process::exit(1);
    });

    println!("file: {}", r1cs_path.display());
    println!("version: {}", r1cs.version);
    println!("field size: {} bytes", r1cs.header.field_size);
    println!("prime: {}", r1cs.header.prime_number);
    println!("wires: {}", r1cs.header.n_wires);
    println!("constraints: {}", r1cs.header.m_constraints);
    println!("public outputs: {}", r1cs.header.n_pub_out);
    println!("public inputs: {}", r1cs.header.n_pub_in);
    println!("private inputs: {}", r1cs.header.n_prv_in);
    println!("labels: {}", r1cs.header.n_labels);
    println!("inputs (0-based): {:?}", r1cs.inputs);
    println!("outputs (0-based): {:?}", r1cs.outputs);

    // Print signal names from .sym if available
    let sym_path = r1cs_path.with_extension("sym");
    if sym_path.exists()
        && let Ok(sym) = picus_r1cs::sym::parse_sym_file(&sym_path, r1cs.header.n_wires as usize)
        {
            println!("symbol map: {} signals", sym.signal_names.len());
        }

    if show_constraints {
        println!();
        for i in 0..r1cs.header.m_constraints as usize {
            println!("[{}] {}", i, r1cs.constraint_to_string(i));
        }
    }
}

fn parse_var_index(name: &str) -> Option<usize> {
    if (name.starts_with('x') || name.starts_with('y')) && name.len() > 1 {
        name[1..].parse().ok()
    } else {
        None
    }
}
