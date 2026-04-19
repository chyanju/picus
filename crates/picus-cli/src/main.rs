use clap::{Parser, Subcommand};
use picus_analysis::dpvl::{DpvlConfig, DpvlResult, LemmaSet};
use picus_analysis::selector::SelectorKind;
use picus_smt::{SolverKind, Theory};
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

        /// Solver backend: cvc5, z3, or none (propagation only)
        #[arg(long, default_value = "cvc5", value_parser = ["z3", "cvc5", "none"])]
        solver: String,

        /// SMT theory
        #[arg(long, default_value = "ff", value_parser = ["ff", "nia"])]
        theory: String,

        /// Per-query solver timeout in milliseconds
        #[arg(long, default_value = "5000")]
        timeout: u64,

        /// Signal selection strategy
        #[arg(long, default_value = "counter", value_parser = ["first", "counter"])]
        selector: String,

        /// Propagation lemmas to enable (comma-separated).
        /// Values: all, none, linear, binary01, basis2, aboz, bim
        #[arg(long, default_value = "all")]
        lemmas: String,

        /// Dump SMT queries to a directory for debugging
        #[arg(long, name = "dump-smt")]
        dump_smt: Option<PathBuf>,
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
            theory,
            timeout,
            selector,
            lemmas,
            dump_smt,
        } => cmd_check(r1cs, &solver, &theory, timeout, &selector, &lemmas, dump_smt),
        Commands::Info { r1cs, constraints } => cmd_info(r1cs, constraints),
    }
}

#[allow(clippy::too_many_arguments)]
fn cmd_check(
    r1cs_path: PathBuf,
    solver_str: &str,
    theory_str: &str,
    timeout: u64,
    selector_str: &str,
    lemmas_str: &str,
    dump_smt: Option<PathBuf>,
) {
    let solver: SolverKind = solver_str.parse().unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    let theory: Theory = theory_str.parse().unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    if let Err(e) = picus_smt::validate_combination(solver, theory) {
        eprintln!("error: {}", e);
        std::process::exit(1);
    }

    let selector: SelectorKind = selector_str.parse().unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    let lemmas = LemmaSet::parse(lemmas_str).unwrap_or_else(|e| {
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

    if let Some(ref dir) = dump_smt {
        let _ = std::fs::create_dir_all(dir);
    }

    let config = DpvlConfig {
        solver,
        theory,
        selector,
        timeout_ms: timeout,
        lemmas,
        dump_smt,
    };

    let result = picus_analysis::dpvl::run_dpvl(&r1cs, &config).unwrap_or_else(|e| {
        eprintln!("error: {}", e);
        std::process::exit(1);
    });

    match result {
        DpvlResult::Safe => {
            println!("uniqueness: safe");
        }
        DpvlResult::Unsafe(model) => {
            println!("uniqueness: unsafe");
            if !model.is_empty() {
                // Filter out named constants (ps1-ps5, p, zero, one) — only show circuit signals
                let constants: std::collections::HashSet<&str> =
                    ["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"].into_iter().collect();

                // Separate x (original) and y (alternative) signals
                let mut x_vals: Vec<_> = Vec::new();
                let mut y_vals: Vec<_> = Vec::new();

                for (var, val) in &model {
                    if constants.contains(var.as_str()) {
                        continue;
                    }
                    if var.starts_with('y') {
                        y_vals.push((var, val));
                    } else {
                        x_vals.push((var, val));
                    }
                }

                x_vals.sort_by_key(|(k, _)| picus_r1cs::parse_var_index(k).unwrap_or(usize::MAX));
                y_vals.sort_by_key(|(k, _)| picus_r1cs::parse_var_index(k).unwrap_or(usize::MAX));

                println!("counter-example (two distinct witnesses for the same inputs):");
                println!("  witness 1 (original):");
                for (var, val) in &x_vals {
                    println!("    {} = {}", var, val);
                }
                println!("  witness 2 (alternative):");
                for (var, val) in &y_vals {
                    println!("    {} = {}", var, val);
                }
            }
        }
        DpvlResult::Unknown => {
            println!("uniqueness: unknown");
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

    if show_constraints {
        println!();
        for i in 0..r1cs.header.m_constraints as usize {
            println!("[{}] {}", i, r1cs.constraint_to_string(i));
        }
    }
}
