use anstream::println as aprintln;
use clap::{Parser, Subcommand, ValueEnum};
use owo_colors::OwoColorize;
use picus_analysis::dpvl::{DpvlConfig, DpvlResult, LemmaSet};
use picus_analysis::selector::SelectorKind;
use picus_smt::{SolverKind, Theory};
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

        /// Output format
        #[arg(long, default_value = "human", value_enum)]
        format: OutputFormat,
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
            format,
        } => cmd_check(r1cs, &solver, &theory, timeout, &selector, &lemmas, dump_smt, format),
        Commands::Info {
            r1cs,
            constraints,
            format,
        } => cmd_info(r1cs, constraints, format),
    }
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
    counter_example: Option<CounterExample>,
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
struct CounterExample {
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

// ============================================================
// check command
// ============================================================

#[allow(clippy::too_many_arguments)]
fn cmd_check(
    r1cs_path: PathBuf,
    solver_str: &str,
    theory_str: &str,
    timeout: u64,
    selector_str: &str,
    lemmas_str: &str,
    dump_smt: Option<PathBuf>,
    format: OutputFormat,
) {
    let solver: SolverKind = solver_str.parse().unwrap_or_else(|e| {
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

    let theory: Theory = theory_str.parse().unwrap_or_else(|e| {
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

    if let Err(e) = picus_smt::validate_combination(solver, theory) {
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    }

    let selector: SelectorKind = selector_str.parse().unwrap_or_else(|e| {
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

    let lemmas = LemmaSet::parse(lemmas_str).unwrap_or_else(|e| {
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

    let r1cs = picus_r1cs::parser::read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        aprintln!("{} failed to read R1CS file: {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

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
        aprintln!("{} {}", "error:".red().bold(), e);
        std::process::exit(1);
    });

    let solver_display = match (solver, theory) {
        (SolverKind::Cvc5, Theory::Ff) => "cvc5 (QF_FF)",
        (SolverKind::Cvc5, Theory::Nia) => "cvc5 (QF_NIA)",
        (SolverKind::Z3, Theory::Nia) => "z3 (QF_NIA)",
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
            print_field("Lemmas", lemmas_str);
            print_field("Timeout", &format!("{}ms", timeout));
            aprintln!();
            print_section("Result");

            match &result {
                DpvlResult::Safe => {
                    aprintln!("  {} {}", "✓".green().bold(), "uniqueness: safe".green().bold());
                }
                DpvlResult::Unsafe(model) => {
                    aprintln!("  {} {}", "✗".red().bold(), "uniqueness: unsafe".red().bold());
                    print_counter_example_human(model);
                }
                DpvlResult::Unknown => {
                    aprintln!("  {} {}", "?".yellow().bold(), "uniqueness: unknown".yellow().bold());
                }
            }
        }
        OutputFormat::Json => {
            let (result_str, cex) = match &result {
                DpvlResult::Safe => ("safe".to_string(), None),
                DpvlResult::Unsafe(model) => ("unsafe".to_string(), Some(build_counter_example(model))),
                DpvlResult::Unknown => ("unknown".to_string(), None),
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
                    solver: solver_str.to_string(),
                    theory: theory_str.to_string(),
                    lemmas: lemmas_str.to_string(),
                    timeout_ms: timeout,
                },
                result: result_str,
                counter_example: cex,
            };

            println!("{}", serde_json::to_string_pretty(&output).unwrap());
        }
    }
}

fn print_counter_example_human(model: &HashMap<String, num_bigint::BigUint>) {
    if model.is_empty() {
        return;
    }

    let constants: std::collections::HashSet<&str> =
        ["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"]
            .into_iter()
            .collect();

    let mut x_vals: Vec<_> = Vec::new();
    let mut y_vals: Vec<_> = Vec::new();

    for (var, val) in model {
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

fn build_counter_example(model: &HashMap<String, num_bigint::BigUint>) -> CounterExample {
    let constants: std::collections::HashSet<&str> =
        ["p", "ps1", "ps2", "ps3", "ps4", "ps5", "zero", "one"]
            .into_iter()
            .collect();

    let mut w1 = HashMap::new();
    let mut w2 = HashMap::new();

    for (var, val) in model {
        if constants.contains(var.as_str()) {
            continue;
        }
        if var.starts_with('y') {
            w2.insert(var.clone(), val.to_string());
        } else {
            w1.insert(var.clone(), val.to_string());
        }
    }

    CounterExample {
        witness_1: w1,
        witness_2: w2,
    }
}

// ============================================================
// info command
// ============================================================

fn cmd_info(r1cs_path: PathBuf, show_constraints: bool, format: OutputFormat) {
    let r1cs = picus_r1cs::parser::read_r1cs_file(&r1cs_path).unwrap_or_else(|e| {
        aprintln!("{} failed to read R1CS file: {}", "error:".red().bold(), e);
        std::process::exit(1);
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

            println!("{}", serde_json::to_string_pretty(&output).unwrap());
        }
    }
}
