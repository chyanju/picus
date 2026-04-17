//! Symbol (.sym) file parser.
//!
//! The .sym file is a CSV mapping signal IDs to Circom variable names.
//! Each row: `signal_id, ?, order, qualified_name`
//! e.g.: `3,0,2,main.adder.out`

use std::collections::{HashMap, HashSet};
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SymParseError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("CSV parse error: {0}")]
    Csv(#[from] csv::Error),
    #[error("Invalid signal ID: {0}")]
    BadSignalId(String),
}

/// Parsed symbol file data.
#[derive(Debug, Clone)]
pub struct SymbolMap {
    /// signal_index → topological order
    pub order_vec: HashMap<usize, usize>,
    /// signal_index → set of scope strings (e.g., {"adder", "main"})
    pub scope_vec: HashMap<usize, HashSet<String>>,
    /// order → scope set
    pub order_to_scope: HashMap<usize, HashSet<String>>,
    /// signal_index → full qualified name (e.g., "main.adder.out")
    pub signal_names: HashMap<usize, String>,
    /// Maximum number of wires (for sizing vectors)
    pub n_wires: usize,
}

/// Parse a .sym file.
pub fn parse_sym_file(path: &Path, n_wires: usize) -> Result<SymbolMap, SymParseError> {
    let content = std::fs::read_to_string(path)?;
    parse_sym(&content, n_wires)
}

/// Parse .sym content from a string.
pub fn parse_sym(content: &str, n_wires: usize) -> Result<SymbolMap, SymParseError> {
    let mut order_vec = HashMap::new();
    let mut scope_vec = HashMap::new();
    let mut order_to_scope = HashMap::new();
    let mut signal_names = HashMap::new();

    // Wire 0 (constant 1) is always present with scope {"main"} and order 0
    let main_scope: HashSet<String> = ["main".to_string()].into_iter().collect();
    order_vec.insert(0, 0);
    scope_vec.insert(0, main_scope.clone());
    order_to_scope.insert(0, main_scope);

    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false)
        .from_reader(content.as_bytes());

    for result in rdr.records() {
        let record = result?;
        if record.len() < 4 {
            continue;
        }

        let signal_id: usize = record[0]
            .trim()
            .parse()
            .map_err(|_| SymParseError::BadSignalId(record[0].to_string()))?;
        let order: usize = record[2].trim().parse().unwrap_or(0);
        let qualified_name = record[3].trim().to_string();

        // Extract scope: split by '.', drop last segment
        let parts: Vec<&str> = qualified_name.split('.').collect();
        let scope: HashSet<String> = if parts.len() > 1 {
            parts[..parts.len() - 1]
                .iter()
                .map(|s| s.to_string())
                .collect()
        } else {
            ["main".to_string()].into_iter().collect()
        };

        // Signal IDs in .sym are 1-based, translate to 0-based
        let idx = signal_id - 1;
        order_vec.insert(idx, order);
        scope_vec.insert(idx, scope.clone());
        order_to_scope.insert(order, scope);
        signal_names.insert(idx, qualified_name);
    }

    Ok(SymbolMap {
        order_vec,
        scope_vec,
        order_to_scope,
        signal_names,
        n_wires,
    })
}
