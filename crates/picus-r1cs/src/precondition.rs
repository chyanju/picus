//! Precondition file parser.
//!
//! Precondition files are JSON arrays of `[tag, expression]` pairs:
//! - `["unique", signal_id]` — declares a signal as assumed unique
//! - `["x", expr]` or `["y", expr]` — additional constraints for original/alternative witness

use crate::grammar::*;
use num_bigint::BigUint;
use serde_json::Value;
use std::collections::HashSet;
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum PreconditionError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("JSON parse error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("Invalid precondition format: {0}")]
    Format(String),
}

/// Parsed preconditions.
#[derive(Debug, Clone)]
pub struct Preconditions {
    /// Set of signal indices assumed to be unique.
    pub unique_set: HashSet<usize>,
    /// List of (tag, command) pairs where tag is "x" or "y".
    pub commands: Vec<(String, RCmd)>,
}

/// Parse a precondition JSON file.
pub fn read_precondition(path: &Path) -> Result<Preconditions, PreconditionError> {
    let content = std::fs::read_to_string(path)?;
    let json: Value = serde_json::from_str(&content)?;

    let arr = json
        .as_array()
        .ok_or_else(|| PreconditionError::Format("top-level must be an array".into()))?;

    let mut unique_set = HashSet::new();
    let mut commands = Vec::new();

    for entry in arr {
        let pair = entry
            .as_array()
            .ok_or_else(|| PreconditionError::Format("each entry must be an array".into()))?;
        if pair.len() != 2 {
            return Err(PreconditionError::Format(format!(
                "entry should have 2 elements, got {}",
                pair.len()
            )));
        }

        let tag = pair[0]
            .as_str()
            .ok_or_else(|| PreconditionError::Format("tag must be a string".into()))?;

        if tag == "unique" {
            let signal_id = pair[1].as_u64().ok_or_else(|| {
                PreconditionError::Format("unique entry value must be a number".into())
            })? as usize;
            unique_set.insert(signal_id);
        } else {
            let expr = parse_precondition_expr(&pair[1])?;
            commands.push((tag.to_string(), RCmd::Assert(expr)));
        }
    }

    Ok(Preconditions {
        unique_set,
        commands,
    })
}

fn parse_precondition_expr(val: &Value) -> Result<RExpr, PreconditionError> {
    let arr = val.as_array().ok_or_else(|| {
        PreconditionError::Format(format!("expected array expression, got {:?}", val))
    })?;

    if arr.is_empty() {
        return Err(PreconditionError::Format("empty expression".into()));
    }

    let tag = arr[0].as_str().ok_or_else(|| {
        PreconditionError::Format(format!("expression tag must be string, got {:?}", arr[0]))
    })?;

    match tag {
        "rassert" => {
            let inner = parse_precondition_expr(&arr[1])?;
            // rassert wraps an expression; we unwrap it since RCmd::Assert already wraps
            Ok(inner)
        }
        "req" => {
            let lhs = parse_precondition_expr(&arr[1])?;
            let rhs = parse_precondition_expr(&arr[2])?;
            Ok(RExpr::Eq(Box::new(lhs), Box::new(rhs)))
        }
        "rneq" => {
            let lhs = parse_precondition_expr(&arr[1])?;
            let rhs = parse_precondition_expr(&arr[2])?;
            Ok(RExpr::Neq(Box::new(lhs), Box::new(rhs)))
        }
        "rmul" => {
            let vs_arr = arr[1].as_array().ok_or_else(|| {
                PreconditionError::Format("rmul argument must be array".into())
            })?;
            let vs: Result<Vec<RExpr>, _> =
                vs_arr.iter().map(parse_precondition_expr).collect();
            Ok(RExpr::Mul(vs?))
        }
        "rmod" => {
            let lhs = parse_precondition_expr(&arr[1])?;
            let rhs = parse_precondition_expr(&arr[2])?;
            Ok(RExpr::Mod(Box::new(lhs), Box::new(rhs)))
        }
        "rvar" => {
            let name = arr[1].as_str().ok_or_else(|| {
                PreconditionError::Format("rvar argument must be string".into())
            })?;
            Ok(RExpr::Var(name.to_string()))
        }
        "rint" => {
            let v = arr[1].as_u64().ok_or_else(|| {
                PreconditionError::Format("rint argument must be a number".into())
            })?;
            Ok(RExpr::Int(BigUint::from(v)))
        }
        _ => Err(PreconditionError::Format(format!(
            "unsupported precondition tag: {}",
            tag
        ))),
    }
}
