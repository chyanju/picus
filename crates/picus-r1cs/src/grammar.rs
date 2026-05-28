//! R1CS binary-file struct types.

use num_bigint::BigUint;

// ============================================================
// Binary R1CS file structs
// ============================================================

/// A parsed R1CS file.
#[derive(Debug, Clone)]
pub struct R1csFile {
    pub magic: [u8; 4],
    pub version: u32,
    pub n_sections: u32,
    pub header: HeaderSection,
    pub constraints: ConstraintSection,
    pub w2l: W2lSection,
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct HeaderSection {
    pub field_size: u32,
    pub prime_number: BigUint,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub m_constraints: u32,
}

#[derive(Debug, Clone)]
pub struct ConstraintSection {
    pub constraints: Vec<Constraint>,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub a: ConstraintBlock,
    pub b: ConstraintBlock,
    pub c: ConstraintBlock,
}

#[derive(Debug, Clone)]
pub struct ConstraintBlock {
    pub nnz: u32,
    pub wire_ids: Vec<u32>,
    pub factors: Vec<BigUint>,
}

#[derive(Debug, Clone)]
pub struct W2lSection {
    pub labels: Vec<u64>,
}

impl R1csFile {
    #[must_use]
    pub fn n_constraints(&self) -> u32 {
        self.header.m_constraints
    }

    #[must_use]
    pub fn n_wires(&self) -> u32 {
        self.header.n_wires
    }

    #[must_use]
    pub fn constraint_to_string(&self, id: usize) -> String {
        let Some(c) = self.constraints.constraints.get(id) else {
            return format!("<constraint index {id} out of range>");
        };
        let block_str = |b: &ConstraintBlock| -> String {
            if b.nnz == 0 {
                return "0".to_string();
            }
            b.wire_ids
                .iter()
                .zip(b.factors.iter())
                .map(|(w, f)| format!("({} * x{})", f, w))
                .collect::<Vec<_>>()
                .join(" + ")
        };
        format!(
            "( {} ) * ( {} ) = {}",
            block_str(&c.a),
            block_str(&c.b),
            block_str(&c.c)
        )
    }
}
