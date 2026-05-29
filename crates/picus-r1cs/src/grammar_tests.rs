use super::*;
use num_bigint::BigUint;

fn block(nnz: u32, wire_ids: Vec<u32>, factors: Vec<BigUint>) -> ConstraintBlock {
    ConstraintBlock { nnz, wire_ids, factors }
}

fn empty_block() -> ConstraintBlock {
    block(0, vec![], vec![])
}

fn dummy_header() -> HeaderSection {
    HeaderSection {
        field_size: 8,
        prime_number: BigUint::from(7u32),
        n_wires: 3,
        n_pub_out: 0,
        n_pub_in: 0,
        n_prv_in: 0,
        n_labels: 3,
        m_constraints: 0,
    }
}

fn r1cs_file(constraints: Vec<Constraint>, m_constraints: u32) -> R1csFile {
    let mut h = dummy_header();
    h.m_constraints = m_constraints;
    R1csFile {
        magic: [0x72, 0x31, 0x63, 0x73],
        version: 1,
        n_sections: 3,
        header: h,
        constraints: ConstraintSection { constraints },
        w2l: W2lSection { labels: vec![0, 1, 2] },
        inputs: vec![],
        outputs: vec![],
    }
}

#[test]
fn test_n_constraints_returns_header_value() {
    let f = r1cs_file(vec![], 5);
    assert_eq!(f.n_constraints(), 5);
}

#[test]
fn test_n_wires_returns_header_value() {
    let f = r1cs_file(vec![], 0);
    // dummy_header sets n_wires = 3
    assert_eq!(f.n_wires(), 3);
}

#[test]
fn test_constraint_to_string_zero_block_is_zero_literal() {
    // Per the doc/code: nnz == 0 ⇒ block renders as "0".
    let c = Constraint {
        a: empty_block(),
        b: empty_block(),
        c: empty_block(),
    };
    let f = r1cs_file(vec![c], 1);
    let s = f.constraint_to_string(0);
    assert_eq!(s, "( 0 ) * ( 0 ) = 0");
}

#[test]
fn test_constraint_to_string_single_term_block() {
    // a: 2 * x0; b: 1 * x1; c: empty
    let c = Constraint {
        a: block(1, vec![0], vec![BigUint::from(2u32)]),
        b: block(1, vec![1], vec![BigUint::from(1u32)]),
        c: empty_block(),
    };
    let f = r1cs_file(vec![c], 1);
    let s = f.constraint_to_string(0);
    assert_eq!(s, "( (2 * x0) ) * ( (1 * x1) ) = 0");
}

#[test]
fn test_constraint_to_string_multi_term_joined_with_plus() {
    // a: 1 * x0 + 3 * x1
    let c = Constraint {
        a: block(
            2,
            vec![0, 1],
            vec![BigUint::from(1u32), BigUint::from(3u32)],
        ),
        b: empty_block(),
        c: empty_block(),
    };
    let f = r1cs_file(vec![c], 1);
    let s = f.constraint_to_string(0);
    assert!(s.contains("(1 * x0) + (3 * x1)"), "got: {}", s);
}

#[test]
fn test_constraint_to_string_out_of_range_yields_diag() {
    // Indexing past the end returns a diagnostic — must NOT panic.
    let f = r1cs_file(vec![], 0);
    let s = f.constraint_to_string(42);
    assert!(s.contains("out of range"), "got: {}", s);
    assert!(s.contains("42"), "got: {}", s);
}

#[test]
fn test_constraint_block_clone_preserves_fields() {
    // Sanity check for #[derive(Clone)] on ConstraintBlock.
    let b = block(2, vec![5, 7], vec![BigUint::from(11u32), BigUint::from(13u32)]);
    let cloned = b.clone();
    assert_eq!(cloned.nnz, 2);
    assert_eq!(cloned.wire_ids, vec![5, 7]);
    assert_eq!(cloned.factors, vec![BigUint::from(11u32), BigUint::from(13u32)]);
}

#[test]
fn test_header_section_clone_preserves_prime() {
    let h = dummy_header();
    let cloned = h.clone();
    assert_eq!(cloned.prime_number, BigUint::from(7u32));
    assert_eq!(cloned.field_size, 8);
}

#[test]
fn test_w2l_section_default_empty() {
    let w = W2lSection { labels: vec![] };
    assert!(w.labels.is_empty());
}
