use super::*;

#[test]
fn test_magic_check() {
    let bad = vec![0x00; 12];
    assert!(read_r1cs(&bad).is_err());
}

#[test]
fn audit_truncated_block_returns_error_not_panic() {
    // Valid magic + version + n_sections, then one section header
    // claiming 100 bytes of content but the file ends right after
    // the header. `parse_constraint_block` must return
    // `R1csParseError::Truncated` rather than panic on
    // out-of-bounds slice indexing.
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    // one truncated section: type 2 (constraints), claiming 100B
    data.extend_from_slice(&2u32.to_le_bytes());
    data.extend_from_slice(&100u64.to_le_bytes());
    // ... no payload ...
    let r = read_r1cs(&data);
    // Either "wrong section count" or "truncated" is acceptable;
    // what must NOT happen is a panic.
    assert!(r.is_err(), "expected error, got Ok");
}

#[test]
fn audit_overflowing_section_size_returns_error_not_panic() {
    // A section header whose claimed size is u64::MAX. In
    // `parse_sections`, `data_start + section_size` would wrap (release)
    // or panic (debug) without the `checked_add` guard, then index an
    // out-of-range slice. Must surface as a clean error, never a panic.
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    data.extend_from_slice(&1u32.to_le_bytes()); // section type
    data.extend_from_slice(&u64::MAX.to_le_bytes()); // adversarial size
    // ... no payload ...
    let r = read_r1cs(&data);
    assert!(r.is_err(), "expected error, got Ok");
}

#[test]
fn audit_implausible_field_size_returns_error_not_oom() {
    // Three valid section headers (types 1 / 2 / 3 so the count
    // check passes), but the header section's payload claims
    // `field_size = 1 << 30` (1 GiB). The parser must reject
    // with `HeaderImplausible` before allocating the prime
    // buffer.
    let header_payload: Vec<u8> = (1u32 << 30).to_le_bytes().to_vec();
    let constraint_payload: Vec<u8> = Vec::new();
    let w2l_payload: Vec<u8> = Vec::new();

    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    for (ty, payload) in [
        (1u32, &header_payload),
        (2u32, &constraint_payload),
        (3u32, &w2l_payload),
    ] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(
        matches!(r, Err(R1csParseError::HeaderImplausible { .. })),
        "expected HeaderImplausible, got {:?}",
        r
    );
}

/// Assemble a 3-section R1CS (types 1/2/3) from raw payloads.
fn assemble(header: &[u8], constraints: &[u8], w2l: &[u8]) -> Vec<u8> {
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    for (ty, payload) in [(1u32, header), (2u32, constraints), (3u32, w2l)] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    data
}

/// Header payload with prime 7 and the given wire/IO counts.
fn header_payload(n_wires: u32, n_pub_out: u32, n_pub_in: u32, n_prv_in: u32) -> Vec<u8> {
    let mut h: Vec<u8> = Vec::new();
    h.extend_from_slice(&8u32.to_le_bytes()); // field_size = 8
    h.extend_from_slice(&[7u8, 0, 0, 0, 0, 0, 0, 0]); // prime = 7
    h.extend_from_slice(&n_wires.to_le_bytes());
    h.extend_from_slice(&n_pub_out.to_le_bytes());
    h.extend_from_slice(&n_pub_in.to_le_bytes());
    h.extend_from_slice(&n_prv_in.to_le_bytes());
    h.extend_from_slice(&1u64.to_le_bytes()); // n_labels
    h.extend_from_slice(&0u32.to_le_bytes()); // m_constraints = 0
    h
}

#[test]
fn audit_implausible_io_count_returns_error_not_oom() {
    // n_wires = 1 but n_pub_in = u32::MAX violates the I/O-subset
    // invariant (1 + n_pub_out + n_pub_in + n_prv_in <= n_wires). The
    // parser must reject before the unbounded input-list build, not
    // hang/OOM constructing a billion-element Vec.
    let header = header_payload(1, 0, u32::MAX, 0);
    let w2l = 1u64.to_le_bytes().to_vec(); // 1 label
    let r = read_r1cs(&assemble(&header, &[], &w2l));
    assert!(
        matches!(r, Err(R1csParseError::HeaderImplausible { .. })),
        "expected HeaderImplausible, got {:?}",
        r
    );
}

#[test]
fn audit_implausible_n_wires_returns_error_not_oom() {
    // n_wires = u32::MAX but the wire-to-label map has one entry. The
    // parser must reject before r1cs_to_poly_ir allocates 2 * n_wires
    // variable names (~8.5 GiB). The I/O guard passes here (io_sum = 1),
    // so this exercises the n_wires <= w2l.labels.len() guard.
    let header = header_payload(u32::MAX, 0, 0, 0);
    let w2l = 1u64.to_le_bytes().to_vec(); // 1 label << n_wires
    let r = read_r1cs(&assemble(&header, &[], &w2l));
    assert!(
        matches!(r, Err(R1csParseError::HeaderImplausible { .. })),
        "expected HeaderImplausible, got {:?}",
        r
    );
}

#[test]
fn audit_zero_prime_returns_error_not_panic() {
    // field_size = 8 (multiple of 8, fits the payload) but the prime
    // bytes are all zero → prime = 0. Must be rejected as a parse error
    // rather than reaching PrimeField::new's `assert!(prime > 1)` and
    // aborting the process during lowering.
    let field_size: u32 = 8;
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&field_size.to_le_bytes());
    header_payload.extend_from_slice(&[0u8; 8]); // prime = 0
    // (the prime check fires before the remaining header fields are read)

    let constraint_payload: Vec<u8> = Vec::new();
    let w2l_payload: Vec<u8> = Vec::new();

    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    for (ty, payload) in [
        (1u32, &header_payload),
        (2u32, &constraint_payload),
        (3u32, &w2l_payload),
    ] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(
        matches!(r, Err(R1csParseError::InvalidPrime(_))),
        "expected InvalidPrime, got {:?}",
        r
    );
}

#[test]
fn audit_malformed_nnz_returns_error_not_panic() {
    // Header is plausible but constraint block claims `nnz` larger
    // than the block payload. The parser must return an error
    // rather than panic on out-of-bounds slice indexing.
    let p_bytes: Vec<u8> = vec![7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]; // prime = 7
    let field_size: u32 = p_bytes.len() as u32; // 8 — multiple of 8 OK

    // Header payload (40 bytes total layout):
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&field_size.to_le_bytes());
    header_payload.extend_from_slice(&p_bytes);
    header_payload.extend_from_slice(&1u32.to_le_bytes()); // n_wires
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_out
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_in
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_prv_in
    header_payload.extend_from_slice(&1u64.to_le_bytes()); // n_labels
    header_payload.extend_from_slice(&1u32.to_le_bytes()); // m_constraints = 1

    // Constraint section: one block with claimed nnz = u32::MAX,
    // payload only 4 bytes for nnz itself.
    let mut constraint_payload: Vec<u8> = Vec::new();
    constraint_payload.extend_from_slice(&u32::MAX.to_le_bytes());

    // w2l section: 8 bytes
    let w2l_payload: Vec<u8> = vec![0u8; 8];

    // Assemble file
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes()); // version
    data.extend_from_slice(&3u32.to_le_bytes()); // n_sections
    for (ty, payload) in [
        (1u32, &header_payload),
        (2u32, &constraint_payload),
        (3u32, &w2l_payload),
    ] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(r.is_err());
}

#[test]
fn audit_small_field_size_one_byte_prime_parses() {
    // `field_size = 1` (a 1-byte prime, e.g. GF(7)) is a legitimate
    // iden3 width and is NOT required to be a multiple of 8. The
    // decoded prime and the small field_size must survive.
    let mut header: Vec<u8> = Vec::new();
    header.extend_from_slice(&1u32.to_le_bytes()); // field_size = 1
    header.push(7u8); // prime = 7 (one byte)
    header.extend_from_slice(&2u32.to_le_bytes()); // n_wires = 2
    header.extend_from_slice(&1u32.to_le_bytes()); // n_pub_out = 1
    header.extend_from_slice(&0u32.to_le_bytes()); // n_pub_in
    header.extend_from_slice(&0u32.to_le_bytes()); // n_prv_in
    header.extend_from_slice(&2u64.to_le_bytes()); // n_labels = 2
    header.extend_from_slice(&0u32.to_le_bytes()); // m_constraints = 0

    // w2l: 2 labels (16 bytes) so n_wires (2) <= labels.len() (2).
    let mut w2l: Vec<u8> = Vec::new();
    w2l.extend_from_slice(&0u64.to_le_bytes());
    w2l.extend_from_slice(&1u64.to_le_bytes());

    let data = assemble(&header, &[], &w2l);
    let r = read_r1cs(&data).expect("1-byte field_size must parse");
    assert_eq!(r.header.field_size, 1);
    assert_eq!(r.header.prime_number, BigUint::from(7u32));
}

#[test]
fn prop_bad_version_rejected() {
    // Versions other than 1 must be rejected with BadVersion.
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&2u32.to_le_bytes()); // version = 2 (unsupported)
    data.extend_from_slice(&0u32.to_le_bytes()); // n_sections
    let r = read_r1cs(&data);
    assert!(matches!(r, Err(R1csParseError::BadVersion(2))), "got {:?}", r);
}

#[test]
fn prop_short_input_io_error() {
    // Less than the magic+version+n_sections preamble => IO read error,
    // not panic.
    let data: Vec<u8> = vec![0x72, 0x31, 0x63]; // "r1c" — 3 bytes only
    let r = read_r1cs(&data);
    assert!(r.is_err());
}

#[test]
fn prop_missing_section_type_three() {
    // Two valid section headers (types 1 and 2) but no type-3 section.
    // After filtering, only 2 sections remain → WrongSectionCount.
    let header_payload = header_payload(1, 0, 0, 0);
    let constraint_payload: Vec<u8> = Vec::new();
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes());
    data.extend_from_slice(&2u32.to_le_bytes()); // n_sections = 2
    for (ty, payload) in [(1u32, &header_payload), (2u32, &constraint_payload)] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(matches!(r, Err(R1csParseError::WrongSectionCount(_))), "got {:?}", r);
}

#[test]
fn prop_constraint_count_mismatch() {
    // Header claims 1 constraint but constraint section has zero bytes.
    let header = header_payload(1, 0, 0, 0);
    // Now patch the header to claim m_constraints = 1.
    // header layout: field_size(4) + prime(8) + n_wires(4) + n_pub_out(4)
    //              + n_pub_in(4) + n_prv_in(4) + n_labels(8) + m_constraints(4)
    let mut h = header.clone();
    let len = h.len();
    h[len - 4..len].copy_from_slice(&1u32.to_le_bytes()); // m_constraints = 1
    let w2l = 0u64.to_le_bytes().to_vec(); // 1 label
    let r = read_r1cs(&assemble(&h, &[], &w2l));
    assert!(matches!(r, Err(R1csParseError::ConstraintCountMismatch { .. })), "got {:?}", r);
}

#[test]
fn prop_bad_w2l_size_not_multiple_of_8() {
    // w2l section with byte length not a multiple of 8 must be rejected.
    let header = header_payload(1, 0, 0, 0);
    let w2l = vec![0u8; 7]; // 7 bytes, not a multiple of 8
    let r = read_r1cs(&assemble(&header, &[], &w2l));
    assert!(matches!(r, Err(R1csParseError::BadW2lSize(7))), "got {:?}", r);
}

#[test]
fn prop_prime_one_rejected() {
    // prime = 1 must be rejected with InvalidPrime (the boundary check is `<= 1`).
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&8u32.to_le_bytes()); // field_size = 8
    header_payload.extend_from_slice(&[1u8, 0, 0, 0, 0, 0, 0, 0]); // prime = 1
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes());
    data.extend_from_slice(&3u32.to_le_bytes());
    for (ty, payload) in [(1u32, &header_payload), (2u32, &Vec::new()), (3u32, &Vec::new())] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(matches!(r, Err(R1csParseError::InvalidPrime(_))), "got {:?}", r);
}

#[test]
fn prop_well_formed_empty_constraints_round_trip() {
    // A header with n_wires=3, n_pub_out=1, n_pub_in=1, n_prv_in=0,
    // m_constraints=0. Verify the parsed file's input/output lists
    // follow the ecne 0-based convention:
    //   outputs = [1]            (1-based [2..=2] → 0-based [1])
    //   inputs  = [0, 2]         (1-based [1] ++ [3..=3] → 0-based [0, 2])
    let header = header_payload(3, 1, 1, 0);
    let mut w2l = Vec::new();
    for i in 0u64..3 {
        w2l.extend_from_slice(&i.to_le_bytes());
    }
    let r = read_r1cs(&assemble(&header, &[], &w2l)).expect("must parse");
    assert_eq!(r.outputs, vec![1]);
    assert_eq!(r.inputs, vec![0, 2]);
    assert_eq!(r.n_constraints(), 0);
    assert_eq!(r.n_wires(), 3);
}

#[test]
fn prop_well_formed_single_constraint_parses() {
    // One constraint: (1 * x0) * (1 * x1) = (1 * x2). field_size=8, prime=7.
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&8u32.to_le_bytes()); // field_size
    header_payload.extend_from_slice(&[7u8, 0, 0, 0, 0, 0, 0, 0]); // prime = 7
    header_payload.extend_from_slice(&3u32.to_le_bytes()); // n_wires
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_out
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_in
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_prv_in
    header_payload.extend_from_slice(&3u64.to_le_bytes()); // n_labels
    header_payload.extend_from_slice(&1u32.to_le_bytes()); // m_constraints = 1

    // Constraint block helper: nnz(4) + nnz * (wire_id(4) + factor(8))
    let mut cp: Vec<u8> = Vec::new();
    // a: 1 * x0
    cp.extend_from_slice(&1u32.to_le_bytes());
    cp.extend_from_slice(&0u32.to_le_bytes());
    cp.extend_from_slice(&[1u8, 0, 0, 0, 0, 0, 0, 0]);
    // b: 1 * x1
    cp.extend_from_slice(&1u32.to_le_bytes());
    cp.extend_from_slice(&1u32.to_le_bytes());
    cp.extend_from_slice(&[1u8, 0, 0, 0, 0, 0, 0, 0]);
    // c: 1 * x2
    cp.extend_from_slice(&1u32.to_le_bytes());
    cp.extend_from_slice(&2u32.to_le_bytes());
    cp.extend_from_slice(&[1u8, 0, 0, 0, 0, 0, 0, 0]);

    let mut w2l: Vec<u8> = Vec::new();
    for i in 0u64..3 {
        w2l.extend_from_slice(&i.to_le_bytes());
    }
    let r = read_r1cs(&assemble(&header_payload, &cp, &w2l)).expect("must parse");
    assert_eq!(r.n_constraints(), 1);
    let c = &r.constraints.constraints[0];
    assert_eq!(c.a.nnz, 1);
    assert_eq!(c.b.nnz, 1);
    assert_eq!(c.c.nnz, 1);
    assert_eq!(c.a.wire_ids, vec![0u32]);
    assert_eq!(c.b.wire_ids, vec![1u32]);
    assert_eq!(c.c.wire_ids, vec![2u32]);
    assert_eq!(c.a.factors, vec![BigUint::from(1u32)]);
}

#[test]
fn prop_factor_reduced_modulo_prime() {
    // A factor of value 9 with prime=7 must reduce to 2.
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&8u32.to_le_bytes()); // field_size
    header_payload.extend_from_slice(&[7u8, 0, 0, 0, 0, 0, 0, 0]); // prime = 7
    header_payload.extend_from_slice(&1u32.to_le_bytes()); // n_wires
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_out
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_pub_in
    header_payload.extend_from_slice(&0u32.to_le_bytes()); // n_prv_in
    header_payload.extend_from_slice(&1u64.to_le_bytes()); // n_labels
    header_payload.extend_from_slice(&1u32.to_le_bytes()); // m_constraints = 1

    let mut cp: Vec<u8> = Vec::new();
    // a: 9 * x0  -> after reduction mod 7 => 2
    cp.extend_from_slice(&1u32.to_le_bytes());
    cp.extend_from_slice(&0u32.to_le_bytes());
    cp.extend_from_slice(&[9u8, 0, 0, 0, 0, 0, 0, 0]);
    // b: zero block
    cp.extend_from_slice(&0u32.to_le_bytes());
    // c: zero block
    cp.extend_from_slice(&0u32.to_le_bytes());

    let w2l = 0u64.to_le_bytes().to_vec();
    let r = read_r1cs(&assemble(&header_payload, &cp, &w2l)).expect("must parse");
    let c = &r.constraints.constraints[0];
    assert_eq!(c.a.factors, vec![BigUint::from(2u32)]);
    assert_eq!(c.b.nnz, 0);
    assert_eq!(c.c.nnz, 0);
}

#[test]
fn prop_extra_unknown_sections_ignored() {
    // Adding a section of type 99 (not 1/2/3) is filtered out; the
    // remaining 3 sections (1/2/3) still pass.
    let header = header_payload(1, 0, 0, 0);
    let w2l = 0u64.to_le_bytes().to_vec();
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes());
    data.extend_from_slice(&4u32.to_le_bytes()); // n_sections = 4
    for (ty, payload) in [
        (1u32, &header),
        (99u32, &vec![0u8; 4]), // unknown section, ignored
        (2u32, &Vec::new()),
        (3u32, &w2l),
    ] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(r.is_ok(), "expected Ok, got {:?}", r);
}

#[test]
fn audit_field_size_larger_than_header_block_rejected() {
    // field_size > header payload length must be rejected with
    // HeaderImplausible — never attempt to allocate the prime buffer.
    let mut header_payload: Vec<u8> = Vec::new();
    header_payload.extend_from_slice(&100u32.to_le_bytes()); // field_size = 100
    // ...but block only contains 4 bytes so far.
    let mut data: Vec<u8> = b"r1cs".to_vec();
    data.extend_from_slice(&1u32.to_le_bytes());
    data.extend_from_slice(&3u32.to_le_bytes());
    for (ty, payload) in [
        (1u32, &header_payload),
        (2u32, &Vec::new()),
        (3u32, &Vec::new()),
    ] {
        data.extend_from_slice(&ty.to_le_bytes());
        data.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        data.extend_from_slice(payload);
    }
    let r = read_r1cs(&data);
    assert!(matches!(r, Err(R1csParseError::HeaderImplausible { .. })), "got {:?}", r);
}
