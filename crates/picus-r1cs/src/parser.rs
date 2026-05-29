//! R1CS binary file parser — reads the iden3 R1CS binary format.
//!
//! Format spec: <https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md>

use crate::grammar::*;
use byteorder::{LittleEndian, ReadBytesExt};
use num_bigint::BigUint;
use std::io::{self, Cursor, Read};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum R1csParseError {
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),
    #[error("Invalid magic number: expected 'r1cs', got {0:?}")]
    BadMagic([u8; 4]),
    #[error("Unsupported version: {0}")]
    BadVersion(u32),
    #[error("Expected 3 sections after filtering, got {0}")]
    WrongSectionCount(usize),
    #[error("Section type {0} not found")]
    SectionNotFound(u32),
    #[error("Constraint count mismatch: header says {expected}, parsed {actual}")]
    ConstraintCountMismatch { expected: u32, actual: u32 },
    #[error("Field size {0} is not a multiple of 8")]
    BadFieldSize(u32),
    #[error("W2L section size {0} is not a multiple of 8")]
    BadW2lSize(usize),
    #[error("Truncated data: need {need} bytes for {ctx}, only {have} available")]
    Truncated {
        ctx: &'static str,
        need: usize,
        have: usize,
    },
    #[error("Header field {field} = {claimed} exceeds sane upper bound {bound}")]
    HeaderImplausible {
        field: &'static str,
        claimed: u64,
        bound: u64,
    },
    #[error("Field modulus {0} is invalid (must be > 1)")]
    InvalidPrime(BigUint),
}

/// Hard upper bound on a header-claimed count before allocating
/// proportional memory. An R1CS file's `m_constraints`, `nnz`, etc.
/// can't legitimately exceed the on-disk payload size (each constraint
/// is at least a few bytes), so this is "what could the file legally
/// describe given its byte count" rather than a hard-coded magic
/// number. Per-call sites multiply against the data slice length.
const ABSOLUTE_COUNT_CAP: usize = 1usize << 30; // 1 G entries

/// Returns a safe `Vec::with_capacity` hint: `min(claimed, data_len)`,
/// further capped at [`ABSOLUTE_COUNT_CAP`]. Adversarial headers
/// claiming 4 G constraints in a 12-byte file now allocate `O(12)`
/// rather than `O(4 G * sizeof)`.
fn capped_capacity(claimed: u64, data_len: usize) -> usize {
    let by_data = data_len;
    let by_claim = usize::try_from(claimed).unwrap_or(ABSOLUTE_COUNT_CAP);
    by_data.min(by_claim).min(ABSOLUTE_COUNT_CAP)
}

/// Safe byte slice with explicit error for header-controlled lengths.
fn slice<'a>(data: &'a [u8], start: usize, end: usize, ctx: &'static str) -> Result<&'a [u8], R1csParseError> {
    data.get(start..end).ok_or(R1csParseError::Truncated {
        ctx,
        need: end,
        have: data.len(),
    })
}

/// Read an R1CS binary file from a byte slice.
pub fn read_r1cs(data: &[u8]) -> Result<R1csFile, R1csParseError> {
    let mut cur = Cursor::new(data);

    // Magic: "r1cs" = 0x72 0x31 0x63 0x73
    let mut magic = [0u8; 4];
    cur.read_exact(&mut magic)?;
    if magic != [0x72, 0x31, 0x63, 0x73] {
        return Err(R1csParseError::BadMagic(magic));
    }

    let version = cur.read_u32::<LittleEndian>()?;
    if version != 1 {
        return Err(R1csParseError::BadVersion(version));
    }

    let n_sections = cur.read_u32::<LittleEndian>()?;

    // Read remaining bytes as raw sections
    let mut sections_raw = Vec::new();
    cur.read_to_end(&mut sections_raw)?;

    // Parse and filter to accepted types (1, 2, 3)
    let sections = parse_sections(&sections_raw)?;
    let filtered: Vec<&Section> = sections
        .iter()
        .filter(|s| s.section_type == 1 || s.section_type == 2 || s.section_type == 3)
        .collect();

    if filtered.len() != 3 {
        return Err(R1csParseError::WrongSectionCount(filtered.len()));
    }

    // Find sections by type
    let header_sec = filtered
        .iter()
        .find(|s| s.section_type == 1)
        .ok_or(R1csParseError::SectionNotFound(1))?;
    let constraint_sec = filtered
        .iter()
        .find(|s| s.section_type == 2)
        .ok_or(R1csParseError::SectionNotFound(2))?;
    let w2l_sec = filtered
        .iter()
        .find(|s| s.section_type == 3)
        .ok_or(R1csParseError::SectionNotFound(3))?;

    let header = parse_header_section(&header_sec.data)?;
    let field_size = header.field_size;
    let m_constraints = header.m_constraints;
    let constraints =
        parse_constraint_section(&constraint_sec.data, field_size, m_constraints, &header.prime_number)?;
    let w2l = parse_w2l_section(&w2l_sec.data)?;

    // Header-count plausibility. Two invariants hold for any well-formed
    // iden3 R1CS: the wire-to-label map carries exactly one label per wire
    // (so `n_wires == w2l.labels.len()`), and the I/O wires plus the
    // constant wire are a subset of all wires. Reject violations here, so
    // an adversarial header (e.g. `n_pub_in = u32::MAX`) cannot drive the
    // unbounded input-list build below or the `2 * n_wires` ring
    // allocation in `r1cs_to_poly_ir`. `io_sum` is computed in `u64` to
    // avoid overflow when the three counts are near `u32::MAX`.
    let io_sum = 1 + header.n_pub_out as u64 + header.n_pub_in as u64 + header.n_prv_in as u64;
    if io_sum > header.n_wires as u64 {
        return Err(R1csParseError::HeaderImplausible {
            field: "1 + n_pub_out + n_pub_in + n_prv_in",
            claimed: io_sum,
            bound: header.n_wires as u64,
        });
    }
    if header.n_wires as usize > w2l.labels.len() {
        return Err(R1csParseError::HeaderImplausible {
            field: "n_wires",
            claimed: header.n_wires as u64,
            bound: w2l.labels.len() as u64,
        });
    }

    // Compute input/output lists. Ecne convention (1-based):
    //   inputs = [1] ++ [istart..iend]
    //     istart = 2 + npubout
    //     iend   = 1 + npubout + npubin + nprvin
    // Translated to 0-based below.
    let n_pub_out = header.n_pub_out as usize;
    let n_pub_in = header.n_pub_in as usize;
    let n_prv_in = header.n_prv_in as usize;

    let istart = 2 + n_pub_out; // inclusive, 1-based
    let iend = 1 + n_pub_out + n_pub_in + n_prv_in; // inclusive, 1-based
    let mut input_list_ecne = vec![1usize];
    for i in istart..=iend {
        input_list_ecne.push(i);
    }
    let inputs: Vec<usize> = input_list_ecne.iter().map(|&i| i - 1).collect(); // 0-based

    let ostart = 2usize; // inclusive, 1-based
    let oend = 1 + n_pub_out; // inclusive, 1-based
    let output_list_ecne: Vec<usize> = (ostart..=oend).collect();
    let outputs: Vec<usize> = output_list_ecne.iter().map(|&i| i - 1).collect(); // 0-based

    Ok(R1csFile {
        magic,
        version,
        n_sections,
        header,
        constraints,
        w2l,
        inputs,
        outputs,
    })
}

/// Read an R1CS binary file from a file path.
pub fn read_r1cs_file(path: &std::path::Path) -> Result<R1csFile, R1csParseError> {
    let data = std::fs::read(path)?;
    read_r1cs(&data)
}

// ---- Internal helpers ----

struct Section {
    section_type: u32,
    data: Vec<u8>,
}

fn parse_sections(raw: &[u8]) -> Result<Vec<Section>, R1csParseError> {
    let mut sections = Vec::new();
    let mut pos = 0;
    while pos < raw.len() {
        if pos + 12 > raw.len() {
            break;
        }
        let mut cur = Cursor::new(&raw[pos..]);
        let section_type = cur.read_u32::<LittleEndian>()?;
        let section_size = cur.read_u64::<LittleEndian>()? as usize;
        let data_start = pos + 12;
        // `section_size` is read straight from the (untrusted) file; guard the
        // add so an adversarial size near usize::MAX can't wrap past the
        // bounds check below into an out-of-range slice (panic / DoS).
        let data_end = match data_start.checked_add(section_size) {
            Some(e) => e,
            None => break,
        };
        if data_end > raw.len() {
            break;
        }
        sections.push(Section {
            section_type,
            data: raw[data_start..data_end].to_vec(),
        });
        pos = data_end;
    }
    Ok(sections)
}

fn parse_header_section(data: &[u8]) -> Result<HeaderSection, R1csParseError> {
    let mut cur = Cursor::new(data);
    let field_size = cur.read_u32::<LittleEndian>()?;
    // `field_size` is the field-element byte width (iden3 format); it is
    // NOT required to be a multiple of 8 — a small prime (e.g. GF(7),
    // 1 byte) is a legitimate width. The real constraints are checked
    // below: the width must fit the header block, and the decoded prime
    // must be > 1 (which also rejects `field_size == 0`).
    // Reject any prime byte width larger than the header data block
    // we just received. A header claiming a 4 GiB prime is malformed;
    // refuse rather than try to allocate.
    let fs = field_size as usize;
    if fs > data.len() {
        return Err(R1csParseError::HeaderImplausible {
            field: "field_size",
            claimed: field_size as u64,
            bound: data.len() as u64,
        });
    }

    let mut prime_bytes = vec![0u8; fs];
    cur.read_exact(&mut prime_bytes)?;
    let prime_number = BigUint::from_bytes_le(&prime_bytes);
    // A field modulus must be > 1 (`field_size = 0`, or all-zero/one prime
    // bytes, decodes to 0/1). Reject here so a malformed file surfaces as a
    // parse error rather than reaching `PrimeField::new`'s `assert!(prime > 1)`
    // during lowering and aborting the process.
    if prime_number <= BigUint::from(1u32) {
        return Err(R1csParseError::InvalidPrime(prime_number));
    }

    let n_wires = cur.read_u32::<LittleEndian>()?;
    let n_pub_out = cur.read_u32::<LittleEndian>()?;
    let n_pub_in = cur.read_u32::<LittleEndian>()?;
    let n_prv_in = cur.read_u32::<LittleEndian>()?;
    let n_labels = cur.read_u64::<LittleEndian>()?;
    let m_constraints = cur.read_u32::<LittleEndian>()?;

    Ok(HeaderSection {
        field_size,
        prime_number,
        n_wires,
        n_pub_out,
        n_pub_in,
        n_prv_in,
        n_labels,
        m_constraints,
    })
}

fn parse_constraint_section(
    data: &[u8],
    field_size: u32,
    m_constraints: u32,
    prime: &BigUint,
) -> Result<ConstraintSection, R1csParseError> {
    let fs = field_size as usize;
    let mut constraints = Vec::with_capacity(capped_capacity(m_constraints as u64, data.len()));
    let mut pos = 0;

    while pos < data.len() {
        let (new_pos, constraint) = parse_single_constraint(&data[pos..], fs, prime)?;
        constraints.push(constraint);
        pos += new_pos;
    }

    if constraints.len() as u32 != m_constraints {
        return Err(R1csParseError::ConstraintCountMismatch {
            expected: m_constraints,
            actual: constraints.len() as u32,
        });
    }

    Ok(ConstraintSection { constraints })
}

fn parse_single_constraint(
    data: &[u8],
    fs: usize,
    p: &BigUint,
) -> Result<(usize, Constraint), R1csParseError> {
    let mut pos = 0;

    let (a, a_end) = parse_constraint_block(&data[pos..], fs, p)?;
    pos += a_end;

    let (b, b_end) = parse_constraint_block(&data[pos..], fs, p)?;
    pos += b_end;

    let (c, c_end) = parse_constraint_block(&data[pos..], fs, p)?;
    pos += c_end;

    Ok((pos, Constraint { a, b, c }))
}

fn parse_constraint_block(
    data: &[u8],
    fs: usize,
    p: &BigUint,
) -> Result<(ConstraintBlock, usize), R1csParseError> {
    let mut cur = Cursor::new(data);
    let nnz = cur.read_u32::<LittleEndian>()?;
    let mut pos = 4usize;

    let mut wire_ids = Vec::with_capacity(capped_capacity(nnz as u64, data.len()));
    let mut factors = Vec::with_capacity(capped_capacity(nnz as u64, data.len()));

    for _ in 0..nnz {
        let wid_bytes = slice(data, pos, pos + 4, "constraint block wire_id")?;
        let mut wid_buf = wid_bytes;
        let wid = wid_buf.read_u32::<LittleEndian>()?;
        pos += 4;

        let factor_bytes = slice(data, pos, pos + fs, "constraint block factor")?;
        let factor = BigUint::from_bytes_le(factor_bytes) % p;
        pos += fs;

        wire_ids.push(wid);
        factors.push(factor);
    }

    Ok((ConstraintBlock { nnz, wire_ids, factors }, pos))
}

#[allow(clippy::manual_is_multiple_of)]
fn parse_w2l_section(data: &[u8]) -> Result<W2lSection, R1csParseError> {
    if data.len() % 8 != 0 {
        return Err(R1csParseError::BadW2lSize(data.len()));
    }
    let n = data.len() / 8;
    // `n` derives from `data.len()`, so the upper bound is the
    // section's own size; no header-controlled multiplier here.
    let mut labels = Vec::with_capacity(n.min(ABSOLUTE_COUNT_CAP));
    let mut cur = Cursor::new(data);
    for _ in 0..n {
        labels.push(cur.read_u64::<LittleEndian>()?);
    }
    Ok(W2lSection { labels })
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
