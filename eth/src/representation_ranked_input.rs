//! Strict, reproducible byte boundary for source-bound ranked contraction.
//!
//! Wire format v1 (little endian, no padding):
//! "RKC1" | n:u64 | classes:u64 | edges:u64 |
//! edge[edges]:(u64,u64) | labels[n]:u64 | roots[classes]:u64 |
//! parent_edge[n]:u64 (u64::MAX means absent) | rank[n]:u64 |
//! weights[n]:(i128,i128).
//!
//! The full length is 28 + 16*edges + 56*n + 8*classes bytes, with every
//! addition/multiplication checked *before allocation*. Trailing bytes,
//! truncated fields, malformed endpoints, invalid parents and oversized
//! indices are refused. No fallback to a guessed class/edge is permitted.
//!
//! Canonicality is byte-for-byte: encode(decode(bytes)) == bytes on success.
//! This is Rust source code; compiler-level equivalence and Lean's independent
//! raw-byte decoder still require proof, not merely tests.
use crate::Error;
use crate::representation_ranked_certificate::{
    RankedComponentCertificate, VerifiedRankedCertificate,
    verify_ranked_component_certificate,
};

const MAGIC: &[u8; 4] = b"RKC1";
const ABSENT_PARENT: u64 = u64::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankedContractionInput {
    pub weights: Vec<[i128; 2]>,
    pub source_edges: Vec<(usize, usize)>,
    pub certificate: RankedComponentCertificate,
}

impl RankedContractionInput {
    /// Verify the exact parsed source data before treating it as authority.
    pub fn verify(&self) -> Result<VerifiedRankedCertificate, Error> {
        verify_ranked_component_certificate(
            self.weights.len(),
            &self.source_edges,
            &self.certificate,
        )
    }
}

fn bad(reason: &str) -> Error {
    Error::Invalid(format!("ranked input v1: {reason}"))
}

fn checked_wire_len(n: usize, classes: usize, edges: usize) -> Result<usize, Error> {
    let edges_len = edges.checked_mul(16).ok_or(Error::Overflow)?;
    let vertices_len = n.checked_mul(56).ok_or(Error::Overflow)?;
    let classes_len = classes.checked_mul(8).ok_or(Error::Overflow)?;
    28usize
        .checked_add(edges_len)
        .and_then(|x| x.checked_add(vertices_len))
        .and_then(|x| x.checked_add(classes_len))
        .ok_or(Error::Overflow)
}

fn from_u64(value: u64) -> Result<usize, Error> {
    usize::try_from(value).map_err(|_| bad("integer cannot be represented as usize"))
}

fn to_u64(value: usize) -> Result<u64, Error> {
    u64::try_from(value).map_err(|_| bad("integer cannot be represented as u64"))
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let end = self.offset.checked_add(N).ok_or(Error::Overflow)?;
        let slice = self
            .bytes
            .get(self.offset..end)
            .ok_or_else(|| bad("truncated field"))?;
        self.offset = end;
        slice.try_into().map_err(|_| bad("field width mismatch"))
    }

    fn word(&mut self) -> Result<usize, Error> {
        from_u64(u64::from_le_bytes(self.take()?))
    }

    fn signed_word(&mut self) -> Result<i128, Error> {
        Ok(i128::from_le_bytes(self.take()?))
    }
}

fn fallible_vec<T>(capacity: usize) -> Result<Vec<T>, Error> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(capacity)
        .map_err(|_| Error::Capacity("ranked input allocation refused".into()))?;
    Ok(output)
}

/// Parse the exact bytes, including source edges and all finite-index checks.
/// No partially decoded input escapes on failure.
pub fn decode_ranked_input(bytes: &[u8]) -> Result<RankedContractionInput, Error> {
    let mut cursor = Cursor::new(bytes);
    if &cursor.take::<4>()? != MAGIC {
        return Err(bad("unexpected version or magic"));
    }
    let n = cursor.word()?;
    let classes = cursor.word()?;
    let edges = cursor.word()?;
    if classes > n {
        return Err(bad("more classes than vertices"));
    }
    if checked_wire_len(n, classes, edges)? != bytes.len() {
        return Err(bad("declared length disagrees with input bytes"));
    }

    let mut source_edges = fallible_vec(edges)?;
    for _ in 0..edges {
        source_edges.push((cursor.word()?, cursor.word()?));
    }
    let mut labels = fallible_vec(n)?;
    for _ in 0..n {
        labels.push(cursor.word()?);
    }
    let mut roots = fallible_vec(classes)?;
    for _ in 0..classes {
        roots.push(cursor.word()?);
    }
    let mut parent_edge_indices = fallible_vec(n)?;
    for _ in 0..n {
        let raw = u64::from_le_bytes(cursor.take()?);
        parent_edge_indices.push(if raw == ABSENT_PARENT {
            None
        } else {
            Some(from_u64(raw)?)
        });
    }
    let mut rank = fallible_vec(n)?;
    for _ in 0..n {
        rank.push(cursor.word()?);
    }
    let mut weights = fallible_vec(n)?;
    for _ in 0..n {
        weights.push([cursor.signed_word()?, cursor.signed_word()?]);
    }
    if cursor.offset != bytes.len() {
        return Err(bad("trailing data"));
    }

    let result = RankedContractionInput {
        weights,
        source_edges,
        certificate: RankedComponentCertificate {
            labels,
            roots,
            parent_edge_indices,
            rank,
        },
    };
    result.verify()?;
    Ok(result)
}

/// Encode a *verified* source input. The output's length and indices are
/// representable in the version-1 format; no truncating casts are allowed.
pub fn encode_ranked_input(input: &RankedContractionInput) -> Result<Vec<u8>, Error> {
    input.verify()?;
    let n = input.weights.len();
    let classes = input.certificate.roots.len();
    let edges = input.source_edges.len();
    let len = checked_wire_len(n, classes, edges)?;
    let mut output = fallible_vec(len)?;
    output.extend_from_slice(MAGIC);
    output.extend_from_slice(&to_u64(n)?.to_le_bytes());
    output.extend_from_slice(&to_u64(classes)?.to_le_bytes());
    output.extend_from_slice(&to_u64(edges)?.to_le_bytes());
    for &(a, b) in &input.source_edges {
        output.extend_from_slice(&to_u64(a)?.to_le_bytes());
        output.extend_from_slice(&to_u64(b)?.to_le_bytes());
    }
    for &index in &input.certificate.labels {
        output.extend_from_slice(&to_u64(index)?.to_le_bytes());
    }
    for &root in &input.certificate.roots {
        output.extend_from_slice(&to_u64(root)?.to_le_bytes());
    }
    for index in &input.certificate.parent_edge_indices {
        let raw = match index {
            None => ABSENT_PARENT,
            Some(index) => {
                let raw = to_u64(*index)?;
                if raw == ABSENT_PARENT {
                    return Err(bad("u64::MAX is reserved for absent parent"));
                }
                raw
            }
        };
        output.extend_from_slice(&raw.to_le_bytes());
    }
    for &rank in &input.certificate.rank {
        output.extend_from_slice(&to_u64(rank)?.to_le_bytes());
    }
    for &pair in &input.weights {
        output.extend_from_slice(&pair[0].to_le_bytes());
        output.extend_from_slice(&pair[1].to_le_bytes());
    }
    debug_assert_eq!(output.len(), len);
    Ok(output)
}
