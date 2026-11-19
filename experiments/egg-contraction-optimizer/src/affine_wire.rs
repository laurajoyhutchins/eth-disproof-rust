//! Strict raw-value boundary for affine row-operation receipts.
//!
//! This models untrusted native *values* (u8 tags and u64 indices), not a
//! byte serialization format. Conversion refuses malformed tags, aliases,
//! overlarge indices, invalid or unsorted pivot columns, unsupported
//! versions and budget overruns before handing the result to the
//! independent dense-Boolean checker.

use crate::affine::{AffineInterface, AffineRegion};
use crate::affine_cert::{
    EliminationCertificate, RowOperation, VerificationLimits, VerificationReceipt,
};

pub const WIRE_VERSION: u8 = 1;
const TAG_SWAP: u8 = 0;
const TAG_XOR: u8 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RawStep {
    pub tag: u8,
    pub first: u64,
    pub second: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RawCertificate {
    pub version: u8,
    pub steps: Vec<RawStep>,
    pub pivot_columns: Vec<u64>,
}

impl RawCertificate {
    /// Encode typed, already allocated receipt values. This is NOT a byte
    /// codec. On architectures where usize exceeds u64, fail explicitly.
    pub fn from_typed(typed: &EliminationCertificate) -> Result<Self, String> {
        let mut steps = Vec::with_capacity(typed.steps.len());
        for step in &typed.steps {
            let (tag, first, second) = match *step {
                RowOperation::Swap { first, second } => (TAG_SWAP, first, second),
                RowOperation::Xor { target, source } => (TAG_XOR, target, source),
            };
            steps.push(RawStep {
                tag,
                first: u64::try_from(first).map_err(|_| "row index does not fit u64")?,
                second: u64::try_from(second).map_err(|_| "row index does not fit u64")?,
            });
        }
        Ok(Self {
            version: WIRE_VERSION,
            steps,
            pivot_columns: typed.pivot_columns.iter()
                .map(|&col| u64::try_from(col).map_err(|_| "pivot column does not fit u64".into()))
                .collect::<Result<Vec<_>, String>>()?,
        })
    }

    /// Decode into the existing typed checker language only after verifying
    /// the exact raw-contract conditions. Indices are validated as u64
    /// before conversion to platform-dependent usize.
    pub fn decode(
        &self,
        row_count: usize,
        internal_columns: usize,
        max_steps: usize,
    ) -> Result<EliminationCertificate, String> {
        if self.version != WIRE_VERSION {
            return Err("unknown affine certificate version".into());
        }
        if self.steps.len() > max_steps {
            return Err("checker transcript budget exceeded".into());
        }
        if self.pivot_columns.len() > row_count ||
            self.pivot_columns.len() > internal_columns
        {
            return Err("pivot rank exceeds dimensions".into());
        }
        let mut pivot_columns = Vec::with_capacity(self.pivot_columns.len());
        let mut previous = None;
        for &raw in &self.pivot_columns {
            let column = usize::try_from(raw)
                .map_err(|_| "pivot column exceeds addressable usize")?;
            if column >= internal_columns ||
                previous.is_some_and(|old| column <= old)
            {
                return Err("invalid or unsorted internal pivot columns".into());
            }
            previous = Some(column);
            pivot_columns.push(column);
        }

        let mut steps = Vec::with_capacity(self.steps.len());
        for raw in &self.steps {
            if raw.tag != TAG_SWAP && raw.tag != TAG_XOR {
                return Err("unknown row-operation tag".into());
            }
            let first = usize::try_from(raw.first)
                .map_err(|_| "row index exceeds addressable usize")?;
            let second = usize::try_from(raw.second)
                .map_err(|_| "row index exceeds addressable usize")?;
            if first >= row_count || second >= row_count || first == second {
                return Err("invalid or aliased raw row indices".into());
            }
            steps.push(if raw.tag == TAG_SWAP {
                RowOperation::Swap { first, second }
            } else {
                RowOperation::Xor { target: first, source: second }
            });
        }
        Ok(EliminationCertificate { steps, pivot_columns })
    }

    /// The raw admission gate is followed by the *independent* replay
    /// checker, not by the producer that created the proposed result.
    pub fn verify(
        &self,
        source: &AffineRegion,
        claimed: &AffineInterface,
        limits: VerificationLimits,
    ) -> Result<VerificationReceipt, String> {
        let receipt = self.decode(
            source.equations.len(),
            source.internal.len(),
            limits.max_steps,
        )?;
        receipt.verify_with_limits(source, claimed, limits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affine::two_equations;

    #[test]
    fn native_to_raw_to_independent_replay_roundtrip() {
        let source = two_equations("b", "c");
        let (interface, original) = source.eliminate_with_certificate().unwrap();
        let raw = RawCertificate::from_typed(&original).unwrap();
        let typed = raw.decode(source.equations.len(), source.internal.len(),
                               VerificationLimits::default().max_steps).unwrap();
        assert_eq!(original, typed);
        let accepted = raw.verify(&source, &interface, VerificationLimits::default()).unwrap();
        assert_eq!(accepted.rank, 1);
        assert_eq!(accepted.free_internal, 1);
    }

    #[test]
    fn invalid_tags_bounds_aliases_versions_are_rejected() {
        let source = two_equations("b", "c");
        let (interface, original) = source.eliminate_with_certificate().unwrap();
        let raw = RawCertificate::from_typed(&original).unwrap();
        assert!(!raw.steps.is_empty());
        let mut bad = raw.clone();
        bad.version = 255;
        assert!(bad.verify(&source, &interface, VerificationLimits::default()).is_err());
        for tag in [2u8, 3, 255] {
            let mut bad = raw.clone();
            bad.steps[0].tag = tag;
            assert!(bad.verify(&source, &interface, VerificationLimits::default()).is_err());
        }
        for (first, second) in [
            (u64::MAX, 0),
            (0, u64::MAX),
            (0, 0),
            (source.equations.len() as u64, 0),
        ] {
            let mut bad = raw.clone();
            bad.steps[0].first = first;
            bad.steps[0].second = second;
            assert!(bad.verify(&source, &interface, VerificationLimits::default()).is_err());
        }
    }

    #[test]
    fn invalid_pivot_lists_and_raw_budget_refuse() {
        let source = two_equations("b", "c");
        let (interface, original) = source.eliminate_with_certificate().unwrap();
        let raw = RawCertificate::from_typed(&original).unwrap();
        for pivots in [
            vec![u64::MAX],
            vec![source.internal.len() as u64],
            vec![0, 0],
            vec![1, 0],
            vec![0, 1, 2],
        ] {
            let mut bad = raw.clone();
            bad.pivot_columns = pivots;
            assert!(bad.verify(&source, &interface, VerificationLimits::default()).is_err());
        }
        assert!(raw.verify(&source, &interface, VerificationLimits {
            max_cells: usize::MAX,
            max_steps: 0,
        }).unwrap_err().contains("budget exceeded"));
        assert!(raw.verify(&source, &interface, VerificationLimits {
            max_cells: 0,
            max_steps: usize::MAX,
        }).unwrap_err().contains("budget exceeded"));
    }

    #[test]
    fn raw_empty_certificate_validates_zero_dimension() {
        let source = AffineRegion {
            internal: vec![], boundary: vec![], equations: vec![],
        };
        let (interface, typed) = source.eliminate_with_certificate().unwrap();
        let raw = RawCertificate::from_typed(&typed).unwrap();
        let receipt = raw.verify(&source, &interface, VerificationLimits {
            max_cells: 0,
            max_steps: 0,
        }).unwrap();
        assert_eq!(receipt.rank, 0);
        assert_eq!(receipt.operations_checked, 0);
        assert_eq!(receipt.residual_rows_checked, 0);
    }
}
