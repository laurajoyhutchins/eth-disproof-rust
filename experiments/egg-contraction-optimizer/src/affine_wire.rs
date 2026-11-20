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
    fn exhaustive_small_raw_step_decisions_match_external_predicate() {
        // Do not ask the decoder to explain itself: construct the expected
        // acceptance predicate independently from tag/index arithmetic.
        for rows in 0..=4usize {
            for tag in [0_u8, 1, 2, 255] {
                for first in [0_u64, 1, 2, 3, 4, u64::MAX] {
                    for second in [0_u64, 1, 2, 3, 4, u64::MAX] {
                        let raw = RawCertificate {
                            version: WIRE_VERSION,
                            steps: vec![RawStep { tag, first, second }],
                            pivot_columns: vec![],
                        };
                        let expected = (tag == 0 || tag == 1)
                            && first < rows as u64
                            && second < rows as u64
                            && first != second;
                        assert_eq!(raw.decode(rows, 0, 1).is_ok(), expected,
                            "rows={rows}, tag={tag}, first={first}, second={second}");
                    }
                }
            }
        }
    }

    #[test]
    fn exhaustive_short_pivot_lists_match_external_strict_ordering() {
        let values = [0_u64, 1, 2, 3, u64::MAX];
        for rows in 0..=4usize {
            for internal in 0..=4usize {
                let mut lists = vec![vec![]];
                lists.extend(values.iter().copied().map(|x| vec![x]));
                for &x in &values {
                    for &y in &values {
                        lists.push(vec![x, y]);
                        for &z in &values { lists.push(vec![x, y, z]); }
                    }
                }
                for pivots in lists {
                    let raw = RawCertificate {
                        version: WIRE_VERSION,
                        steps: vec![],
                        pivot_columns: pivots.clone(),
                    };
                    let expected = pivots.len() <= rows
                        && pivots.len() <= internal
                        && pivots.iter().all(|&p| p < internal as u64)
                        && pivots.windows(2).all(|pair| pair[0] < pair[1]);
                    assert_eq!(raw.decode(rows, internal, 0).is_ok(), expected,
                        "rows={rows}, internal={internal}, pivots={pivots:?}");
                }
            }
        }
    }

    /// Independent arithmetic predicate for all raw admission branches.
    /// Unlike decode(), it never converts raw indices into usize.
    fn reference_acceptance(
        certificate: &RawCertificate,
        rows: usize,
        internal: usize,
        max_steps: usize,
        address_bits: u32,
    ) -> bool {
        let addressable = (1u128 << address_bits) - 1;
        if certificate.version != 1 ||
            certificate.steps.len() > max_steps ||
            certificate.pivot_columns.len() > rows ||
            certificate.pivot_columns.len() > internal
        {
            return false;
        }
        let pivots_ok = certificate.pivot_columns.iter().all(|&value| {
            (value as u128) <= addressable && (value as u128) < internal as u128
        }) && certificate.pivot_columns.windows(2)
            .all(|pair| pair[0] < pair[1]);
        let steps_ok = certificate.steps.iter().all(|step| {
            (step.tag == 0 || step.tag == 1) &&
            (step.first as u128) <= addressable &&
            (step.second as u128) <= addressable &&
            (step.first as u128) < rows as u128 &&
            (step.second as u128) < rows as u128 &&
            step.first != step.second
        });
        pivots_ok && steps_ok
    }

    #[test]
    fn full_width_raw_admission_matches_independent_arithmetic_contract() {
        // Exercises complete 8/64-bit values without indexing a huge matrix.
        // This is implementation evidence; the corresponding Lean theorem
        // quantifies over all raw values and arbitrary transcript lengths.
        let mut state = 0x9E3779B97F4A7C15u64;
        let mut random = || {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            state.wrapping_mul(2685821657736338717)
        };
        for case in 0..4096usize {
            let rows = match case % 7 {
                0 => 0,
                1 => 1,
                2 => 4,
                3 => 64,
                4 => 1usize << 16,
                5 => usize::MAX,
                _ => 1usize << 20,
            };
            let internal = match case % 5 {
                0 => 0,
                1 => 3,
                2 => 64,
                3 => usize::MAX,
                _ => 1usize << 20,
            };
            let max_steps = case % 4;
            let raw = RawCertificate {
                version: if case % 13 == 0 { 1 } else { random() as u8 },
                steps: (0..case % 4).map(|i| {
                    let first = if i == 0 && case % 3 == 0 {
                        (case % 5) as u64
                    } else { random() };
                    RawStep {
                        tag: if case % 7 == 0 { (case % 3) as u8 }
                            else { random() as u8 },
                        first,
                        second: if case % 9 == 0 { first } else { random() },
                    }
                }).collect(),
                pivot_columns: (0..case % 5).map(|_| random()).collect(),
            };
            let expected = reference_acceptance(
                &raw, rows, internal, max_steps, usize::BITS,
            );
            assert_eq!(raw.decode(rows, internal, max_steps).is_ok(), expected,
                "case={case} rows={rows} internal={internal}");
        }

        // Target-specific width matters. On a 32-bit architecture a
        // 2^40 raw index must refuse before converting to usize, whereas
        // a 64-bit architecture can represent it when rows permit.
        let huge = RawCertificate {
            version: 1,
            steps: vec![RawStep {
                tag: 1, first: 1u64 << 40, second: 2,
            }],
            pivot_columns: vec![],
        };
        assert!(!reference_acceptance(
            &huge, usize::MAX, 0, 1, 32,
        ));
        assert_eq!(
            huge.decode(usize::MAX, 0, 1).is_ok(),
            reference_acceptance(&huge, usize::MAX, 0, 1, usize::BITS),
        );
    }

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
