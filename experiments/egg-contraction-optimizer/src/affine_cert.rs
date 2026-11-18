//! Independent dense-Boolean replay of a packed-GF(2) elimination receipt.
//!
//! No calls to the producer's packed elimination routine. Every emitted step
//! is an invertible row operation. The terminal matrix must have exactly
//! one isolated pivot per recorded internal column and no internal bits in residual rows.
//! Those conditions imply the claimed number of free internal bits.

use crate::affine::{AffineInterface, AffineRegion};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RowOperation {
    Swap { first: usize, second: usize },
    Xor { target: usize, source: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EliminationCertificate {
    pub steps: Vec<RowOperation>,
    pub pivot_columns: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerificationReceipt {
    pub rank: usize,
    pub free_internal: usize,
    pub operations_checked: usize,
    pub residual_rows_checked: usize,
}

impl EliminationCertificate {
    /// Reconstruct the source system using a different data structure from
    /// the packed-bit producer. Reject any ill-formed or incomplete transcript.
    pub fn verify(
        &self,
        source: &AffineRegion,
        claimed: &AffineInterface,
    ) -> Result<VerificationReceipt, String> {
        let k = source.internal.len();
        let b = source.boundary.len();
        let width = k.checked_add(b)
            .and_then(|x| x.checked_add(1))
            .ok_or("checker matrix width overflow")?;
        let size = source.equations.len().checked_mul(width)
            .ok_or("checker matrix storage overflow")?;
        if size > 8_000_000 {
            return Err("checker matrix storage budget exceeded".into());
        }
        if self.steps.len() > 8_000_000 {
            return Err("checker transcript budget exceeded".into());
        }
        if claimed.boundary != source.boundary {
            return Err("boundary names/order were changed".into());
        }
        let mut locations = BTreeMap::new();
        for (column, name) in source.internal.iter().chain(&source.boundary).enumerate() {
            if name.is_empty() ||
                locations.insert(name.as_str(), column).is_some() {
                return Err("duplicate or empty source variable".into());
            }
        }
        let mut rows = vec![vec![false; width]; source.equations.len()];
        for (i, equation) in source.equations.iter().enumerate() {
            for variable in &equation.variables {
                let &col = locations.get(variable.as_str())
                    .ok_or("undeclared source equation variable")?;
                rows[i][col] ^= true;
            }
            rows[i][width - 1] = equation.rhs;
        }
        for op in &self.steps {
            match *op {
                RowOperation::Swap { first, second } => {
                    if first >= rows.len() || second >= rows.len() || first == second {
                        return Err("invalid row swap in certificate".into());
                    }
                    rows.swap(first, second);
                }
                RowOperation::Xor { target, source } => {
                    if target >= rows.len() || source >= rows.len() || target == source {
                        return Err("invalid row XOR in certificate".into());
                    }
                    // Deliberately dense, independent of the producer's u64
                    // packed-mask XOR operation.
                    let read = rows[source].clone();
                    for (bit, other) in rows[target].iter_mut().zip(read) {
                        *bit ^= other;
                    }
                }
            }
        }
        let r = self.pivot_columns.len();
        if r > k || r > rows.len() {
            return Err("pivot rank exceeds dimensions".into());
        }
        if claimed.rank != r || claimed.free_internal != k - r {
            return Err("claimed rank or free dimension disagrees with certificate".into());
        }
        let mut pivots = BTreeSet::new();
        let mut previous = None;
        for (row_index, &column) in self.pivot_columns.iter().enumerate() {
            if column >= k || previous.is_some_and(|p| column <= p) ||
                !pivots.insert(column) {
                return Err("invalid or unsorted internal pivot columns".into());
            }
            previous = Some(column);
            for (j, row) in rows.iter().enumerate() {
                if row[column] != (j == row_index) {
                    return Err("pivot column is not isolated in terminal matrix".into());
                }
            }
        }
        // Free internal columns MAY occur in pivot rows: those rows solve
        // each pivot variable as a function of free bits and boundary.
        // They must be absent only from residual (nonpivot) rows.
        for column in 0..k {
            if !pivots.contains(&column) &&
                rows.iter().skip(r).any(|row| row[column]) {
                return Err("free internal column survives in residual rows".into());
            }
        }
        if claimed.residual.len() != rows.len() - r {
            return Err("claimed residual row count disagrees with certificate".into());
        }
        let mut xors = 0usize;
        for op in &self.steps {
            if matches!(op, RowOperation::Xor { .. }) {
                xors = xors.checked_add(1).ok_or("operation counter overflow")?;
            }
        }
        if xors != claimed.elimination_xors {
            return Err("claimed elimination XOR count disagrees with transcript".into());
        }
        for (source_row, claimed_row) in rows.iter().skip(r).zip(&claimed.residual) {
            let boundary_bits = (0..b)
                .filter(|j| source_row[k + j])
                .collect::<Vec<_>>();
            if claimed_row.boundary_indices != boundary_bits ||
                claimed_row.rhs != source_row[width - 1] {
                return Err("residual boundary equation differs from replay".into());
            }
        }
        Ok(VerificationReceipt {
            rank: r,
            free_internal: k - r,
            operations_checked: self.steps.len(),
            residual_rows_checked: rows.len() - r,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affine::{AffineRegion, Equation};

    fn example() -> AffineRegion {
        crate::affine::two_equations("b", "c")
    }

    #[test]
    fn replays_a_genuine_elimination_transcript() {
        let region = example();
        let (interface, receipt) = region.eliminate_with_certificate().unwrap();
        let verified = receipt.verify(&region, &interface).unwrap();
        assert_eq!(verified.rank, interface.rank);
        assert_eq!(verified.free_internal, interface.free_internal);
        assert_eq!(verified.residual_rows_checked, interface.residual.len());
    }

    #[test]
    fn altered_receipts_and_results_fail_closed() {
        let region = example();
        let (interface, certificate) = region.eliminate_with_certificate().unwrap();

        let mut invalid = certificate.clone();
        invalid.pivot_columns.clear();
        assert!(invalid.verify(&region, &interface).is_err());

        let mut invalid = certificate.clone();
        invalid.steps.clear();
        assert!(invalid.verify(&region, &interface).is_err());

        let mut invalid = certificate.clone();
        invalid.steps.push(RowOperation::Xor { target: 0, source: 0 });
        assert!(invalid.verify(&region, &interface).is_err());

        let mut invalid = interface.clone();
        invalid.free_internal += 1;
        assert!(certificate.verify(&region, &invalid).is_err());

        let mut invalid = interface.clone();
        invalid.residual[0].rhs = !invalid.residual[0].rhs;
        assert!(certificate.verify(&region, &invalid).is_err());

        let mut invalid = interface.clone();
        invalid.boundary.reverse();
        assert!(certificate.verify(&region, &invalid).is_err());
    }

    #[test]
    fn mutated_source_is_detected() {
        let region = example();
        let (interface, certificate) = region.eliminate_with_certificate().unwrap();
        let mut other = region.clone();
        other.equations[1].rhs = !other.equations[1].rhs;
        assert!(certificate.verify(&other, &interface).is_err());
    }

    #[test]
    fn seeded_matrices_exactly_match_direct_enumeration() {
        // Independent Boolean oracle and an independent dense Boolean
        // transcript replay, over 200 deterministic small GF(2) systems.
        fn draw(state: &mut u64) -> u64 {
            *state ^= *state << 13;
            *state ^= *state >> 7;
            *state ^= *state << 17;
            *state
        }
        for seed in 1..=200u64 {
            let mut s = seed;
            let k = (draw(&mut s) % 5) as usize;
            let b = (draw(&mut s) % 4) as usize;
            let m = (draw(&mut s) % 8) as usize;
            let internal = (0..k).map(|i| format!("u{i}")).collect::<Vec<_>>();
            let boundary = (0..b).map(|i| format!("b{i}")).collect::<Vec<_>>();
            let names = internal.iter().chain(&boundary).cloned().collect::<Vec<_>>();
            let mut equations = Vec::new();
            for _ in 0..m {
                let mut variables = Vec::new();
                for name in &names {
                    if draw(&mut s) & 1 != 0 {
                        variables.push(name.clone());
                    }
                    // Repeated variables should cancel.
                    if draw(&mut s) % 13 == 0 {
                        variables.push(name.clone());
                        variables.push(name.clone());
                    }
                }
                equations.push(Equation {
                    variables,
                    rhs: draw(&mut s) & 1 != 0,
                });
            }
            let region = AffineRegion { internal, boundary, equations };
            let (interface, certificate) = region.eliminate_with_certificate().unwrap();
            certificate.verify(&region, &interface).unwrap();
            for mask in 0..(1usize << b) {
                let values = region.boundary.iter().enumerate().map(|(j, name)| {
                    (name.clone(), mask & (1 << j) != 0)
                }).collect::<BTreeMap<_, _>>();
                assert_eq!(
                    interface.evaluate(&values).unwrap(),
                    region.direct_count(&values, 16).unwrap(),
                    "seed={seed}, mask={mask}"
                );
            }
        }
    }

    #[test]
    fn witness_is_compact_even_at_large_free_dimension() {
        let internal = (0..128).map(|i| format!("u{i}")).collect::<Vec<_>>();
        let region = AffineRegion {
            internal: internal.clone(), boundary: vec!["b".into()],
            equations: vec![Equation {
                variables: internal.into_iter().chain(["b".to_owned()]).collect(),
                rhs: true,
            }],
        };
        let (iface, certificate) = region.eliminate_with_certificate().unwrap();
        assert_eq!(iface.free_internal, 127);
        assert_eq!(certificate.verify(&region, &iface).unwrap().rank, 1);
        assert!(certificate.steps.len() < 10);
    }
    #[test]
    fn packed_words_cross_63_64_127_128_and_preserve_rhs() {
        // The source rows cross several 64-bit boundaries. The second
        // equation shares the internal parity of the first with opposite
        // RHS, forcing a nontrivial residual boundary equation.
        let internal = (0..130).map(|i| format!("u{i}")).collect::<Vec<_>>();
        let region = AffineRegion {
            internal,
            boundary: vec!["b0".into(), "b1".into(), "b2".into()],
            equations: vec![
                Equation { variables: vec!["u63".into(), "u64".into(), "b0".into()], rhs: false },
                Equation { variables: vec!["u63".into(), "u64".into(), "b1".into()], rhs: true },
                Equation { variables: vec!["u127".into(), "u128".into(), "b2".into()], rhs: false },
                Equation { variables: vec!["u129".into(), "u0".into()], rhs: true },
            ],
        };
        let (interface, certificate) = region.eliminate_with_certificate().unwrap();
        let receipt = certificate.verify(&region, &interface).unwrap();
        assert_eq!(receipt.rank, 3);
        assert_eq!(receipt.free_internal, 127);
        assert!(certificate.steps.iter().any(|op| matches!(op, RowOperation::Swap { .. })));
        assert!(certificate.steps.iter().any(|op| matches!(op, RowOperation::Xor { .. })));
        for mask in 0..8 {
            let boundary = (0..3).map(|i| {
                (format!("b{i}"), mask & (1 << i) != 0)
            }).collect::<BTreeMap<_, _>>();
            let expected = if boundary["b0"] ^ boundary["b1"] {
                num_bigint::BigUint::from(1u8) << 127
            } else {
                num_bigint::BigUint::from(0u8)
            };
            assert_eq!(interface.evaluate(&boundary).unwrap(), expected, "mask={mask}");
        }
    }

    #[test]
    fn zero_dimension_empty_and_inconsistent_equations_are_replayable() {
        let empty = AffineRegion {
            internal: vec![], boundary: vec![], equations: vec![],
        };
        let (interface, proof) = empty.eliminate_with_certificate().unwrap();
        proof.verify(&empty, &interface).unwrap();
        assert_eq!(interface.evaluate(&BTreeMap::new()).unwrap(),
            num_bigint::BigUint::from(1u8));
        let impossible = AffineRegion {
            equations: vec![Equation { variables: vec![], rhs: true }],
            ..empty
        };
        let (interface, proof) = impossible.eliminate_with_certificate().unwrap();
        proof.verify(&impossible, &interface).unwrap();
        assert_eq!(interface.evaluate(&BTreeMap::new()).unwrap(),
            num_bigint::BigUint::from(0u8));
    }

    #[test]
    fn raw_invalid_indices_and_self_swaps_are_refused() {
        let region = example();
        let (result, valid) = region.eliminate_with_certificate().unwrap();
        for step in [
            RowOperation::Swap { first: 0, second: 0 },
            RowOperation::Swap { first: 0, second: 999 },
            RowOperation::Xor { target: 999, source: 0 },
            RowOperation::Xor { target: 0, source: 999 },
        ] {
            let mut bad = valid.clone();
            bad.steps.push(step);
            assert!(bad.verify(&region, &result).is_err());
        }
    }

}
