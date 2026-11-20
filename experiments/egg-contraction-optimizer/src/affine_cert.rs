//! Independent dense-Boolean replay of a packed-GF(2) elimination receipt.
//!
//! No calls to the producer's packed elimination routine. Every emitted step
//! is an invertible row operation. The terminal matrix must have exactly
//! one isolated pivot per recorded internal column and no internal bits in residual rows.
//! Those conditions imply the claimed number of free internal bits.

use crate::affine::{AffineInterface, AffineRegion, BoundaryRow};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

/// An arbitrary BTreeMap index is treated only as a *proposal*.
/// The original source name must match before any row mutation.
/// The bounded machine proof targets the exact slice primitive called here.
fn toggle_registered_bit(
    names: &[&str],
    row: &mut [bool],
    proposed: usize,
    requested: &str,
) -> Result<(), &'static str> {
    if names.get(proposed).copied() != Some(requested) {
        return Err("checker source lookup does not match declared column");
    }
    crate::checked_toggle::flip_checked(row, proposed)
}

/// A checked source-name registry for independent matrix reconstruction.
///
/// The tree determines a candidate location, but does not get to assert
/// correctness of that location: each successful lookup is independently
/// checked against the original ordered source names before any bit
/// mutation. This makes the name-to-column premise of the Lean indexed-row
/// theorem an *enforced acceptance condition*, rather than an assumption
/// about the tree implementation. It does not formally verify BTreeMap.
struct CheckedColumns<'a> {
    names: Vec<&'a str>,
    positions: BTreeMap<&'a str, usize>,
}

impl<'a> CheckedColumns<'a> {
    fn from_source(source: &'a AffineRegion) -> Result<Self, String> {
        let source_count = source.internal.len().checked_add(source.boundary.len())
            .ok_or("checker source name count overflow")?;
        let mut names = Vec::new();
        names.try_reserve_exact(source_count)
            .map_err(|_| "checker source name reservation failed")?;
        let mut positions = BTreeMap::new();
        for name in source.internal.iter().chain(&source.boundary) {
            if !crate::affine::valid_source_identifier(name) {
                return Err("invalid source variable identifier".into());
            }
            let column = names.len();
            if positions.insert(name.as_str(), column).is_some() {
                return Err("duplicated source variable".into());
            }
            names.push(name.as_str());
        }
        Ok(Self { names, positions })
    }

    fn toggle_occurrence(&self, row: &mut [bool], variable: &str) -> Result<(), String> {
        let &column = self.positions.get(variable)
            .ok_or("undeclared source equation variable")?;
        // The same primitive verified by the bounded Rust model checker.
        // An invalid proposal is refused before any row bit changes.
        toggle_registered_bit(&self.names, row, column, variable)?;
        Ok(())
    }
}


/// Fallible allocation of the dense Boolean witness matrix. The
/// caller must first enforce its checked cell budget. A failed capacity
/// reservation returns an explicit error instead of panicking in vec!.
/// This does not prove that an operating system cannot terminate a
/// process after overcommitting memory.
fn try_zeroed_matrix(height: usize, width: usize) -> Result<Vec<Vec<bool>>, String> {
    let mut matrix = Vec::new();
    matrix.try_reserve_exact(height)
        .map_err(|_| "checker matrix row reservation failed")?;
    for _ in 0..height {
        let mut row = Vec::new();
        row.try_reserve_exact(width)
            .map_err(|_| "checker matrix column reservation failed")?;
        row.resize(width, false);
        matrix.push(row);
    }
    Ok(matrix)
}

/// Row-XOR replay must copy the source before mutating the target.
/// Reserve explicitly so failure occurs before the target row changes.
fn try_copy_row(row: &[bool]) -> Result<Vec<bool>, String> {
    let mut copy = Vec::new();
    copy.try_reserve_exact(row.len())
        .map_err(|_| "checker row snapshot reservation failed")?;
    copy.extend_from_slice(row);
    Ok(copy)
}

/// Explicit verifier resources. These bound the *independent checker*, not
/// the producer or the arbitrary-precision result allocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerificationLimits {
    pub max_cells: usize,
    pub max_steps: usize,
}

impl Default for VerificationLimits {
    fn default() -> Self {
        Self { max_cells: 8_000_000, max_steps: 8_000_000 }
    }
}

impl VerificationLimits {
    /// Fail before constructing the dense matrix or replaying the transcript.
    /// Kept as a pure function so overflow/refusal can be tested without
    /// attempting to allocate pathological inputs.
    pub fn check(self, rows: usize, columns: usize, steps: usize) -> Result<(), String> {
        // A product-only test would admit an empty (zero-row) matrix
        // with arbitrarily many declared columns, even though name
        // registration and the free-column receipt still allocate.
        let cells = rows.checked_mul(columns)
            .ok_or("checker matrix storage overflow")?;
        // The appended RHS is not a source variable. In the empty
        // 0-by-0 system the augmented width is one but no matrix cells
        // or variable registry entries are allocated.
        if columns.saturating_sub(1) > self.max_cells || rows > self.max_cells {
            return Err("checker matrix dimension budget exceeded".into());
        }
        if cells > self.max_cells {
            return Err("checker matrix storage budget exceeded".into());
        }
        if steps > self.max_steps {
            return Err("checker transcript budget exceeded".into());
        }
        Ok(())
    }
}

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

/// A normal-form witness reconstructed from an independently replayed
/// terminal matrix, not copied from the producer's proposed interface.
/// Pivots can be at arbitrary internal columns; free columns are the
/// complement, ordered increasingly. This is the Rust schema for the
/// Lean pivot/free/residual terminal theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedTerminal {
    internal_width: usize,
    boundary_width: usize,
    pub pivot_columns: Vec<usize>,
    free_columns: Vec<usize>,
    pivot_free_coefficients: Vec<Vec<usize>>,
    pivot_boundary_coefficients: Vec<Vec<usize>>,
    pivot_rhs: Vec<bool>,
    residual_rows: Vec<BoundaryRow>,
}

impl VerifiedTerminal {
    /// Return the unique completion of all pivot variables for one free
    /// assignment if the boundary satisfies every residual constraint.
    pub fn complete(
        &self,
        free: &[bool],
        boundary: &[bool],
    ) -> Result<Option<Vec<bool>>, String> {
        if free.len() != self.free_columns.len() ||
            boundary.len() != self.boundary_width {
            return Err("terminal completion dimension mismatch".into());
        }
        for row in &self.residual_rows {
            let mut parity = false;
            for &index in &row.boundary_indices {
                let bit = boundary.get(index)
                    .ok_or("malformed terminal boundary index")?;
                parity ^= *bit;
            }
            if parity != row.rhs {
                return Ok(None);
            }
        }
        let mut internal = vec![false; self.internal_width];
        for (i, &column) in self.free_columns.iter().enumerate() {
            let slot = internal.get_mut(column)
                .ok_or("malformed terminal free column")?;
            *slot = free[i];
        }
        for (i, &column) in self.pivot_columns.iter().enumerate() {
            let mut value = *self.pivot_rhs.get(i)
                .ok_or("malformed terminal pivot RHS")?;
            for &free_position in self.pivot_free_coefficients.get(i)
                .ok_or("malformed terminal pivot/free row")? {
                value ^= *free.get(free_position)
                    .ok_or("malformed terminal free position")?;
            }
            for &boundary_position in self.pivot_boundary_coefficients.get(i)
                .ok_or("malformed terminal pivot/boundary row")? {
                value ^= *boundary.get(boundary_position)
                    .ok_or("malformed terminal boundary position")?;
            }
            let slot = internal.get_mut(column)
                .ok_or("malformed terminal pivot column")?;
            *slot = value;
        }
        Ok(Some(internal))
    }

    pub fn count_at(&self, boundary: &[bool]) -> Result<BigUint, String> {
        let free = vec![false; self.free_columns.len()];
        Ok(if self.complete(&free, boundary)?.is_some() {
            BigUint::from(1u8) << self.free_columns.len()
        } else {
            BigUint::from(0u8)
        })
    }
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
        self.verify_with_limits(source, claimed, VerificationLimits::default())
    }

    pub fn verify_with_limits(
        &self,
        source: &AffineRegion,
        claimed: &AffineInterface,
        limits: VerificationLimits,
    ) -> Result<VerificationReceipt, String> {
        self.verify_with_terminal(source, claimed, limits).map(|(receipt, _)| receipt)
    }

    /// Produce a semantic terminal witness *only after* checking all
    /// source, transcript, pivot, rank and residual conditions.
    pub fn verify_with_terminal(
        &self,
        source: &AffineRegion,
        claimed: &AffineInterface,
        limits: VerificationLimits,
    ) -> Result<(VerificationReceipt, VerifiedTerminal), String> {
        let k = source.internal.len();
        let b = source.boundary.len();
        let width = k.checked_add(b)
            .and_then(|x| x.checked_add(1))
            .ok_or("checker matrix width overflow")?;
        limits.check(source.equations.len(), width, self.steps.len())?;
        if claimed.boundary != source.boundary {
            return Err("boundary names/order were changed".into());
        }
        let columns = CheckedColumns::from_source(source)?;
        let mut rows = try_zeroed_matrix(source.equations.len(), width)?;
        for (i, equation) in source.equations.iter().enumerate() {
            for variable in &equation.variables {
                columns.toggle_occurrence(&mut rows[i], variable)?;
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
                    let read = try_copy_row(&rows[source])?;
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
        // The checker has proved all pivot columns isolated and all
        // residual internal columns zero. Materialize the corresponding
        // pivot/free system from replayed rows, not from the claimed result.
        let free_columns = (0..k).filter(|col| !pivots.contains(col))
            .collect::<Vec<_>>();
        let pivot_free_coefficients = rows.iter().take(r).map(|row| {
            free_columns.iter().enumerate()
                .filter_map(|(i, &col)| row[col].then_some(i))
                .collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        let pivot_boundary_coefficients = rows.iter().take(r).map(|row| {
            (0..b).filter(|&col| row[k + col]).collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        let pivot_rhs = rows.iter().take(r)
            .map(|row| row[width - 1]).collect::<Vec<_>>();
        let terminal = VerifiedTerminal {
            internal_width: k,
            boundary_width: b,
            pivot_columns: self.pivot_columns.clone(),
            free_columns,
            pivot_free_coefficients,
            pivot_boundary_coefficients,
            pivot_rhs,
            residual_rows: claimed.residual.clone(),
        };
        Ok((VerificationReceipt {
            rank: r,
            free_internal: k - r,
            operations_checked: self.steps.len(),
            residual_rows_checked: rows.len() - r,
        }, terminal))
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
    fn matrix_reservation_fails_closed_before_any_partial_result_escapes() {
        let row = try_zeroed_matrix(2, 3).unwrap();
        assert_eq!(row, vec![vec![false; 3]; 2]);
        assert_eq!(try_zeroed_matrix(0, 0).unwrap().len(), 0);
        assert!(try_zeroed_matrix(1, usize::MAX).unwrap_err()
            .contains("column reservation failed"));
        assert!(try_zeroed_matrix(usize::MAX, 1).unwrap_err()
            .contains("row reservation failed"));
        assert!(try_copy_row(&[true, false, true]).unwrap() == vec![true, false, true]);
    }

    #[test]
    fn preflight_resource_refusal_cannot_reach_dense_allocation() {
        let source = example();
        let (claimed, cert) = source.eliminate_with_certificate().unwrap();
        // An empty cell budget refuses before matrix reconstruction.
        let refusal = cert.verify_with_terminal(&source, &claimed, VerificationLimits {
            max_cells: 0,
            max_steps: 0,
        });
        assert!(refusal.unwrap_err().contains("budget exceeded"));
    }

    #[test]
    fn checked_registry_refuses_corrupted_indices_before_bit_mutation() {
        let source = AffineRegion {
            internal: vec!["u".into(), "v".into()],
            boundary: vec!["b".into()],
            equations: vec![],
        };
        let mut columns = CheckedColumns::from_source(&source).unwrap();
        let mut row = vec![false; 4];
        columns.toggle_occurrence(&mut row, "u").unwrap();
        assert_eq!(row, vec![true, false, false, false]);

        // A forged tree entry for a different *in-range* name must not
        // silently toggle the wrong coordinate.
        columns.positions.insert("u", 1);
        let before = row.clone();
        assert!(columns.toggle_occurrence(&mut row, "u").is_err());
        assert_eq!(row, before);
        // An out-of-range entry must also fail without touching RHS.
        columns.positions.insert("u", usize::MAX);
        assert!(columns.toggle_occurrence(&mut row, "u").is_err());
        assert_eq!(row, before);
        // Pointing to the RHS column is invalid even if row is long.
        columns.positions.insert("u", 3);
        assert!(columns.toggle_occurrence(&mut row, "u").is_err());
        assert_eq!(row, before);
        columns.positions.remove("u");
        assert!(columns.toggle_occurrence(&mut row, "u").is_err());
        assert_eq!(row, before);
        assert!(columns.toggle_occurrence(&mut row, "undeclared").is_err());
        assert_eq!(row, before);
        // Even a valid map cannot mutate a row shorter than the source
        // declaration if the requested column is absent.
        columns.positions.insert("v", 1);
        assert!(columns.toggle_occurrence(&mut row[..1], "v").is_err());
        assert_eq!(row, before);
    }

    #[test]
    fn checked_registry_matches_direct_source_occurrence_parity() {
        fn draw(seed: &mut u64) -> u64 {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        }
        for initial in 1..=128u64 {
            let mut state = initial;
            let k = (draw(&mut state) % 16 + 1) as usize;
            let b = (draw(&mut state) % 8) as usize;
            let source = AffineRegion {
                internal: (0..k).map(|i| format!("u{i}")).collect(),
                boundary: (0..b).map(|i| format!("b{i}")).collect(),
                equations: vec![],
            };
            let columns = CheckedColumns::from_source(&source).unwrap();
            let all_names = source.internal.iter().chain(&source.boundary)
                .map(String::as_str).collect::<Vec<_>>();
            let mut actual = vec![false; all_names.len() + 1];
            let mut occurrences = Vec::new();
            for _ in 0..128 {
                let index = (draw(&mut state) as usize) % all_names.len();
                let name = all_names[index];
                occurrences.push(name);
                columns.toggle_occurrence(&mut actual, name).unwrap();
                for (column, &declared) in all_names.iter().enumerate() {
                    let expected = occurrences.iter()
                        .filter(|&&occurrence| occurrence == declared)
                        .count() % 2 == 1;
                    assert_eq!(actual[column], expected,
                        "seed={initial}, column={column}, length={}", occurrences.len());
                }
                assert!(!actual[all_names.len()], "RHS bit was toggled");
            }
        }
    }

    #[test]
    fn checker_refuses_malformed_registered_names_even_if_equations_are_consistent() {
        let original = example();
        let (claimed, certificate) = original.eliminate_with_certificate().unwrap();
        for malformed in ["1u", "_u", "u-name", "u name", "é", "u🙂", ""] {
            // Rename every occurrence as well: this deliberately remains
            // the same *mathematical* parity system. A checker which merely
            // validates lookup success, not the source grammar, would accept.
            let mut source = original.clone();
            let previous = source.internal[0].clone();
            source.internal[0] = malformed.to_owned();
            for equation in &mut source.equations {
                for name in &mut equation.variables {
                    if *name == previous {
                        *name = malformed.to_owned();
                    }
                }
            }
            assert!(certificate.verify(&source, &claimed).is_err(),
                "source grammar incorrectly admitted {malformed:?}");
            assert!(source.eliminate().is_err(),
                "producer grammar incorrectly admitted {malformed:?}");
        }
        for valid in ["u_1", "U", "a9", "z_9_A"] {
            assert!(crate::affine::valid_source_identifier(valid));
        }
    }

    #[test]
    fn checker_rejects_every_violated_terminal_shape_condition() {
        use crate::affine::BoundaryRow;
        fn source(rows: Vec<Vec<&str>>) -> AffineRegion {
            AffineRegion {
                internal: vec!["u".into(), "v".into()],
                boundary: vec!["b".into()],
                equations: rows.into_iter().map(|variables| Equation {
                    variables: variables.into_iter().map(str::to_owned).collect(),
                    rhs: false,
                }).collect(),
            }
        }
        let base = source(vec![vec!["u", "v", "b"]]);
        let certificate = EliminationCertificate {
            steps: vec![], pivot_columns: vec![0],
        };
        let claimed = AffineInterface {
            boundary: base.boundary.clone(),
            residual: vec![], rank: 1, free_internal: 1, elimination_xors: 0,
        };
        let (_, terminal) = certificate
            .verify_with_terminal(&base, &claimed, VerificationLimits::default())
            .unwrap();
        assert_eq!(terminal.count_at(&[false]).unwrap(), BigUint::from(2u8));
        assert_eq!(terminal.count_at(&[true]).unwrap(), BigUint::from(2u8));

        // A free variable is permitted in pivot rows, but NOT below them.
        let residual_free = source(vec![vec!["u"], vec!["v"]]);
        let residual_claim = AffineInterface {
            boundary: residual_free.boundary.clone(),
            residual: vec![BoundaryRow {
                boundary_indices: vec![], rhs: false,
            }],
            rank: 1, free_internal: 1, elimination_xors: 0,
        };
        assert!(certificate.verify(&residual_free, &residual_claim).is_err());

        // Pivot must occur in its own row, not in any residual row.
        let residual_pivot = source(vec![vec!["u"], vec!["u"]]);
        assert!(certificate.verify(&residual_pivot, &residual_claim).is_err());

        // The claimed pivot must exist and be equal to 1.
        let missing_pivot = source(vec![vec!["v"]]);
        assert!(certificate.verify(&missing_pivot, &claimed).is_err());

        // A genuine residual boundary equation must not be edited.
        let boundary_only = source(vec![vec!["u"], vec!["b"]]);
        let good_claim = AffineInterface {
            boundary: boundary_only.boundary.clone(),
            residual: vec![BoundaryRow {
                boundary_indices: vec![0], rhs: false,
            }],
            rank: 1, free_internal: 1, elimination_xors: 0,
        };
        let (_, terminal) = certificate.verify_with_terminal(
            &boundary_only, &good_claim, VerificationLimits::default()
        ).unwrap();
        assert_eq!(terminal.count_at(&[false]).unwrap(), BigUint::from(2u8));
        assert_eq!(terminal.count_at(&[true]).unwrap(), BigUint::from(0u8));
        let mut changed_rhs = good_claim.clone();
        changed_rhs.residual[0].rhs = true;
        assert!(certificate.verify(&boundary_only, &changed_rhs).is_err());
        let mut changed_boundary = good_claim;
        changed_boundary.residual[0].boundary_indices.clear();
        assert!(certificate.verify(&boundary_only, &changed_boundary).is_err());

        // A source with two pivot columns is rejected if the columns are
        // not isolated (even if a claimed result names two pivots).
        let two = source(vec![vec!["u", "v"], vec!["v"]]);
        let wrong = EliminationCertificate {
            steps: vec![], pivot_columns: vec![0, 1],
        };
        let two_claim = AffineInterface {
            boundary: two.boundary.clone(), residual: vec![],
            rank: 2, free_internal: 0, elimination_xors: 0,
        };
        assert!(wrong.verify(&two, &two_claim).is_err());
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
            let (_, terminal) = certificate
                .verify_with_terminal(&region, &interface, VerificationLimits::default())
                .unwrap();
            assert_eq!(terminal.free_columns.len(), interface.free_internal);
            assert_eq!(terminal.pivot_columns.len(), interface.rank);
            for mask in 0..(1usize << b) {
                let values = region.boundary.iter().enumerate().map(|(j, name)| {
                    (name.clone(), mask & (1 << j) != 0)
                }).collect::<BTreeMap<_, _>>();
                let expected = region.direct_count(&values, 16).unwrap();
                assert_eq!(interface.evaluate(&values).unwrap(), expected,
                    "interface seed={seed}, mask={mask}");
                let boundary_bits = region.boundary.iter().map(|key| values[key])
                    .collect::<Vec<_>>();
                assert_eq!(terminal.count_at(&boundary_bits).unwrap(), expected,
                    "terminal seed={seed}, mask={mask}");
                let mut seen = BTreeSet::new();
                for free_mask in 0..(1usize << terminal.free_columns.len()) {
                    let free = (0..terminal.free_columns.len())
                        .map(|i| free_mask & (1 << i) != 0)
                        .collect::<Vec<_>>();
                    if let Some(internal) = terminal.complete(&free, &boundary_bits).unwrap() {
                        assert!(seen.insert(internal.clone()));
                        let all = region.internal.iter().zip(&internal)
                            .map(|(key, value)| (key.clone(), *value))
                            .chain(values.iter().map(|(k, v)| (k.clone(), *v)))
                            .collect::<BTreeMap<_, _>>();
                        assert!(region.equations.iter().all(|eq| {
                            eq.variables.iter().fold(false, |p, v| p ^ all[v]) == eq.rhs
                        }), "invalid pivot completion seed={seed}, mask={mask}");
                    }
                }
                assert_eq!(num_bigint::BigUint::from(seen.len()), expected,
                    "non-bijective pivot/free completion seed={seed}, mask={mask}");
            }
        }
    }

    #[test]
    fn noncontiguous_pivot_columns_have_unique_free_completions() {
        let internal = (0..6).map(|i| format!("u{i}")).collect::<Vec<_>>();
        let region = AffineRegion {
            internal,
            boundary: vec!["b".into(), "c".into(), "d".into()],
            equations: vec![
                Equation { variables: vec!["u1".into(), "u3".into(), "b".into()], rhs: false },
                Equation { variables: vec!["u4".into(), "u5".into(), "c".into()], rhs: true },
                Equation { variables: vec!["u1".into(), "u3".into(), "d".into()], rhs: false },
            ],
        };
        let (interface, certificate) = region.eliminate_with_certificate().unwrap();
        let (receipt, terminal) = certificate
            .verify_with_terminal(&region, &interface, VerificationLimits::default())
            .unwrap();
        assert_eq!(receipt.rank, 2);
        assert_eq!(terminal.pivot_columns, vec![1, 4]);
        assert_eq!(terminal.free_columns, vec![0, 2, 3, 5]);
        for mask in 0..8 {
            let bits = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
            let expected = if bits[0] == bits[2] {
                num_bigint::BigUint::from(16_u8)
            } else {
                num_bigint::BigUint::from(0_u8)
            };
            assert_eq!(terminal.count_at(&bits).unwrap(), expected);
            let mut seen = BTreeSet::new();
            for free_mask in 0..16usize {
                let free = (0..4).map(|i| free_mask & (1 << i) != 0)
                    .collect::<Vec<_>>();
                if let Some(internal) = terminal.complete(&free, &bits).unwrap() {
                    assert!(seen.insert(internal.clone()));
                    assert_eq!(internal[1] ^ internal[3] ^ bits[0], false);
                    assert_eq!(internal[4] ^ internal[5] ^ bits[1], true);
                    assert_eq!(internal[1] ^ internal[3] ^ bits[2], false);
                }
            }
            assert_eq!(num_bigint::BigUint::from(seen.len()), expected);
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
    fn native_u64_transcripts_agree_with_separate_boolean_bit_replay() {
        // An implementation-side correspondence test for the Lean BitVec
        // model. The packed u64 transition and flat Boolean transition
        // have different data structures and separate mutation code.
        fn draw(s: &mut u64) -> u64 {
            *s ^= *s << 13;
            *s ^= *s >> 7;
            *s ^= *s << 17;
            *s
        }
        for seed in 1..=128u64 {
            let mut state = seed;
            let m = (draw(&mut state) % 6 + 2) as usize;
            let words = (draw(&mut state) % 5 + 1) as usize;
            let width = words * 64;
            let mut packed = vec![vec![0_u64; words]; m];
            let mut rhs = vec![false; m];
            let mut flat = vec![vec![false; width + 1]; m];
            for r in 0..m {
                for w in 0..words {
                    packed[r][w] = draw(&mut state);
                    for bit in 0..64 {
                        flat[r][64 * w + bit] = (packed[r][w] >> bit) & 1 == 1;
                    }
                }
                rhs[r] = draw(&mut state) & 1 == 1;
                flat[r][width] = rhs[r];
            }
            for iteration in 0..32 {
                let target = (draw(&mut state) as usize) % m;
                let mut source = (draw(&mut state) as usize) % (m - 1);
                if source >= target { source += 1; }
                if iteration % 3 == 0 {
                    packed.swap(target, source);
                    rhs.swap(target, source);
                    flat.swap(target, source);
                } else {
                    let src_words = packed[source].clone();
                    for (dst, src) in packed[target].iter_mut().zip(src_words) {
                        *dst ^= src;
                    }
                    let source_rhs = rhs[source];
                    rhs[target] ^= source_rhs;
                    let src_bits = flat[source].clone();
                    for (bit, src) in flat[target].iter_mut().zip(src_bits) {
                        *bit ^= src;
                    }
                }
                for r in 0..m {
                    for col in 0..width {
                        assert_eq!(
                            (packed[r][col / 64] >> (col % 64)) & 1 != 0,
                            flat[r][col],
                            "seed={seed}, iteration={iteration}, row={r}, column={col}",
                        );
                    }
                    assert_eq!(rhs[r], flat[r][width],
                        "seed={seed}, iteration={iteration}, row={r}, rhs");
                }
            }
        }
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
    fn configurable_checker_limits_fail_before_allocation_or_replay() {
        let region = example();
        let (interface, transcript) = region.eliminate_with_certificate().unwrap();
        let width = region.internal.len() + region.boundary.len() + 1;
        let cells = region.equations.len() * width;
        let steps = transcript.steps.len();
        transcript.verify_with_limits(&region, &interface, VerificationLimits {
            max_cells: cells,
            max_steps: steps,
        }).unwrap();
        assert!(transcript.verify_with_limits(&region, &interface, VerificationLimits {
            max_cells: cells - 1,
            max_steps: steps,
        }).unwrap_err().contains("storage budget exceeded"));
        assert!(steps > 0);
        assert!(transcript.verify_with_limits(&region, &interface, VerificationLimits {
            max_cells: cells,
            max_steps: steps - 1,
        }).unwrap_err().contains("transcript budget exceeded"));
        assert!(VerificationLimits::default()
            .check(usize::MAX, 2, 0).unwrap_err().contains("overflow"));
        assert!(VerificationLimits { max_cells: usize::MAX, max_steps: 0 }
            .check(0, usize::MAX, 1).unwrap_err().contains("transcript budget"));
        assert!(VerificationLimits { max_cells: 0, max_steps: 0 }
            .check(0, usize::MAX, 0).unwrap_err()
            .contains("dimension budget"));
        assert!(VerificationLimits { max_cells: 4, max_steps: 0 }
            .check(0, 6, 0).unwrap_err()
            .contains("dimension budget"));
        VerificationLimits { max_cells: 4, max_steps: 0 }
            .check(0, 5, 0).unwrap();
        // Zero equations and zero declared variables allocate no cells.
        VerificationLimits { max_cells: 0, max_steps: 0 }
            .check(0, 1, 0).unwrap();
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
