//! Certified *structural* recognition of a restricted non-affine 3-CNF family.
//!
//! Variables x[0..n] obey parity recurrences
//! x[i] XOR x[i+1] XOR x[i+3] = rhs[i], i=0..n-4,
//! each encoded by exactly four signed 3-clauses, plus the positive clause
//! x[i] OR x[i+1] OR x[i+2], i=0..n-3.
//!
//! This module does not claim a generic #SAT algorithm. Failure to recognize
//! the *entire* normalized incidence matrix is a refusal, not a guess.

use std::collections::BTreeMap;

use crate::{Cnf, Error};

/// A zero-based, row-sorted signed CSR incidence matrix.
///
/// Each nonzero polarity is exactly +1 or -1; an empty row would be encoded
/// by consecutive equal row offsets, but is not accepted by this recognizer.
#[derive(Clone, Copy, Debug)]
pub struct SignedCsr<'a> {
    pub variables: usize,
    pub row_offsets: &'a [usize],
    pub column_indices: &'a [usize],
    pub signs: &'a [i8],
}

/// Owned construction from the canonical Cnf model. The declared number of
/// variables is retained even when a column has no literal occurrences.
#[derive(Clone, Debug)]
pub struct OwnedSignedCsr {
    pub variables: usize,
    pub row_offsets: Vec<usize>,
    pub column_indices: Vec<usize>,
    pub signs: Vec<i8>,
}

impl OwnedSignedCsr {
    pub fn from_cnf(cnf: &Cnf) -> Self {
        let mut result = Self {
            variables: cnf.variables(),
            row_offsets: vec![0],
            column_indices: Vec::new(),
            signs: Vec::new(),
        };
        for clause in cnf.clauses() {
            for lit in clause.literals() {
                result.column_indices.push(lit.variable);
                result.signs.push(if lit.positive { 1 } else { -1 });
            }
            result.row_offsets.push(result.column_indices.len());
        }
        result
    }

    pub fn view(&self) -> SignedCsr<'_> {
        SignedCsr {
            variables: self.variables,
            row_offsets: &self.row_offsets,
            column_indices: &self.column_indices,
            signs: &self.signs,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecurrenceReceipt {
    /// One RHS bit per complete, independently verified four-clause XOR gadget.
    pub rhs: Vec<bool>,
    /// Bit s is set iff initial three-bit state s violates at least one OR.
    pub forbidden_seeds: u8,
}

impl RecurrenceReceipt {
    /// At most eight seeds exist; this count does not enumerate 2^n assignments.
    pub fn count(&self) -> u8 {
        8 - self.forbidden_seeds.count_ones() as u8
    }
}

fn refuse(reason: &str) -> Error {
    Error::Invalid(format!(
        "unsupported signed-CSR recurrence family: {reason}"
    ))
}

/// One checked source of truth for the restricted recurrence's CSR shape.
/// At n >= 4, successful multiplication implies both the row count
/// (5*n - 14) and the trailing offset count (5*n - 13) fit in usize.
/// Never substitute saturation for a representability check.
fn expected_csr_shape(n: usize) -> Result<(usize, usize), Error> {
    let rows = n
        .checked_mul(5)
        .and_then(|v| v.checked_sub(14))
        .ok_or(Error::Overflow)?;
    let offsets = rows.checked_add(1).ok_or(Error::Overflow)?;
    Ok((rows, offsets))
}

/// The complete, checked representation boundary of one signed CSR row.
/// Consumers share only decoding, not the recurrence recognition or receipt
/// comparison algorithms. This operation neither allocates nor panics on
/// malformed offsets, missing elements, invalid signs or column ordering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CheckedCsrRow {
    columns: [usize; 3],
    signs: [i8; 3],
}

impl SignedCsr<'_> {
    /// One fail-closed outer CSR contract shared by the recognizer and
    /// independent receipt replay. This validates the declared shape,
    /// not the row contents; checked_row validates those separately.
    fn validated_row_count(&self) -> Result<usize, Error> {
        if self.variables < 4 {
            return Err(refuse("requires at least four variables"));
        }
        let (rows, offsets) = expected_csr_shape(self.variables)?;
        if self.row_offsets.len() != offsets
            || self.column_indices.len() != self.signs.len()
            || self.row_offsets.first() != Some(&0)
            || self.row_offsets.last() != Some(&self.column_indices.len())
        {
            return Err(refuse("incorrect matrix shape or CSR offsets"));
        }
        Ok(rows)
    }

    /// Return the exact ternary row or refuse. All indexing is checked.
    /// In particular, start+3 and row+1 are checked before slicing; there
    /// is no unchecked access even when called before outer-shape validation.
    fn checked_row(&self, row: usize) -> Option<CheckedCsrRow> {
        let start = *self.row_offsets.get(row)?;
        let stop = *self.row_offsets.get(row.checked_add(1)?)?;
        if start.checked_add(3)? != stop {
            return None;
        }
        let columns: [usize; 3] = self.column_indices.get(start..stop)?.try_into().ok()?;
        let signs: [i8; 3] = self.signs.get(start..stop)?.try_into().ok()?;
        if columns[0] >= columns[1]
            || columns[1] >= columns[2]
            || columns[2] >= self.variables
            || !signs.iter().all(|s| *s == -1 || *s == 1)
        {
            return None;
        }
        Some(CheckedCsrRow { columns, signs })
    }

    /// Verify the complete formula, not just some matching XOR/OR subgraph.
    ///
    /// Complexity: O(n log n) comparison work for row grouping, O(n) seed
    /// evaluation, and O(n) extra memory for the receipt and row-group map.
    /// This is a word-operation bound; no whole-machine bit-cost theorem.
    pub fn recognize_recurrence(&self) -> Result<RecurrenceReceipt, Error> {
        let n = self.variables;
        let expected_rows = self.validated_row_count()?;

        // Group exact rows by their three distinct variable indices; an
        // eight-bit value records which of the eight polarities occur.
        let mut groups: BTreeMap<[usize; 3], u8> = BTreeMap::new();
        for row_index in 0..expected_rows {
            let CheckedCsrRow {
                columns: cols,
                signs,
            } = self
                .checked_row(row_index)
                .ok_or_else(|| refuse("malformed signed CSR row"))?;
            let polarity = signs.iter().enumerate().fold(0u8, |mask, (i, sign)| {
                if *sign == -1 { mask | (1 << i) } else { mask }
            });
            let key = [cols[0], cols[1], cols[2]];
            let seen = groups.entry(key).or_default();
            let bit = 1 << polarity;
            if *seen & bit != 0 {
                return Err(refuse("duplicate literal-polarity row"));
            }
            *seen |= bit;
        }

        // The forbidden local assignments have opposite parity to the RHS.
        // For rhs=0: 001,010,100,111 -> bits 1,2,4,7 -> 0x96.
        // For rhs=1: 000,011,101,110 -> bits 0,3,5,6 -> 0x69.
        let mut rhs = Vec::new();
        rhs.try_reserve_exact(n - 3)
            .map_err(|_| Error::Capacity("unable to reserve recurrence RHS".into()))?;
        for i in 0..n - 3 {
            let key = [i, i + 1, i + 3];
            match groups.remove(&key) {
                Some(0x96) => rhs.push(false),
                Some(0x69) => rhs.push(true),
                _ => return Err(refuse("incomplete or incorrect four-clause parity gadget")),
            }
        }
        for i in 0..n - 2 {
            let key = [i, i + 1, i + 2];
            if groups.remove(&key) != Some(0x01) {
                return Err(refuse("missing or incorrect positive OR clause"));
            }
        }
        if !groups.is_empty() {
            return Err(refuse("unrecognized additional clauses"));
        }

        // Each start seed extends uniquely through the certified recurrence.
        // The eight-bit mask records which seeds ever pass through state 000.
        let mut forbidden = 0u8;
        for seed in 0..8u8 {
            let mut state = [seed & 1 != 0, seed & 2 != 0, seed & 4 != 0];
            for &bit in &rhs {
                if !state[0] && !state[1] && !state[2] {
                    forbidden |= 1 << seed;
                }
                state = [state[1], state[2], state[0] ^ state[1] ^ bit];
            }
            // The final sliding OR has no following parity transition.
            if !state[0] && !state[1] && !state[2] {
                forbidden |= 1 << seed;
            }
        }
        Ok(RecurrenceReceipt {
            rhs,
            forbidden_seeds: forbidden,
        })
    }
}

/// Independently replay a receipt against the *whole* source CSR.
///
/// The producer groups actual clauses by scope and infers polarity masks.
/// This verifier instead generates the complete expected signed row set from
/// the claimed RHS, compares all source rows, then directly evaluates the
/// original signed rows on all eight reconstructed full assignments.
///
/// No trust is placed in the producer's group map, inferred masks, or seed
/// traversal. This is an independent Rust check, not a Lean-to-Rust proof.
pub fn verify_recurrence_receipt(
    csr: SignedCsr<'_>,
    receipt: &RecurrenceReceipt,
) -> Result<u8, Error> {
    use std::collections::BTreeSet;

    let n = csr.variables;
    if n < 4 || receipt.rhs.len() != n - 3 {
        return Err(refuse("receipt has incorrect variable count or RHS length"));
    }

    let expected_rows = csr.validated_row_count()?;

    let mut actual = BTreeSet::new();
    for row_index in 0..expected_rows {
        let CheckedCsrRow { columns, signs } = csr
            .checked_row(row_index)
            .ok_or_else(|| refuse("invalid source CSR row"))?;
        if !actual.insert((columns, signs)) {
            return Err(refuse("duplicate source CSR row"));
        }
    }
    // Source shape and every row are validated before expanding the
    // receipt into a potentially large expected set. A malformed CSR
    // must not pay for receipt-derived allocations.
    let mut expected = BTreeSet::<([usize; 3], [i8; 3])>::new();
    for (i, rhs) in receipt.rhs.iter().copied().enumerate() {
        for mask in 0..8u8 {
            if (mask.count_ones() % 2 == 1) != rhs {
                let columns = [i, i + 1, i + 3];
                let signs = std::array::from_fn(|j| if mask & (1 << j) != 0 { -1 } else { 1 });
                expected.insert((columns, signs));
            }
        }
    }
    for i in 0..n - 2 {
        expected.insert(([i, i + 1, i + 2], [1, 1, 1]));
    }

    if actual != expected {
        return Err(refuse("receipt does not describe all source clauses"));
    }

    let mut observed_mask = 0u8;
    for seed in 0..8u8 {
        let mut x = Vec::new();
        x.try_reserve_exact(n)
            .map_err(|_| Error::Capacity("unable to reserve seed assignment".into()))?;
        x.extend([seed & 1 != 0, seed & 2 != 0, seed & 4 != 0]);
        for (i, rhs) in receipt.rhs.iter().copied().enumerate() {
            let left = *x
                .get(i)
                .ok_or_else(|| refuse("missing recurrence state input"))?;
            let right = *x
                .get(i + 1)
                .ok_or_else(|| refuse("missing recurrence state input"))?;
            x.push(left ^ right ^ rhs);
        }

        // Evaluate the *validated source rows* independently of the
        // producer's parity/OR computation. The set was decoded from the
        // original CSR before expected rows were constructed; both source
        // reads and assignment lookups are checked and fail closed.
        let mut is_satisfied = true;
        for (columns, signs) in &actual {
            let mut clause_satisfied = false;
            for (&column, &sign) in columns.iter().zip(signs.iter()) {
                let bit = *x
                    .get(column)
                    .ok_or_else(|| refuse("decoded source column outside assignment"))?;
                clause_satisfied |= bit == (sign == 1);
            }
            if !clause_satisfied {
                is_satisfied = false;
                break;
            }
        }
        if !is_satisfied {
            observed_mask |= 1 << seed;
        }
    }
    if observed_mask != receipt.forbidden_seeds {
        return Err(refuse("receipt forbids an incorrect set of seeds"));
    }
    Ok(receipt.count())
}

/// Fail-closed recognition from a canonical normalized CNF (no matching-only
/// shortcut). Independently replay the receipt against the entire CSR before
/// exposing it to callers. No unsupported formula is treated as a zero count.
pub fn recognize_cnf(cnf: &Cnf) -> Result<RecurrenceReceipt, Error> {
    let csr = OwnedSignedCsr::from_cnf(cnf);
    let receipt = csr.view().recognize_recurrence()?;
    verify_recurrence_receipt(csr.view(), &receipt)?;
    Ok(receipt)
}

/// The public exact-counting path uses both the producer and the independent
/// source-and-seed receipt checker. Restricted-family refusal is explicit.
pub fn count_recognized_cnf(cnf: &Cnf) -> Result<u8, Error> {
    Ok(recognize_cnf(cnf)?.count())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(n: usize, rhs: &[bool]) -> Cnf {
        assert!(n >= 4 && rhs.len() == n - 3);
        let mut rows = Vec::new();
        for (i, &bit) in rhs.iter().enumerate() {
            for mask in 0u8..8 {
                let parity = mask.count_ones() % 2 == 1;
                if parity != bit {
                    let vars = [i + 1, i + 2, i + 4];
                    let row = vars
                        .iter()
                        .enumerate()
                        .map(|(j, v)| {
                            if mask & (1 << j) == 0 {
                                *v as i64
                            } else {
                                -(*v as i64)
                            }
                        })
                        .collect::<Vec<_>>();
                    rows.push(row);
                }
            }
        }
        for i in 0..n - 2 {
            rows.push(vec![(i + 1) as i64, (i + 2) as i64, (i + 3) as i64]);
        }
        let refs = rows.iter().map(Vec::as_slice).collect::<Vec<_>>();
        Cnf::from_signed(n, &refs).unwrap()
    }

    fn oracle(n: usize, cnf: &Cnf) -> u8 {
        (0..(1u128 << n))
            .filter(|assignment| cnf.eval_mask_checked(*assignment).unwrap())
            .count() as u8
    }

    /// Test the shared usize computation independently of CSR allocation.
    /// A successful row shape must equal both unbounded integer formulas;
    /// overflow must refuse rather than wrap or saturate.
    #[test]
    fn checked_csr_shape_matches_machine_bounds() {
        for n in 4..=4096usize {
            let (rows, offsets) = expected_csr_shape(n).unwrap();
            assert_eq!(rows, 5 * n - 14);
            assert_eq!(offsets, rows + 1);
            assert_eq!(offsets, 5 * n - 13);
        }

        let largest_fitting_n = usize::MAX / 5;
        for n in [
            largest_fitting_n - 1,
            largest_fitting_n,
            largest_fitting_n + 1,
            usize::MAX,
        ] {
            match expected_csr_shape(n) {
                Ok((rows, offsets)) => {
                    let product = n.checked_mul(5).expect("accepted overflow");
                    assert_eq!(rows, product - 14);
                    assert_eq!(offsets, rows + 1);
                    assert_eq!(offsets, product - 13);
                }
                Err(Error::Overflow) => {
                    assert!(n.checked_mul(5).is_none(), "unexpected refusal for n={n}");
                }
                Err(other) => panic!("unexpected shape error for n={n}: {other}"),
            }
        }
    }

    /// Exercise the production recognizer and independent receipt replay on
    /// invalid one-row representations. In particular, no usize boundary or
    /// i8 sentinel may become a valid signed literal or trigger a panic.
    /// Malformed outer shapes must refuse before the verifier expands a
    /// large, untrusted RHS receipt into a BTreeSet of expected clauses.
    /// The result is checked independently from the recognized CNF path.
    #[test]
    fn malformed_shape_refuses_before_receipt_expansion() {
        let n = 100_000_usize;
        let rhs = vec![false; n - 3];
        let receipt = RecurrenceReceipt {
            rhs,
            forbidden_seeds: 0,
        };
        let offsets = [0_usize];
        let csr = SignedCsr {
            variables: n,
            row_offsets: &offsets,
            column_indices: &[],
            signs: &[],
        };
        assert!(matches!(
            verify_recurrence_receipt(csr, &receipt),
            Err(Error::Invalid(_))
        ));
    }

    #[test]
    fn machine_row_boundaries_refuse_without_panicking() {
        let good = OwnedSignedCsr::from_cnf(&source(4, &[false]));
        let receipt = good.view().recognize_recurrence().unwrap();
        let mut cases: Vec<(&str, OwnedSignedCsr)> = Vec::new();

        for sign in [0_i8, 2, -2, i8::MIN, i8::MAX] {
            let mut bad = good.clone();
            bad.signs[0] = sign;
            cases.push(("invalid signed i8", bad));
        }

        for (label, col) in [
            ("out-of-range usize column", usize::MAX),
            ("duplicate column", good.column_indices[1]),
            ("reversed column order", good.column_indices[2]),
        ] {
            let mut bad = good.clone();
            bad.column_indices[0] = col;
            cases.push((label, bad));
        }

        for (label, offset) in [
            ("empty row", 0_usize),
            ("short row", 2),
            ("long row", 4),
            ("overflow-sized offset", usize::MAX),
        ] {
            let mut bad = good.clone();
            bad.row_offsets[1] = offset;
            cases.push((label, bad));
        }

        let mut nonzero_start = good.clone();
        nonzero_start.row_offsets[0] = 1;
        cases.push(("nonzero starting offset", nonzero_start));

        let mut missing_sign = good.clone();
        missing_sign.signs.pop();
        cases.push(("sign array length mismatch", missing_sign));

        let mut missing_column = good.clone();
        missing_column.column_indices.pop();
        cases.push(("column array length mismatch", missing_column));

        let mut missing_row_offset = good.clone();
        missing_row_offset.row_offsets.pop();
        cases.push(("row-offset count mismatch", missing_row_offset));

        let mut duplicate_row = good.clone();
        duplicate_row.signs[0..3].copy_from_slice(&good.signs[3..6]);
        cases.push(("duplicate signed row", duplicate_row));

        let mut unrepresentable_count = good.clone();
        unrepresentable_count.variables = usize::MAX;
        cases.push(("checked row-count overflow", unrepresentable_count));

        for (label, invalid) in cases {
            let producer = std::panic::catch_unwind(|| invalid.view().recognize_recurrence())
                .unwrap_or_else(|_| panic!("recognizer panicked on {label}"));
            assert!(producer.is_err(), "recognizer accepted {label}");

            let verifier =
                std::panic::catch_unwind(|| verify_recurrence_receipt(invalid.view(), &receipt))
                    .unwrap_or_else(|_| panic!("verifier panicked on {label}"));
            assert!(verifier.is_err(), "verifier accepted {label}");
        }
    }

    #[test]
    fn signed_row_falsifying_bits_are_the_negated_literals() {
        let good = OwnedSignedCsr::from_cnf(&source(4, &[false]));
        for row in good.row_offsets.windows(2) {
            let signs = &good.signs[row[0]..row[1]];
            for word in 0u8..8 {
                let bits = std::array::from_fn::<_, 3, _>(|i| word & (1 << i) != 0);
                let clause_true = signs
                    .iter()
                    .enumerate()
                    .any(|(i, sign)| bits[i] == (*sign == 1));
                let falsifying_word = signs
                    .iter()
                    .enumerate()
                    .all(|(i, sign)| bits[i] == (*sign == -1));
                assert_eq!(clause_true, !falsifying_word);
            }
        }
    }

    /// Any change to a canonical CSR row boundary must refuse, even when the
    /// replacement remains within the flattened literal arrays. This tests
    /// both adjacent row widths, not only the first offset or a huge sentinel.
    #[test]
    fn all_modified_row_offsets_refuse_without_panicking() {
        for n in [4_usize, 6, 8] {
            let rhs = vec![false; n - 3];
            let good = OwnedSignedCsr::from_cnf(&source(n, &rhs));
            let receipt = good.view().recognize_recurrence().unwrap();
            let nnz = good.column_indices.len();

            for index in 0..good.row_offsets.len() {
                let original = good.row_offsets[index];
                for altered in [
                    0,
                    nnz,
                    usize::MAX,
                    original.saturating_sub(1),
                    original.saturating_add(1),
                ] {
                    if altered == original {
                        continue;
                    }
                    let mut corrupted = good.clone();
                    corrupted.row_offsets[index] = altered;

                    let recognizer =
                        std::panic::catch_unwind(|| corrupted.view().recognize_recurrence())
                            .expect("recognizer panicked on an altered CSR row offset");
                    assert!(
                        recognizer.is_err(),
                        "accepted n={n} offset[{index}]={altered}"
                    );

                    let replay = std::panic::catch_unwind(|| {
                        verify_recurrence_receipt(corrupted.view(), &receipt)
                    })
                    .expect("receipt verifier panicked on an altered CSR row offset");
                    assert!(
                        replay.is_err(),
                        "replay accepted n={n} offset[{index}]={altered}"
                    );
                }
            }
        }
    }

    /// Row-set semantics must not accidentally depend on serialization
    /// order. A duplicate exact signed row must refuse even when lengths
    /// and row widths are unchanged.
    #[test]
    fn row_permutations_preserve_receipts_and_duplicates_refuse() {
        for n in [4_usize, 5, 8, 12] {
            let rhs = (0..n - 3).map(|i| i % 2 != 0).collect::<Vec<_>>();
            let base = OwnedSignedCsr::from_cnf(&source(n, &rhs));
            let expected = base.view().recognize_recurrence().unwrap();
            let rows = base
                .row_offsets
                .windows(2)
                .map(|span| {
                    (
                        base.column_indices[span[0]..span[1]].to_vec(),
                        base.signs[span[0]..span[1]].to_vec(),
                    )
                })
                .collect::<Vec<_>>();

            for shift in [0, 1, rows.len() / 2, rows.len() - 1] {
                let mut reordered = rows.clone();
                reordered.rotate_left(shift);
                if shift % 2 != 0 {
                    reordered.reverse();
                }
                let mut csr = OwnedSignedCsr {
                    variables: n,
                    row_offsets: vec![0],
                    column_indices: Vec::new(),
                    signs: Vec::new(),
                };
                for (columns, signs) in reordered {
                    csr.column_indices.extend(columns);
                    csr.signs.extend(signs);
                    csr.row_offsets.push(csr.column_indices.len());
                }
                assert_eq!(csr.view().recognize_recurrence(), Ok(expected.clone()));
                assert_eq!(
                    verify_recurrence_receipt(csr.view(), &expected),
                    Ok(expected.count())
                );
            }

            let mut duplicate = base.clone();
            let a = duplicate.row_offsets[0];
            let b = duplicate.row_offsets[1];
            let c = duplicate.row_offsets[2];
            assert_eq!(b - a, 3);
            assert_eq!(c - b, 3);
            duplicate.column_indices[b..c].copy_from_slice(&base.column_indices[a..b]);
            duplicate.signs[b..c].copy_from_slice(&base.signs[a..b]);
            assert!(duplicate.view().recognize_recurrence().is_err());
            assert!(verify_recurrence_receipt(duplicate.view(), &expected).is_err());
        }
    }

    /// Independent per-row oracle: checked *individual* array lookups,
    /// not the production decoder's range slicing and array conversions.
    /// It is deliberately callable on malformed and truncated CSR arrays.
    fn reference_checked_row(csr: SignedCsr<'_>, row: usize) -> Option<CheckedCsrRow> {
        let start = *csr.row_offsets.get(row)?;
        let stop = *csr.row_offsets.get(row.checked_add(1)?)?;
        if stop != start.checked_add(3)? {
            return None;
        }

        let mut columns = [0; 3];
        let mut signs = [0; 3];
        for i in 0..3 {
            let at = start.checked_add(i)?;
            columns[i] = *csr.column_indices.get(at)?;
            signs[i] = *csr.signs.get(at)?;
        }
        if columns[0] >= columns[1]
            || columns[1] >= columns[2]
            || columns[2] >= csr.variables
            || signs.iter().any(|s| *s != -1 && *s != 1)
        {
            None
        } else {
            Some(CheckedCsrRow { columns, signs })
        }
    }

    /// The concrete shared row reader has no dependence on outer CSR shape:
    /// every checked slice access agrees with independent checked element
    /// reads, including malformed offsets and extreme machine integers.
    #[test]
    fn checked_row_matches_independent_indexed_model() {
        let cases = [4_usize, 5, 8];
        for n in cases {
            let rhs = vec![false; n - 3];
            let source = OwnedSignedCsr::from_cnf(&source(n, &rhs));

            let check = |csr: &OwnedSignedCsr| {
                for row in 0..=csr.row_offsets.len() {
                    assert_eq!(
                        csr.view().checked_row(row),
                        reference_checked_row(csr.view(), row),
                        "row={row}, csr={csr:?}"
                    );
                }
                assert_eq!(
                    csr.view().checked_row(usize::MAX),
                    reference_checked_row(csr.view(), usize::MAX)
                );
            };
            check(&source);

            for index in 0..source.row_offsets.len() {
                for value in [
                    0,
                    source.column_indices.len(),
                    usize::MAX,
                    source.row_offsets[index].saturating_sub(1),
                    source.row_offsets[index].saturating_add(1),
                ] {
                    let mut changed = source.clone();
                    changed.row_offsets[index] = value;
                    check(&changed);
                }
            }
            for index in 0..source.column_indices.len() {
                for value in [0, 1, n - 1, n, usize::MAX] {
                    let mut changed = source.clone();
                    changed.column_indices[index] = value;
                    check(&changed);
                }
            }
            for index in 0..source.signs.len() {
                for value in [-2, -1, 0, 1, 2, i8::MIN, i8::MAX] {
                    let mut changed = source.clone();
                    changed.signs[index] = value;
                    check(&changed);
                }
            }
            let mut shortened = source.clone();
            shortened.signs.pop();
            check(&shortened);
            let mut shortened = source.clone();
            shortened.column_indices.pop();
            check(&shortened);
            let mut shortened = source.clone();
            shortened.row_offsets.pop();
            check(&shortened);
        }
    }

    /// A second, test-only decoder of Lean's signed-CSR *input* semantics.
    /// This deliberately does not call either the Rust recognizer or receipt
    /// verifier. It keeps duplicate rows, malformed widths, missing elements,
    /// and out-of-range columns observable as an Option refusal.
    fn model_signed_csr_rows(
        csr: SignedCsr<'_>,
    ) -> Option<std::collections::BTreeSet<([usize; 3], [i8; 3])>> {
        use std::collections::BTreeSet;

        if csr.variables < 4 {
            return None;
        }
        let rows = csr.variables.checked_mul(5)?.checked_sub(14)?;
        if csr.row_offsets.len() != rows.checked_add(1)?
            || csr.column_indices.len() != csr.signs.len()
            || csr.row_offsets.first().copied() != Some(0)
            || csr.row_offsets.get(rows).copied() != Some(csr.column_indices.len())
        {
            return None;
        }

        let mut decoded = BTreeSet::new();
        for i in 0..rows {
            let start = *csr.row_offsets.get(i)?;
            let stop = *csr.row_offsets.get(i + 1)?;
            if stop != start.checked_add(3)? {
                return None;
            }
            let columns = [
                *csr.column_indices.get(start)?,
                *csr.column_indices.get(start.checked_add(1)?)?,
                *csr.column_indices.get(start.checked_add(2)?)?,
            ];
            let signs = [
                *csr.signs.get(start)?,
                *csr.signs.get(start.checked_add(1)?)?,
                *csr.signs.get(start.checked_add(2)?)?,
            ];
            if columns[0] >= columns[1]
                || columns[1] >= columns[2]
                || columns[2] >= csr.variables
                || signs.iter().any(|s| *s != -1 && *s != 1)
                || !decoded.insert((columns, signs))
            {
                return None;
            }
        }
        Some(decoded)
    }

    /// On the actual Rust execution path, acceptance of an independent
    /// receipt must imply *complete* equality with the separately decoded
    /// source rows. Systematic mutations test both acceptance and refusal.
    /// This is differential implementation evidence, not formal refinement.
    #[test]
    fn receipt_execution_agrees_with_independent_csr_decoder() {
        for n in [4_usize, 5, 8] {
            let rhs = (0..n - 3).map(|i| i % 2 == 0).collect::<Vec<_>>();
            let original = OwnedSignedCsr::from_cnf(&source(n, &rhs));
            let receipt = original.view().recognize_recurrence().unwrap();
            let expected = model_signed_csr_rows(original.view()).unwrap();

            let agrees = |case: &OwnedSignedCsr| {
                let decoded = model_signed_csr_rows(case.view());
                let should_accept = decoded.as_ref() == Some(&expected);
                let actual = verify_recurrence_receipt(case.view(), &receipt);
                assert_eq!(
                    actual.is_ok(),
                    should_accept,
                    "independent CSR model disagrees for n={n}, case={case:?}"
                );
                if should_accept {
                    assert_eq!(actual, Ok(receipt.count()));
                }
            };
            agrees(&original);

            let nnz = original.column_indices.len();
            for index in 0..original.row_offsets.len() {
                for value in [
                    0,
                    nnz,
                    usize::MAX,
                    original.row_offsets[index].saturating_sub(1),
                    original.row_offsets[index].saturating_add(1),
                ] {
                    let mut case = original.clone();
                    case.row_offsets[index] = value;
                    agrees(&case);
                }
            }

            for index in 0..original.column_indices.len() {
                for value in [0, 1, n - 1, n, usize::MAX] {
                    let mut case = original.clone();
                    case.column_indices[index] = value;
                    agrees(&case);
                }
            }

            for index in 0..original.signs.len() {
                for value in [-2, -1, 0, 1, 2, i8::MIN, i8::MAX] {
                    let mut case = original.clone();
                    case.signs[index] = value;
                    agrees(&case);
                }
            }
        }
    }

    /// The source-to-CSR adapter preserves every canonical literal row.
    /// This covers empty, unary, ternary, long, mixed-polarity, tautological,
    /// and duplicate source clauses. Cnf's canonical set normalization is
    /// performed before encoding; no claim is made about raw DIMACS parsing.
    #[test]
    fn canonical_cnf_survives_csr_encoding_and_reconstruction() {
        use crate::{Clause, Literal};

        for n in [4_usize, 8, 16] {
            let mut clauses = vec![
                Clause::new(Vec::new()),
                Clause::new(vec![Literal {
                    variable: n - 1,
                    positive: false,
                }]),
                Clause::new(vec![
                    Literal {
                        variable: n - 1,
                        positive: true,
                    },
                    Literal {
                        variable: 0,
                        positive: false,
                    },
                    Literal {
                        variable: 0,
                        positive: true,
                    },
                ]),
            ];
            for row in 0..n {
                let signed = (0..=row)
                    .map(|j| Literal {
                        variable: j,
                        positive: (j + row) % 2 == 0,
                    })
                    .collect::<Vec<_>>();
                clauses.push(Clause::new(signed));
            }
            clauses.push(clauses[1].clone());

            let source = Cnf::new(n, clauses).unwrap();
            let encoded = OwnedSignedCsr::from_cnf(&source);
            assert_eq!(encoded.variables, source.variables());
            assert_eq!(encoded.row_offsets.len(), source.clauses().len() + 1);
            assert_eq!(encoded.row_offsets.first(), Some(&0));
            assert_eq!(
                encoded.row_offsets.last(),
                Some(&encoded.column_indices.len())
            );
            assert_eq!(encoded.column_indices.len(), encoded.signs.len());

            let restored_rows = encoded
                .row_offsets
                .windows(2)
                .map(|window| {
                    let literals = (window[0]..window[1])
                        .map(|i| {
                            let polarity = encoded.signs[i];
                            assert!(polarity == -1 || polarity == 1);
                            Literal {
                                variable: encoded.column_indices[i],
                                positive: polarity == 1,
                            }
                        })
                        .collect::<Vec<_>>();
                    Clause::new(literals)
                })
                .collect::<Vec<_>>();
            let restored = Cnf::new(encoded.variables, restored_rows).unwrap();
            assert_eq!(restored, source);
        }
    }

    /// Preserve the verifier's source-assignment semantics after changing
    /// its traversal from raw CSR row order to a validated BTreeSet.
    /// This compares the former literal-index implementation to the new
    /// signed-row set evaluation on every small complete Boolean word.
    #[test]
    fn validated_row_set_preserves_source_clause_truth_tables() {
        use std::collections::BTreeSet;

        for n in 4_usize..=8 {
            let rhs = (0..n - 3).map(|i| i % 2 == 0).collect::<Vec<_>>();
            let encoded = OwnedSignedCsr::from_cnf(&source(n, &rhs));
            let csr = encoded.view();
            let rows = (0..csr.row_offsets.len() - 1)
                .map(|i| {
                    let row = csr.checked_row(i).unwrap();
                    (row.columns, row.signs)
                })
                .collect::<BTreeSet<_>>();

            for mask in 0..(1_usize << n) {
                let x = (0..n).map(|i| mask & (1 << i) != 0).collect::<Vec<_>>();
                let direct = csr.row_offsets.windows(2).all(|bounds| {
                    (bounds[0]..bounds[1]).any(|p| x[csr.column_indices[p]] == (csr.signs[p] == 1))
                });
                let decoded = rows.iter().all(|(columns, signs)| {
                    columns
                        .iter()
                        .zip(signs.iter())
                        .any(|(&column, &sign)| x.get(column).copied() == Some(sign == 1))
                });
                assert_eq!(decoded, direct, "word mask={mask}, variable count={n}");
            }
        }
    }

    #[test]
    fn fixed_lean_csr_vector_matches_rust_encoding() {
        // The same six complete clauses and all arrays are kernel-checked
        // by smallHomogeneousCsr in IndependentNonAffineRecurrence.lean.
        let cnf = source(4, &[false]);
        let csr = OwnedSignedCsr::from_cnf(&cnf);
        assert_eq!(csr.variables, 4);
        assert_eq!(csr.row_offsets, [0, 3, 6, 9, 12, 15, 18]);
        assert_eq!(
            csr.column_indices,
            [0, 1, 3, 0, 1, 3, 0, 1, 3, 0, 1, 2, 0, 1, 3, 1, 2, 3]
        );
        assert_eq!(
            csr.signs,
            [-1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1]
        );
        assert_eq!(count_recognized_cnf(&cnf), Ok(7));
        assert_eq!(oracle(4, &cnf), 7);
    }

    #[test]
    fn homogeneous_all_scales() {
        for n in [4, 5, 6, 8, 12, 14, 100, 1000] {
            let cnf = source(n, &vec![false; n - 3]);
            let csr = OwnedSignedCsr::from_cnf(&cnf);
            let receipt = csr.view().recognize_recurrence().unwrap();
            assert_eq!(receipt.rhs, vec![false; n - 3]);
            assert_eq!(receipt.forbidden_seeds, 1);
            assert_eq!(receipt.count(), 7);
            assert_eq!(csr.row_offsets.len(), 5 * n - 13);
            if n <= 14 {
                assert_eq!(oracle(n, &cnf), receipt.count());
            }
        }
    }

    #[test]
    fn public_count_replays_source_certificate() {
        for n in [4, 8, 12, 1000] {
            let rhs = (0..n - 3).map(|i| i % 3 == 0).collect::<Vec<_>>();
            let cnf = source(n, &rhs);
            let expected = recognize_cnf(&cnf).unwrap().count();
            assert_eq!(count_recognized_cnf(&cnf), Ok(expected));
            if n <= 12 {
                assert_eq!(expected, oracle(n, &cnf));
            }
        }

        let rows = [vec![1_i64, 2, 3]];
        let refs = rows.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let unsupported = Cnf::from_signed(4, &refs).unwrap();
        assert!(count_recognized_cnf(&unsupported).is_err());
    }

    #[test]
    fn inhomogeneous_exhaustive_rhs_small() {
        // Every RHS for n <= 8; compare against an independent full CNF
        // evaluator, rather than the recurrence used by the recognizer.
        for n in 4..=8 {
            for mask in 0..(1usize << (n - 3)) {
                let rhs = (0..n - 3).map(|i| mask & (1 << i) != 0).collect::<Vec<_>>();
                let cnf = source(n, &rhs);
                let receipt = recognize_cnf(&cnf).unwrap();
                assert_eq!(receipt.rhs, rhs);
                assert_eq!(receipt.count(), oracle(n, &cnf));
            }
        }
    }

    #[test]
    fn malformed_or_incomplete_refused() {
        let n = 8;
        let cnf = source(n, &vec![false; n - 3]);
        let good = OwnedSignedCsr::from_cnf(&cnf);

        let mut missing = good.clone();
        let start = missing.row_offsets[0];
        let end = missing.row_offsets[1];
        missing.column_indices.drain(start..end);
        missing.signs.drain(start..end);
        missing.row_offsets.remove(1);
        for offset in &mut missing.row_offsets[1..] {
            *offset -= end - start;
        }
        assert!(missing.view().recognize_recurrence().is_err());

        let mut wrong_sign = good.clone();
        wrong_sign.signs[0] = 0;
        assert!(wrong_sign.view().recognize_recurrence().is_err());

        let mut wrong_col = good.clone();
        wrong_col.column_indices[0] = n;
        assert!(wrong_col.view().recognize_recurrence().is_err());

        let mut duplicate = good.clone();
        let a = duplicate.row_offsets[0];
        let b = duplicate.row_offsets[1];
        duplicate.column_indices[a + 1] = duplicate.column_indices[a];
        assert!(duplicate.view().recognize_recurrence().is_err());
        assert_eq!(b - a, 3);

        let mut bad_offset = good.clone();
        bad_offset.row_offsets[2] = usize::MAX;
        assert!(bad_offset.view().recognize_recurrence().is_err());

        let mut wrong_polarity = good.clone();
        wrong_polarity.signs[0] *= -1;
        assert!(wrong_polarity.view().recognize_recurrence().is_err());
    }

    #[test]
    fn extra_and_wrong_clause_refused() {
        let n = 6;
        let mut rows = source(n, &vec![false; n - 3])
            .clauses()
            .iter()
            .map(|c| {
                c.literals()
                    .iter()
                    .map(|l| {
                        if l.positive {
                            l.variable as i64 + 1
                        } else {
                            -(l.variable as i64 + 1)
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        rows.push(vec![1, 4, 6]);
        let refs = rows.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let invalid = Cnf::from_signed(n, &refs).unwrap();
        assert!(recognize_cnf(&invalid).is_err());
    }
    #[test]
    fn independent_receipt_replay_and_tampering() {
        for n in [4, 6, 8, 12, 1000] {
            let rhs = (0..n - 3).map(|i| i % 3 == 0).collect::<Vec<_>>();
            let cnf = source(n, &rhs);
            let csr = OwnedSignedCsr::from_cnf(&cnf);
            let receipt = csr.view().recognize_recurrence().unwrap();
            assert_eq!(
                verify_recurrence_receipt(csr.view(), &receipt),
                Ok(receipt.count())
            );

            let mut bad_mask = receipt.clone();
            bad_mask.forbidden_seeds ^= 1;
            assert!(verify_recurrence_receipt(csr.view(), &bad_mask).is_err());

            let mut bad_rhs = receipt.clone();
            bad_rhs.rhs[0] = !bad_rhs.rhs[0];
            assert!(verify_recurrence_receipt(csr.view(), &bad_rhs).is_err());

            let mut bad_csr = csr.clone();
            bad_csr.signs[0] *= -1;
            assert!(verify_recurrence_receipt(bad_csr.view(), &receipt).is_err());
        }
    }

    #[test]
    fn verifier_rejects_bad_offsets_and_row_permutations_do_not_matter() {
        let cnf = source(8, &[true, false, true, false, true]);
        let original = OwnedSignedCsr::from_cnf(&cnf);
        let receipt = original.view().recognize_recurrence().unwrap();

        let mut reversed_rows = original.clone();
        let chunks = original
            .row_offsets
            .windows(2)
            .map(|v| {
                (
                    original.column_indices[v[0]..v[1]].to_vec(),
                    original.signs[v[0]..v[1]].to_vec(),
                )
            })
            .rev()
            .collect::<Vec<_>>();
        reversed_rows.column_indices.clear();
        reversed_rows.signs.clear();
        reversed_rows.row_offsets.clear();
        reversed_rows.row_offsets.push(0);
        for (cols, signs) in chunks {
            reversed_rows.column_indices.extend(cols);
            reversed_rows.signs.extend(signs);
            reversed_rows.row_offsets.push(reversed_rows.signs.len());
        }
        assert_eq!(
            verify_recurrence_receipt(reversed_rows.view(), &receipt),
            Ok(receipt.count())
        );

        let mut bad_offset = original.clone();
        bad_offset.row_offsets[1] = usize::MAX;
        assert!(verify_recurrence_receipt(bad_offset.view(), &receipt).is_err());
    }
}
