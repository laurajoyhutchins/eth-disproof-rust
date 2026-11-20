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

impl SignedCsr<'_> {
    /// Verify the complete formula, not just some matching XOR/OR subgraph.
    ///
    /// Complexity: O(n log n) comparison work for row grouping, O(n) seed
    /// evaluation, and O(n) extra memory for the receipt and row-group map.
    /// This is a word-operation bound; no whole-machine bit-cost theorem.
    pub fn recognize_recurrence(&self) -> Result<RecurrenceReceipt, Error> {
        let n = self.variables;
        if n < 4 {
            return Err(refuse("requires at least four variables"));
        }
        let expected_rows = n
            .checked_mul(5)
            .and_then(|v| v.checked_sub(14))
            .ok_or(Error::Overflow)?;
        if self.row_offsets.len() != expected_rows.saturating_add(1)
            || self.column_indices.len() != self.signs.len()
            || self.row_offsets.first() != Some(&0)
            || self.row_offsets.last() != Some(&self.column_indices.len())
        {
            return Err(refuse("incorrect matrix shape or CSR offsets"));
        }

        // Group exact rows by their three distinct variable indices; an
        // eight-bit value records which of the eight polarities occur.
        let mut groups: BTreeMap<[usize; 3], u8> = BTreeMap::new();
        for row in self.row_offsets.windows(2) {
            let (start, end) = (row[0], row[1]);
            if end < start || end > self.column_indices.len() || end - start != 3 {
                return Err(refuse("malformed offset or non-ternary clause"));
            }
            let cols = &self.column_indices[start..end];
            let signs = &self.signs[start..end];
            if cols[0] >= cols[1] || cols[1] >= cols[2] || cols[2] >= n {
                return Err(refuse("columns must be strictly sorted and in range"));
            }
            if !signs.iter().all(|sign| *sign == 1 || *sign == -1) {
                return Err(refuse("polarity must be +1 or -1"));
            }
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
        let mut rhs = Vec::with_capacity(n - 3);
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

    let row_count = n
        .checked_mul(5)
        .and_then(|v| v.checked_sub(14))
        .ok_or(Error::Overflow)?;
    if csr.row_offsets.len() != row_count + 1
        || csr.row_offsets.first() != Some(&0)
        || csr.row_offsets.last() != Some(&csr.column_indices.len())
        || csr.column_indices.len() != csr.signs.len()
    {
        return Err(refuse("invalid source offsets or row count"));
    }

    let mut actual = BTreeSet::new();
    for offsets in csr.row_offsets.windows(2) {
        let (start, end) = (offsets[0], offsets[1]);
        if end < start || end > csr.column_indices.len() || end - start != 3 {
            return Err(refuse("invalid source row"));
        }
        let columns: [usize; 3] = csr.column_indices[start..end]
            .try_into()
            .map_err(|_| refuse("not a ternary source row"))?;
        let signs: [i8; 3] = csr.signs[start..end]
            .try_into()
            .map_err(|_| refuse("invalid source sign array"))?;
        if columns[0] >= columns[1]
            || columns[1] >= columns[2]
            || columns[2] >= n
            || !signs.iter().all(|v| *v == -1 || *v == 1)
            || !actual.insert((columns, signs))
        {
            return Err(refuse("noncanonical, duplicated, or out-of-domain row"));
        }
    }
    if actual != expected {
        return Err(refuse("receipt does not describe all source clauses"));
    }

    let mut observed_mask = 0u8;
    for seed in 0..8u8 {
        let mut x = Vec::with_capacity(n);
        x.extend([seed & 1 != 0, seed & 2 != 0, seed & 4 != 0]);
        for (i, rhs) in receipt.rhs.iter().copied().enumerate() {
            x.push(x[i] ^ x[i + 1] ^ rhs);
        }

        // Evaluate the signed CSR directly; parity and OR logic are not
        // reused from the receipt producer.
        let is_satisfied = csr.row_offsets.windows(2).all(|offsets| {
            (offsets[0]..offsets[1]).any(|p| x[csr.column_indices[p]] == (csr.signs[p] == 1))
        });
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
/// shortcut). Returns an error for all unsupported formula structures.
pub fn recognize_cnf(cnf: &Cnf) -> Result<RecurrenceReceipt, Error> {
    OwnedSignedCsr::from_cnf(cnf).view().recognize_recurrence()
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
