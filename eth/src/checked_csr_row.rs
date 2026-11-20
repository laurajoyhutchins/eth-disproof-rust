//! Exact source of the production signed-CSR row decoder.
//!
//! This module deliberately has no dependencies on Cnf, recurrence groups,
//! BTreeMap or BTreeSet. The production recognizer and independent receipt
//! verifier call this function, while a separate Charon/Aeneas verification
//! crate imports **this same file** through #[path]. Extraction failure is
//! an unsupported result, never a substitute model or an accepted proof.

/// The result of decoding exactly three valid signed literals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CheckedCsrRow {
    pub(crate) columns: [usize; 3],
    pub(crate) signs: [i8; 3],
}

/// Decode one row of the *actual* CSR arrays, failing closed on every
/// malformed width, offset, column or sign. All indexing is checked;
/// notably row+1 and start+3 cannot wrap usize.
pub(crate) fn checked_row(
    row_offsets: &[usize],
    column_indices: &[usize],
    signs: &[i8],
    variables: usize,
    row: usize,
) -> Option<CheckedCsrRow> {
    let start = *row_offsets.get(row)?;
    let stop = *row_offsets.get(row.checked_add(1)?)?;
    if start.checked_add(3)? != stop {
        return None;
    }
    let columns: [usize; 3] = column_indices.get(start..stop)?.try_into().ok()?;
    let signs: [i8; 3] = signs.get(start..stop)?.try_into().ok()?;
    if columns[0] >= columns[1]
        || columns[1] >= columns[2]
        || columns[2] >= variables
        || !signs.iter().all(|s| *s == -1 || *s == 1)
    {
        return None;
    }
    Some(CheckedCsrRow { columns, signs })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standalone_boundary_refuses_malformed_rows() {
        let columns = [0, 1, 2];
        let signs = [1, -1, 1];
        assert_eq!(
            checked_row(&[0, 3], &columns, &signs, 4, 0),
            Some(CheckedCsrRow { columns, signs })
        );
        for stop in [0, 1, 2, 4, usize::MAX] {
            assert_eq!(checked_row(&[0, stop], &columns, &signs, 4, 0), None);
        }
        assert_eq!(checked_row(&[0, 3], &columns, &signs, 4, usize::MAX), None);
        assert_eq!(checked_row(&[usize::MAX, 3], &columns, &signs, 4, 0), None);
    }
}
