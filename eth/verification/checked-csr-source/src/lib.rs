//! Source-identity wrapper for Charon/Aeneas extraction.
//!
//! This crate imports the real production method's implementation without
//! copying its body. Source extraction is evidence only when the LLBC and
//! generated Lean actually contain this function and translation succeeds.
#![allow(dead_code)]

#[path = "../../../src/checked_csr_row.rs"]
mod checked_csr_row;

/// A public, monomorphized, allocation-free entrypoint to the actual
/// checked CSR decoder. The return pair exposes all three columns and signs.
pub fn checked_row_source(
    row_offsets: &[usize],
    column_indices: &[usize],
    signs: &[i8],
    variables: usize,
    row: usize,
) -> Option<([usize; 3], [i8; 3])> {
    checked_csr_row::checked_row(row_offsets, column_indices, signs, variables, row)
        .map(|r| (r.columns, r.signs))
}

#[cfg(test)]
mod tests {
    use super::checked_row_source;

    #[test]
    fn direct_production_source_accepts_and_refuses() {
        let columns = [0, 1, 2];
        let signs = [1, -1, 1];
        assert_eq!(
            checked_row_source(&[0, 3], &columns, &signs, 4, 0),
            Some((columns, signs))
        );
        for offset in [0, 1, 2, 4, usize::MAX] {
            assert_eq!(
                checked_row_source(&[0, offset], &columns, &signs, 4, 0),
                None
            );
        }
        assert_eq!(
            checked_row_source(&[0, 3], &columns, &signs, 4, usize::MAX),
            None
        );
        assert_eq!(
            checked_row_source(&[usize::MAX, 3], &columns, &signs, 4, 0),
            None
        );
        assert_eq!(checked_row_source(&[0, 3], &[0, 0, 2], &signs, 4, 0), None);
        assert_eq!(
            checked_row_source(&[0, 3], &columns, &[1, 0, 1], 4, 0),
            None
        );
        assert_eq!(
            checked_row_source(&[0, 3], &columns[..2], &signs, 4, 0),
            None
        );
    }
}
