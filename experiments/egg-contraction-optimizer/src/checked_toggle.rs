//! The real Rust coefficient-mutation primitive, isolated so Kani can
//! check its machine semantics without compiling the entire egg crate.
//!
//! An earlier whole-crate Kani harness proved short-row refusal, but the
//! symbolic string-comparison harness spent the remaining 15-minute
//! budget unwinding CBMC's memcmp model. Name/index matching is checked
//! separately in Rust and proved at the abstract level in Lean.
//! This file isolates the actual bounds-checked mutable slice operation.

/// Flip precisely one bit when the proposed position exists. Refusal
/// happens before any write; an invalid index leaves the row unchanged.
pub(crate) fn flip_checked(
    row: &mut [bool],
    proposed: usize,
) -> Result<(), &'static str> {
    let bit = row.get_mut(proposed)
        .ok_or("checker matrix column outside allocated row")?;
    *bit = !*bit;
    Ok(())
}

#[cfg(kani)]
mod verification {
    use super::flip_checked;

    /// Covers every u8 candidate index and every four-bit input row.
    /// The fourth coordinate represents an RHS slot; it is not a source
    /// coefficient in the enclosing verifier, so this inner primitive
    /// only proves index/bit mutation, not the name/admission boundary.
    #[kani::proof]
    fn one_flip_or_atomic_refusal() {
        let raw: u8 = kani::any();
        let before = [
            kani::any::<bool>(),
            kani::any::<bool>(),
            kani::any::<bool>(),
            kani::any::<bool>(),
        ];
        let mut after = before;
        let result = flip_checked(&mut after, usize::from(raw));
        assert_eq!(result.is_ok(), raw < 4);
        for col in 0..4usize {
            let expected = if col == usize::from(raw) {
                !before[col]
            } else {
                before[col]
            };
            if result.is_ok() {
                assert_eq!(after[col], expected);
            } else {
                assert_eq!(after[col], before[col]);
            }
        }
    }

    /// Empty and truncated rows must refuse every absent index without
    /// mutating any surviving bit.
    #[kani::proof]
    fn truncated_rows_refuse_atomically() {
        let before = [kani::any::<bool>()];
        let mut after = before;
        let result = flip_checked(&mut after, 1);
        assert!(result.is_err());
        assert_eq!(after, before);
        let empty: [bool; 0] = [];
        let mut empty_after = empty;
        assert!(flip_checked(&mut empty_after, 0).is_err());
    }
}

// The same file is compiled directly with "kani src/checked_toggle.rs"
// and as a module of the running verifier. The entrypoint does no work:
// the #[kani::proof] harnesses, not main, supply symbolic executions.
#[cfg(kani)]
fn main() {}
