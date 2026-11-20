//! Isolated, source-identical frontend for Charon/Aeneas extraction.
//!
//! The implementation is included from the actual running affine
//! checker's module. The public function makes it reachable by Charon.
//! Passing a Rust build or extracting an LLBC file is NOT by itself
//! a source-level Lean refinement theorem.
#![allow(dead_code)]

#[path = "../../../src/checked_toggle.rs"]
mod checked_toggle;

/// Exact operational Rust function used by the real checker.
pub fn checked_flip(row: &mut [bool], proposed: usize) -> Result<(), &'static str> {
    checked_toggle::flip_checked(row, proposed)
}

#[cfg(test)]
mod tests {
    use super::checked_flip;

    #[test]
    fn source_is_reused_and_refusals_are_atomic() {
        let mut x = [true, false, true];
        assert!(checked_flip(&mut x, 1).is_ok());
        assert_eq!(x, [true, true, true]);
        assert!(checked_flip(&mut x, usize::MAX).is_err());
        assert_eq!(x, [true, true, true]);
    }
}
