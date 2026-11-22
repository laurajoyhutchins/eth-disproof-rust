//! Source-identical Charon/Aeneas frontend for the production native
//! BitProgram checked live-bit counter. The implementation is the exact file
//! included by the real flat, deferred, and generated runner.
//!
//! Charon extraction is not a theorem about actual native execution; proofs
//! must import the generated Lean declaration and state translator assumptions.
#![allow(dead_code)]

#[path = "../../../src/bit_program/checked_counter.rs"]
pub mod checked_counter;

pub use checked_counter::{CounterAction, CounterOutcome};

/// Make the production source operation explicitly reachable from Charon.
pub fn source_counter_step(action: CounterAction, cached: usize, limit: usize) -> CounterOutcome {
    checked_counter::checked_live_bit_step(action, cached, limit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_operational_source_is_used() {
        assert_eq!(
            source_counter_step(CounterAction::Push, 0, 1),
            CounterOutcome::Allowed(1)
        );
        assert_eq!(
            source_counter_step(CounterAction::PopNonempty, 0, 1),
            CounterOutcome::Overflow
        );
        assert_eq!(
            source_counter_step(CounterAction::Push, usize::MAX, usize::MAX),
            CounterOutcome::Capacity
        );
    }
}
