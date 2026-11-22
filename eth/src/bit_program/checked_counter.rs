//! The production checked BitProgram live-cell counter, isolated for source
//! extraction with the same pinned Charon/Aeneas pipeline already used for
//! the affine checked-slice primitive.
//!
//! This is genuinely called by the flat, deferred, and generated bounded
//! runners. It models *only* scalar preflight, not VecDeque, callbacks,
//! instruction decoding, allocation, or the original source table.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterAction {
    Push,
    PopNonempty,
    Unchanged,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterOutcome {
    Allowed(usize),
    Capacity,
    Overflow,
}

/// All fallible scalar checks are completed before the caller mutates its
/// program state. A Push at the physical cap is a logical refusal; a
/// nonempty Pop with zero cached cells is an invariant violation and is
/// reported as overflow rather than wrapping or panicking.
pub fn checked_live_bit_step(
    action: CounterAction,
    cached: usize,
    limit: usize,
) -> CounterOutcome {
    match action {
        CounterAction::Push => {
            if cached >= limit {
                CounterOutcome::Capacity
            } else {
                match cached.checked_add(1) {
                    Some(next) => CounterOutcome::Allowed(next),
                    None => CounterOutcome::Overflow,
                }
            }
        }
        CounterAction::PopNonempty => match cached.checked_sub(1) {
            Some(next) => CounterOutcome::Allowed(next),
            None => CounterOutcome::Overflow,
        },
        CounterAction::Unchanged => CounterOutcome::Allowed(cached),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_action_cases_and_machine_boundaries() {
        assert_eq!(
            checked_live_bit_step(CounterAction::Push, 0, 0),
            CounterOutcome::Capacity
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::Push, 0, 1),
            CounterOutcome::Allowed(1)
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::Push, usize::MAX - 1, usize::MAX),
            CounterOutcome::Allowed(usize::MAX)
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::Push, usize::MAX, usize::MAX),
            CounterOutcome::Capacity
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::PopNonempty, 0, 0),
            CounterOutcome::Overflow
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::PopNonempty, usize::MAX, 0),
            CounterOutcome::Allowed(usize::MAX - 1)
        );
        assert_eq!(
            checked_live_bit_step(CounterAction::Unchanged, usize::MAX, 0),
            CounterOutcome::Allowed(usize::MAX)
        );
    }
}
