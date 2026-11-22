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
pub fn checked_live_bit_step(action: CounterAction, cached: usize, limit: usize) -> CounterOutcome {
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

#[cfg(kani)]
mod verification {
    use super::*;

    /// Model-check the *actual production Rust primitive*, with arbitrary
    /// machine-word cached counts and limits and all action constructors.
    /// This is CBMC/Kani evidence under its Rust models, not a Lean theorem.
    #[kani::proof]
    fn checked_counter_exact_for_all_machine_words() {
        let choice: u8 = kani::any();
        let cached: usize = kani::any();
        let limit: usize = kani::any();
        let action = if choice == 0 {
            CounterAction::Push
        } else if choice == 1 {
            CounterAction::PopNonempty
        } else {
            CounterAction::Unchanged
        };
        let actual = checked_live_bit_step(action, cached, limit);
        match action {
            CounterAction::Push => {
                if cached >= limit {
                    assert_eq!(actual, CounterOutcome::Capacity);
                } else {
                    // The machine representability guard is a consequence
                    // of comparing against a representable usize limit.
                    assert!(cached < usize::MAX);
                    assert_eq!(actual, CounterOutcome::Allowed(cached + 1));
                    assert!(cached + 1 <= limit);
                }
            }
            CounterAction::PopNonempty => {
                if cached == 0 {
                    assert_eq!(actual, CounterOutcome::Overflow);
                } else {
                    assert_eq!(actual, CounterOutcome::Allowed(cached - 1));
                }
            }
            CounterAction::Unchanged => {
                assert_eq!(actual, CounterOutcome::Allowed(cached));
            }
        }
    }
}

// Direct invocation by Kani's single-file Rust harness, not a production main.
#[cfg(kani)]
fn main() {}
