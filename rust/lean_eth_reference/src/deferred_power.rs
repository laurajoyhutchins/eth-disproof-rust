//! Experimental, non-literal representation of `LayoutProgram.powerCommand`.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! `SqrtLogSpace/LayoutProgramPower.lean`. The unchanged interpreter in
//! `native_integer_cache::power_program` remains the correctness oracle.
//!
//! A power is carried as an exponent until a consumer actually requires
//! the source little-endian bit stack. This is NOT a source instruction port:
//! symbolic and physical states have different representations and costs.

use std::collections::VecDeque;

use crate::Error;
use crate::bit_program::Config;

/// The exact nonnegative integer `2^exponent`, without its zero-filled word.
/// Construction from a binary exponent is O(1); obtaining the exponent from
/// an existing unary input does not eliminate the cost of that input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeferredPower {
    exponent: usize,
}

impl DeferredPower {
    pub fn new(exponent: usize) -> Self {
        Self { exponent }
    }

    pub fn exponent(self) -> usize {
        self.exponent
    }

    /// The source layout has `exponent` zeros followed by one true bit.
    pub fn source_word_bits(self) -> Result<usize, Error> {
        self.exponent.checked_add(1).ok_or(Error::Overflow)
    }

    /// Read any source-word bit without building the intervening zeros.
    pub fn bit(self, position: usize) -> bool {
        position == self.exponent
    }

    /// Exact multiplication of powers without constructing either word.
    pub fn checked_mul(self, other: Self) -> Result<Self, Error> {
        Ok(Self::new(
            self.exponent
                .checked_add(other.exponent)
                .ok_or(Error::Overflow)?,
        ))
    }

    /// `IntegerCache.makePower`: one element of the copied unary length is
    /// removed before `powerCommand` runs. The source treats an empty word
    /// as exponent zero. This only describes the produced power, not the
    /// complete physical `makePower` stack/register effects.
    pub fn from_make_power_input_len(input_len: usize) -> Self {
        Self::new(input_len.saturating_sub(1))
    }

    /// Materialize the original output prefix, *prepending* to any existing
    /// destination suffix. A denied capacity request changes no state.
    pub fn prepend_to(
        self,
        destination: &mut VecDeque<bool>,
        max_total_bits: usize,
    ) -> Result<(), Error> {
        let needed = self
            .source_word_bits()?
            .checked_add(destination.len())
            .ok_or(Error::Overflow)?;
        if needed > max_total_bits {
            return Err(Error::Capacity("deferred power output limit".into()));
        }
        destination.push_front(true);
        for _ in 0..self.exponent {
            destination.push_front(false);
        }
        Ok(())
    }
}

/// Testable semantic shortcut for the *complete* standalone two-register,
/// two-stack power program. Matches final machine state, not intermediate
/// instructions or source-step counts. In a future optimized caller, retain
/// the deferred representation instead of invoking this materializer.
///
/// Source `Pop` observes input length, not its bit values. Both registers
/// are false after the final failed pop. Preserve the dirty output suffix.
/// On capacity refusal, leave the entire configuration untouched.
pub fn finish_standalone_power(
    config: &mut Config<2, 2>,
    max_stack_bits: usize,
) -> Result<(), Error> {
    let power = DeferredPower::new(config.stacks[0].len());
    let required = power
        .source_word_bits()?
        .checked_add(config.stacks[1].len())
        .ok_or(Error::Overflow)?;
    if required > max_stack_bits {
        return Err(Error::Capacity("deferred source power stack limit".into()));
    }
    config.stacks[0].clear();
    power.prepend_to(&mut config.stacks[1], max_stack_bits)?;
    config.regs = [false; 2];
    config.pc = None;
    Ok(())
}
