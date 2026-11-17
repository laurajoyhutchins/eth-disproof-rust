//! Source-defined *preparation* for the signed difference-pair accumulator.
//!
//! Pinned to `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! - `SqrtLogSpace/QueryAssembler.lean` (`pairScratch`, `clearPair`, `preparePair`)
//! - `SqrtLogSpace/FactorEnvironment.lean` (`registerMap`, `pairs`, `bootstrap`)
//! - `SqrtLogSpace/QueryTupleVisitor.lean` (`overwrite`)
//! - `SubexpSetupStorage.lean` (`clearMany`, `copyMany`)
//!
//! This is deliberately NOT `QueryAssembler.commitPair`. The signed
//! `pairUpdate` is absent, and these commands do not alter accumulator 850.
//! No semantic arithmetic, host-side pair counting, or signed result is used.

use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_high::{clear_program, copy_program};

/// `QueryAssembler.pairScratch`: 56 low arithmetic words, 28 normalization
/// words, and four additional temporary ports, in the original source order.
pub const PAIR_SCRATCH: [usize; 88] = {
    let mut ports = [0; 88];
    let mut i = 0;
    while i < 56 {
        ports[i] = i;
        i += 1;
    }
    while i < 84 {
        ports[i] = 100 + i - 56;
        i += 1;
    }
    ports[84] = 159;
    ports[85] = 841;
    ports[86] = 848;
    ports[87] = 849;
    ports
};

/// `FactorEnvironment.pairs`: master cache -> arithmetic workspace.
pub const CACHE_PAIRS: [(usize, usize); 7] = [
    (194, 5),
    (202, 12),
    (203, 17),
    (201, 22),
    (204, 39),
    (212, 45),
    (243, 46),
];

fn clear_many(ports: &[usize]) -> Result<Cmd<16, 896>, Error> {
    let mut tail = Cmd::Skip;
    for &port in ports.iter().rev() {
        tail = Cmd::seq(Cmd::Call(clear_program(port, 0, 1)?), tail);
    }
    Ok(tail)
}

fn copy_many() -> Result<Cmd<16, 896>, Error> {
    let mut tail = Cmd::Skip;
    for &(src, dst) in CACHE_PAIRS.iter().rev() {
        tail = Cmd::seq(Cmd::Call(copy_program(src, dst, 159, 0, 1)?), tail);
    }
    Ok(tail)
}

/// Source `FactorEnvironment.registerMap = Fin.castAdd 24` extends the type
/// bound, *without shifting the register indices*: local registers 0..15
/// still map to caller registers 0..15. All stack indices are unchanged.
fn lifted(command: Cmd<16, 896>, input: usize, output: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(
        command
            .compiled(input, output)?
            .lift::<40, 896>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    ))
}

/// Literal `QueryAssembler.clearPair`, one lifted compiled call. The final
/// `.base .skip` is retained from the original `clearMany` recursion.
pub fn clear_pair_command() -> Result<Cmd<40, 896>, Error> {
    lifted(clear_many(&PAIR_SCRATCH)?, 0, 0)
}

/// Literal `FactorEnvironment.bootstrap`: seven preserving copies using
/// scratch 159, which must initially be empty (as enforced by `clearPair`).
pub fn bootstrap_environment_command() -> Result<Cmd<40, 896>, Error> {
    lifted(copy_many()?, 194, 5)
}

/// Original `QueryTupleVisitor.overwrite 211 34`, with scratch 841 empty.
/// Unlike a mere copy, this clears the previous destination first.
fn overwrite_scale_word() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(34, 0, 1)?),
        Cmd::Call(copy_program(211, 34, 841, 0, 1)?),
    ))
}

/// Complete original `QueryAssembler.preparePair`:
/// clearPair ; FactorEnvironment.bootstrap ; overwrite 211 34.
///
/// This prepares the physical arithmetic environment, but the subsequent
/// signed `pairUpdate` and final clear remain outstanding. It must not be
/// exposed as the complete production pair callback.
pub fn prepare_pair_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear_pair_command()?,
        Cmd::seq(bootstrap_environment_command()?, overwrite_scale_word()?),
    ))
}

pub fn prepare_pair_program() -> Result<Program<40, 896>, Error> {
    prepare_pair_command()?.compiled(851, 850)
}
