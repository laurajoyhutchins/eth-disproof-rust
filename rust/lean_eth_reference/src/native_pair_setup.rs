//! Source-instruction port of the first real pair-controller preparation.
//!
//! Pinned files: `SqrtLogSpace/PairNativeSetup.lean`, `UnaryForPrograms.lean`,
//! `SubexpSetupStorage.lean` at openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! This physically counts *false* high-mask coordinates onto unary stack 832
//! and copies the original parameter word at 243 onto stack 833. It does not
//! execute the signed pair iterator, whose arithmetic is still unported.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};

const SCRATCH: [usize; 5] = [325, 326, 327, 328, 329];

fn clear<const R: usize, const S: usize>(stack: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(stack, 0, 1)?))
}
fn copy<const R: usize, const S: usize>(from: usize, to: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(copy_program(from, to, 329, 0, 1)?))
}
fn clear_many<const R: usize, const S: usize>(ports: &[usize]) -> Result<Cmd<R, S>, Error> {
    let mut command = Cmd::Skip;
    for &stack in ports.iter().rev() {
        command = Cmd::seq(clear(stack)?, command);
    }
    Ok(command)
}
fn reset_work() -> Cmd<16, 896> {
    (0..9).rev().fold(Cmd::Skip, |tail, dst| {
        Cmd::seq(Cmd::Atom(Atom::Set { dst, value: false }), tail)
    })
}

/// `PairNativeSetup.CountFalse.command`, with the original unary iterator
/// and one branch/conditional output push for every consumed mask bit.
pub fn count_false_command() -> Cmd<3, 2> {
    let pop = Cmd::Atom(Atom::Pop {
        stack: 0,
        value: 0,
        present: 1,
    });
    let body = Cmd::ite(0, Cmd::Skip, Cmd::Atom(Atom::Push { stack: 1, src: 2 }));
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 2,
            value: true,
        }),
        Cmd::seq(pop.clone(), Cmd::while_(1, Cmd::seq(body, pop))),
    )
}
pub fn count_false_program() -> Result<Program<3, 2>, Error> {
    count_false_command().compiled(0, 1)
}

/// `SubexpSetupStorage.prepare 329 scratch [(338,325)]`.
fn prepare_count() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        clear_many(&[329])?,
        Cmd::seq(
            clear_many(&SCRATCH)?,
            Cmd::seq(reset_work(), copy(338, 325)?),
        ),
    ))
}

/// `SubexpSetupStorage.finish 329 scratch [(326,832)]`.
fn finish_count() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        clear_many(&[832])?,
        Cmd::seq(
            copy(326, 832)?,
            Cmd::seq(clear_many(&SCRATCH)?, reset_work()),
        ),
    ))
}

/// The exact `SubexpSetupStorage.isolated CountFalse.program` in the 16×896
/// machine. The nested call writes only registers 0..2 and stacks 325/326.
pub fn count_command() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        prepare_count()?,
        Cmd::seq(
            Cmd::Call(count_false_program()?.lift::<16, 896>([0, 1, 2], [325, 326])?),
            finish_count()?,
        ),
    ))
}

/// `PairNativeSetup.setupCommand`: the fixed free-coordinate counter followed
/// by the actual metadata (243→833) copy, with 833–835 cleared first.
pub fn setup_command() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        count_command()?,
        Cmd::seq(clear_many(&[833, 834, 835])?, copy(243, 833)?),
    ))
}

/// `PairNativeSetup.setupCaller`, exactly one lifted compiled call.
pub fn setup_caller_command() -> Result<Cmd<40, 896>, Error> {
    let code = setup_command()?.compiled(338, 832)?;
    Ok(Cmd::Call(code.lift::<40, 896>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

pub fn setup_caller_program() -> Result<Program<40, 896>, Error> {
    setup_caller_command()?.compiled(338, 832)
}

// Reuse the one existing source-defined restriction table, rather than
// maintaining a second copy of this finite program in the pair adapter.
pub use crate::native_query_prefix::{restriction_command, restriction_program};

/// The physical `SubexpSetupStorage.prepare` for one fill. Both input words
/// are preserving-copied into the now-empty scratch bank after the source's
/// nine work-register resets.
fn prepare_fill(is_e: bool) -> Result<Cmd<16, 896>, Error> {
    let input = if is_e { 834 } else { 835 };
    Ok(Cmd::seq(
        clear_many(&[329])?,
        Cmd::seq(
            clear_many(&SCRATCH)?,
            Cmd::seq(reset_work(), Cmd::seq(copy(338, 325)?, copy(input, 327)?)),
        ),
    ))
}

/// Source `SubexpSetupStorage.finish`: overwrite the destination, preserving
/// copy from scratch 328 through empty temporary 329, clear all five work
/// stacks, and reset source work registers 0..8.
fn finish_fill(is_e: bool) -> Result<Cmd<16, 896>, Error> {
    let output = if is_e { 858 } else { 857 };
    Ok(Cmd::seq(
        clear_many(&[output])?,
        Cmd::seq(
            copy(328, output)?,
            Cmd::seq(clear_many(&SCRATCH)?, reset_work()),
        ),
    ))
}

/// `PairNativeSetup.fillCommand isE`: the fully paid isolation boundary.
/// Incoming high/fixed and free-mask words are on source stacks 338 and
/// 834/835 respectively, preserved by the call. Scratch 325..329 returns
/// empty; only selected output 858 (E) or 857 (U) is overwritten.
pub fn fill_command(is_e: bool) -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(
        prepare_fill(is_e)?,
        Cmd::seq(
            Cmd::Call(restriction_program()?.lift::<16, 896>([0, 1, 2, 3], [325, 326, 327, 328])?),
            finish_fill(is_e)?,
        ),
    ))
}

/// `PairNativeSetup.expandCommand`, E followed by U. Input mask 338 and
/// both residual assignment words 834/835 are source-preserved.
pub fn expand_command() -> Result<Cmd<16, 896>, Error> {
    Ok(Cmd::seq(fill_command(true)?, fill_command(false)?))
}

pub fn expand_program() -> Result<Program<16, 896>, Error> {
    expand_command()?.compiled(338, 857)
}

/// Literal source `PairNativeSetup.expandCaller`: a single lifted call of the
/// complete compiled 16×896 program, with the low 16 registers embedded at
/// their identical indexes in the 40×896 caller.
pub fn expand_caller_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(expand_program()?.lift::<40, 896>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

/// Runnable wrapper of the exact caller command. The extra terminal halt
/// belongs to this standalone test harness, not `expandCaller` itself.
pub fn expand_caller_program() -> Result<Program<40, 896>, Error> {
    expand_caller_command()?.compiled(338, 857)
}
