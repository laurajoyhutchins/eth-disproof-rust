//! Physical native count-word positivity suffix, pinned to
//! openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//!
//! CounterPrograms.zeroProgram (10 labels), CounterForPrograms.testCmd,
//! and SqrtLogSpace/NativeProgram.lean: Native.answerCommand.
//! This consumes no SAT formula and computes no count. It reports whether
//! the *entire* little-endian count word is nonzero, including noncanonical
//! words with leading/trailing zero bits, without changing that word.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::clear_program;

pub const COUNT_STACK: usize = 256;
pub const ANSWER_STACK: usize = 1216;
pub const SCRATCH_STACK: usize = 1217;

/// Exact ten-label source program. The counter is on stack 0, scratch on 1;
/// registers 0/1 hold the popped bit/presence and register 2 returns zero.
pub fn zero_program() -> Result<Program<3, 2>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            Instr::Set {
                dst: 2,
                value: true,
                next: 1,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 2,
            },
            Instr::Branch {
                test: 1,
                yes: 3,
                no: 6,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 4,
            },
            Instr::Not {
                dst: 0,
                src: 0,
                next: 5,
            },
            Instr::And {
                dst: 2,
                left: 2,
                right: 0,
                next: 1,
            },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 7,
            },
            Instr::Branch {
                test: 1,
                yes: 8,
                no: 9,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 6,
            },
            Instr::Halt,
        ],
    )
}

/// Actual fixed-control count positivity test. The zero program returns isZero
/// on register 74 and the source bnot inverts it to 0 < count.
/// Caller must supply an empty scratch stack, as in Native.answerCommand.
pub fn positivity_command() -> Result<Cmd<80, 1220>, Error> {
    let zero =
        Cmd::Call(zero_program()?.lift::<80, 1220>([72, 73, 74], [COUNT_STACK, SCRATCH_STACK])?);
    Ok(Cmd::seq(
        zero,
        Cmd::seq(
            Cmd::Atom(Atom::Not { dst: 74, src: 74 }),
            Cmd::Atom(Atom::Push {
                stack: ANSWER_STACK,
                src: 74,
            }),
        ),
    ))
}

/// The complete executable Native.answerCommand from NativeProgram.lean.
/// First clear stale answer/scratch, then preserve-and-scan every count bit.
pub fn answer_command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(ANSWER_STACK, 72, 73)?),
        Cmd::seq(
            Cmd::Call(clear_program(SCRATCH_STACK, 72, 73)?),
            positivity_command()?,
        ),
    ))
}

pub fn answer_program() -> Result<Program<80, 1220>, Error> {
    answer_command()?.compiled(COUNT_STACK, ANSWER_STACK)
}
