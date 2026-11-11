//! Literal pair-sign stage of the original Lean `QueryProgram.pairUpdate`.
//!
//! Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`,
//! `SqrtLogSpace/QueryProgram.lean`: `parityProgram`, `pairSign`,
//! `pairSignProgram`, `pairRegisters`, `pairStacks`, `pairSignCall`.
//!
//! This is a physical parity scan of masks 834/835, not a host-side sign
//! oracle. It produces the one-bit sign on 848 and preserves both masks.
//! `signedAccumulate` and the rest of `pairUpdate` are not implemented here.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::copy_program;

pub const PAIR_SIGN_STACKS: [usize; 4] = [834, 835, 848, 849];
pub const PAIR_SIGN_REGISTERS: [usize; 3] = [0, 1, 2];

/// Source `QueryProgram.parityProgram`, exact four-label finite table.
/// Consumes the source word and XORs every bit into register 2.
pub fn parity_program() -> Result<Program<3, 1>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Instr::Xor {
                dst: 2,
                left: 2,
                right: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

fn scan_call(port: usize) -> Result<Cmd<3, 4>, Error> {
    Ok(Cmd::Call(
        parity_program()?.lift::<3, 4>([0, 1, 2], [port])?,
    ))
}

/// Source `QueryProgram.pairSign`, 3 registers x 4 stacks.
/// Inputs E/U (0/1) are source-preserved. Stack 2 and scratch 3 must be
/// empty on entry. Its exact source cost is 10*(|E|+|U|)+18 steps.
pub fn pair_sign_command() -> Result<Cmd<3, 4>, Error> {
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 2,
            value: false,
        }),
        Cmd::seq(
            Cmd::Call(copy_program(0, 2, 3, 0, 1)?),
            Cmd::seq(
                scan_call(2)?,
                Cmd::seq(
                    Cmd::Call(copy_program(1, 2, 3, 0, 1)?),
                    Cmd::seq(scan_call(2)?, Cmd::Atom(Atom::Push { stack: 2, src: 2 })),
                ),
            ),
        ),
    ))
}

pub fn pair_sign_program() -> Result<Program<3, 4>, Error> {
    pair_sign_command()?.compiled(0, 2)
}

/// Source `QueryProgram.pairSignCall`, one lifted compiled program.
/// The `Fin.castAdd 37` embedding retains indices 0..2: no offset.
pub fn pair_sign_call() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(
        pair_sign_program()?.lift::<40, 896>(PAIR_SIGN_REGISTERS, PAIR_SIGN_STACKS)?,
    ))
}

pub fn pair_sign_call_program() -> Result<Program<40, 896>, Error> {
    pair_sign_call()?.compiled(834, 848)
}
