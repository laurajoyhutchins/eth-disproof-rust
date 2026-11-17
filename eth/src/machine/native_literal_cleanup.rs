//! Exact source ExecCleanLiteralsProgram.clean, 13-register/11-stack bank.
//!
//! Pinned original: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! ExecCleanLiteralsProgram.lean, blob 113bb3895170816c4b7e5c6dd3581308e37ba5e3.
//! Physically deduplicates literal fields clause by clause while preserving
//! formula clause order. Tautology removal and absorption are separate stages.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_literal_dedup::dedup_program;
use crate::native_normalization_primitives::{
    clean_literals_reverse_program, emit_if_selected_command,
};
use crate::native_record_membership::frame_program;

/// The exact four-label StackRoutines.transferProgram.
fn transfer(src: usize, dst: usize) -> Result<Program<13, 11>, Error> {
    if src == dst {
        return Err(Error::Invalid("transfer source/destination alias".into()));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Instr::Push {
                stack: dst,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// Original literalProgram with Fin.castAdd 3 identity registers 0..9,
/// and Fin.natAdd 3 shifted work stacks 3..10.
pub fn literal_program() -> Result<Program<13, 11>, Error> {
    dedup_program()?.lift::<13, 11>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8, 9, 10])
}

/// Original physical emitProgram, compiled then lifted into the 13x11 bank.
pub fn emit_program() -> Result<Program<13, 11>, Error> {
    emit_if_selected_command()?
        .compiled(3, 2)?
        .lift::<13, 11>([10, 11, 12], [0, 10, 2, 1])
}

/// Original callback: reverse the framed clause payload onto work port 3,
/// execute complete nested literal dedup, reverse back to payload 1, set
/// selected=12 true and encode the cleaned clause into the output accumulator.
pub fn callback_command() -> Result<Cmd<13, 11>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer(1, 3)?),
        Cmd::seq(
            Cmd::Call(literal_program()?),
            Cmd::seq(
                Cmd::Call(transfer(3, 1)?),
                Cmd::seq(
                    Cmd::Atom(Atom::Set {
                        dst: 12,
                        value: true,
                    }),
                    Cmd::Call(emit_program()?),
                ),
            ),
        ),
    ))
}

/// Exact source RecordPrograms.iterate: tag/present/found=10/11/12,
/// source=0, reversed payload=1, with the physical nested callback.
pub fn scan_command() -> Result<Cmd<13, 11>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<13, 11>([10, 11], [0, 1])?);
    let advance = Cmd::ite(
        12,
        Cmd::Atom(Atom::Set {
            dst: 10,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 0,
            value: 10,
            present: 11,
        }),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback_command()?, advance));
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 12,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 10,
                present: 11,
            }),
            Cmd::while_(10, body),
        ),
    ))
}

fn push_false(stack: usize) -> Cmd<13, 11> {
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack, src: 0 }),
    )
}

/// Full source ExecCleanLiteralsProgram.clean. The input is
/// Encoding.encodeList clauseCode formula on stack 0 with work 1..10 empty.
pub fn clean_command() -> Result<Cmd<13, 11>, Error> {
    Ok(Cmd::seq(
        push_false(2),
        Cmd::seq(
            scan_command()?,
            Cmd::seq(push_false(0), Cmd::Call(clean_literals_reverse_program()?)),
        ),
    ))
}

pub fn clean_program() -> Result<Program<13, 11>, Error> {
    clean_command()?.compiled(0, 0)
}
