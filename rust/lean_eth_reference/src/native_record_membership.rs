//! Exact source-native framed-record scanner and encoded-record membership.
//! Pinned upstream: ParserProgram.frameProgram, RecordPrograms.iterate,
//! ExecCNFMembership.membership and rawMembership.
//! No host-side record decoding, classification or SAT oracle is used.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::clear_program;
use crate::native_membership::membership_callback_command;

/// Seven-label source ParserProgram.frameProgram, including the final halt.
/// Escape-tagged bits are pushed reversed onto stack 1.
pub fn frame_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
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
                no: 6,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 6,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 4,
            },
            Instr::Branch {
                test: 1,
                yes: 5,
                no: 6,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// RecordPrograms.iterate specialized to the original ExecCNFMembership ports:
/// tag=5, present=6, found=4, source=0, payload=1.
/// Requires canonical framed input, clean work stacks 1/3/4, query on 2.
pub fn iterate_command() -> Result<Cmd<7, 5>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<7, 5>([5, 6], [0, 1])?);
    let callback = membership_callback_command()?;
    let advance = Cmd::ite(
        4,
        Cmd::Atom(Atom::Set {
            dst: 5,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 0,
            value: 5,
            present: 6,
        }),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback, advance));
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 4,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 5,
                present: 6,
            }),
            Cmd::while_(5, body),
        ),
    ))
}

/// Exact ExecCNFMembership.membership: run the iterator and push the found bit.
pub fn membership_command() -> Result<Cmd<7, 5>, Error> {
    Ok(Cmd::seq(
        iterate_command()?,
        Cmd::Atom(Atom::Push { stack: 1, src: 4 }),
    ))
}

pub fn membership_program() -> Result<Program<7, 5>, Error> {
    membership_command()?.compiled(0, 1)
}

/// Exact ExecCNFMembership.rawMembership: parse the query frame into port 2,
/// run membership, clear original source/query and reset all seven registers.
/// The record loop and equality callback are entirely finite machine code.
pub fn raw_membership_command() -> Result<Cmd<7, 5>, Error> {
    let read_query = Cmd::Call(frame_program()?.lift::<7, 5>([5, 6], [0, 2])?);
    let clear_source = Cmd::Call(clear_program(0, 0, 1)?);
    let clear_query = Cmd::Call(clear_program(2, 0, 1)?);
    let mut reset = Cmd::Skip;
    for reg in (0..7).rev() {
        reset = Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: reg,
                value: false,
            }),
            reset,
        );
    }
    Ok(Cmd::seq(
        read_query,
        Cmd::seq(
            membership_command()?,
            Cmd::seq(clear_source, Cmd::seq(clear_query, reset)),
        ),
    ))
}

pub fn raw_membership_program() -> Result<Program<7, 5>, Error> {
    raw_membership_command()?.compiled(0, 1)
}
