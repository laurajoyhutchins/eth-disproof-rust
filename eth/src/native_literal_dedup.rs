//! Source-native physical last-occurrence literal deduplication, 10x8.
//! Original: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! ExecLiteralDedupProgram.lean (blob ed06095d27e9f739e5febde59da81c0f8bf43523).
//! This is not full CNF normalization and has no host equality oracle.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_normalization_primitives::{
    emit_if_selected_command, literal_dedup_reverse_program,
};
use crate::native_record_membership::frame_program;
use crate::native_terminal_classifier::subset_member_call;

/// Literal source emitIfSelectedProgram is compiled before its mapped call.
pub fn emit_program() -> Result<Program<10, 8>, Error> {
    emit_if_selected_command()?
        .compiled(3, 2)?
        .lift::<10, 8>([7, 8, 9], [0, 7, 2, 1])
}

/// The source physical callback: preserve-copy unread suffix, compare the
/// payload using real ExecCNFSubset.memberCall, invert register 4 into
/// selected flag 9, clear comparison work, and emit iff not found later.
pub fn callback_command() -> Result<Cmd<10, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(0, 3, 7, 0, 1)?),
        Cmd::seq(
            subset_member_call()?,
            Cmd::seq(
                Cmd::Atom(Atom::Not { dst: 9, src: 4 }),
                Cmd::seq(
                    Cmd::Call(clear_program(3, 0, 1)?),
                    Cmd::seq(
                        Cmd::Call(clear_program(4, 0, 1)?),
                        Cmd::Call(emit_program()?),
                    ),
                ),
            ),
        ),
    ))
}

/// RecordPrograms.iterate with exact tag/present/found ports 7/8/9,
/// source 0 and payload 1. Every record is consumed by the source machine.
pub fn scan_command() -> Result<Cmd<10, 8>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<10, 8>([7, 8], [0, 1])?);
    let advance = Cmd::ite(
        9,
        Cmd::Atom(Atom::Set {
            dst: 7,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 0,
            value: 7,
            present: 8,
        }),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback_command()?, advance));
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 9,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 7,
                present: 8,
            }),
            Cmd::while_(7, body),
        ),
    ))
}

fn push_false(stack: usize) -> Cmd<10, 8> {
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack, src: 0 }),
    )
}

/// Full ExecLiteralDedupProgram.dedup: seed empty output 2, physically
/// scan and test each record against the unread suffix, then reverse the
/// kept record order into the original input port 0. Work ports begin empty.
pub fn dedup_command() -> Result<Cmd<10, 8>, Error> {
    Ok(Cmd::seq(
        push_false(2),
        Cmd::seq(
            scan_command()?,
            Cmd::seq(push_false(0), Cmd::Call(literal_dedup_reverse_program()?)),
        ),
    ))
}

pub fn dedup_program() -> Result<Program<10, 8>, Error> {
    dedup_command()?.compiled(0, 0)
}
