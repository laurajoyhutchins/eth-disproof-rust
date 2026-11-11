//! The *actual first command* in `QueryStreamProgram.command`:
//! `HighQueryAdapter.prepareHigh` (plus the immediately preceding
//! `HighQueryAdapter.copyHighCounter` from `HighQueryProgram.conditioned`).
//!
//! These are fixed, concrete tables from `openai/math` revision
//! 4eaee87548250b2682affda7d05d947c05554bae. No semantic oracle or
//! input-dependent program construction is used. Neither the node/pair DFS
//! nor `QueryReconstruction.command` is implemented by this module.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};

fn pop<const R: usize, const S: usize>(stack: usize, value: usize, present: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Pop {
        stack,
        value,
        present,
    })
}
fn push<const R: usize, const S: usize>(stack: usize, src: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Push { stack, src })
}

/// Source `StackRoutines.transferProgram`: four labels, including the halt.
/// Its preconditions require different source/destination stacks and read
/// registers. The word is reversed as it is transferred.
pub fn transfer_program<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if src == dst || value == present {
        return Err(Error::Invalid("transfer requires disjoint ports".into()));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 3,
            },
            Instr::Push {
                stack: dst,
                src: value,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// The exact seven-label source `ParserProgram.frameProgram`.
/// Input: `Encoding.frame bits ++ rest`; output is `bits.reverse ++ out`.
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

/// Source `Subexp.AssignmentRecordViews.flatten` and its full compiled table.
/// The parser is a physically lifted call on registers [0,1], stacks [0,1].
pub fn flatten_command() -> Result<Cmd<3, 3>, Error> {
    let parse = Cmd::Call(frame_program()?.lift::<3, 3>([0, 1], [0, 1])?);
    let next_tag = pop(0, 2, 1);
    let transfer = Cmd::Call(transfer_program(1, 2, 0, 1)?);
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            next_tag.clone(),
            Cmd::seq(Cmd::while_(2, Cmd::seq(parse, next_tag)), transfer),
        ),
    ))
}
pub fn flatten_program() -> Result<Program<3, 3>, Error> {
    flatten_command()?.compiled(0, 2)
}

/// Source `SqrtLog.HighIncidenceProgram.Mask.command`, preserving the original
/// descending high mask while producing its reverse on output stack 2.
pub fn mask_program() -> Result<Program<2, 4>, Error> {
    Cmd::seq(
        Cmd::Call(copy_program(0, 1, 3, 0, 1)?),
        Cmd::Call(transfer_program(1, 2, 0, 1)?),
    )
    .compiled(0, 2)
}

/// Source `HighIncidenceProgram.Restriction.command`: one initial mask pop,
/// followed by one selected high/low bit and one output push per mask bit.
pub fn restriction_program() -> Result<Program<4, 4>, Error> {
    let pop_mask = pop(0, 0, 1);
    let load = Cmd::ite(0, pop(1, 2, 3), pop(2, 2, 3));
    let body = Cmd::seq(load, Cmd::seq(push(3, 2), pop_mask.clone()));
    Cmd::seq(pop_mask, Cmd::while_(1, body)).compiled(0, 3)
}

/// Exact `LeafHighContextProgram.Local.command`: mask reverse, counter copy,
/// physical framed-record flatten, mask copy, and coordinate merge.
pub fn local_high_context_command() -> Result<Cmd<4, 10>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(mask_program()?.lift::<4, 10>([0, 1], [1, 7, 2, 8])?),
        Cmd::seq(
            Cmd::Call(copy_program(0, 4, 8, 0, 1)?),
            Cmd::seq(
                Cmd::Call(flatten_program()?.lift::<4, 10>([0, 1, 2], [4, 5, 6])?),
                Cmd::seq(
                    Cmd::Call(copy_program(1, 7, 8, 0, 1)?),
                    Cmd::Call(restriction_program()?.lift::<4, 10>([0, 1, 2, 3], [7, 6, 9, 3])?),
                ),
            ),
        ),
    ))
}
pub fn local_high_context_program() -> Result<Program<4, 10>, Error> {
    local_high_context_command()?.compiled(0, 3)
}

/// Source `HighQueryAdapter.highCommand`, a fixed lifted call with physical
/// upper-leaf stacks. No allocation of a context object at runtime.
pub fn high_command() -> Result<Cmd<40, 896>, Error> {
    let local = local_high_context_program()?.lift::<40, 896>(
        [0, 1, 2, 3],
        [330, 338, 702, 703, 680, 681, 682, 683, 684, 685],
    )?;
    Ok(Cmd::Call(local))
}

/// Exact `HighQueryAdapter.resetHigh`: first clears 702 then clears the eight
/// changed banks (including 702) and clears the temporary 702 once more.
pub fn reset_high_command() -> Result<Cmd<40, 896>, Error> {
    let mut cmd = Cmd::Call(clear_program(702, 0, 1)?);
    for port in [702, 703, 680, 681, 682, 683, 684, 685] {
        cmd = Cmd::seq(cmd, Cmd::Call(clear_program(port, 0, 1)?));
    }
    Ok(Cmd::seq(cmd, Cmd::Call(clear_program(702, 0, 1)?)))
}

/// First real query-stream operation, `HighQueryAdapter.prepareHigh`.
/// Input shape contract: stack 330 is `encodeList id words`; stack 338 is a
/// descending mask with exactly one true bit per one-bit framed word.
/// Output: stack 702 is mask.reverse; 703 is aligned high vector.reverse.
pub fn prepare_high_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(reset_high_command()?, high_command()?))
}
pub fn prepare_high_program() -> Result<Program<40, 896>, Error> {
    prepare_high_command()?.compiled(330, 703)
}

/// Physical copy of the current enumerator assignment into its query buffer,
/// from `HighQueryAdapter.copyHighCounter`.
pub fn copy_high_counter_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(330, 0, 1)?),
        Cmd::seq(
            Cmd::Call(clear_program(792, 0, 1)?),
            Cmd::Call(copy_program(789, 330, 792, 0, 1)?),
        ),
    ))
}

/// The *executable prefix* of `HighQueryProgram.conditioned`, ending at the
/// entry of `QueryStreamProgram.command`'s node traversal. This does not
/// execute node or pair reconstruction, and does not return a count.
pub fn query_stream_prefix_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        copy_high_counter_command()?,
        prepare_high_command()?,
    ))
}
