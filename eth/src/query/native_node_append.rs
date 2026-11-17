//! Literal, independently executable subcommands of `NodeAppendSpace`.
//!
//! Pinned Lean source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
//! `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NodeAppendSpace.lean`
//! Git blob `a02eb4aeceee50a2e125b242f088bbf1b6f3a43b`.
//!
//! These three commands use only physical `BitProgram` calls. The complete
//! `NodeAppendSpace.command` ALSO invokes `NodeReadoutSpace.command`, which is
//! not implemented by this module. Never mistake a stand-alone append for the
//! signed native node result or a completed `QueryStreamProgram`.

use crate::Error;
use crate::bit_program::Cmd;
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::transfer_program;

fn clear(stack: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(clear_program(stack, 0, 1)?))
}

fn copy(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(copy_program(src, dst, 89, 0, 1)?))
}

fn transfer(src: usize, dst: usize) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(transfer_program(src, dst, 0, 1)?))
}

/// Exact `NodeAppendSpace.prepare`:
/// clear [89, 5, 12, 39], then preserving copies 194→5, 202→12, 204→39,
/// each with scratch stack 89, which is empty before and after every copy.
/// The three source words are preserved; existing destination tails are not.
pub fn prepare_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear(89)?,
        Cmd::seq(
            clear(5)?,
            Cmd::seq(
                clear(12)?,
                Cmd::seq(
                    clear(39)?,
                    Cmd::seq(copy(194, 5)?, Cmd::seq(copy(202, 12)?, copy(204, 39)?)),
                ),
            ),
        ),
    ))
}

/// Exact `NodeAppendSpace.append` with source precondition stack 89 empty.
/// Three preserving-order transfers: 863→89, 862→89, 89→863.
/// Appends the entire word on 862 after the existing word on 863, then
/// empties 862 and 89. Does NOT compute the contents of 862.
pub fn append_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        transfer(863, 89)?,
        Cmd::seq(transfer(862, 89)?, transfer(89, 863)?),
    ))
}

/// Exact `NodeAppendSpace.handoff`, with source precondition stack 89 empty.
/// Clear stack 265, then transfer 863→89→265, preserving word order and
/// consuming the old stream on 863. No host-side stream rearrangement.
pub fn handoff_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear(265)?,
        Cmd::seq(transfer(863, 89)?, transfer(89, 265)?),
    ))
}
