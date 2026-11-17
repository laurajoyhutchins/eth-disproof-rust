//! Source-instruction port of the interpolation-node cursor, not the
//! numerical node evaluator.
//!
//! `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! - `SqrtLogSpace/RingNodeSetup.lean`: `initNodes`, `readNode`
//! - `SqrtLogSpace/QueryAssembler.lean`: `Nodes.initializeNodes`, `Nodes.beginNode`
//! - `SqrtLogSpace/NodeReadoutSpace.lean`: `clearMany`
//! - `SqrtLogSpace/QueryNodeFinish.lean`: `guardCursor`, `finishNode`
//! - `SqrtLogSpace/QueryStreamProgram.lean`: entry prefix of `nodes`
//!
//! Both node-reader and initializer execute actual finite instruction tables.
//! A complete QueryStreamProgram still requires layout, signature, pair,
//! jet, and reconstruction code, which is deliberately not substituted here.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::{frame_program, transfer_program};

fn clear_call<const R: usize, const S: usize>(stack: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(stack, 0, 1)?))
}

/// The exact recursive `NodeReadoutSpace.clearMany` command. An empty set of
/// ports becomes `skip`, and duplicate ports still execute duplicate clears.
pub fn clear_many(ports: &[usize]) -> Result<Cmd<40, 896>, Error> {
    let mut cmd = Cmd::Skip;
    for &stack in ports.iter().rev() {
        cmd = Cmd::seq(clear_call(stack)?, cmd);
    }
    Ok(cmd)
}

/// The 40-register/768-stack `RingNodeSetup.initNodes`. The copy's temporary
/// stack 305 is cleared first, as required by `StackRoutines.copyProgram`.
pub fn init_nodes_low_command() -> Result<Cmd<40, 768>, Error> {
    let mut cmd = Cmd::Skip;
    for port in [301, 302, 305, 307, 78] {
        cmd = Cmd::seq(cmd, clear_call(port)?);
    }
    Ok(Cmd::seq(cmd, Cmd::Call(copy_program(300, 301, 305, 0, 1)?)))
}

/// `RingNodeSetup.readNode`, consuming one list tag and then its escaped
/// payload frame. The exact parser touches registers 37/38, never register 39.
pub fn read_node_low_command() -> Result<Cmd<40, 768>, Error> {
    let tag = Cmd::Atom(Atom::Pop {
        stack: 301,
        value: 37,
        present: 38,
    });
    let parser = Cmd::Call(frame_program()?.lift::<40, 768>([37, 38], [301, 302])?);
    let restore = Cmd::Call(transfer_program(302, 78, 0, 1)?);
    Ok(Cmd::seq(tag, Cmd::seq(parser, restore)))
}

fn low_call(command: Cmd<40, 768>, input: usize, output: usize) -> Result<Cmd<40, 896>, Error> {
    let low = command.compiled(input, output)?;
    let registers: [usize; 40] = std::array::from_fn(|i| i);
    let stacks: [usize; 768] = std::array::from_fn(|i| i);
    Ok(Cmd::Call(low.lift::<40, 896>(registers, stacks)?))
}

/// `QueryAssembler.Nodes.initializeNodes`, including its embedded local
/// compiler halt and the three upper-bank clear calls.
pub fn initialize_nodes_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        low_call(init_nodes_low_command()?, 301, 78)?,
        clear_many(&[850, 851, 863])?,
    ))
}

pub fn initialize_nodes_program() -> Result<Program<40, 896>, Error> {
    initialize_nodes_command()?.compiled(300, 863)
}

/// `QueryNodeFinish.guardCursor`. Peeking does not consume stack 301.
pub fn guard_cursor_command() -> Cmd<40, 896> {
    Cmd::Atom(Atom::Peek {
        stack: 301,
        value: 37,
        present: 38,
    })
}

/// Literal first two commands of `QueryStreamProgram.nodes`: initialize the
/// node table, then test the cursor. Does not execute `nodeLoop`.
pub fn nodes_entry_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        initialize_nodes_command()?,
        guard_cursor_command(),
    ))
}

/// `QueryAssembler.Nodes.beginNode`. All nine named scratch ports are cleared
/// *before* a framed record is consumed. The nested call has its own halt.
pub fn begin_node_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear_many(&[78, 302, 660, 665, 710, 711, 712, 850, 851])?,
        low_call(read_node_low_command()?, 301, 78)?,
    ))
}

pub fn begin_node_program() -> Result<Program<40, 896>, Error> {
    begin_node_command()?.compiled(301, 78)
}

/// Exact control suffix `QueryNodeFinish.finishNode` (NOT its full
/// `QueryNodeFinish.command`, which first appends the computed node result).
pub fn finish_node_control_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear_many(&[78, 850])?,
        Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: 0,
                value: true,
            }),
            Cmd::seq(
                Cmd::Atom(Atom::Push { stack: 307, src: 0 }),
                guard_cursor_command(),
            ),
        ),
    ))
}

/// The actual *query-stream prefix*, through `QueryStreamProgram.nodes`'s
/// initial cursor peek. The real node loop is not executed here.
pub fn query_nodes_entry_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        crate::native_query_prefix::prepare_high_command()?,
        nodes_entry_command()?,
    ))
}
