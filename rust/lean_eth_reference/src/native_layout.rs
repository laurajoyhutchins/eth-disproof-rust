//! The actual node-start layout loader from pinned OpenAI Lean source.
//!
//! `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! - `SqrtLogSpace/NativeLayoutLoad.lean`
//! - `SqrtLog/LeafProgramLayoutMasters.lean`
//! - `SubexpSetupStorage.lean`, `StackRoutines.lean`
//!
//! Explicitly executes the two `liftCommand` boundaries and the nested
//! `LayoutMasters.load` call. Not the subsequent numerical head evaluator.

use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use std::collections::VecDeque;

pub const LOW_START: usize = 128;
pub const HIGH_START: usize = 730;
pub const MASTER_COUNT: usize = 14;

/// `NativeLayoutLoad.clearPorts`: three retained scratch ports and fourteen
/// low masters; the parked high masters are never cleared.
pub fn clear_ports() -> Vec<usize> {
    let mut result = vec![684, 660, 665];
    result.extend(LOW_START..LOW_START + MASTER_COUNT);
    result
}

fn clear_many<const R: usize, const S: usize>(ports: &[usize]) -> Result<Cmd<R, S>, Error> {
    let mut command = Cmd::Skip;
    // `SubexpSetupStorage.clearMany` is a right-associated `seq`.
    for &stack in ports.iter().rev() {
        command = Cmd::seq(Cmd::Call(clear_program(stack, 0, 1)?), command);
    }
    Ok(command)
}

/// Fourteen static preserving copies, source high port to destination low
/// port, with the real scratch stack 684.
pub fn load_local_command() -> Result<Cmd<16, 768>, Error> {
    let mut command = Cmd::Skip;
    for i in 0..MASTER_COUNT {
        command = Cmd::seq(
            command,
            Cmd::Call(copy_program(HIGH_START + i, LOW_START + i, 684, 0, 1)?),
        );
    }
    Ok(command)
}

/// `LayoutMasters.load : Cmd 40 768` is itself a nested program call.
pub fn load_low_command() -> Result<Cmd<40, 768>, Error> {
    let local = load_local_command()?.compiled(HIGH_START, LOW_START)?;
    Ok(Cmd::Call(local.lift::<40, 768>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

/// First `liftCommand`, retaining the actual compiled halt.
pub fn prepare_command() -> Result<Cmd<40, 896>, Error> {
    let local: Program<16, 896> = clear_many(&clear_ports())?.compiled(730, 128)?;
    Ok(Cmd::Call(local.lift::<40, 896>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

/// Second `liftCommand`, containing `LayoutMasters.load`'s nested call.
pub fn load_command() -> Result<Cmd<40, 896>, Error> {
    let local: Program<40, 768> = load_low_command()?.compiled(HIGH_START, LOW_START)?;
    Ok(Cmd::Call(local.lift::<40, 896>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

pub fn command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(prepare_command()?, load_command()?))
}

pub fn program() -> Result<Program<40, 896>, Error> {
    command()?.compiled(HIGH_START, LOW_START)
}

/// The source's exact step formula, including all nested halts and returns.
pub fn expected_steps<const S: usize>(stacks: &[VecDeque<bool>; S]) -> Result<u64, Error> {
    let mut total = 0u64;
    for port in clear_ports() {
        let n = u64::try_from(stacks[port].len()).map_err(|_| Error::Overflow)?;
        total = total
            .checked_add(
                n.checked_mul(2)
                    .and_then(|x| x.checked_add(3))
                    .ok_or(Error::Overflow)?,
            )
            .ok_or(Error::Overflow)?;
    }
    for stack in stacks.iter().skip(HIGH_START).take(MASTER_COUNT) {
        let n = u64::try_from(stack.len()).map_err(|_| Error::Overflow)?;
        total = total
            .checked_add(
                n.checked_mul(7)
                    .and_then(|x| x.checked_add(5))
                    .ok_or(Error::Overflow)?,
            )
            .ok_or(Error::Overflow)?;
    }
    // prepare lift: +1; nested LayoutMasters.load and outer load: +2;
    // final compiled NativeLayoutLoad.command halt: +1.
    total.checked_add(4).ok_or(Error::Overflow)
}

/// Exact *first-iteration prefix* of `QueryStreamProgram.command`, stopping
/// immediately after the node's parked layout has been loaded. The branch
/// tests the real guard from `QueryNodeFinish.guardCursor`, so empty node
/// tables skip the body. Not the complete `nodeLoop`, `NativeLayoutLoad`'s
/// downstream integer calculations, or an end-to-end query answer.
pub fn first_node_layout_prefix_command() -> Result<Cmd<40, 896>, Error> {
    use crate::native_nodes::{begin_node_command, nodes_entry_command};
    let first_body = Cmd::seq(begin_node_command()?, command()?);
    Ok(Cmd::seq(
        crate::native_query_prefix::prepare_high_command()?,
        Cmd::seq(nodes_entry_command()?, Cmd::ite(37, first_body, Cmd::Skip)),
    ))
}
