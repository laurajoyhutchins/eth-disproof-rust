//! Physical `NodeReadoutSpace` port mapping and source-defined clearing prefix.
//!
//! Lean: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! `SqrtLogSpace/NodeReadoutSpace.lean` (blob b474a040a06f4fd1abbdcd12901dc11490351666).
//!
//! The numerical `MomentsReadoutProgram.program` is NOT ported here.
//! This module only implements its source ABI and the preceding cleanup;
//! it must not be used to claim that `NodeReadoutSpace.command` is complete.

use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_nodes::clear_many;

/// `NodeReadoutSpace.registers = Fin.castAdd 32`.
/// `Fin.castAdd` does NOT add 32 to each register; indices remain 0..7.
pub const READOUT_REGISTERS: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

/// Source `NodeReadoutSpace.ports`: 40 physical stack locations.
/// Masters are the nine exceptional ports; the remainder are scratch 88..127.
pub fn readout_stack_ports() -> [usize; 40] {
    std::array::from_fn(|i| match i {
        0 => 862,
        5 => 5,
        12 => 12,
        15 => 850,
        24 => 39,
        27 => 280,
        28 => 212,
        29 => 243,
        36 => 128,
        _ => 88 + i,
    })
}

/// `NodeReadoutSpace.scratchPorts`, in `List.ofFn` ascending source index order.
pub fn scratch_ports() -> Vec<usize> {
    let ports = readout_stack_ports();
    (0..40)
        .filter(|i| !matches!(*i, 0 | 5 | 12 | 15 | 24 | 27 | 28 | 29 | 36))
        .map(|i| ports[i])
        .collect()
}

/// `NodeReadoutSpace.clearPorts = 862 :: scratchPorts`.
pub fn clear_ports() -> Vec<usize> {
    let mut ports = Vec::with_capacity(32);
    ports.push(862);
    ports.extend(scratch_ports());
    ports
}

/// Exact finite `NodeReadoutSpace.clearMany clearPorts` prefix.
/// Every specified stack is cleared by a physical `clearProgram` invocation.
pub fn clear_prefix_command() -> Result<Cmd<40, 896>, Error> {
    clear_many(&clear_ports())
}

/// The source `ProgramLinking.liftProgram` boundary for the *eventual* genuine
/// `MomentsReadoutProgram.program`. Supplying a different test program here
/// proves only the port map, NOT the missing numerical readout.
pub fn lift_readout_program(program: Program<8, 40>) -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(program.lift::<40, 896>(
        READOUT_REGISTERS,
        readout_stack_ports(),
    )?))
}

/// The complete executable prefix of `NodeAppendSpace.command` through
/// its `NodeReadoutSpace` cleanup; stops BEFORE numerical readout and append.
pub fn node_append_readout_prefix() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        crate::native_node_append::prepare_command()?,
        clear_prefix_command()?,
    ))
}
