//! Exact generic source NativeLeafDispatch.command, without a fake leaf.
//!
//! The nonterminal argument is an actual physical command, supplied by
//! the future NativeLeafProgram. A diagnostic marker is used only in tests.

use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_terminal_classifier::ready_command;

/// Original NativeLeafDispatch.command. After classification and terminal
/// count: skip on empty clause, run nonterminal for nonempty formula, otherwise
/// skip because the empty formula already emitted 2^n.
pub fn command(nonterminal: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        ready_command()?,
        Cmd::ite(0, Cmd::Skip, Cmd::ite(7, nonterminal, Cmd::Skip)),
    ))
}

/// Compiled wrapper for a caller-supplied physical command; the Lean source
/// itself defines a command factory, not a closed executable program.
pub fn program(nonterminal: Cmd<80, 1220>) -> Result<Program<80, 1220>, Error> {
    command(nonterminal)?.compiled(265, 263)
}
