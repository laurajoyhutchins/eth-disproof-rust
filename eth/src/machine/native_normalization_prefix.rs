//! Exact SubexpNormalizationPrefixProgram.command on the original 13x11 machine.
//! This composes physical literal cleanup followed by physical tautology removal.
//! It does NOT perform clause deduplication or strict-subset removal.
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_literal_cleanup::clean_command;
use crate::native_tautology_filter::filter_command;
pub fn command() -> Result<Cmd<13, 11>, Error> {
    Ok(Cmd::seq(clean_command()?, filter_command()?))
}
pub fn program() -> Result<Program<13, 11>, Error> {
    command()?.compiled(0, 0)
}
