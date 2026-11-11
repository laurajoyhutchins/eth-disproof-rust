//! Original `Native.frontendCommand`, composing source-defined physical commands.
//! The entire CNF body is normalized by the Boolean stack machine, not Rust.
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_frontend_header::header_command;
use crate::native_frontend_tail::frontend_tail_command;
use crate::native_outer_normalization::command as normalization_command;

/// Literal source: headerCommand ; normalizationCommand ;
///                 placeBodyCommand ; ambientCommand.
/// Requires canonical Encoding.encodeCNF input at stack 256 and all other
/// work stacks empty (as in the original source theorem).
pub fn command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        header_command()?,
        Cmd::seq(normalization_command()?, frontend_tail_command()?),
    ))
}

/// Compiled `Native.frontendProgram` with the source ABI count/answer ports.
pub fn program() -> Result<Program<80, 1220>, Error> {
    command()?.compiled(256, 263)
}
