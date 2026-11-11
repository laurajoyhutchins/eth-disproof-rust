//! Literal source suffix of `Native.frontendCommand`, after the original
//! `headerCommand` and `normalizationCommand` have completed.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! SqrtLogSpace/NativeFrontend.lean (`placeBodyCommand`, `ambientCommand`).
//! This module does *not* normalize an input formula, validate its encoding,
//! or implement the missing frontend prefix.
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_high::{clear_program, copy_program};

/// Exact `Native.placeBodyCommand`: preserving copy 1218 -> 265 through 1219,
/// then clear 1218. `copyProgram` prepends the source word to any existing
/// destination word; it does not silently discard stale data.
///
/// Premise: scratch stack 1219 is initially empty. Expected source step cost
/// `9 * |stack 1218| + 8` (plus one if compiled as a standalone program).
pub fn place_body_command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(1218, 265, 1219, 72, 73)?),
        Cmd::Call(clear_program(1218, 72, 73)?),
    ))
}

pub fn place_body_program() -> Result<Program<80, 1220>, Error> {
    place_body_command()?.compiled(1218, 265)
}

/// Literal `seq placeBodyCommand ambientCommand`, the final two operations of
/// `Native.frontendCommand`. Input 1218 already holds the normalized body and
/// the original encoded count/header remains on 256.
///
/// Premises: normalized body 1218 is canonical, stacks 265/258/1219 empty,
/// stack 256 has canonical unary ambient header followed by its original body.
/// The missing header/normalizer must establish these premises upstream.
pub fn frontend_tail_command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        place_body_command()?,
        crate::native_ambient::ambient_command()?,
    ))
}

pub fn frontend_tail_program() -> Result<Program<80, 1220>, Error> {
    frontend_tail_command()?.compiled(256, 258)
}
