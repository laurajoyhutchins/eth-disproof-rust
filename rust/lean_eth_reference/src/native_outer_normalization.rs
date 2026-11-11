//! Original `Native.normalizationCommand` ABI lift of complete source normalizer.
//! This is only the normalization stage, not the entire outer frontend.
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_normalization_full;

pub fn command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::Call(
        native_normalization_full::program()?.lift::<80, 1220>(
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1218, 14, 15],
        )?,
    ))
}
pub fn program() -> Result<Program<80, 1220>, Error> {
    command()?.compiled(1218, 1218)
}
