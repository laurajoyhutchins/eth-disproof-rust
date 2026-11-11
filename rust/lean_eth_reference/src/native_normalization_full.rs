//! Complete original source SubexpNormalizationProgram.program on 15x16.
//! Physical literal cleanup -> tautology -> clause dedup -> strict absorption.
use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::native_clause_dedup;
use crate::native_clause_filter;
use crate::native_clause_relation_scan::Mode;
use crate::native_normalization_prefix;

/// Original prefixProgram: identity registers 0..12 and stack map i -> 13-i.
pub fn prefix_program() -> Result<Program<15, 16>, Error> {
    native_normalization_prefix::program()?.lift::<15, 16>(
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
        [13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3],
    )
}
pub fn command() -> Result<Cmd<15, 16>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(prefix_program()?),
        Cmd::seq(
            Cmd::Call(native_clause_dedup::program()?),
            Cmd::Call(native_clause_filter::self_filter_program(Mode::StrictSubset)?),
        ),
    ))
}
pub fn program() -> Result<Program<15, 16>, Error> {
    command()?.compiled(13, 13)
}
