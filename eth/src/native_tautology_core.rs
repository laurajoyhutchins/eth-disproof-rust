//! Exact source SubexpTautologyProgram: scan a clause and physically test whether
//! any literal's polarity-complement occurs elsewhere in the encoded clause.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_negated_query;
use crate::native_query_prefix::frame_program;
use crate::native_terminal_classifier::subset_member_call;

/// Original SubexpTautologyProgram.negateQueryProgram lift.
pub fn negate_query_program() -> Result<Program<10, 8>, Error> {
    native_negated_query::program()?.lift::<10, 8>([0, 1], [7, 1, 5, 6])
}

pub fn callback_command() -> Result<Cmd<10, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(negate_query_program()?),
        Cmd::seq(
            Cmd::Call(copy_program(2, 3, 4, 0, 1)?),
            Cmd::seq(
                subset_member_call()?,
                Cmd::seq(
                    Cmd::Atom(Atom::Copy { dst: 9, src: 4 }),
                    Cmd::seq(
                        Cmd::Call(clear_program(1, 0, 1)?),
                        Cmd::seq(
                            Cmd::Call(clear_program(3, 0, 1)?),
                            Cmd::seq(
                                Cmd::Call(clear_program(4, 0, 1)?),
                                Cmd::Call(clear_program(7, 0, 1)?),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ))
}

/// RecordPrograms.iterate with source ports tag=7, present=8, found=9,
/// source=0 and reversed literal payload=7.
pub fn scan_command() -> Result<Cmd<10, 8>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<10, 8>([7, 8], [0, 7])?);
    let advance = Cmd::ite(
        9,
        Cmd::Atom(Atom::Set {
            dst: 7,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 0,
            value: 7,
            present: 8,
        }),
    );
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 9,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 7,
                present: 8,
            }),
            Cmd::while_(7, Cmd::seq(reader, Cmd::seq(callback_command()?, advance))),
        ),
    ))
}

pub fn tautology_command() -> Result<Cmd<10, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(0, 2, 4, 0, 1)?),
        Cmd::seq(
            scan_command()?,
            Cmd::seq(
                Cmd::Call(clear_program(0, 0, 1)?),
                Cmd::Atom(Atom::Push { stack: 1, src: 9 }),
            ),
        ),
    ))
}
pub fn program() -> Result<Program<10, 8>, Error> {
    tautology_command()?.compiled(0, 1)
}
