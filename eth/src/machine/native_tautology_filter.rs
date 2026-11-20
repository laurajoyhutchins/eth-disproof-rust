//! Original SubexpTautologyFilterProgram: process each CNF clause through the
//! actual 10x8 tautology machine, retain only nontautologies, restore order.
use crate::Error;
use crate::bit_program::record_iteration::{RecordPorts, iterate};
use crate::bit_program::stack_routines::transfer_program;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::clear_program;
use crate::native_normalization_primitives::{
    emit_if_selected_command, tautology_filter_reverse_program,
};
use crate::native_query_prefix::frame_program;
use crate::native_tautology_core;

fn transfer(src: usize, dst: usize) -> Result<Program<13, 11>, Error> {
    if src == dst {
        return Err(Error::Invalid("transfer ports must differ".into()));
    }
    transfer_program(src, dst, 0, 1)
}
pub fn core_program() -> Result<Program<13, 11>, Error> {
    native_tautology_core::program()?
        .lift::<13, 11>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8, 9, 10])
}
pub fn emit_program() -> Result<Program<13, 11>, Error> {
    emit_if_selected_command()?
        .compiled(3, 2)?
        .lift::<13, 11>([10, 11, 12], [0, 3, 2, 1])
}
pub fn callback_command() -> Result<Cmd<13, 11>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer(1, 3)?),
        Cmd::seq(
            Cmd::Call(core_program()?),
            Cmd::seq(
                Cmd::Call(transfer(5, 1)?),
                Cmd::seq(
                    Cmd::Call(clear_program(4, 0, 1)?),
                    Cmd::seq(
                        Cmd::Atom(Atom::Not { dst: 12, src: 9 }),
                        Cmd::Call(emit_program()?),
                    ),
                ),
            ),
        ),
    ))
}
pub fn scan_command() -> Result<Cmd<13, 11>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<13, 11>([10, 11], [0, 1])?);
    Ok(iterate(
        RecordPorts {
            tag: 10,
            present: 11,
            found: 12,
            source: 0,
        },
        reader,
        callback_command()?,
    ))
}
fn push_false(stack: usize) -> Cmd<13, 11> {
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack, src: 0 }),
    )
}
pub fn filter_command() -> Result<Cmd<13, 11>, Error> {
    Ok(Cmd::seq(
        push_false(2),
        Cmd::seq(
            scan_command()?,
            Cmd::seq(
                push_false(0),
                Cmd::Call(tautology_filter_reverse_program()?),
            ),
        ),
    ))
}
pub fn program() -> Result<Program<13, 11>, Error> {
    filter_command()?.compiled(0, 0)
}
