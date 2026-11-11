//! Literal source-defined terminal classification for the 80x1220 machine.
//! Composes ExecCNFSubset.memberCall, SubexpScopeMembershipProgram.member,
//! SubexpEmptyClauseProgram.command, LeafProgram.Trivial.command and
//! NativeTerminal.readyCommand. No host membership predicate or SAT oracle.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_record_membership::membership_program;
use crate::native_terminal::{terminal_power_command, terminal_zero_command};

/// Source Fin.castAdd 3 leaves registers 0..6 unshifted.
pub fn subset_member_call() -> Result<Cmd<10, 8>, Error> {
    let member = membership_program()?.lift::<10, 8>([0, 1, 2, 3, 4, 5, 6], [3, 4, 1, 5, 6])?;
    Ok(Cmd::Call(member))
}

/// Source SubexpScopeMembershipProgram.member compiles the 10x8 call first
/// and then lifts its eight source stacks into the 10x10 scope bank.
pub fn scope_member_command() -> Result<Cmd<10, 10>, Error> {
    let program = subset_member_call()?.compiled(3, 4)?;
    let lifted =
        program.lift::<10, 10>([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [5, 2, 6, 0, 1, 3, 4, 7])?;
    Ok(Cmd::Call(lifted))
}

/// Actual SubexpEmptyClauseProgram.command. Requires canonical encoded list
/// on stack 9; work stacks 0..4 and 8 initially empty. Retains the source.
pub fn empty_clause_command() -> Result<Cmd<10, 10>, Error> {
    let copy = Cmd::Call(copy_program(9, 0, 8, 0, 1)?);
    let load_query = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack: 2, src: 0 }),
    );
    let member = scope_member_command()?;
    let mut reset = Cmd::Skip;
    for reg in (1..=6).rev() {
        reset = Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: reg,
                value: false,
            }),
            reset,
        );
    }
    reset = Cmd::seq(Cmd::Atom(Atom::Copy { dst: 0, src: 4 }), reset);
    Ok(Cmd::seq(
        copy,
        Cmd::seq(
            load_query,
            Cmd::seq(
                member,
                Cmd::seq(
                    Cmd::Call(clear_program(0, 0, 1)?),
                    Cmd::seq(
                        Cmd::Call(clear_program(1, 0, 1)?),
                        Cmd::seq(Cmd::Call(clear_program(2, 0, 1)?), reset),
                    ),
                ),
            ),
        ),
    ))
}

pub fn empty_clause_program() -> Result<Program<10, 10>, Error> {
    empty_clause_command()?.compiled(9, 9)
}

/// Exact LeafProgram.Trivial.command; peek stack 9 for nonempty-list flag 7.
pub fn trivial_command() -> Result<Cmd<10, 10>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(empty_clause_program()?),
        Cmd::Atom(Atom::Peek {
            stack: 9,
            value: 7,
            present: 8,
        }),
    ))
}

pub fn trivial_program() -> Result<Program<10, 10>, Error> {
    trivial_command()?.compiled(9, 9)
}

/// Source classifier maps registers 0..9 unchanged, stacks 0..8 unchanged,
/// and local source stack 9 to outer leaf-body stack 265.
pub fn terminal_classifier_command() -> Result<Cmd<80, 1220>, Error> {
    let local = trivial_program()?;
    let lifted = local.lift::<80, 1220>(
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 265],
    )?;
    Ok(Cmd::Call(lifted))
}

/// Actual NativeTerminal.command, not the still-missing NativeLeafDispatch.
pub fn terminal_command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        terminal_classifier_command()?,
        Cmd::ite(
            0,
            terminal_zero_command(),
            Cmd::ite(7, Cmd::Skip, terminal_power_command()?),
        ),
    ))
}

/// Source NativeTerminal.readyCommand clears the three terminal work outputs
/// before running classification. Nonterminals retain an EMPTY count stack:
/// this is not accepted as an answer and must be passed to the real leaf.
pub fn ready_command() -> Result<Cmd<80, 1220>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(263, 72, 73)?),
        Cmd::seq(
            Cmd::Call(clear_program(268, 72, 73)?),
            Cmd::seq(Cmd::Call(clear_program(269, 72, 73)?), terminal_command()?),
        ),
    ))
}

pub fn ready_program() -> Result<Program<80, 1220>, Error> {
    ready_command()?.compiled(265, 263)
}
