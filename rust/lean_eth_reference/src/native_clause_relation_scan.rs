//! Actual source `ExecClauseRelationScan.command mode`, not host set logic.
//! Source has 15 one-bit registers and 12 Boolean stacks.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_clause_relations::relation_program;
use crate::native_high::clear_program;
use crate::native_query_prefix::frame_program;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Equivalent,
    StrictSubset,
    MissingCore,
}
impl Mode {
    fn result_register(self) -> usize {
        match self {
            Self::Equivalent => 10,
            Self::StrictSubset => 11,
            Self::MissingCore => 9,
        }
    }
}

pub fn transfer_candidate() -> Result<Program<15, 12>, Error> {
    Program::new(
        11,
        8,
        0,
        vec![
            Instr::Pop {
                stack: 11,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Instr::Push {
                stack: 8,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

pub fn relation_lift() -> Result<Program<15, 12>, Error> {
    relation_program()?.lift::<15, 12>(
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    )
}

pub fn callback(mode: Mode) -> Result<Cmd<15, 12>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer_candidate()?),
        Cmd::seq(
            Cmd::Call(relation_lift()?),
            Cmd::seq(
                Cmd::Atom(Atom::Copy {
                    dst: 14,
                    src: mode.result_register(),
                }),
                Cmd::Call(clear_program(8, 0, 1)?),
            ),
        ),
    ))
}

/// Original RecordPrograms ports: tag 12, present 13, found 14,
/// unread input stack 10, reversed payload stack 11.
pub fn scan_command(mode: Mode) -> Result<Cmd<15, 12>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<15, 12>([12, 13], [10, 11])?);
    let advance = Cmd::ite(
        14,
        Cmd::Atom(Atom::Set {
            dst: 12,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: 10,
            value: 12,
            present: 13,
        }),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback(mode)?, advance));
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 14,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 10,
                value: 12,
                present: 13,
            }),
            Cmd::while_(12, body),
        ),
    ))
}

pub fn command(mode: Mode) -> Result<Cmd<15, 12>, Error> {
    Ok(Cmd::seq(
        scan_command(mode)?,
        Cmd::Atom(Atom::Push { stack: 11, src: 14 }),
    ))
}
pub fn program(mode: Mode) -> Result<Program<15, 12>, Error> {
    command(mode)?.compiled(10, 11)
}
