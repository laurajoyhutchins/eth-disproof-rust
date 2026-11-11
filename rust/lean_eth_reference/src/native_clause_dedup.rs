//! Actual original ExecClauseDedupProgram.command on 15x16 BitProgram.
//! Uses the preserving three-mode scanner to remove equivalent clauses while
//! retaining only the last occurrence and original order of surviving clauses.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_clause_relation_scan::{self, Mode};
use crate::native_high::{clear_program, copy_program};
use crate::native_normalization_primitives::{
    clause_filter_reverse_program, emit_if_selected_command,
};
use crate::native_query_prefix::frame_program;

pub fn transfer(src: usize, dst: usize) -> Result<Program<15, 16>, Error> {
    if src == dst {
        return Err(Error::Invalid("transfer ports must differ".into()));
    }
    Program::new(
        src, dst, 0,
        vec![
            Instr::Pop { stack: src, value: 0, present: 1, next: 1 },
            Instr::Branch { test: 1, yes: 2, no: 3 },
            Instr::Push { stack: dst, src: 0, next: 0 },
            Instr::Halt,
        ],
    )
}

/// Original ExecClauseRelationScan.Preserving.command on 15x13:
/// preserve master 12, scan a copy at 10, clear residual 10.
pub fn preserving_scan_command(mode: Mode) -> Result<Cmd<15, 13>, Error> {
    let scan = native_clause_relation_scan::program(mode)?;
    let lifted = scan.lift::<15, 13>(
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    )?;
    Ok(Cmd::seq(
        Cmd::Call(copy_program(12, 10, 8, 0, 1)?),
        Cmd::seq(Cmd::Call(lifted), Cmd::Call(clear_program(10, 0, 1)?)),
    ))
}
pub fn preserving_scan_program(mode: Mode) -> Result<Program<15, 13>, Error> {
    preserving_scan_command(mode)?.compiled(12, 11)
}

/// Actual ExecClauseFiltersProgram.callback: transfer candidate to query,
/// physically scan preserved master, negate found, emit/discard framed record.
pub fn filter_callback(mode: Mode) -> Result<Cmd<15, 16>, Error> {
    let scan = preserving_scan_program(mode)?.lift::<15, 16>(
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    )?;
    let emit = emit_if_selected_command()?
        .compiled(3, 2)?
        .lift::<15, 16>([0, 1, 14], [13, 9, 14, 15])?;
    Ok(Cmd::seq(
        Cmd::Call(transfer(15, 9)?),
        Cmd::seq(
            Cmd::Call(scan),
            Cmd::seq(
                Cmd::Call(clear_program(11, 0, 1)?),
                Cmd::seq(
                    Cmd::Call(transfer(9, 15)?),
                    Cmd::seq(Cmd::Atom(Atom::Not { dst: 14, src: 14 }), Cmd::Call(emit)),
                ),
            ),
        ),
    ))
}

/// Original ExecClauseDedupProgram.callback: copy unread suffix 13 -> master12,
/// compare equivalent records, clear the copied master.
pub fn dedup_callback() -> Result<Cmd<15, 16>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(13, 12, 9, 0, 1)?),
        Cmd::seq(
            filter_callback(Mode::Equivalent)?,
            Cmd::Call(clear_program(12, 0, 1)?),
        ),
    ))
}

/// Original outer iterator ports tag0/present1/found14/source13/payload15.
pub fn scan_command() -> Result<Cmd<15, 16>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<15, 16>([0, 1], [13, 15])?);
    let advance = Cmd::ite(
        14,
        Cmd::Atom(Atom::Set { dst: 0, value: false }),
        Cmd::Atom(Atom::Pop { stack: 13, value: 0, present: 1 }),
    );
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set { dst: 14, value: false }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop { stack: 13, value: 0, present: 1 }),
            Cmd::while_(0, Cmd::seq(reader, Cmd::seq(dedup_callback()?, advance))),
        ),
    ))
}
fn push_false(stack: usize) -> Cmd<15, 16> {
    Cmd::seq(
        Cmd::Atom(Atom::Set { dst: 0, value: false }),
        Cmd::Atom(Atom::Push { stack, src: 0 }),
    )
}
/// Source complete dedup, compiled with input/output 13/13.
pub fn command() -> Result<Cmd<15, 16>, Error> {
    Ok(Cmd::seq(
        push_false(14),
        Cmd::seq(
            scan_command()?,
            Cmd::seq(push_false(13), Cmd::Call(clause_filter_reverse_program()?)),
        ),
    ))
}
pub fn program() -> Result<Program<15, 16>, Error> {
    command()?.compiled(13, 13)
}
