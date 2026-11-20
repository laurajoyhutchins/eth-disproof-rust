//! Complete source `ExecClauseFiltersProgram.selfFilterProgram mode` on 15x16.
//! Uses preserving real relation scanner and original emit + reverse routines.
use crate::Error;
use crate::bit_program::record_iteration::{RecordPorts, iterate};
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_clause_dedup::filter_callback;
use crate::native_clause_relation_scan::Mode;
use crate::native_high::{clear_program, copy_program};
use crate::native_normalization_primitives::clause_filter_reverse_program;
use crate::native_query_prefix::frame_program;

pub fn filter_scan(mode: Mode) -> Result<Cmd<15, 16>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<15, 16>([0, 1], [13, 15])?);
    Ok(iterate(
        RecordPorts {
            tag: 0,
            present: 1,
            found: 14,
            source: 13,
        },
        reader,
        filter_callback(mode)?,
    ))
}
fn push_false(stack: usize) -> Cmd<15, 16> {
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack, src: 0 }),
    )
}

/// Source full fixed-master self-filter: preserving copy, physical predicate,
/// clear master and restore order. The only data-dependent control is the
/// original finite machine's conditional and while instructions.
pub fn self_filter_command(mode: Mode) -> Result<Cmd<15, 16>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(13, 12, 9, 0, 1)?),
        Cmd::seq(
            push_false(14),
            Cmd::seq(
                filter_scan(mode)?,
                Cmd::seq(
                    Cmd::Call(clear_program(12, 0, 1)?),
                    Cmd::seq(push_false(13), Cmd::Call(clause_filter_reverse_program()?)),
                ),
            ),
        ),
    ))
}
pub fn self_filter_program(mode: Mode) -> Result<Program<15, 16>, Error> {
    self_filter_command(mode)?.compiled(13, 13)
}
