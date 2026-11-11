//! Source-pinned executable H-cache iteration, not yet `hFlatProgram`.
//! Pinned: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Sources: ParserProgram, SubexpPostfixControl, RowSelectionProgramParser,
//! RowSelectionProgramEntriesEmit, LayoutScalarEmitter,
//! LayoutProgramScalarCacheCell. All loops are finite static instruction tables.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_integer_cache::{cache_cell_command, initial_h_build_command};
use crate::native_query_prefix::{frame_program, transfer_program};

fn pop<const R: usize, const S: usize>(stack: usize, value: usize, present: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Pop {
        stack,
        value,
        present,
    })
}
fn copy<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(copy_program(src, dst, tmp, 0, 1)?))
}

/// Exact `SubexpPostfixControl.literalService` 17-label table, entered at 7.
pub fn emit_record_program() -> Result<Program<3, 4>, Error> {
    let parser = frame_program()?.lift::<3, 4>([0, 1], [0, 3])?;
    let mut code = parser.code().to_vec();
    code[6] = Instr::Goto { next: 7 };
    code.extend([
        Instr::Set {
            dst: 0,
            value: false,
            next: 8,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Pop {
            stack: 3,
            value: 0,
            present: 1,
            next: 10,
        },
        Instr::Branch {
            test: 1,
            yes: 11,
            no: 14,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 12,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 13,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 15,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 16,
        },
        Instr::Halt,
    ]);
    Program::new(3, 2, 7, code)
}
fn emit_one(negative: bool) -> Result<Cmd<3, 6>, Error> {
    let stacks = if negative { [3, 4, 2, 1] } else { [3, 4, 2, 0] };
    Ok(Cmd::Call(
        emit_record_program()?.lift::<3, 6>([0, 1, 2], stacks)?,
    ))
}
pub fn emit_pair_inner_command() -> Result<Cmd<3, 6>, Error> {
    Ok(Cmd::seq(
        emit_one(true)?,
        Cmd::seq(pop(2, 0, 1), emit_one(false)?),
    ))
}
pub fn scalar_emit_pair_command() -> Result<Cmd<8, 7>, Error> {
    let inner = emit_pair_inner_command()?
        .compiled(0, 2)?
        .lift::<8, 7>([0, 1, 2], [3, 4, 6, 0, 1, 2])?;
    Ok(Cmd::seq(
        copy(0, 3, 5)?,
        Cmd::seq(
            copy(1, 4, 5)?,
            Cmd::seq(Cmd::Call(inner), Cmd::Call(transfer_program(6, 2, 0, 1)?)),
        ),
    ))
}
pub fn scalar_emit_pair_program() -> Result<Program<8, 7>, Error> {
    scalar_emit_pair_command()?.compiled(0, 2)
}
pub fn cache_emit_command() -> Result<Cmd<8, 18>, Error> {
    Ok(Cmd::Call(scalar_emit_pair_program()?.lift::<8, 18>(
        std::array::from_fn(|i| i),
        [0, 1, 16, 5, 6, 7, 8],
    )?))
}
/// Exact `RowSelectionProgram.parsePair` under a 16-stack working frame.
pub fn parse_pair_inner_command() -> Result<Cmd<8, 16>, Error> {
    let positive = frame_program()?.lift::<8, 16>([0, 1], [15, 2])?;
    let negative = frame_program()?.lift::<8, 16>([0, 1], [15, 3])?;
    Ok(Cmd::seq(
        pop(15, 7, 6),
        Cmd::ite(
            7,
            Cmd::seq(Cmd::Call(positive), Cmd::Call(negative)),
            Cmd::Skip,
        ),
    ))
}
pub fn cache_parse_command() -> Result<Cmd<8, 18>, Error> {
    Ok(Cmd::Call(
        parse_pair_inner_command()?
            .compiled(0, 1)?
            .lift::<8, 18>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    ))
}
pub fn cache_row_command() -> Result<Cmd<8, 18>, Error> {
    let parse = cache_parse_command()?;
    Ok(Cmd::seq(
        parse.clone(),
        Cmd::while_(
            7,
            Cmd::seq(
                cache_cell_command()?,
                Cmd::seq(cache_emit_command()?, parse),
            ),
        ),
    ))
}
pub fn cache_row_program() -> Result<Program<8, 18>, Error> {
    cache_row_command()?.compiled(15, 16)
}
pub fn scalar_finish_list_command() -> Result<Cmd<8, 7>, Error> {
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 2, src: 0 }),
            Cmd::Call(transfer_program(2, 6, 0, 1)?),
        ),
    ))
}
pub fn cache_finish_list_command() -> Result<Cmd<8, 18>, Error> {
    Ok(Cmd::Call(
        scalar_finish_list_command()?
            .compiled(2, 6)?
            .lift::<8, 18>(std::array::from_fn(|i| i), [0, 1, 16, 5, 6, 7, 15])?,
    ))
}
pub fn cache_pass_command() -> Result<Cmd<8, 18>, Error> {
    Ok(Cmd::seq(
        cache_row_command()?,
        Cmd::seq(
            cache_finish_list_command()?,
            Cmd::Call(clear_program(0, 0, 1)?),
        ),
    ))
}
pub fn cache_pass_program() -> Result<Program<8, 18>, Error> {
    cache_pass_command()?.compiled(15, 15)
}
pub fn cache_iteration_command() -> Result<Cmd<8, 18>, Error> {
    let read = pop(17, 7, 6);
    Ok(Cmd::seq(
        read.clone(),
        Cmd::while_(6, Cmd::seq(cache_pass_command()?, read)),
    ))
}
pub fn cache_iteration_program() -> Result<Program<8, 18>, Error> {
    cache_iteration_command()?.compiled(17, 15)
}
pub fn h_build_command() -> Result<Cmd<8, 19>, Error> {
    let iter = cache_iteration_program()?
        .lift::<8, 19>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    Ok(Cmd::seq(initial_h_build_command()?, Cmd::Call(iter)))
}
pub fn h_build_program() -> Result<Program<8, 19>, Error> {
    h_build_command()?.compiled(17, 15)
}
