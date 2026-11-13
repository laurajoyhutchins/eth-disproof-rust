//! Exact source-defined head selection, from fixed bit/array machines through
//! `LeafHeadSetupProgram.heads` and the following `support` stage.
//!
//! Source revision: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
//! The original unary input words and uniformly wide rows are caller
//! preconditions. This does not implement factor selection or matrix arithmetic.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_bootstrap::stage;
use crate::native_head_scatter::counted_transfer_program;
use crate::native_head_support::support_command;
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::transfer_program;

fn pop<const R: usize, const S: usize>(stack: usize, value: usize, present: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Pop {
        stack,
        value,
        present,
    })
}
fn set<const R: usize, const S: usize>(dst: usize, value: bool) -> Cmd<R, S> {
    Cmd::Atom(Atom::Set { dst, value })
}
fn push<const R: usize, const S: usize>(stack: usize, src: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Push { stack, src })
}
fn copy<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(copy_program(src, dst, tmp, 0, 1)?))
}

/// Exact 9-label `ArrayPrograms.countedCopyProgram`.
fn counted_copy_program<const R: usize, const S: usize>(
    counter: usize,
    src: usize,
    dst: usize,
    tmp: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if counter == src
        || counter == dst
        || counter == tmp
        || src == dst
        || src == tmp
        || dst == tmp
        || value == present
    {
        return Err(Error::Invalid(
            "counted copy requires disjoint stacks and registers".into(),
        ));
    }
    use Instr::*;
    Program::new(
        src,
        dst,
        0,
        vec![
            Pop {
                stack: counter,
                value,
                present,
                next: 1,
            },
            Branch {
                test: present,
                yes: 2,
                no: 4,
            },
            Pop {
                stack: src,
                value,
                present,
                next: 3,
            },
            Push {
                stack: tmp,
                src: value,
                next: 0,
            },
            Pop {
                stack: tmp,
                value,
                present,
                next: 5,
            },
            Branch {
                test: present,
                yes: 6,
                no: 8,
            },
            Push {
                stack: src,
                src: value,
                next: 7,
            },
            Push {
                stack: dst,
                src: value,
                next: 4,
            },
            Halt,
        ],
    )
}

/// Exact `ArrayUpdatePrograms.readCmd`, dual to the already ported 44-label
/// replacement. The selected word is appended to stack 1 in forward order,
/// preserving the complete packed source array on stack 0.
pub fn read_command<const R: usize>(value: usize, present: usize) -> Result<Cmd<R, 8>, Error> {
    if value >= R || present >= R || value == present {
        return Err(Error::Invalid(
            "invalid array read register assignment".into(),
        ));
    }
    let read_index = pop(2, value, present);
    let save_record = Cmd::seq(
        copy(3, 4, 5)?,
        Cmd::Call(counted_transfer_program(4, 0, 7, value, present)?),
    );
    let save_before = Cmd::seq(
        read_index.clone(),
        Cmd::while_(present, Cmd::seq(save_record, read_index)),
    );
    let read_selected = Cmd::seq(
        copy(3, 4, 5)?,
        Cmd::Call(counted_copy_program(4, 0, 1, 6, value, present)?),
    );
    Ok(Cmd::seq(
        save_before,
        Cmd::seq(
            read_selected,
            Cmd::Call(transfer_program(7, 0, value, present)?),
        ),
    ))
}

pub fn read_program<const R: usize>(value: usize, present: usize) -> Result<Program<R, 8>, Error> {
    read_command(value, present)?.compiled(0, 1)
}

/// `SubexpHeadColorProgram.Prefix.program`. Each leading false bit emits
/// one unary unit; the first true bit halts without consuming its suffix.
pub fn color_prefix_program() -> Result<Program<2, 2>, Error> {
    use Instr::*;
    Program::new(
        0,
        1,
        0,
        vec![
            Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Branch {
                test: 0,
                yes: 4,
                no: 2,
            },
            Set {
                dst: 0,
                value: true,
                next: 3,
            },
            Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Halt,
        ],
    )
}

/// `SubexpHeadColorProgram.select`: preserving copy index 1→4, then an
/// actual 38-label indexed read from the packed head words.
pub fn color_select_command() -> Result<Cmd<5, 10>, Error> {
    let read = read_program::<5>(0, 1)?
        .lift::<5, 10>(std::array::from_fn(|i| i), [0, 5, 4, 2, 6, 7, 8, 9])?;
    Ok(Cmd::seq(copy(1, 4, 6)?, Cmd::Call(read)))
}

pub fn color_select_program() -> Result<Program<5, 10>, Error> {
    color_select_command()?.compiled(0, 5)
}

/// The complete source `SubexpHeadColorProgram.command`, which preserves
/// the flat table, unary index, and width while producing a unary color
/// on stack 3. The source's one-hot input shape remains a precondition.
pub fn color_command() -> Result<Cmd<5, 10>, Error> {
    let prefix = color_prefix_program()?.lift::<5, 10>([3, 4], [5, 3])?;
    Ok(Cmd::seq(
        color_select_command()?,
        Cmd::seq(Cmd::Call(prefix), Cmd::Call(clear_program(5, 0, 1)?)),
    ))
}

pub fn color_program() -> Result<Program<5, 10>, Error> {
    color_command()?.compiled(0, 3)
}

/// Literal 7-label runtime-indexed Boolean read, including out-of-range false
/// and consumption of both indexed input stacks (`Subexp.TypeBitProgram`).
pub fn type_bit_program() -> Result<Program<3, 2>, Error> {
    use Instr::*;
    Program::new(
        1,
        1,
        0,
        vec![
            Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 0,
            },
            Pop {
                stack: 1,
                value: 2,
                present: 1,
                next: 4,
            },
            Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 5,
            },
            Branch {
                test: 1,
                yes: 4,
                no: 6,
            },
            Halt,
        ],
    )
}

/// `HeadIdentifierProgram.test`: two runtime indexed bit reads around a
/// real indexed row lookup. `regs[6]` receives the low mask bit, `regs[4]`
/// the selected head color bit, with all inspection scratch cleared.
pub fn head_test_command() -> Result<Cmd<16, 64>, Error> {
    let low_bit = type_bit_program()?.lift::<16, 64>([0, 1, 6], [12, 13])?;
    let word_bit = type_bit_program()?.lift::<16, 64>([0, 1, 4], [12, 36])?;
    let word = color_select_program()?.lift::<16, 64>(
        [11, 12, 13, 14, 15],
        [33, 39, 38, 16, 17, 36, 18, 19, 20, 21],
    )?;
    Ok(Cmd::seq(
        copy(39, 12, 42)?,
        Cmd::seq(
            copy(31, 13, 42)?,
            Cmd::seq(
                Cmd::Call(low_bit),
                Cmd::seq(
                    Cmd::Call(word),
                    Cmd::seq(copy(32, 12, 42)?, Cmd::Call(word_bit)),
                ),
            ),
        ),
    ))
}

pub fn head_test_program() -> Result<Program<16, 64>, Error> {
    head_test_command()?.compiled(39, 36)
}

/// The 6-label source `TupleProgram.escapeProgram`, which consumes unary
/// bits on its input and creates the escaped frame in the destination.
pub(crate) fn escape_program() -> Result<Program<2, 2>, Error> {
    use Instr::*;
    Program::new(
        0,
        1,
        0,
        vec![
            Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Branch {
                test: 1,
                yes: 2,
                no: 5,
            },
            Push {
                stack: 1,
                src: 0,
                next: 3,
            },
            Set {
                dst: 0,
                value: true,
                next: 4,
            },
            Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Halt,
        ],
    )
}

/// Head `record(j)` emission by the actual unary frame writer. A physical
/// prepending stream ensures descending visiting order yields ascending IDs.
fn head_emit_command() -> Result<Cmd<16, 64>, Error> {
    let esc = escape_program()?.lift::<16, 64>([0, 1], [34, 0])?;
    Ok(Cmd::seq(
        copy(39, 34, 42)?,
        Cmd::seq(
            set(0, false),
            Cmd::seq(
                push(0, 0),
                Cmd::seq(
                    Cmd::Call(esc),
                    Cmd::seq(
                        set(0, true),
                        Cmd::seq(push(0, 0), Cmd::seq(set(0, false), push(1, 0))),
                    ),
                ),
            ),
        ),
    ))
}

/// Full Lean `HeadIdentifierProgram.visit` for one concrete row index.
pub fn head_visit_command() -> Result<Cmd<16, 64>, Error> {
    Ok(Cmd::seq(
        head_test_command()?,
        Cmd::ite(6, Cmd::ite(4, head_emit_command()?, Cmd::Skip), Cmd::Skip),
    ))
}

pub fn head_visit_program() -> Result<Program<16, 64>, Error> {
    head_visit_command()?.compiled(39, 0)
}

/// Runtime counted descent through the first `n` rows of the ambient table.
/// `HeadIdentifierProgram.FullTable.program` is statically identical to the
/// original `HeadIdentifierProgram.program`, but inputs only a prefix length.
pub fn head_full_command() -> Result<Cmd<16, 64>, Error> {
    let pop_index = pop(39, 14, 15);
    let loop_cmd = Cmd::seq(
        pop_index.clone(),
        Cmd::while_(15, Cmd::seq(head_visit_command()?, pop_index)),
    );
    let reset = (0..16)
        .rev()
        .fold(Cmd::Skip, |rest, reg| Cmd::seq(set(reg, false), rest));
    Ok(Cmd::seq(
        copy(30, 39, 42)?,
        Cmd::seq(
            set(0, false),
            Cmd::seq(push(0, 0), Cmd::seq(loop_cmd, reset)),
        ),
    ))
}

pub fn head_full_program() -> Result<Program<16, 64>, Error> {
    head_full_command()?.compiled(30, 0)
}

/// Exact `LeafHeadSetupProgram.heads`, paid and isolated in work 340..403.
/// Source→callee: 128→30, 134→31, 649→32, 133→33, 132→38.
/// Callee→source: 0→650 (indices), 1→651 (zero word).
pub fn heads_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        head_full_program()?,
        std::array::from_fn(|i| i),
        &[(128, 30), (134, 31), (649, 32), (133, 33), (132, 38)],
        &[(0, 650), (1, 651)],
    )
}

pub fn heads_program() -> Result<Program<16, 768>, Error> {
    heads_command()?.compiled(128, 650)
}

/// First complete composition of the head selection and previously ported
/// support stages. This is only `seq heads support`, *not* `prepareHead`,
/// which still requires `LeafHeadFactorsProgram`.
pub fn heads_support_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(heads_command()?, support_command()?))
}

pub fn heads_support_program() -> Result<Program<16, 768>, Error> {
    heads_support_command()?.compiled(128, 670)
}
