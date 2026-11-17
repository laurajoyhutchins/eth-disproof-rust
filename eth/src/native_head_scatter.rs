//! Physical fixed-width array replacement and head-bit scatter.
//!
//! Source pinned at `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! - `ArrayPrograms.countedTransferProgram`, `countedSkipProgram`
//! - `ArrayUpdatePrograms.replaceProgram` (exact 44-label compiled command)
//! - `SqrtLog.HeadScatterProgram.scatterStep`
//!
//! All loops operate over unary stack data. No semantic array splice is used
//! to implement the runtime programs. The input invariants in the Lean proofs
//! (uniform record widths, in-range index, empty work stacks) are still caller
//! obligations; the executable code does not magically validate them.
use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::{frame_program, transfer_program};

fn pop<const R: usize, const S: usize>(stack: usize, value: usize, present: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Pop {
        stack,
        value,
        present,
    })
}

/// The actual 5-label counted stack transfer. The counter length is runtime
/// data, and the transferred prefix is reversed on the destination stack.
pub fn counted_transfer_program<const R: usize, const S: usize>(
    counter: usize,
    src: usize,
    dst: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if value == present || counter == src || counter == dst || src == dst {
        return Err(Error::Invalid(
            "counted transfer requires disjoint ports".into(),
        ));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: counter,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 4,
            },
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 3,
            },
            Instr::Push {
                stack: dst,
                src: value,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// The actual 7-label counted skip. Work stack `tmp` must start empty.
pub fn counted_skip_program<const R: usize, const S: usize>(
    counter: usize,
    src: usize,
    tmp: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if value == present || counter == src || counter == tmp || src == tmp {
        return Err(Error::Invalid(
            "counted skip requires disjoint ports".into(),
        ));
    }
    Program::new(
        src,
        src,
        0,
        vec![
            Instr::Pop {
                stack: counter,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 4,
            },
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 3,
            },
            Instr::Push {
                stack: tmp,
                src: value,
                next: 0,
            },
            Instr::Pop {
                stack: tmp,
                value,
                present,
                next: 5,
            },
            Instr::Branch {
                test: present,
                yes: 4,
                no: 6,
            },
            Instr::Halt,
        ],
    )
}

fn save_record<const R: usize>(value: usize, present: usize) -> Result<Cmd<R, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(3, 4, 5, value, present)?),
        Cmd::Call(counted_transfer_program(4, 0, 7, value, present)?),
    ))
}

fn save_before<const R: usize>(value: usize, present: usize) -> Result<Cmd<R, 8>, Error> {
    let read_index = pop(2, value, present);
    Ok(Cmd::seq(
        read_index.clone(),
        Cmd::while_(present, Cmd::seq(save_record(value, present)?, read_index)),
    ))
}

fn replace_selected<const R: usize>(value: usize, present: usize) -> Result<Cmd<R, 8>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(3, 4, 5, value, present)?),
        Cmd::seq(
            Cmd::Call(counted_skip_program(4, 0, 6, value, present)?),
            Cmd::Call(copy_program(1, 0, 6, value, present)?),
        ),
    ))
}

/// Original `ArrayUpdatePrograms.replaceCmd`: save `index` preceding records,
/// replace the selected word with the preserving word on stack 1, and restore
/// the earlier array prefix in correct order. Source stacks:
/// array 0, replacement 1, unary index 2, unary width 3, work 4..7.
pub fn replace_command<const R: usize>(value: usize, present: usize) -> Result<Cmd<R, 8>, Error> {
    if value == present || value >= R || present >= R {
        return Err(Error::Invalid(
            "array replacement read registers invalid".into(),
        ));
    }
    Ok(Cmd::seq(
        save_before(value, present)?,
        Cmd::seq(
            replace_selected(value, present)?,
            Cmd::Call(transfer_program(7, 0, value, present)?),
        ),
    ))
}

/// Source `ArrayUpdatePrograms.replaceProgram` has 44 labels, independent of
/// the array length, index, and record width.
pub fn replace_program<const R: usize>(
    value: usize,
    present: usize,
) -> Result<Program<R, 8>, Error> {
    replace_command(value, present)?.compiled(0, 0)
}

/// The complete single-index `HeadScatterProgram.scatterStep` machine.
/// Its input is the source-encoded unary index record on stack 2, the next
/// head bit on stack 1, ambient bit array on stack 0, and width `[true]` on 5.
/// Output is an updated physical ambient mask with consumed index/bit.
pub fn scatter_step_command() -> Result<Cmd<8, 13>, Error> {
    let pop_index_tag = pop(2, 0, 1);
    let read_index = Cmd::Call(frame_program()?.lift::<8, 13>([0, 1], [2, 3])?);
    let pop_bit = pop(1, 0, 1);
    let push_bit = Cmd::Atom(Atom::Push { stack: 4, src: 0 });
    let replace = Cmd::Call(
        replace_program::<8>(0, 1)?
            .lift::<8, 13>(std::array::from_fn(|i| i), [0, 4, 3, 5, 6, 7, 8, 9])?,
    );
    let clear_bit = Cmd::Call(clear_program(4, 0, 1)?);
    Ok(Cmd::seq(
        pop_index_tag,
        Cmd::seq(
            read_index,
            Cmd::seq(pop_bit, Cmd::seq(push_bit, Cmd::seq(replace, clear_bit))),
        ),
    ))
}

pub fn scatter_step_program() -> Result<Program<8, 13>, Error> {
    scatter_step_command()?.compiled(2, 0)
}

/// Five-label constant-work zero-array emitter from `HeadScatterProgramInit`.
/// Its loop consumes the copied unary ambient size on stack 3 and pushes a
/// false bit for every unit onto stack 0.
pub fn zero_mask_program() -> Result<Program<8, 13>, Error> {
    Program::new(
        3,
        0,
        0,
        vec![
            Instr::Pop {
                stack: 3,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 4,
            },
            Instr::Set {
                dst: 0,
                value: false,
                next: 3,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// `HeadScatterProgram.initCommand`: preservation copies of index stream,
/// head-bit stream and ambient size, a real zero mask, and unary width one.
pub fn scatter_init_command() -> Result<Cmd<8, 13>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(10, 2, 3, 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(11, 1, 3, 0, 1)?),
            Cmd::seq(
                Cmd::Call(copy_program(12, 3, 4, 0, 1)?),
                Cmd::seq(
                    Cmd::Call(zero_mask_program()?),
                    Cmd::seq(
                        Cmd::Atom(Atom::Set {
                            dst: 0,
                            value: true,
                        }),
                        Cmd::Atom(Atom::Push { stack: 5, src: 0 }),
                    ),
                ),
            ),
        ),
    ))
}

/// `HeadScatterProgramScan.scanCommand`. Each iteration runs the complete
/// source `scatterStep` machine and a non-consuming guard peek.
pub fn scatter_scan_command() -> Result<Cmd<8, 13>, Error> {
    let peek = Cmd::Atom(Atom::Peek {
        stack: 1,
        value: 0,
        present: 1,
    });
    Ok(Cmd::seq(
        peek.clone(),
        Cmd::while_(1, Cmd::seq(scatter_step_command()?, peek)),
    ))
}

/// `HeadScatterProgramRun.command`, including the paid cleanups of ports 2
/// and 5. This is the *whole* source head-scatter program, not only one step.
pub fn head_scatter_command() -> Result<Cmd<8, 13>, Error> {
    Ok(Cmd::seq(
        scatter_init_command()?,
        Cmd::seq(
            scatter_scan_command()?,
            Cmd::seq(
                Cmd::Call(clear_program(2, 0, 1)?),
                Cmd::seq(Cmd::Call(clear_program(5, 0, 1)?), Cmd::Skip),
            ),
        ),
    ))
}

pub fn head_scatter_program() -> Result<Program<8, 13>, Error> {
    head_scatter_command()?.compiled(10, 0)
}
