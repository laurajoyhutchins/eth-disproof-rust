//! Source-instruction arithmetic for signed incidence entries.
//!
//! Pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! `ModularPrograms`, `SaturatingSubtractionProgram`,
//! `ArithmeticCalls`, `SqrtLog/BucketProgram{Arithmetic,Shift}`.
//!
//! Every arithmetic step below is a finite Boolean-stack instruction.
//! Numeric conversions belong only in the independent test oracle.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_integer_cache::little_endian_add_program;
use crate::native_query_prefix::transfer_program;

fn atom<const R: usize, const S: usize>(a: Atom) -> Cmd<R, S> {
    Cmd::Atom(a)
}
fn call<const R: usize, const S: usize>(p: Program<R, S>) -> Cmd<R, S> {
    Cmd::Call(p)
}
fn series<const R: usize, const S: usize>(cmds: impl IntoIterator<Item = Cmd<R, S>>) -> Cmd<R, S> {
    cmds.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(Cmd::Skip, |rest, first| Cmd::seq(first, rest))
}

/// Exact 13-label `ModularPrograms.subtractProgram` (reverse output).
/// Register 0 is the incoming and outgoing borrow bit.
pub fn subtract_program() -> Result<Program<8, 3>, Error> {
    use Instr::*;
    Program::new(
        0,
        2,
        0,
        vec![
            Pop {
                stack: 0,
                value: 1,
                present: 3,
                next: 1,
            },
            Branch {
                test: 3,
                yes: 2,
                no: 12,
            },
            Pop {
                stack: 1,
                value: 2,
                present: 4,
                next: 3,
            },
            Xor {
                dst: 5,
                left: 1,
                right: 2,
                next: 4,
            },
            Xor {
                dst: 6,
                left: 5,
                right: 0,
                next: 5,
            },
            Not {
                dst: 7,
                src: 1,
                next: 6,
            },
            And {
                dst: 7,
                left: 7,
                right: 2,
                next: 7,
            },
            Not {
                dst: 5,
                src: 5,
                next: 8,
            },
            And {
                dst: 5,
                left: 5,
                right: 0,
                next: 9,
            },
            Xor {
                dst: 0,
                left: 7,
                right: 5,
                next: 10,
            },
            Push {
                stack: 2,
                src: 6,
                next: 11,
            },
            Goto { next: 0 },
            Halt,
        ],
    )
}

/// Literal 5-label source padding table. The caller requires input length
/// no larger than shape length; the machine itself operates on raw stacks.
pub fn padding_program() -> Result<Program<8, 3>, Error> {
    use Instr::*;
    Program::new(
        0,
        2,
        0,
        vec![
            Pop {
                stack: 0,
                value: 1,
                present: 3,
                next: 1,
            },
            Branch {
                test: 3,
                yes: 2,
                no: 4,
            },
            Pop {
                stack: 1,
                value: 2,
                present: 4,
                next: 3,
            },
            Push {
                stack: 2,
                src: 2,
                next: 0,
            },
            Halt,
        ],
    )
}

/// `ProgramLinking.link` has *one* final halt; the inner halt is relocated
/// into the four-label transfer suffix. No extra host-language reversal.
fn append_reverse(p: Program<8, 3>) -> Result<Program<8, 3>, Error> {
    let offset = p.code().len();
    let mut code = p.code().to_vec();
    if !matches!(code[offset - 1], Instr::Halt) {
        return Err(Error::Invalid(
            "arithmetic program must terminate in halt".into(),
        ));
    }
    code[offset - 1] = Instr::Goto { next: offset };
    let reverse = transfer_program::<8, 3>(2, 0, 1, 3)?;
    for ins in reverse.code() {
        let next = match ins {
            Instr::Pop {
                stack,
                value,
                present,
                next,
            } => Instr::Pop {
                stack: *stack,
                value: *value,
                present: *present,
                next: offset + next,
            },
            Instr::Branch { test, yes, no } => Instr::Branch {
                test: *test,
                yes: offset + yes,
                no: offset + no,
            },
            Instr::Push { stack, src, next } => Instr::Push {
                stack: *stack,
                src: *src,
                next: offset + next,
            },
            Instr::Halt => Instr::Halt,
            _ => return Err(Error::Invalid("unexpected transfer instruction".into())),
        };
        code.push(next);
    }
    Program::new(0, 0, 0, code)
}

/// Exact 17-label linked little-endian subtractor, preserving borrow.
pub fn subtract_le_program() -> Result<Program<8, 3>, Error> {
    append_reverse(subtract_program()?)
}
/// Exact 9-label linked little-endian padding machine.
pub fn padding_le_program() -> Result<Program<8, 3>, Error> {
    append_reverse(padding_program()?)
}

/// Source `SaturatingSubtractionProgram.command` in its full 8×8 bank.
/// Preserves both input words; computes `max(W-N,0)` as little-endian bits.
/// Critically, this calls the *actual* padding and borrow-tracking subtractor.
pub fn saturating_subtract_command() -> Result<Cmd<8, 8>, Error> {
    let mut parts = Vec::new();
    for (src, dst) in [(1, 2), (0, 2), (1, 3), (0, 3), (0, 4), (1, 5)] {
        parts.push(call(copy_program(src, dst, 6, 0, 1)?));
    }
    let pad = padding_le_program()?;
    parts.push(call(
        pad.lift::<8, 8>(std::array::from_fn(|i| i), [2, 4, 6])?,
    ));
    parts.push(call(
        pad.lift::<8, 8>(std::array::from_fn(|i| i), [3, 5, 6])?,
    ));
    parts.push(atom(Atom::Set {
        dst: 0,
        value: false,
    }));
    parts.push(call(
        subtract_le_program()?.lift::<8, 8>(std::array::from_fn(|i| i), [2, 3, 6])?,
    ));
    parts.push(Cmd::ite(0, call(clear_program(2, 0, 1)?), Cmd::Skip));
    for r in 0..8 {
        parts.push(atom(Atom::Set {
            dst: r,
            value: false,
        }));
    }
    Ok(series(parts))
}
pub fn saturating_subtract_program() -> Result<Program<8, 8>, Error> {
    saturating_subtract_command()?.compiled(0, 2)
}

/// `ArithmeticCalls.addAt` on fixed physical ports, with scratch [3..7].
/// The incoming operands remain intact and the result is written on output.
pub fn add_at_command<const S: usize>(
    left: usize,
    right: usize,
    out: usize,
    work: [usize; 5],
) -> Result<Cmd<8, S>, Error> {
    // Left and right are permitted to coincide in the Lean Ports contract.
    if [out, work[0], work[1], work[2], work[3], work[4]]
        .iter()
        .any(|x| *x >= S)
        || left >= S
        || right >= S
        || left == out
        || right == out
        || work
            .iter()
            .enumerate()
            .any(|(i, w)| left == *w || right == *w || out == *w || work[i + 1..].contains(w))
    {
        return Err(Error::Invalid("invalid arithmetic work ports".into()));
    }
    let add = little_endian_add_program()?
        .lift::<8, S>(std::array::from_fn(|i| i), [out, work[1], work[2]])?;
    Ok(series([
        call(copy_program(left, out, work[3], 0, 1)?),
        call(copy_program(right, work[1], work[3], 0, 1)?),
        atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        call(add),
    ]))
}

/// `BucketProgram.shiftCommand`: little-endian subtraction W-N with
/// saturation followed by paid addition of P. Input stacks 0=W, 1=N,
/// 8=P; result stack 9, difference workspace 2. Stack 0 and 1 survive.
pub fn shift_command() -> Result<Cmd<8, 10>, Error> {
    Ok(series([
        call(
            saturating_subtract_program()?
                .lift::<8, 10>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
        ),
        add_at_command(2, 8, 9, [3, 4, 5, 6, 7])?,
    ]))
}
pub fn shift_program() -> Result<Program<8, 10>, Error> {
    shift_command()?.compiled(0, 9)
}
