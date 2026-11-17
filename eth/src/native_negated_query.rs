//! Literal source SubexpNegatedQueryProgram: preserve a reversed unary query,
//! reverse to canonical order, invert encoded polarity, then reverse back.
use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_high::copy_program;
use crate::native_normalization_primitives::negate_literal_program;

/// Exact ten-label StackRoutines.reverseProgram using two empty scratch stacks.
pub fn reverse_program<const R: usize, const S: usize>(
    src: usize,
    tmp1: usize,
    tmp2: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if src == tmp1 || src == tmp2 || tmp1 == tmp2 || value == present {
        return Err(Error::Invalid("reverse requires distinct ports".into()));
    }
    use Instr as I;
    Program::new(
        src,
        src,
        0,
        vec![
            I::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            I::Branch {
                test: present,
                yes: 2,
                no: 3,
            },
            I::Push {
                stack: tmp1,
                src: value,
                next: 0,
            },
            I::Pop {
                stack: tmp1,
                value,
                present,
                next: 4,
            },
            I::Branch {
                test: present,
                yes: 5,
                no: 6,
            },
            I::Push {
                stack: tmp2,
                src: value,
                next: 3,
            },
            I::Pop {
                stack: tmp2,
                value,
                present,
                next: 7,
            },
            I::Branch {
                test: present,
                yes: 8,
                no: 9,
            },
            I::Push {
                stack: src,
                src: value,
                next: 6,
            },
            I::Halt,
        ],
    )
}

/// Source command: copy 0 -> 2 through 3, reverse 2 in-place via 1/3,
/// complement unary from 2 to 1, reverse 1 in-place via 2/3.
pub fn command() -> Result<Cmd<2, 4>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(0, 2, 3, 0, 1)?),
        Cmd::seq(
            Cmd::Call(reverse_program(2, 1, 3, 0, 1)?),
            Cmd::seq(
                Cmd::Call(negate_literal_program()?.lift::<2, 4>([0, 1], [2, 1])?),
                Cmd::Call(reverse_program(1, 2, 3, 0, 1)?),
            ),
        ),
    ))
}
pub fn program() -> Result<Program<2, 4>, Error> {
    command()?.compiled(0, 1)
}
