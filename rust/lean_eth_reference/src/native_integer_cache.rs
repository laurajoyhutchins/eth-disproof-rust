//! Concrete arithmetic and framing prerequisites for the integer H cache.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! - `BinaryPrograms.lean`: `Add.program`, `Add.littleEndianProgram`
//! - `SqrtLog/LayoutProgramScalarCacheCell.lean`: `cacheCellLocal`, `cacheCell`
//! - `SqrtLog/LayoutProgramPower.lean`: `powerCommand`
//! - `SqrtLog/LayoutProgramIntegerCache.lean`: `copies`, `makePower`
//!
//! IMPORTANT: `LayoutProgramScalar.hFlatProgram` (the coefficient-table
//! producer) is not implemented. In particular, these independent prefix,
//! cell and suffix commands are *not* an implementation of the complete
//! `LayoutProgram.IntegerCache.program` or `SignatureHeadLoader.bootstrapProgram`.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::copy_program;

/// The exact 13 labels of `BinaryPrograms.Add.program`.
/// The result is written in reverse order to stack 2.
pub fn binary_add_program() -> Result<Program<8, 3>, Error> {
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
            Pop {
                stack: 1,
                value: 2,
                present: 4,
                next: 2,
            },
            Branch {
                test: 3,
                yes: 4,
                no: 3,
            },
            Branch {
                test: 4,
                yes: 4,
                no: 10,
            },
            Xor {
                dst: 5,
                left: 1,
                right: 2,
                next: 5,
            },
            And {
                dst: 6,
                left: 1,
                right: 2,
                next: 6,
            },
            And {
                dst: 7,
                left: 5,
                right: 0,
                next: 7,
            },
            Xor {
                dst: 1,
                left: 5,
                right: 0,
                next: 8,
            },
            Xor {
                dst: 0,
                left: 6,
                right: 7,
                next: 9,
            },
            Push {
                stack: 2,
                src: 1,
                next: 0,
            },
            Branch {
                test: 0,
                yes: 11,
                no: 12,
            },
            Push {
                stack: 2,
                src: 0,
                next: 12,
            },
            Halt,
        ],
    )
}

/// Source `ProgramLinking.link Add.program (transferProgram 2 0 1 3)`.
/// The literal 17-label table has *one* final halt, with the adder's first
/// halt relocated to label 13. No extra compiled wrapper or virtual reversal.
pub fn little_endian_add_program() -> Result<Program<8, 3>, Error> {
    let mut code = binary_add_program()?.code().to_vec();
    code[12] = Instr::Goto { next: 13 };
    code.extend([
        Instr::Pop {
            stack: 2,
            value: 1,
            present: 3,
            next: 14,
        },
        Instr::Branch {
            test: 3,
            yes: 15,
            no: 16,
        },
        Instr::Push {
            stack: 0,
            src: 1,
            next: 13,
        },
        Instr::Halt,
    ]);
    Program::new(0, 0, 0, code)
}

/// `LayoutProgramScalar.cacheCellLocal`: prepend one zero to the prior H
/// coefficient (multiplication by two), then run the exact linked adder.
pub fn cache_cell_local_command() -> Result<Cmd<8, 3>, Error> {
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 0, src: 0 }),
            Cmd::Call(little_endian_add_program()?),
        ),
    ))
}

pub fn cache_cell_local_program() -> Result<Program<8, 3>, Error> {
    cache_cell_local_command()?.compiled(0, 0)
}

/// Actual 8x18 cache cell, mapping physical stacks 0,2,4.
pub fn cache_cell_command() -> Result<Cmd<8, 18>, Error> {
    Ok(Cmd::Call(
        cache_cell_local_program()?.lift::<8, 18>(std::array::from_fn(|i| i), [0, 2, 4])?,
    ))
}

pub fn cache_cell_program() -> Result<Program<8, 18>, Error> {
    cache_cell_command()?.compiled(0, 0)
}

/// `LayoutProgram.IntegerCache.copies` (the full pre-H-flat prefix).
/// The source parameters at 20..22 are preserved, and copies at 17..19 are
/// prepended to their existing destinations, as in `StackRoutines.copyProgram`.
pub fn cache_copies_command() -> Result<Cmd<8, 24>, Error> {
    let c =
        |src, dst| -> Result<Cmd<8, 24>, Error> { Ok(Cmd::Call(copy_program(src, dst, 3, 0, 1)?)) };
    Ok(Cmd::seq(c(20, 17)?, Cmd::seq(c(21, 18)?, c(22, 19)?)))
}

pub fn cache_copies_program() -> Result<Program<8, 24>, Error> {
    cache_copies_command()?.compiled(20, 0)
}

/// `LayoutProgram.powerCommand` in the original 2x2 machine. The exponent
/// is unary, and the little-endian output is 2^q, not a host integer.
pub fn power_command() -> Cmd<2, 2> {
    let read = Cmd::Atom(Atom::Pop {
        stack: 0,
        value: 0,
        present: 1,
    });
    let put_zero = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
    );
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
            Cmd::seq(read.clone(), Cmd::while_(1, Cmd::seq(put_zero, read))),
        ),
    )
}

pub fn power_program() -> Result<Program<2, 2>, Error> {
    power_command().compiled(0, 1)
}

/// Literal `IntegerCache.makePower` suffix. Presumes `hFlatProgram` has
/// already produced the coefficient stacks; does not create those stacks.
pub fn make_power_command() -> Result<Cmd<8, 24>, Error> {
    let copy = Cmd::Call(copy_program(21, 23, 3, 0, 1)?);
    let pop = Cmd::Atom(Atom::Pop {
        stack: 23,
        value: 0,
        present: 1,
    });
    let power = Cmd::Call(power_program()?.lift::<8, 24>([0, 1], [23, 2])?);
    Ok(Cmd::seq(copy, Cmd::seq(pop, power)))
}

pub fn make_power_program() -> Result<Program<8, 24>, Error> {
    make_power_command()?.compiled(21, 2)
}

/// `ArithmeticExpressionSupport.pushWord`, the literal sequence of register
/// sets and stack pushes. The bits are supplied in *logical* top-first order;
/// the instruction sequence emits them from the tail to preserve that order.
fn push_word<const R: usize, const S: usize>(port: usize, bits: &[bool]) -> Cmd<R, S> {
    bits.iter().rev().fold(Cmd::Skip, |prefix, &bit| {
        Cmd::seq(
            prefix,
            Cmd::seq(
                Cmd::Atom(Atom::Set { dst: 0, value: bit }),
                Cmd::Atom(Atom::Push {
                    stack: port,
                    src: 0,
                }),
            ),
        )
    })
}

/// `LayoutProgramScalar.initialCommand`: physically creates the framed
/// all-one binomial row from the length of stack 17. This is the *H* builder's
/// initial row, not `LayoutBinomialProgram.initialCommand`'s different row.
pub fn initial_h_command() -> Cmd<8, 18> {
    let pop = Cmd::Atom(Atom::Pop {
        stack: 17,
        value: 7,
        present: 6,
    });
    Cmd::seq(
        push_word(15, &[false]),
        Cmd::seq(
            pop.clone(),
            Cmd::while_(
                6,
                Cmd::seq(push_word(15, &[true, true, true, false, false]), pop),
            ),
        ),
    )
}

pub fn initial_h_program() -> Result<Program<8, 18>, Error> {
    initial_h_command().compiled(17, 15)
}

/// Source `LayoutProgramScalar.initialBuild` (the lifted initial row in the
/// 8×19 coefficient-builder). Low stack17 maps to high stack18; all other
/// low ports retain their physical addresses.
pub fn initial_h_build_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::Call(initial_h_program()?.lift::<8, 19>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| if i == 17 { 18 } else { i }),
    )?))
}

pub fn initial_h_build_program() -> Result<Program<8, 19>, Error> {
    initial_h_build_command()?.compiled(18, 15)
}
