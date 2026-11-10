//! Executable, source-pinned physical normalization and H coefficient cache.
//!
//! Lean pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Definitions:
//! - ModularPrograms.paddingProgram (5 labels)
//! - ModularRingPrograms.normalizeProgram (12 linked labels)
//! - LayoutBinomialProgram.normalizeComponent, flatRow, flatProgram, finalFlatten
//! - LayoutProgramScalar.hFlatProgram
//! - LayoutProgram.IntegerCache.program
//!
//! These are fixed finite BitProgram instruction tables. Width, height, and
//! coefficient count enter as unary stack data, never as generated code size.
//! Caller preconditions (scratch stacks empty, admissible output width) remain
//! essential, just as in the Lean Eval theorems.

use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_cache_iteration::{cache_parse_command, h_build_program};
use crate::native_high::copy_program;
use crate::native_integer_cache::make_power_command;
use crate::native_query_prefix::transfer_program;

/// Literal `ModularPrograms.paddingProgram`: shape 0, word 1, reverse output 2.
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

/// Literal `ModularRingPrograms.normalizeProgram` (5+3+4 labels). The two
/// earlier halts link to the next table; the last halt remains terminal.
/// Source maps padding stacks [shape, input, output] to [7,0,2].
pub fn normalize_program() -> Result<Program<8, 8>, Error> {
    use Instr::*;
    Program::new(
        7,
        0,
        0,
        vec![
            Pop {
                stack: 7,
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
                stack: 0,
                value: 2,
                present: 4,
                next: 3,
            },
            Push {
                stack: 2,
                src: 2,
                next: 0,
            },
            Goto { next: 5 },
            Pop {
                stack: 0,
                value: 1,
                present: 3,
                next: 6,
            },
            Branch {
                test: 3,
                yes: 5,
                no: 7,
            },
            Goto { next: 8 },
            Pop {
                stack: 2,
                value: 1,
                present: 3,
                next: 9,
            },
            Branch {
                test: 3,
                yes: 10,
                no: 11,
            },
            Push {
                stack: 0,
                src: 1,
                next: 8,
            },
            Halt,
        ],
    )
}

/// The real `normalizeComponent`, including a paid width copy and paid
/// transfer into the reversed output buffer. Its input word is on stack 0,
/// unary width on stack 1, and existing output buffer on stack 2.
pub fn normalize_component_command() -> Result<Cmd<8, 9>, Error> {
    let copy_width = Cmd::Call(copy_program(1, 3, 4, 0, 1)?);
    let normalize = Cmd::Call(
        normalize_program()?.lift::<8, 9>(std::array::from_fn(|i| i), [0, 4, 5, 6, 7, 2, 8, 3])?,
    );
    let reverse_to_buffer = Cmd::Call(transfer_program(0, 2, 0, 1)?);
    Ok(Cmd::seq(copy_width, Cmd::seq(normalize, reverse_to_buffer)))
}

pub fn normalize_component_program() -> Result<Program<8, 9>, Error> {
    normalize_component_command()?.compiled(0, 2)
}

/// `LayoutBinomialProgram.flatParse`: fixed program lift of existing parser.
fn flat_parse_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::Call(
        cache_parse_command()?
            .compiled(15, 15)?
            .lift::<8, 19>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    ))
}

fn flat_positive_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::Call(normalize_component_program()?.lift::<8, 19>(
        std::array::from_fn(|i| i),
        [2, 18, 16, 4, 5, 6, 7, 8, 9],
    )?))
}

fn flat_negative_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::Call(normalize_component_program()?.lift::<8, 19>(
        std::array::from_fn(|i| i),
        [3, 18, 17, 4, 5, 6, 7, 8, 9],
    )?))
}

/// Parse every framed signed component, normalize both words and write them
/// to reverse buffers 16 and 17. Source: `flatRow`.
pub fn flat_row_command() -> Result<Cmd<8, 19>, Error> {
    let parse = flat_parse_command()?;
    Ok(Cmd::seq(
        parse.clone(),
        Cmd::while_(
            7,
            Cmd::seq(
                flat_positive_command()?,
                Cmd::seq(flat_negative_command()?, parse),
            ),
        ),
    ))
}

pub fn flat_row_program() -> Result<Program<8, 19>, Error> {
    flat_row_command()?.compiled(15, 16)
}

/// Physical transfers from reverse accumulators to ascending flat arrays.
pub fn flat_finish_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer_program(16, 0, 0, 1)?),
        Cmd::Call(transfer_program(17, 1, 0, 1)?),
    ))
}

pub fn flat_command() -> Result<Cmd<8, 19>, Error> {
    Ok(Cmd::seq(flat_row_command()?, flat_finish_command()?))
}

pub fn flat_program() -> Result<Program<8, 19>, Error> {
    flat_command()?.compiled(15, 0)
}

/// Source `LayoutBinomialProgram.finalFlatten` into 8 registers / 20 stacks.
/// `flatFinalPorts` preserves stacks 0..17 and maps width 18 to 19.
pub fn final_flatten_command() -> Result<Cmd<8, 20>, Error> {
    Ok(Cmd::Call(flat_program()?.lift::<8, 20>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| if i == 18 { 19 } else { i }),
    )?))
}

/// `LayoutProgramScalar.hFlatCommand` = lifted H build + `finalFlatten`.
pub fn h_flat_command() -> Result<Cmd<8, 20>, Error> {
    let builder = Cmd::Call(
        h_build_program()?.lift::<8, 20>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    );
    Ok(Cmd::seq(builder, final_flatten_command()?))
}

pub fn h_flat_program() -> Result<Program<8, 20>, Error> {
    h_flat_command()?.compiled(17, 0)
}

/// `LayoutProgram.IntegerCache.command`: preserve all three runtime unary
/// inputs, build both flat coefficient arrays, then generate 2^(R-1).
/// Outputs are positive 0, negative 1, denominator 2, retained width 19.
pub fn integer_cache_command() -> Result<Cmd<8, 24>, Error> {
    let copy_a = Cmd::Call(copy_program(20, 17, 3, 0, 1)?);
    let copy_r = Cmd::Call(copy_program(21, 18, 3, 0, 1)?);
    let copy_width = Cmd::Call(copy_program(22, 19, 3, 0, 1)?);
    let flat = Cmd::Call(
        h_flat_program()?.lift::<8, 24>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    );
    Ok(Cmd::seq(
        copy_a,
        Cmd::seq(
            copy_r,
            Cmd::seq(copy_width, Cmd::seq(flat, make_power_command()?)),
        ),
    ))
}

pub fn integer_cache_program() -> Result<Program<8, 24>, Error> {
    integer_cache_command()?.compiled(20, 0)
}
