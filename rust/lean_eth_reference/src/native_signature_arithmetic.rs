//! Source-literal arithmetic and row loops for attained-signature keys.
//!
//! Pinned Lean: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
//! `ArithmeticCalls.addAt`, `BucketProgramArithmetic.choiceAdd`,
//! `BucketProgramDot.dotStep`, `BucketProgramRow.rowCommand`, and
//! `BucketProgramNormalize.canonicalRowCommand`.
//!
//! All operands are stack words. There is no host integer addition in the
//! production path. Precondition: scratch/output ports reserved by the Lean
//! routines are empty at entry, and each row has one coefficient per bit.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_integer_cache::little_endian_add_program;
use crate::native_query_prefix::{frame_program, transfer_program};
use crate::native_signature_key::{attained_signature_program, canonical_row_normalize_call};

/// Source `ArithmeticCalls.addAt` at the physical `choicePorts` for a
/// particular assignment bit. Source stacks: left=2, right=0 or 1, out=3,
/// five work stacks=4..8. `addRaw` uses [out,work1,work2]=[3,5,6].
fn add_at(right: usize) -> Result<Cmd<8, 9>, Error> {
    if right != 0 && right != 1 {
        return Err(Error::Invalid(
            "choiceAdd right stack must be 0 or 1".into(),
        ));
    }
    let add = little_endian_add_program()?.lift::<8, 9>(std::array::from_fn(|i| i), [3, 5, 6])?;
    Ok(Cmd::seq(
        Cmd::Call(copy_program(2, 3, 7, 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(right, 5, 7, 0, 1)?),
            Cmd::seq(
                Cmd::Atom(Atom::Set {
                    dst: 0,
                    value: false,
                }),
                Cmd::Call(add),
            ),
        ),
    ))
}

/// Exact `BucketProgramArithmetic.choiceAdd` at 8 registers by 9 stacks.
/// The assignment bit selects source stack 1 (W+A) or stack 0 (W).
/// The previous accumulator on stack 2 is never consumed.
pub fn choice_add_command() -> Result<Cmd<8, 9>, Error> {
    Ok(Cmd::ite(0, add_at(1)?, add_at(0)?))
}

pub fn choice_add_program() -> Result<Program<8, 9>, Error> {
    choice_add_command()?.compiled(0, 3)
}

/// `BucketProgramDot.choiceCall`: place the 8x9 program on the first nine
/// stacks of the 8x12 dot machine, with the identity register map.
pub fn choice_call() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::Call(choice_add_program()?.lift::<8, 12>(
        std::array::from_fn(|i| i),
        std::array::from_fn(|i| i),
    )?))
}

/// `MatrixProgramSupport.readWord` at source ports (9,1,11).
fn read_coefficient() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(frame_program()?.lift::<8, 12>([0, 1], [9, 11])?),
        Cmd::Call(transfer_program(11, 1, 0, 1)?),
    ))
}

/// `MatrixProgramSupport.move 3 2 11`: reverse twice to preserve bit order.
fn move_sum_to_accumulator() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(transfer_program(3, 11, 0, 1)?),
        Cmd::Call(transfer_program(11, 2, 0, 1)?),
    ))
}

/// `BucketProgramDot.dotStep`: pop one framed coefficient, pop its matching
/// assignment bit, physically add the selected word to the accumulator,
/// clear the copied coefficient and old accumulator, and move the new sum.
pub fn dot_step_command() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::seq(
        read_coefficient()?,
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: 10,
                value: 0,
                present: 1,
            }),
            Cmd::seq(
                choice_call()?,
                Cmd::seq(
                    Cmd::Call(clear_program(1, 0, 1)?),
                    Cmd::seq(
                        Cmd::Call(clear_program(2, 0, 1)?),
                        move_sum_to_accumulator()?,
                    ),
                ),
            ),
        ),
    ))
}

pub fn dot_step_program() -> Result<Program<8, 12>, Error> {
    dot_step_command()?.compiled(9, 2)
}

/// `BucketProgramRow.rowCommand`: source end-of-frame guard, not a Rust-side
/// iterator over coefficient arrays. Empty heads perform no body calls.
pub fn row_command() -> Result<Cmd<8, 12>, Error> {
    let peek = Cmd::Atom(Atom::Peek {
        stack: 9,
        value: 0,
        present: 1,
    });
    Ok(Cmd::seq(
        peek.clone(),
        Cmd::while_(1, Cmd::seq(dot_step_command()?, peek)),
    ))
}

pub fn row_program() -> Result<Program<8, 12>, Error> {
    row_command()?.compiled(9, 2)
}

/// Exact `BucketProgramNormalize.canonicalRowCommand`, with the actual row
/// arithmetic followed by the already source-pinned 20-label normalizer.
pub fn canonical_row_command() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::seq(row_command()?, canonical_row_normalize_call()?))
}

pub fn canonical_row_program() -> Result<Program<8, 12>, Error> {
    canonical_row_command()?.compiled(9, 2)
}

/// The actual `AttainedSignatureProgram.program` assembled with its true
/// `canonicalRowProgram`, not a semantic evaluator supplied as a callback.
pub fn attained_key_program() -> Result<Program<8, 16>, Error> {
    attained_signature_program(&canonical_row_program()?)
}
