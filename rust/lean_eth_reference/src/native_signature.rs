//! Fully executable finite signature-key pipeline over shifted matrix words.
//!
//! Pinned source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! - `SubexpParameterProgram.prepareLogProgram` (linked 10-label table)
//! - `CounterNormalizeProgram.program` (canonical little-endian positive word)
//! - `BucketProgramArithmetic.choiceAdd`, `BucketProgramDot.dotStep`
//! - `BucketProgramRow.rowProgram`, `BucketProgramNormalize.canonicalRowProgram`
//! - `BucketProgramSignature.signatureProgram` (complete nested row scanner)
//!
//! All operations use actual compiled Boolean-stack instructions. The only
//! arithmetic oracle is in the tests. `signatureProgram` requires a shifted
//! (nonnegative) coefficient matrix and head-assignment bits of matching width.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_matrix_preprocess::{emit_frame_command, read_word_command};
use crate::native_query_prefix::transfer_program;
use crate::native_signed_arithmetic::add_at_command;

fn seq<const R: usize, const S: usize>(cmds: impl IntoIterator<Item = Cmd<R, S>>) -> Cmd<R, S> {
    cmds.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(Cmd::Skip, |rest, first| Cmd::seq(first, rest))
}
fn atom<const R: usize, const S: usize>(a: Atom) -> Cmd<R, S> {
    Cmd::Atom(a)
}
fn call<const R: usize, const S: usize>(p: Program<R, S>) -> Cmd<R, S> {
    Cmd::Call(p)
}
fn peek<const R: usize, const S: usize>(stack: usize) -> Cmd<R, S> {
    atom(Atom::Peek {
        stack,
        value: 0,
        present: 1,
    })
}
fn move_word<const S: usize>(src: usize, dst: usize, tmp: usize) -> Result<Cmd<8, S>, Error> {
    Ok(seq([
        call(transfer_program(src, tmp, 0, 1)?),
        call(transfer_program(tmp, dst, 0, 1)?),
    ]))
}

/// Actual 10-label link `reverseTransfer ++ trimProgram`.
/// `reverseTransfer` physically transfers input stack 0 to stack 1 in reverse,
/// then `trimProgram` consumes the high zeros and the highest one.
pub fn prepare_log_program() -> Result<Program<3, 3>, Error> {
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
                no: 3,
            },
            Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Goto { next: 4 },
            Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 5,
            },
            Branch {
                test: 1,
                yes: 6,
                no: 7,
            },
            Branch {
                test: 0,
                yes: 7,
                no: 4,
            },
            Set {
                dst: 0,
                value: false,
                next: 8,
            },
            Set {
                dst: 1,
                value: false,
                next: 9,
            },
            Halt,
        ],
    )
}

/// `CounterNormalizeProgram.command` and its actual compiled machine.
/// For positive input, output stack 0 has no unnecessary most-significant zeros.
pub fn normalize_command() -> Result<Cmd<3, 3>, Error> {
    Ok(seq([
        atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        atom(Atom::Set {
            dst: 1,
            value: false,
        }),
        atom(Atom::Set {
            dst: 2,
            value: false,
        }),
        call(prepare_log_program()?),
        atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        atom(Atom::Push { stack: 1, src: 0 }),
        call(transfer_program(1, 0, 0, 1)?),
    ]))
}
pub fn normalize_program() -> Result<Program<3, 3>, Error> {
    normalize_command()?.compiled(0, 0)
}

/// `BucketProgram.choiceAdd`: conditional addition of W or coefficient to
/// the incoming accumulator. Ports: 0=W, 1=coefficient, 2=accumulator,
/// 3=result; scratch 4..8. The selector is register 0.
pub fn choice_add_command() -> Result<Cmd<8, 9>, Error> {
    Ok(Cmd::ite(
        0,
        add_at_command(2, 1, 3, [4, 5, 6, 7, 8])?,
        add_at_command(2, 0, 3, [4, 5, 6, 7, 8])?,
    ))
}
pub fn choice_add_program() -> Result<Program<8, 9>, Error> {
    choice_add_command()?.compiled(0, 3)
}

/// Original `BucketProgram.dotStep`:
/// read framed coefficient, pop bit, conditionally add, clear used operands,
/// and transfer the new accumulator back to stack2.
pub fn dot_step_command() -> Result<Cmd<8, 12>, Error> {
    Ok(seq([
        read_word_command(9, 1, 11)?,
        atom(Atom::Pop {
            stack: 10,
            value: 0,
            present: 1,
        }),
        call(
            choice_add_program()?
                .lift::<8, 12>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
        ),
        call(clear_program(1, 0, 1)?),
        call(clear_program(2, 0, 1)?),
        move_word(3, 2, 11)?,
    ]))
}
pub fn row_command() -> Result<Cmd<8, 12>, Error> {
    Ok(seq([
        peek(9),
        Cmd::while_(1, seq([dot_step_command()?, peek(9)])),
    ]))
}
pub fn row_program() -> Result<Program<8, 12>, Error> {
    row_command()?.compiled(9, 2)
}
/// Original `BucketProgram.canonicalRowCommand`, using actual binary
/// normalization, not a host integer conversion.
pub fn canonical_row_command() -> Result<Cmd<8, 12>, Error> {
    Ok(seq([
        row_command()?,
        call(normalize_program()?.lift::<8, 12>([0, 1, 2], [2, 3, 4])?),
    ]))
}
pub fn canonical_row_program() -> Result<Program<8, 12>, Error> {
    canonical_row_command()?.compiled(9, 2)
}

/// `BucketProgram.signatureStep`: framed row decode, assignment copy,
/// accumulator seed (1), canonical row call, framed key emission.
pub fn signature_step_command() -> Result<Cmd<8, 15>, Error> {
    Ok(seq([
        read_word_command(13, 9, 11)?,
        call(copy_program(12, 10, 11, 0, 1)?),
        atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        atom(Atom::Push { stack: 2, src: 0 }),
        call(
            canonical_row_program()?
                .lift::<8, 15>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
        ),
        emit_frame_command(2, 14, 11)?,
    ]))
}
/// Complete source `BucketProgram.signatureProgram`, compiled on 8×15.
/// Input stacks 0=W, 12=assignment bits, 13=framed unsigned rows;
/// output stack14 contains framed canonical row keys in reverse row order.
pub fn signature_command() -> Result<Cmd<8, 15>, Error> {
    Ok(seq([
        peek(13),
        Cmd::while_(1, seq([signature_step_command()?, peek(13)])),
    ]))
}
pub fn signature_program() -> Result<Program<8, 15>, Error> {
    signature_command()?.compiled(13, 14)
}

/// Integration adapter built *only* from the two independently source-defined
/// fixed programs: `BucketProgram.preMatrixProgram` followed by
/// `BucketProgram.signatureProgram`. This combined adapter is **not** an
/// additional upstream Lean definition and is not the native incidence-entry
/// generator. Its purpose is an executable, direct, single-machine proof gate
/// across the signed matrix / shifted matrix / signature ABI boundary.
///
/// Physical 8×64 ports: 0=offset W, 14=raw signed rows, 17=assignment bits,
/// 15=produced unsigned matrix, 18=canonical framed signature keys.
/// The internal work ports are 1..13 and 16; they must start empty.
/// The adapter consumes 14 and preserves 0/15/17. It never moves data through
/// the host outside Boolean-stack machine instructions.
pub fn signed_matrix_signature_command() -> Result<Cmd<8, 64>, Error> {
    use crate::native_matrix_preprocess::pre_matrix_program;
    let pre = pre_matrix_program()?
        .lift::<8, 64>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    let signature_stack_map = std::array::from_fn(|i| if i == 14 { 18 } else { i });
    let signature =
        signature_program()?.lift::<8, 64>(std::array::from_fn(|i| i), signature_stack_map)?;
    Ok(seq([
        call(pre),
        call(copy_program(17, 12, 16, 0, 1)?),
        call(copy_program(15, 13, 16, 0, 1)?),
        call(signature),
        call(clear_program(12, 0, 1)?),
    ]))
}
pub fn signed_matrix_signature_program() -> Result<Program<8, 64>, Error> {
    signed_matrix_signature_command()?.compiled(14, 18)
}
