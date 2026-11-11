//! Complete physical signed-matrix preprocessing and signature shift readout.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! `SqrtLog/BucketProgramPreprocess{Reverse,Step,Row,Matrix}.lean`,
//! `SqrtLogSpace/SignatureHeadLoaderCore.lean`.
//!
//! Each `readWord`, `emitFrame`, nested scan, and order-repair operation is a
//! compiled finite Boolean-stack program. No Rust decoding or arithmetic
//! shortcut executes in the production machine.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_bootstrap::stage;
use crate::native_head_selection::escape_program;
use crate::native_high::clear_program;
use crate::native_query_prefix::{frame_program, transfer_program};
use crate::native_signed_arithmetic::shift_program;

fn atom<const R: usize, const S: usize>(a: Atom) -> Cmd<R, S> {
    Cmd::Atom(a)
}
fn seq<const R: usize, const S: usize>(cmds: impl IntoIterator<Item = Cmd<R, S>>) -> Cmd<R, S> {
    cmds.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(Cmd::Skip, |tail, x| Cmd::seq(x, tail))
}
fn transfer<const S: usize>(src: usize, dst: usize) -> Result<Cmd<8, S>, Error> {
    Ok(Cmd::Call(transfer_program(src, dst, 0, 1)?))
}
/// Exact `MatrixProgramSupport.readFrame` plus `transfer`: parses a framed
/// word, consumes the input frame and appends its payload to `dst`.
pub fn read_word_command<const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
) -> Result<Cmd<8, S>, Error> {
    if src == dst || src == tmp || dst == tmp || [src, dst, tmp].iter().any(|&s| s >= S) {
        return Err(Error::Invalid(
            "readWord requires three disjoint stacks".into(),
        ));
    }
    Ok(seq([
        Cmd::Call(frame_program()?.lift::<8, S>([0, 1], [src, tmp])?),
        transfer(tmp, dst)?,
    ]))
}
/// Exact `MatrixProgramSupport.emitFrame`, not an encoder shortcut.
/// Runtime byte stream uses `Encoding.frame` with true escape flags.
pub fn emit_frame_command<const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
) -> Result<Cmd<8, S>, Error> {
    if src == dst || src == tmp || dst == tmp || [src, dst, tmp].iter().any(|&s| s >= S) {
        return Err(Error::Invalid(
            "emitFrame requires three disjoint stacks".into(),
        ));
    }
    Ok(seq([
        transfer(src, tmp)?,
        atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        atom(Atom::Push { stack: dst, src: 0 }),
        Cmd::Call(escape_program()?.lift::<8, S>([0, 1], [tmp, dst])?),
    ]))
}
fn move_word<const S: usize>(src: usize, dst: usize, tmp: usize) -> Result<Cmd<8, S>, Error> {
    Ok(seq([transfer(src, tmp)?, transfer(tmp, dst)?]))
}
fn peek<const S: usize>(src: usize) -> Cmd<8, S> {
    atom(Atom::Peek {
        stack: src,
        value: 0,
        present: 1,
    })
}
/// The full source order-repair loop, independently compiled once and lifted
/// into row and matrix callers via their exact mappings.
pub fn pre_reverse_command() -> Result<Cmd<8, 4>, Error> {
    let scan = seq([
        read_word_command(0, 1, 2)?,
        emit_frame_command(1, 3, 2)?,
        peek(0),
    ]);
    Ok(seq([peek(0), Cmd::while_(1, scan)]))
}
pub fn pre_reverse_program() -> Result<Program<8, 4>, Error> {
    pre_reverse_command()?.compiled(0, 3)
}
/// A signed coefficient P-N is read as two frames from stack 10. The result
/// frame is prepended to stack 11 after a physical `W-N+P` run and cleanup.
pub fn pre_step_command() -> Result<Cmd<8, 14>, Error> {
    let shift =
        shift_program()?.lift::<8, 14>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    Ok(seq([
        read_word_command(10, 8, 12)?,
        read_word_command(10, 1, 12)?,
        Cmd::Call(shift),
        Cmd::Call(clear_program(1, 0, 1)?),
        Cmd::Call(clear_program(2, 0, 1)?),
        Cmd::Call(clear_program(8, 0, 1)?),
        emit_frame_command(9, 11, 12)?,
    ]))
}

pub fn pre_row_command() -> Result<Cmd<8, 14>, Error> {
    let body = seq([pre_step_command()?, peek(10)]);
    let repair = seq([
        Cmd::Call(
            pre_reverse_program()?.lift::<8, 14>(std::array::from_fn(|i| i), [11, 8, 12, 13])?,
        ),
        move_word(13, 11, 12)?,
    ]);
    Ok(seq([peek(10), Cmd::while_(1, body), repair]))
}
pub fn pre_row_program() -> Result<Program<8, 14>, Error> {
    pre_row_command()?.compiled(10, 11)
}

/// The entire `BucketProgram.preMatrixProgram`. Its input is a row-framed
/// matrix of framed signed P/N pairs, output is row-framed shifted unsigned
/// coefficients in original row-major order. Width is stack 0.
pub fn pre_matrix_command() -> Result<Cmd<8, 17>, Error> {
    let row =
        pre_row_program()?.lift::<8, 17>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?;
    let body = seq([
        read_word_command(14, 10, 12)?,
        Cmd::Call(row),
        emit_frame_command(11, 15, 12)?,
        peek(14),
    ]);
    let repair = seq([
        Cmd::Call(
            pre_reverse_program()?.lift::<8, 17>(std::array::from_fn(|i| i), [15, 11, 12, 16])?,
        ),
        move_word(16, 15, 12)?,
    ]);
    Ok(seq([peek(14), Cmd::while_(1, body), repair]))
}
pub fn pre_matrix_program() -> Result<Program<8, 17>, Error> {
    pre_matrix_command()?.compiled(14, 15)
}

/// Exact `SignatureHeadLoader.shiftCommand` physical stage in the 16×768
/// leaf machine. The raw signed matrix sits on 669 and physical offset W
/// sits on 141; transformed unsigned matrix is returned on 668.
/// The full native incidence entry producer is a *separate missing stage*.
pub fn signature_shift_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        pre_matrix_program()?,
        std::array::from_fn(|i| i + 8),
        &[(141, 0), (669, 14)],
        &[(15, 668)],
    )
}
pub fn signature_shift_program() -> Result<Program<16, 768>, Error> {
    signature_shift_command()?.compiled(669, 668)
}

/// The source `localCommand` clears the raw signed matrix after shifting.
/// Given a physically produced raw matrix, this is the complete *readout*
/// suffix, not `localProgram` (which additionally produces that matrix).
pub fn signature_shift_and_clear_command() -> Result<Cmd<16, 768>, Error> {
    Ok(seq([
        signature_shift_command()?,
        Cmd::Call(clear_program(669, 0, 1)?),
    ]))
}
pub fn signature_shift_and_clear_program() -> Result<Program<16, 768>, Error> {
    signature_shift_and_clear_command()?.compiled(669, 668)
}
