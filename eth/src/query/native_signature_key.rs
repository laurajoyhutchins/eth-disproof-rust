//! Source-pinned finite-machine stages of the attained-signature key pipeline.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae:
//! `SubexpParameterProgram.prepareLogProgram`, `CounterNormalizeProgram.program`,
//! `BucketProgramSignature.signatureCommand`, and
//! `AttainedSignatureProgram.command`.
//!
//! The signature scanner requires the ACTUAL `canonicalRowProgram` as an
//! argument. Its arithmetic implementation is not provided by this module.
//! Callers must not substitute a semantic host-language evaluator for that
//! finite program or claim that `Rescan.candidateProgram` has been ported.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::copy_program;
use crate::native_query_prefix::{frame_program, transfer_program};

/// The six-label source `SubexpParameterProgram.trimProgram`. The input is
/// reversed (most significant bit first); the leading one and zeros before it
/// are consumed, leaving the remaining low bits in stack 1.
pub fn trim_program() -> Result<Program<3, 3>, Error> {
    Program::new(
        1,
        1,
        0,
        vec![
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 0,
            },
            Instr::Set {
                dst: 0,
                value: false,
                next: 4,
            },
            Instr::Set {
                dst: 1,
                value: false,
                next: 5,
            },
            Instr::Halt,
        ],
    )
}

/// Exact ten-label link of `reverseTransfer` and `trimProgram`, not two
/// independently compiled calls (which would insert an extra jump).
pub fn prepare_log_program() -> Result<Program<3, 3>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 3,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Goto { next: 4 },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 5,
            },
            Instr::Branch {
                test: 1,
                yes: 6,
                no: 7,
            },
            Instr::Branch {
                test: 0,
                yes: 7,
                no: 4,
            },
            Instr::Set {
                dst: 0,
                value: false,
                next: 8,
            },
            Instr::Set {
                dst: 1,
                value: false,
                next: 9,
            },
            Instr::Halt,
        ],
    )
}

/// Literal `CounterNormalizeProgram.command` on 3 registers and 3 stacks.
/// For a positive little-endian binary word, output 0 is the same value with
/// width `log2(value)+1`, and scratch 1 and 2 are empty.
pub fn counter_normalize_command() -> Result<Cmd<3, 3>, Error> {
    let reset = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: 1,
                value: false,
            }),
            Cmd::Atom(Atom::Set {
                dst: 2,
                value: false,
            }),
        ),
    );
    let restore = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
            Cmd::Call(transfer_program(1, 0, 0, 1)?),
        ),
    );
    Ok(Cmd::seq(
        reset,
        Cmd::seq(Cmd::Call(prepare_log_program()?), restore),
    ))
}

pub fn counter_normalize_program() -> Result<Program<3, 3>, Error> {
    counter_normalize_command()?.compiled(0, 0)
}

/// Source `BucketProgramNormalize.normalizeCall`: 3x3 normalizer lifted to
/// register ports [0,1,2] and stack ports [2,3,4] of the 8x12 row machine.
pub fn canonical_row_normalize_call() -> Result<Cmd<8, 12>, Error> {
    Ok(Cmd::Call(
        counter_normalize_program()?.lift::<8, 12>([0, 1, 2], [2, 3, 4])?,
    ))
}

/// Exact `MatrixProgramSupport.readWord`: decode a framed word into `dst`
/// through `tmp`, restoring original bit order. `src`, `dst`, `tmp` distinct.
fn read_word(src: usize, dst: usize, tmp: usize) -> Result<Cmd<8, 15>, Error> {
    if src == dst || src == tmp || dst == tmp {
        return Err(Error::Invalid("readWord requires disjoint ports".into()));
    }
    Ok(Cmd::seq(
        Cmd::Call(frame_program()?.lift::<8, 15>([0, 1], [src, tmp])?),
        Cmd::Call(transfer_program(tmp, dst, 0, 1)?),
    ))
}

/// Exact six-label `TupleProgram.escapeProgram`: the framing delimiter is
/// installed separately, as in `MatrixProgramSupport.emitFrame`.
fn escape_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 5,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 3,
            },
            Instr::Set {
                dst: 0,
                value: true,
                next: 4,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// `MatrixProgramSupport.emitFrame`: reverse word into tmp, prepend `false`
/// delimiter, then escape every bit. For n bits the charged command cost is
/// `8*n+8`, as in the pinned Lean theorem.
fn emit_frame(src: usize, dst: usize, tmp: usize) -> Result<Cmd<8, 15>, Error> {
    if src == dst || src == tmp || dst == tmp {
        return Err(Error::Invalid("emitFrame requires disjoint ports".into()));
    }
    Ok(Cmd::seq(
        Cmd::Call(transfer_program(src, tmp, 0, 1)?),
        Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: 0,
                value: false,
            }),
            Cmd::seq(
                Cmd::Atom(Atom::Push { stack: dst, src: 0 }),
                Cmd::Call(escape_program()?.lift::<8, 15>([0, 1], [tmp, dst])?),
            ),
        ),
    ))
}

/// `BucketProgramSignature.signatureStep` for an actual fixed 8x12
/// `canonicalRowProgram`. This command never enumerates or computes row
/// signatures in Rust host code; the supplied program is called in 8x15 at
/// registers 0..7 and stacks 0..11 (the source's `rowCallPorts`).
pub fn signature_step(canonical_row: &Program<8, 12>) -> Result<Cmd<8, 15>, Error> {
    let row = Cmd::Call(
        canonical_row.lift::<8, 15>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    );
    let seed = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 2, src: 0 }),
    );
    Ok(Cmd::seq(
        read_word(13, 9, 11)?,
        Cmd::seq(
            Cmd::Call(copy_program(12, 10, 11, 0, 1)?),
            Cmd::seq(seed, Cmd::seq(row, emit_frame(2, 14, 11)?)),
        ),
    ))
}

/// Exact `BucketProgramSignature.signatureCommand`: `peek; while guard
/// (signatureStep; peek)`. Only finite commands occur in this loop.
pub fn signature_command(canonical_row: &Program<8, 12>) -> Result<Cmd<8, 15>, Error> {
    let peek = Cmd::Atom(Atom::Peek {
        stack: 13,
        value: 0,
        present: 1,
    });
    let body = Cmd::seq(signature_step(canonical_row)?, peek.clone());
    Ok(Cmd::seq(peek, Cmd::while_(1, body)))
}

pub fn signature_program(canonical_row: &Program<8, 12>) -> Result<Program<8, 15>, Error> {
    signature_command(canonical_row)?.compiled(13, 14)
}

/// `AttainedSignatureProgram.command`: preserve the serialized matrix on
/// stack 15, copy it to 13 with scratch 11, then call the 8x15 scanner on
/// stacks 0..14. No semantic direct signature evaluator is present.
pub fn attained_signature_command(canonical_row: &Program<8, 12>) -> Result<Cmd<8, 16>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(15, 13, 11, 0, 1)?),
        Cmd::Call(
            signature_program(canonical_row)?
                .lift::<8, 16>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
        ),
    ))
}

pub fn attained_signature_program(canonical_row: &Program<8, 12>) -> Result<Program<8, 16>, Error> {
    attained_signature_command(canonical_row)?.compiled(12, 14)
}

/// The exact `Rescan.keyCall` wrapper, assuming the caller supplies the
/// REAL `canonicalRowProgram` in order to obtain a source-complete key.
pub fn rescan_key_call(canonical_row: &Program<8, 12>) -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::Call(
        attained_signature_program(canonical_row)?
            .lift::<16, 24>(std::array::from_fn(|i| i), std::array::from_fn(|i| i))?,
    ))
}
