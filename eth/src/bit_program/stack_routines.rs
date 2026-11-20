//! Canonical finite tables for the pinned Lean `StackRoutines` commands.
//!
//! Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
//! The fixed label tables are source operations, not host-level stack edits.
//! Callers retain their original public entry points through re-exports.

use crate::Error;

use super::{Instr, Program};

/// Exact three-instruction source table (`StackRoutines.clearProgram`).
pub fn clear_program<const R: usize, const S: usize>(
    src: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    Program::new(
        src,
        src,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 0,
                no: 2,
            },
            Instr::Halt,
        ],
    )
}

/// Exact eight-instruction preserving-copy source table.
/// The source requires `src`, `dst`, `tmp` to be distinct and `tmp` empty.
/// We reject invalid port aliases; absence of scratch contents is a caller
/// precondition, rather than silently clearing unrequested data.
pub fn copy_program<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if src == dst || src == tmp || dst == tmp || value == present {
        return Err(Error::Invalid(
            "copy requires disjoint ports and read registers".into(),
        ));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 3,
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
                next: 4,
            },
            Instr::Branch {
                test: present,
                yes: 5,
                no: 7,
            },
            Instr::Push {
                stack: src,
                src: value,
                next: 6,
            },
            Instr::Push {
                stack: dst,
                src: value,
                next: 3,
            },
            Instr::Halt,
        ],
    )
}

/// Source `StackRoutines.transferProgram`: four labels, including the halt.
/// Its preconditions require different source/destination stacks and read
/// registers. The word is reversed as it is transferred.
pub fn transfer_program<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if src == dst || value == present {
        return Err(Error::Invalid("transfer requires disjoint ports".into()));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 3,
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
