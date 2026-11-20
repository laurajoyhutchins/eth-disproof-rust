//! Original finite-program tables for `ParserProgram.frameProgram` and
//! `SubexpPostfixControl.literalService`.
//!
//! The seven-label frame parser and seventeen-label record writer are
//! physical `BitProgram` instructions from pinned Lean source, not
//! host-side encoding. Both keep their original public module entry points
//! as compatibility re-exports.
//!
//! Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

use crate::Error;

use super::{Instr, Program};

/// The exact seven-label source `ParserProgram.frameProgram`.
/// Input: `Encoding.frame bits ++ rest`; output: `bits.reverse ++ out`.
pub fn frame_program() -> Result<Program<2, 2>, Error> {
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
                no: 6,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 6,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 4,
            },
            Instr::Branch {
                test: 1,
                yes: 5,
                no: 6,
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

/// Original `SubexpPostfixControl.literalService` 17-label table.
/// The source parser is lifted into stacks [0, 3]; its terminal halt
/// becomes the continuation at label 7. This starts at entry label 7
/// and encodes the reversed input payload into a framed record.
pub fn emit_record_program() -> Result<Program<3, 4>, Error> {
    let parser = frame_program()?.lift::<3, 4>([0, 1], [0, 3])?;
    let mut code = parser.code().to_vec();
    code[6] = Instr::Goto { next: 7 };
    code.extend([
        Instr::Set {
            dst: 0,
            value: false,
            next: 8,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Pop {
            stack: 3,
            value: 0,
            present: 1,
            next: 10,
        },
        Instr::Branch {
            test: 1,
            yes: 11,
            no: 14,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 12,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 13,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 15,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 16,
        },
        Instr::Halt,
    ]);
    Program::new(3, 2, 7, code)
}
