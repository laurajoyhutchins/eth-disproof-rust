//! Source-defined *actual* input/header prefix of the 80×1220 frontend.
//!
//! Pinned source: `FrontendProgram.initializeProgram` (linked fixed finite 19
//! labels) and `Native.headerCommand` in SqrtLogSpace/NativeProgram.lean.
//! The prefix only parses the unary ambient and calculates its binary length.
//! It does not normalize the remaining encoded formula body.
use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_high::copy_program;

/// Exact 19-label source link of the five-label unary parser into the
/// fourteen-label binary length counter. The parser's final halt becomes
/// a goto to label 5; the counter's last label remains the only halt.
/// These are physical finite instructions, not an integer decoding shortcut.
pub fn initialize_program() -> Result<Program<3, 4>, Error> {
    Program::new(
        0,
        2,
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
                no: 4,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 4,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Goto { next: 5 },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 6,
            },
            Instr::Branch {
                test: 1,
                yes: 7,
                no: 18,
            },
            Instr::Pop {
                stack: 2,
                value: 0,
                present: 1,
                next: 8,
            },
            Instr::Branch {
                test: 1,
                yes: 9,
                no: 12,
            },
            Instr::Branch {
                test: 0,
                yes: 10,
                no: 12,
            },
            Instr::Not {
                dst: 0,
                src: 0,
                next: 11,
            },
            Instr::Push {
                stack: 3,
                src: 0,
                next: 7,
            },
            Instr::Set {
                dst: 0,
                value: true,
                next: 13,
            },
            Instr::Push {
                stack: 2,
                src: 0,
                next: 14,
            },
            Instr::Pop {
                stack: 3,
                value: 0,
                present: 1,
                next: 15,
            },
            Instr::Branch {
                test: 1,
                yes: 16,
                no: 17,
            },
            Instr::Push {
                stack: 2,
                src: 0,
                next: 14,
            },
            Instr::Goto { next: 5 },
            Instr::Halt,
        ],
    )
}

/// Exact `Native.headerCommand`: copy the canonical input word 256 to work
/// 1218 through scratch 1219, then execute the source initializer at
/// register ports [72,73,74], stack ports [1218,268,267,269].
/// Premises: source stack 256 begins with terminated unary n, and scratch
/// 1219 plus output/work stacks 268/267/269 begin empty.
pub fn header_command() -> Result<Cmd<80, 1220>, Error> {
    let copy = Cmd::Call(copy_program(256, 1218, 1219, 72, 73)?);
    let init =
        Cmd::Call(initialize_program()?.lift::<80, 1220>([72, 73, 74], [1218, 268, 267, 269])?);
    Ok(Cmd::seq(copy, init))
}

pub fn header_program() -> Result<Program<80, 1220>, Error> {
    header_command()?.compiled(256, 1216)
}
