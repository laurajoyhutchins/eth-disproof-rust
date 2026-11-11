//! Source-defined physical input header extraction for the outer native frontend.
//!
//! Pinned upstream sources: ParserProgram.natProgram and
//! SqrtLogSpace/NativeFrontend.lean: Native.ambientCommand.
//! This command assumes the canonical Encoding.encodeCNF header and clean
//! ports 258/1218/1219. It is NOT the full frontend normalization, and is
//! not a validating arbitrary-input parser; source correctness has premises.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};

/// The exact five-label source unary natural parser.
/// Register 1 reports present on a terminating zero and false if truncated.
pub fn nat_program() -> Result<Program<2, 2>, Error> {
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
            Instr::Halt,
        ],
    )
}

/// Source Native.ambientCommand, a physical 80-register/1220-stack command:
/// 1. Preserve-copy input stack 256 to work stack 1218 using scratch 1219.
/// 2. Seed unary stack 258 with the terminator zero.
/// 3. Parse the unary header from 1218, building 1^n 0 on 258.
/// 4. Clear the remaining payload body from 1218.
/// Preconditions: 258, 1218, 1219 initially empty and input starts with a
/// terminated unary field. No semantic formula/count computation occurs.
pub fn ambient_command() -> Result<Cmd<80, 1220>, Error> {
    let copy = Cmd::Call(copy_program(256, 1218, 1219, 72, 73)?);
    let seed = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 72,
            value: false,
        }),
        Cmd::Atom(Atom::Push {
            stack: 258,
            src: 72,
        }),
    );
    let parse = Cmd::Call(nat_program()?.lift::<80, 1220>([72, 73], [1218, 258])?);
    let clear = Cmd::Call(clear_program(1218, 72, 73)?);
    Ok(Cmd::seq(copy, Cmd::seq(seed, Cmd::seq(parse, clear))))
}

/// A testable wrapper. The Lean source defines a command, not this Program.
pub fn ambient_program() -> Result<Program<80, 1220>, Error> {
    ambient_command()?.compiled(256, 258)
}
