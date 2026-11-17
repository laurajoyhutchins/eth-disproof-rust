//! Source-defined native terminal count producers for the shared 80×1220 ABI.
//!
//! Pinned source: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//!
//! - `Native.powerProgram` from SqrtLogSpace/NativeProgram.lean
//! - `NativeTerminal.power` and `NativeTerminal.zero` from NativeTerminal.lean
//!
//! The source's *classifier* (`NativeTerminal.classifier`) is NOT ported here.
//! The caller must separately establish whether a formula is empty (2^n),
//! contains an empty clause (0), or requires the nonterminal leaf. This module
//! never inspects a CNF or substitutes an unproved semantic SAT count.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::copy_program;

/// Exact seed/loop of `Native.powerCommand` in the two-register, two-stack
/// source machine. The canonical input is `true^n ++ [false]`; the output is
/// the little-endian full count word `false^n ++ [true]` (the value 2^n).
/// No host arithmetic or width-bounded integer conversion is used.
pub fn power_command() -> Cmd<2, 2> {
    let seed = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 0,
                present: 1,
            }),
        ),
    );
    let body = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
            Cmd::Atom(Atom::Pop {
                stack: 0,
                value: 0,
                present: 1,
            }),
        ),
    );
    Cmd::seq(seed, Cmd::while_(0, body))
}

pub fn power_program() -> Result<Program<2, 2>, Error> {
    power_command().compiled(0, 1)
}

/// Exact `NativeTerminal.power`: preserve-copy ambient unary header 258 to
/// work stack 268 using scratch 269, then lift the `powerProgram` with
/// register mapping `[72, 73]` and stack mapping `[268, 263]`.
///
/// Preconditions from Lean: stack 258 contains `true^n ++ [false]`; stacks
/// 263, 268 and 269 are empty. The program preserves ambient stack 258 and
/// leaves the work/scratch stacks empty after a complete run.
pub fn terminal_power_command() -> Result<Cmd<80, 1220>, Error> {
    let copy = Cmd::Call(copy_program(258, 268, 269, 72, 73)?);
    let power = Cmd::Call(power_program()?.lift::<80, 1220>([72, 73], [268, 263])?);
    Ok(Cmd::seq(copy, power))
}

/// A testable compiled wrapper, not an alternative source `NativeTerminal`.
pub fn terminal_power_program() -> Result<Program<80, 1220>, Error> {
    terminal_power_command()?.compiled(258, 263)
}

/// Exact `NativeTerminal.zero`. The classifier must have established that an
/// empty clause is present, and the destination 263 must initially be empty.
pub fn terminal_zero_command() -> Cmd<80, 1220> {
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 72,
            value: false,
        }),
        Cmd::Atom(Atom::Push {
            stack: 263,
            src: 72,
        }),
    )
}

pub fn terminal_zero_program() -> Result<Program<80, 1220>, Error> {
    terminal_zero_command().compiled(258, 263)
}
