//! Exact bit-string equality component of original encoded-CNF membership.
//!
//! Pinned Lean:
//! - ExecClauseCost.lean: ExecClauseCost.bitEqualityProgram
//! - ExecClauseCost39Lift.lean: ExecClauseCost.membershipEqProgram
//! - ExecCNFMembership.lean: ExecCNFMembership.callback
//!
//! A real physical comparison, not a host equality check or a CNF-membership
//! oracle. The record parser/iterator and terminal classifier remain pending.

use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};

/// Exact 10-label source table. The first stack is compared with the second
/// destructively, with register 4 set to equality; early mismatches retain
/// suffixes as the original machine does.
pub fn bit_equality_program() -> Result<Program<5, 2>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Pop {
                stack: 1,
                value: 2,
                present: 3,
                next: 2,
            },
            Instr::Xor {
                dst: 4,
                left: 1,
                right: 3,
                next: 3,
            },
            Instr::Branch {
                test: 4,
                yes: 8,
                no: 4,
            },
            Instr::Branch {
                test: 1,
                yes: 5,
                no: 7,
            },
            Instr::Xor {
                dst: 4,
                left: 0,
                right: 2,
                next: 6,
            },
            Instr::Branch {
                test: 4,
                yes: 8,
                no: 0,
            },
            Instr::Set {
                dst: 4,
                value: true,
                next: 9,
            },
            Instr::Set {
                dst: 4,
                value: false,
                next: 9,
            },
            Instr::Halt,
        ],
    )
}

/// Source `Fin.castAdd 2` port map: identity registers 0..=4 into 7,
/// stack ports 1 and 3. This preserves outer registers 5 and 6.
pub fn membership_eq_program() -> Result<Program<7, 5>, Error> {
    bit_equality_program()?.lift::<7, 5>([0, 1, 2, 3, 4], [1, 3])
}

/// Source `ExecCNFMembership.callback`: copy the preserved reversed query
/// stack 2 to compare stack 3 with scratch 4, execute the actual 10-label
/// comparator against the reversed payload on stack 1, and physically clear
/// the inspected payload and copy. The preserved query 2 is not consumed.
///
/// Preconditions: stacks 3 and 4 initially empty; the inputs are already
/// reversed as defined by Lean's encoded-record iterator.
pub fn membership_callback_command() -> Result<Cmd<7, 5>, Error> {
    let copy = Cmd::Call(copy_program(2, 3, 4, 0, 1)?);
    let compare = Cmd::Call(membership_eq_program()?);
    let clear_left = Cmd::Call(clear_program(1, 0, 1)?);
    let clear_copy = Cmd::Call(clear_program(3, 0, 1)?);
    Ok(Cmd::seq(
        copy,
        Cmd::seq(compare, Cmd::seq(clear_left, clear_copy)),
    ))
}

/// Testable compilation of the source callback, with a final halt.
pub fn membership_callback_program() -> Result<Program<7, 5>, Error> {
    membership_callback_command()?.compiled(1, 1)
}
