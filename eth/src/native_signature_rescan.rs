//! Physical bit-string predecessor comparator and rescan latch.
//!
//! Exact source pins (openai/math@4eaee87548250b2682affda7d05d947c05554bae):
//! * `ExecClauseCost.bitEqualityProgram` (10 instructions),
//! * `AttainedSignatureProgram.KeyEquality.command` (preserving copies and cleanup),
//! * `AttainedSignatureProgram.Rescan` (equalityCall, storeFresh,
//!   updateFresh, setup and cleanup), and
//! * `SignatureTupleNative.rescanStacks` (24-source-stack physical ABI).
//!
//! `candidateProgram` is NOT complete. Producing the actual signature key
//! from records and running the predecessor countdown are separate work.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_query_prefix::transfer_program;

/// `SignatureTupleNative.rescanRegisters`: Fin 16 -> Fin 40.
const RESCAN_REGISTERS: [usize; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

/// `SignatureTupleNative.rescanStacks`: exact source-defined private bank.
/// The exception ports hold source input, raw row table, candidate, key,
/// and predecessor; the remaining entries live in physical 340..363.
pub const RESCAN_STACKS: [usize; 24] = [
    141, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 847, 838, 839, 844,
    359, 360, 361, 362, 363,
];

/// The precise destructive equality machine, `ExecClauseCost.bitEqualityProgram`.
/// The answer is register 4, and both input stacks may be consumed.
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

/// `AttainedSignatureProgram.KeyEquality.command`, still in its native 5x6
/// address space. Inputs 0 and 2 are preserved; copies 1 and 3 are destroyed.
/// Temporary 4 must be empty, just as in the Lean source contract.
pub fn key_equality_command() -> Result<Cmd<5, 6>, Error> {
    let preserve_left = Cmd::Call(copy_program(0, 1, 4, 0, 1)?);
    let preserve_right = Cmd::Call(copy_program(2, 3, 4, 0, 1)?);
    let destructive = Cmd::Call(bit_equality_program()?.lift::<5, 6>([0, 1, 2, 3, 4], [1, 3])?);
    let cleanup_left = Cmd::Call(clear_program(1, 0, 1)?);
    let cleanup_right = Cmd::Call(clear_program(3, 0, 1)?);
    Ok(Cmd::seq(
        preserve_left,
        Cmd::seq(
            preserve_right,
            Cmd::seq(destructive, Cmd::seq(cleanup_left, cleanup_right)),
        ),
    ))
}

pub fn key_equality_program() -> Result<Program<5, 6>, Error> {
    key_equality_command()?.compiled(0, 0)
}

/// `Rescan.equalityCall`: full 16x24 source-machine embedding of the
/// five-register key comparator, including all six actual local stack ports.
pub fn equality_call() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::Call(
        key_equality_program()?.lift::<16, 24>([0, 1, 2, 3, 4], [14, 1, 17, 3, 4, 5])?,
    ))
}

/// Port-preserving installation of the local source command in the 40x896
/// physical signature-tuple machine. Input key on 354, saved key on 839.
pub fn equality_caller() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(key_equality_program()?.lift::<40, 896>(
        [0, 1, 2, 3, 4],
        [354, 341, 839, 343, 344, 345],
    )?))
}

fn clear<const R: usize, const S: usize>(stack: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(stack, 0, 1)?))
}

/// `Rescan.storeFresh b`: destructive clear, then one physical latch bit.
pub fn store_fresh(b: bool) -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        clear(22)?,
        Cmd::seq(
            Cmd::Atom(Atom::Set { dst: 0, value: b }),
            Cmd::Atom(Atom::Push { stack: 22, src: 0 }),
        ),
    ))
}

/// `Rescan.updateFresh`: reject a key only when equality register 4 is true.
pub fn update_fresh() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::ite(4, store_fresh(false)?, Cmd::Skip))
}

pub fn update_fresh_caller() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::ite(
        4,
        Cmd::seq(
            clear(362)?,
            Cmd::seq(
                Cmd::Atom(Atom::Set {
                    dst: 0,
                    value: false,
                }),
                Cmd::Atom(Atom::Push { stack: 362, src: 0 }),
            ),
        ),
        Cmd::Skip,
    ))
}

/// Concrete physical duplicate-key gate, without a host-language equality
/// operation: source `equalityCall ; updateFresh`. Inputs on 354 / 839.
pub fn duplicate_key_gate_caller() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(equality_caller()?, update_fresh_caller()?))
}

/// `Rescan.setup`: copy candidate 16 -> countdown 19 (scratch 21), then
/// set freshness to one true bit on 22. Requires empty 21 and 19.
pub fn setup() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(16, 19, 21, 0, 1)?),
        store_fresh(true)?,
    ))
}

/// `Rescan.cleanup`: clear predecessor 18 then physically transfer the
/// exhausted countdown word 19 -> 18 (the source assumes a fixed-width zero
/// word after the predecessor loop).
pub fn cleanup() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        clear(18)?,
        Cmd::Call(transfer_program(19, 18, 0, 1)?),
    ))
}

/// The same setup, directly composed on concrete source-mapped 40x896 ports.
pub fn setup_caller() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(838, 359, 361, 0, 1)?),
        Cmd::seq(
            clear(362)?,
            Cmd::seq(
                Cmd::Atom(Atom::Set {
                    dst: 0,
                    value: true,
                }),
                Cmd::Atom(Atom::Push { stack: 362, src: 0 }),
            ),
        ),
    ))
}

pub fn cleanup_caller() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        clear(844)?,
        Cmd::Call(transfer_program(359, 844, 0, 1)?),
    ))
}

/// Static embedding map verification via an actual lifted finite table.
pub fn equality_caller_via_two_stage_lift() -> Result<Cmd<40, 896>, Error> {
    let source = key_equality_program()?.lift::<16, 24>([0, 1, 2, 3, 4], [14, 1, 17, 3, 4, 5])?;
    Ok(Cmd::Call(
        source.lift::<40, 896>(RESCAN_REGISTERS, RESCAN_STACKS)?,
    ))
}
