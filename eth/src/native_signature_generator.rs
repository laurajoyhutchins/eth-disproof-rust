//! Source-defined initialization of the attained-signature generator.
//!
//! Pinned source `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:
//! `SqrtLogSpace/Counters.lean` (powerTwoProgram),
//! `SqrtLogSpace/SignatureTupleProgram.lean` (initialFuelCommand,
//! resetCommand, resetGeneratorCommand), and
//! `SqrtLogSpace/SignatureTupleNative.lean` (setupWith).
//!
//! Every operation is a finite bit instruction or a call to another finite
//! program. These constructors do not invent a predecessor predicate or a
//! signature-head loader, and do not construct a list of candidates.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::clear_program;
use crate::native_high::copy_program;
use crate::native_signature_frames::{CONTROLLER_REGISTERS, TUPLE_STACKS};
use crate::native_signature_tuple::initialize_levels_command;

/// The exact seven-label `SqrtLogSpace.Counters.powerTwoProgram`.
/// Consumes a unary length witness, leaves `[false; h] ++ [true]` on stack 1.
/// As in Lean, stack 1 is assumed empty by the semantic contract.
pub fn power_two_program() -> Result<Program<3, 2>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Set {
                dst: 0,
                value: true,
                next: 1,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 2,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 3,
            },
            Instr::Branch {
                test: 1,
                yes: 4,
                no: 6,
            },
            Instr::Set {
                dst: 0,
                value: false,
                next: 5,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 2,
            },
            Instr::Halt,
        ],
    )
}

/// Actual `SignatureTupleProgram.initialFuelCommand` on register ports 0..2,
/// input 840 and output 843. The source consumes the temporary 840 word.
pub fn initial_fuel_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(power_two_program()?.lift::<40, 896>(
        [0, 1, 2],
        [TUPLE_STACKS[4], TUPLE_STACKS[7]],
    )?))
}

/// Actual `SignatureTupleProgram.resetCommand`. The word at 651 is copied
/// to the candidate 838 and temporary 840, then the temporary is consumed
/// to initialize binary fuel 843. The scratch 841 must be empty.
pub fn reset_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(651, TUPLE_STACKS[2], TUPLE_STACKS[5], 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(651, TUPLE_STACKS[4], TUPLE_STACKS[5], 0, 1)?),
            Cmd::seq(
                initial_fuel_command()?,
                Cmd::seq(
                    Cmd::Atom(Atom::Set {
                        dst: CONTROLLER_REGISTERS[2],
                        value: true,
                    }),
                    Cmd::Atom(Atom::Set {
                        dst: CONTROLLER_REGISTERS[3],
                        value: false,
                    }),
                ),
            ),
        ),
    ))
}

/// `SignatureTupleProgram.resetGeneratorCommand` additionally seeds the
/// previous-assignment word on 844, with source-defined preserving copy.
pub fn reset_generator_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        reset_command()?,
        Cmd::Call(copy_program(651, TUPLE_STACKS[8], TUPLE_STACKS[5], 0, 1)?),
    ))
}

/// `SignatureTupleNative.setupWith loadHead`: clears all 12 tuple tapes,
/// copies remaining head count and initial physical address, then loads the
/// first head and resets its candidate generator iff there are heads.
///
/// `load_head` is a *real finite Cmd* supplied by the caller. Until the
/// pinned `SignatureTupleLoader.loadHead` is executable, this is a reusable
/// source-defined constructor, not a closed native signature-tuple solver.
pub fn setup_with(load_head: Cmd<40, 896>) -> Result<Cmd<40, 896>, Error> {
    let mut clear_tuples = Cmd::Skip;
    for &stack in TUPLE_STACKS.iter().rev() {
        clear_tuples = Cmd::seq(Cmd::Call(clear_program(stack, 0, 1)?), clear_tuples);
    }
    Ok(Cmd::seq(
        clear_tuples,
        Cmd::seq(
            initialize_levels_command()?,
            Cmd::ite(
                CONTROLLER_REGISTERS[1],
                Cmd::Skip,
                Cmd::seq(load_head, reset_generator_command()?),
            ),
        ),
    ))
}
