//! Actual source-assembled predecessor rescan for attained signatures.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! - `CounterPrograms.rippleProgram/zeroProgram`;
//! - `CounterForPrograms.{testCmd,advanceCmd,forCmd}`;
//! - `AttainedSignatureProgram.Rescan.{body,prepareKey,command,candidateCommand}`.
//!
//! This is an executable, fixed-control binary-stack machine. It makes no
//! host-language call to enumerate predecessors, compute their signature, or
//! compare keys. Those operations are actual finite subprograms, linked into
//! the compiled instruction table. Precondition: the source's `Rescan.workState`
//! layout, empty work stacks, a width-h predecessor zero word, and a candidate
//! in 0..2^h. For 40x896, the full 24-stack rescan mapping is source-pinned.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};
use crate::native_signature_arithmetic::canonical_row_program;
use crate::native_signature_key::rescan_key_call;
use crate::native_signature_rescan::{RESCAN_STACKS, cleanup, equality_call, setup, update_fresh};

/// Literal 11-label ripple control from `CounterPrograms.lean`. The fixed
/// `carry` selects increment (true) versus decrement (false), NOT a runtime
/// parameter. The second stack is a restoring scratch buffer.
pub fn ripple_program(carry: bool) -> Result<Program<3, 2>, Error> {
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
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 5,
            },
            Instr::Branch {
                test: 0,
                yes: if carry { 3 } else { 5 },
                no: if carry { 5 } else { 3 },
            },
            Instr::Not {
                dst: 0,
                src: 0,
                next: 4,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Set {
                dst: 0,
                value: carry,
                next: 6,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 7,
            },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 8,
            },
            Instr::Branch {
                test: 1,
                yes: 9,
                no: 10,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 7,
            },
            Instr::Halt,
        ],
    )
}

/// The original `CounterPrograms.zeroProgram`: physically scan a binary
/// counter without consuming it; report zero in register 2.
pub fn zero_program() -> Result<Program<3, 2>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            Instr::Set {
                dst: 2,
                value: true,
                next: 1,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 2,
            },
            Instr::Branch {
                test: 1,
                yes: 3,
                no: 6,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 4,
            },
            Instr::Not {
                dst: 0,
                src: 0,
                next: 5,
            },
            Instr::And {
                dst: 2,
                left: 2,
                right: 0,
                next: 1,
            },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 7,
            },
            Instr::Branch {
                test: 1,
                yes: 8,
                no: 9,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 6,
            },
            Instr::Halt,
        ],
    )
}

/// Exact `CounterForPrograms.testCmd` for countdown at stack 19. Register 15
/// is !zero(counter). As in Lean, registers [13,14] are scratch.
pub fn countdown_test() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(zero_program()?.lift::<16, 24>([13, 14, 15], [19, 20])?),
        Cmd::Atom(Atom::Not { dst: 15, src: 15 }),
    ))
}

/// `CounterForPrograms.advanceCmd`: decrement the remaining count, then
/// inspect it; the same three source registers are reused.
pub fn countdown_advance() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(ripple_program(false)?.lift::<16, 24>([13, 14, 15], [19, 20])?),
        countdown_test()?,
    ))
}

/// `SqrtLogSpace.Counters.incrementCmd predecessorPorts` at the source's
/// actual data bank. Both counters use scratch stack 20 sequentially.
pub fn predecessor_increment() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::Call(
        ripple_program(true)?.lift::<16, 24>([13, 14, 15], [18, 20])?,
    ))
}

/// `Rescan.body`: read one predecessor, calculate its complete signature via
/// the actual coefficient arithmetic, compare against the saved candidate
/// signature using the destructive fixed equality machine, update freshness,
/// clear local words, then advance predecessor by one.
pub fn predecessor_body() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(18, 12, 21, 0, 1)?),
        Cmd::seq(
            rescan_key_call(&canonical_row_program()?)?,
            Cmd::seq(
                equality_call()?,
                Cmd::seq(
                    update_fresh()?,
                    Cmd::seq(
                        Cmd::Call(clear_program(12, 0, 1)?),
                        Cmd::seq(
                            Cmd::Call(clear_program(14, 0, 1)?),
                            predecessor_increment()?,
                        ),
                    ),
                ),
            ),
        ),
    ))
}

/// Binary `forCmd countdownPorts body`; not an unrolled list of predecessors.
pub fn predecessor_loop() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        countdown_test()?,
        Cmd::while_(15, Cmd::seq(predecessor_body()?, countdown_advance()?)),
    ))
}

/// `Rescan.prepareKey`: preserve the candidate, calculate its full key once,
/// and retain it on stack 17 across every predecessor visit.
pub fn prepare_key() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(16, 12, 21, 0, 1)?),
        Cmd::seq(
            rescan_key_call(&canonical_row_program()?)?,
            Cmd::seq(
                Cmd::Call(copy_program(14, 17, 21, 0, 1)?),
                Cmd::seq(
                    Cmd::Call(clear_program(12, 0, 1)?),
                    Cmd::Call(clear_program(14, 0, 1)?),
                ),
            ),
        ),
    ))
}

/// `Rescan.command` is source `setup ; forCmd ; cleanup`. It consumes all
/// countdown fuel, yet leaves the candidate and key intact in caller ports.
pub fn rescan_command() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(
        setup()?,
        Cmd::seq(predecessor_loop()?, cleanup()?),
    ))
}

/// `AttainedSignatureProgram.Rescan.candidateCommand` in its exact 16x24
/// machine, with the real arithmetic and full key equality subprograms.
pub fn candidate_command() -> Result<Cmd<16, 24>, Error> {
    Ok(Cmd::seq(prepare_key()?, rescan_command()?))
}

pub fn candidate_program() -> Result<Program<16, 24>, Error> {
    candidate_command()?.compiled(16, 22)
}

/// `SignatureTupleNative.candidateMachine` 40x896 physical lift through the
/// exact source `rescanStacks` map. Does not implement the outer DFS by itself.
pub fn tuple_candidate_machine() -> Result<Program<40, 896>, Error> {
    candidate_program()?.lift::<40, 896>(std::array::from_fn(|i| i), RESCAN_STACKS)
}

/// Exact `SignatureTupleProgram.testAvailableCommand`: source remainingPorts
/// use registers [0,1,2], counter 843, scratch 841, and copy their nonzero
/// result to controller register 38. It does not inspect a low-order bit only.
pub fn test_available_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(zero_program()?.lift::<40, 896>([0, 1, 2], [843, 841])?),
        Cmd::seq(
            Cmd::Atom(Atom::Not { dst: 2, src: 2 }),
            Cmd::Atom(Atom::Copy { dst: 38, src: 2 }),
        ),
    ))
}

/// Complete `SignatureTupleNative.probeWith` instantiated with the real
/// `AttainedSignatureProgram.Rescan.candidateProgram`. The predicate is called
/// only if the full remaining binary word is positive; the result is read
/// from the physical fresh-latch stack 362 into controller register 39.
///
/// This is one source-defined DFS routine, not the whole tuple controller.
pub fn probe_command() -> Result<Cmd<40, 896>, Error> {
    let initialize_fresh = Cmd::seq(
        Cmd::Call(clear_program(362, 0, 1)?),
        Cmd::seq(
            Cmd::Atom(Atom::Set {
                dst: 0,
                value: false,
            }),
            Cmd::Atom(Atom::Push { stack: 362, src: 0 }),
        ),
    );
    Ok(Cmd::seq(
        test_available_command()?,
        Cmd::ite(
            38,
            Cmd::seq(
                initialize_fresh,
                Cmd::seq(
                    Cmd::Call(tuple_candidate_machine()?),
                    Cmd::Atom(Atom::Peek {
                        stack: 362,
                        value: 39,
                        present: 0,
                    }),
                ),
            ),
            Cmd::Skip,
        ),
    ))
}

pub fn probe_program() -> Result<Program<40, 896>, Error> {
    probe_command()?.compiled(843, 362)
}
