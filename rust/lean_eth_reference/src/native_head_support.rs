//! Source-defined `LeafHeadSetupProgram.support`: a real unary true-count
//! followed by a complete staged ambient-mask scatter.
//!
//! Pinned: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! `SqrtLog/PackingHeadProgramPrepareCount.lean`,
//! `SqrtLog/LeafHeadSetupProgramSupport.lean`, and
//! `SqrtLog/LeafHeadSetupProgramStorage.lean`.
//!
//! Unlike a shortcut from selected indices directly to a Rust bit vector,
//! this compiles the original 3x2 count machine and 8x13 scatter machine
//! through the *same* paid `stage` used by the integer-cache bootstrap.
//! The stage clears the 340-based work bank, copies protected input stacks,
//! calls the lifted finite callee, exports the output, and clears its workspace.
//! The source's well-formed encoded indices, equal bit/ID counts, and in-range
//! positions are caller preconditions, not silently repaired here.

use crate::Error;
use crate::bit_program::{Cmd, Instr, Program};
use crate::native_bootstrap::stage;
use crate::native_head_scatter::head_scatter_program;

/// Exact 6-label source table, including the final two register clears.
/// Consumes a Boolean word and emits one `true` per bit, independent of values.
pub fn true_count_program() -> Result<Program<3, 2>, Error> {
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
            Instr::Set {
                dst: 2,
                value: true,
                next: 3,
            },
            Instr::Push {
                stack: 1,
                src: 2,
                next: 0,
            },
            Instr::Set {
                dst: 2,
                value: false,
                next: 5,
            },
            Instr::Halt,
        ],
    )
}

/// Stage `trueCount`: source 651 -> callee 0, callee 1 -> output 652.
/// The source maps its 3 registers to caller 0..2 and two stacks to
/// the isolated physical work ports 340 and 341.
pub fn true_count_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        true_count_program()?,
        [0, 1, 2],
        &[(651, 0)],
        &[(1, 652)],
    )
}

pub fn true_count_standalone_program() -> Result<Program<16, 768>, Error> {
    true_count_command()?.compiled(651, 652)
}

/// Stage `scatterSupport`: copies indices 650, unary head count 652, and
/// ambient size 128 to callee stacks 10, 11, 12, then exports callee 0 to 670.
/// The complete 8x13 scatter call uses caller registers 0..7.
pub fn scatter_support_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        head_scatter_program()?,
        std::array::from_fn(|i| i),
        &[(650, 10), (652, 11), (128, 12)],
        &[(0, 670)],
    )
}

pub fn scatter_support_standalone_program() -> Result<Program<16, 768>, Error> {
    scatter_support_command()?.compiled(650, 670)
}

/// The complete source `LeafHeadSetupProgram.support` in the lower 16x768
/// machine. It is a *component*, not the full `prepareHead`, `localProgram`,
/// or native signed incidence evaluator.
pub fn support_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(true_count_command()?, scatter_support_command()?))
}

pub fn support_program() -> Result<Program<16, 768>, Error> {
    support_command()?.compiled(650, 670)
}
