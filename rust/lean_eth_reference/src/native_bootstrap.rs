//! Executable finite-table stages of `SignatureHeadLoader.bootstrapProgram`.
//!
//! Source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
//! - `SqrtLog/LeafHeadSetupProgramAddress.lean` (`Address.command`)
//! - `SubexpSunflowerProgram.lean` (`CountRecords.program`)
//! - `SubexpScopeCountSetup.lean` (`countCommand`)
//! - `SqrtLog/LeafHeadSetupProgramBoot.lean` (`initializeAddress`, `countRows`)
//! - `SqrtLog/LeafHeadSetupProgramStorage.lean` (`stage`)
//! - `SubexpSetupStorage.lean` (`prepare`, `finish`)
//! - `SqrtLog/LeafHeadSetupProgramRetain.lean` (`retainCache`)
//!
//! The full SignatureHeadLoader bootstrap is now assembled from the actual
//! source-defined isolated stages and preserving retention suffix.
//! No runtime mathematical coefficients are injected as an oracle.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_flatten::integer_cache_program;
use crate::native_high::{clear_program, copy_program};

const TEMPORARY: usize = 659;
const WORK_BASE: usize = 340;

fn clear<const R: usize, const S: usize>(port: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(port, 0, 1)?))
}

fn copy<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(copy_program(src, dst, tmp, 0, 1)?))
}

fn clear_many<const R: usize, const S: usize>(ports: &[usize]) -> Result<Cmd<R, S>, Error> {
    let mut out = Cmd::Skip;
    for &port in ports.iter().rev() {
        out = Cmd::seq(clear(port)?, out);
    }
    Ok(out)
}

fn copy_many<const R: usize, const S: usize>(
    tmp: usize,
    ports: &[(usize, usize)],
) -> Result<Cmd<R, S>, Error> {
    let mut out = Cmd::Skip;
    for &(src, dst) in ports.iter().rev() {
        out = Cmd::seq(copy(src, dst, tmp)?, out);
    }
    Ok(out)
}

fn reset_work() -> Cmd<16, 768> {
    (0..9).rev().fold(Cmd::Skip, |rest, dst| {
        Cmd::seq(Cmd::Atom(Atom::Set { dst, value: false }), rest)
    })
}

/// `BasisTransposePlanProgram.multiply` uses the literal `UnaryForPrograms.forCmd`:
/// pop counter stack 5; copy from 0 to 4 once per present bit; pop again.
/// This changes actual stacks, not just their lengths.
pub fn address_local_command() -> Result<Cmd<3, 7>, Error> {
    let pop = Cmd::Atom(Atom::Pop {
        stack: 5,
        value: 0,
        present: 1,
    });
    let multiply = Cmd::seq(pop.clone(), Cmd::while_(1, Cmd::seq(copy(0, 4, 6)?, pop)));
    Ok(Cmd::seq(copy(2, 5, 6)?, Cmd::seq(multiply, copy(0, 3, 6)?)))
}

pub fn address_local_program() -> Result<Program<3, 7>, Error> {
    address_local_command()?.compiled(2, 4)
}

/// The 13 physical instructions in `SubexpSunflowerProgram.CountRecords.program`.
/// Entry label 2 skips the two list-seed instructions (the count stack starts
/// empty) exactly as `SubexpScopeCountSetup.counterProgram` does.
pub fn record_counter_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
        2,
        vec![
            Instr::Set {
                dst: 0,
                value: false,
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
                test: 0,
                yes: 4,
                no: 10,
            },
            Instr::Set {
                dst: 0,
                value: true,
                next: 5,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 6,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 7,
            },
            Instr::Branch {
                test: 0,
                yes: 8,
                no: 2,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 9,
            },
            Instr::Goto { next: 6 },
            Instr::Set {
                dst: 0,
                value: false,
                next: 11,
            },
            Instr::Set {
                dst: 1,
                value: false,
                next: 12,
            },
            Instr::Halt,
        ],
    )
}

/// `SubexpScopeCountSetup.countCommand`, not its later fuel setup command.
pub fn row_count_local_command() -> Result<Cmd<8, 15>, Error> {
    let counter = record_counter_program()?.lift::<8, 15>([6, 7], [14, 2])?;
    Ok(Cmd::seq(copy(1, 14, 5)?, Cmd::Call(counter)))
}

pub fn row_count_local_program() -> Result<Program<8, 15>, Error> {
    row_count_local_command()?.compiled(1, 2)
}

/// Physical `LeafHeadSetupProgramStorage.stage` for a fixed finite callee.
/// Clearing the entire work bank and copying *both* directions are charged.
/// All scratch operations use the same physical port 659 as the Lean source.
pub(crate) fn stage<const R: usize, const S: usize>(
    callee: Program<R, S>,
    registers: [usize; R],
    inputs: &[(usize, usize)],
    outputs: &[(usize, usize)],
) -> Result<Cmd<16, 768>, Error> {
    if S > 288 || registers.iter().any(|&r| r >= 16) {
        return Err(Error::Invalid(
            "bootstrap stage exceeds fixed workspace".into(),
        ));
    }
    let work: Vec<_> = (WORK_BASE..WORK_BASE + S).collect();
    let input_copies: Vec<_> = inputs
        .iter()
        .map(|&(src, dst)| (src, WORK_BASE + dst))
        .collect();
    let output_copies: Vec<_> = outputs
        .iter()
        .map(|&(src, dst)| (WORK_BASE + src, dst))
        .collect();
    if inputs.iter().any(|&(_, dst)| dst >= S) || outputs.iter().any(|&(src, _)| src >= S) {
        return Err(Error::Invalid(
            "stage input/output port is out of range".into(),
        ));
    }
    let prepare = Cmd::seq(
        clear_many(&[TEMPORARY])?,
        Cmd::seq(
            clear_many(&work)?,
            Cmd::seq(reset_work(), copy_many(TEMPORARY, &input_copies)?),
        ),
    );
    let call =
        Cmd::Call(callee.lift::<16, 768>(registers, std::array::from_fn(|i| WORK_BASE + i))?);
    let destinations: Vec<_> = output_copies.iter().map(|&(_, dst)| dst).collect();
    let finish = Cmd::seq(
        clear_many(&destinations)?,
        Cmd::seq(
            copy_many(TEMPORARY, &output_copies)?,
            Cmd::seq(clear_many(&work)?, reset_work()),
        ),
    );
    Ok(Cmd::seq(prepare, Cmd::seq(call, finish)))
}

/// Actual `LeafHeadSetupProgram.initializeAddress` stage. Consumes low-bank
/// source stacks 130 and 307 and produces first address on 649 and its
/// preserved color count on 648.
pub fn initialize_address_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        address_local_program()?,
        [13, 14, 15],
        &[(130, 0), (307, 2)],
        &[(3, 648), (4, 649)],
    )
}

/// Actual `LeafHeadSetupProgram.countRows` stage. A framed list of arbitrary
/// bit words on stack 136 yields a unary number of records on stack 647.
pub fn count_rows_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        row_count_local_program()?,
        std::array::from_fn(|i| 8 + i),
        &[(136, 1)],
        &[(2, 647)],
    )
}

/// The exact first two stages of `boot` (not the complete `boot`).
pub fn bootstrap_prefix_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(
        initialize_address_command()?,
        count_rows_command()?,
    ))
}

pub fn bootstrap_prefix_program() -> Result<Program<16, 768>, Error> {
    bootstrap_prefix_command()?.compiled(307, 647)
}

/// Actual `LeafHeadSetupProgram.retainCache`, to be appended AFTER a real
/// integer-cache producer has populated 640, 641, and 642. It intentionally
/// does not clear destinations 710–712; the Lean source preserves their tails.
pub fn retain_cache_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(
        clear_many(&[TEMPORARY])?,
        copy_many(TEMPORARY, &[(640, 710), (641, 711), (642, 712)])?,
    ))
}

pub fn retain_cache_program() -> Result<Program<16, 768>, Error> {
    retain_cache_command()?.compiled(307, 647)
}

/// The real node callback lifts the lower 16×768 machine into registers
/// 24..39, stacks 128..895. This is a *prefix only* until integer-cache
/// construction was implemented. The full callback is provided below.
pub fn bootstrap_prefix_node_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(bootstrap_prefix_program()?.lift::<40, 896>(
        std::array::from_fn(|i| 24 + i),
        std::array::from_fn(|i| 128 + i),
    )?))
}

/// LeafHeadSetupProgram.initializeCache: an isolated source-defined 8×24
/// integer-cache program, with paid copies in both directions.
/// Its theorem assumes width >= 1 + 2 * height * interpolation_order.
/// The underlying machine does not enforce this precondition.
pub fn initialize_cache_command() -> Result<Cmd<16, 768>, Error> {
    stage(
        integer_cache_program()?,
        std::array::from_fn(|i| 8 + i),
        &[(139, 20), (138, 21), (140, 22)],
        &[(0, 640), (1, 641), (2, 642), (19, 643)],
    )
}

/// Exact LeafHeadSetupProgram.boot sequence.
pub fn boot_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(
        initialize_address_command()?,
        Cmd::seq(count_rows_command()?, initialize_cache_command()?),
    ))
}

/// The source's SignatureHeadLoader.bootstrapProgram compiles
/// (boot ;; retainCache) with input 307 and output 647.
pub fn bootstrap_command() -> Result<Cmd<16, 768>, Error> {
    Ok(Cmd::seq(boot_command()?, retain_cache_command()?))
}

pub fn bootstrap_program() -> Result<Program<16, 768>, Error> {
    bootstrap_command()?.compiled(307, 647)
}

/// QueryStreamProgram.bootstrapNode lifts registers by 24 and stacks by 128.
pub fn bootstrap_node_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::Call(bootstrap_program()?.lift::<40, 896>(
        std::array::from_fn(|i| 24 + i),
        std::array::from_fn(|i| 128 + i),
    )?))
}
