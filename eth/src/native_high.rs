//! Source-pinned executable marked-query odometer initialization.
//!
//! Direct finite instruction programs from:
//! - `StackRoutines.clearProgram` and `.copyProgram`
//! - `BankRoutines.clearCmd`
//! - `SqrtLog/HighIncidenceProgramBranches.lean` (`Branches.command`)
//! - `SqrtLogSpace/HighCountSeed.lean` (`command`, `initializeCmd`)
//! - `SqrtLogSpace/HighCountInit.lean` (`command`)
//!
//! Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
//! This is an actual source-instruction port of a marked-query *initializer*,
//! not yet the substantive `HighQueryProgram.marked` query, native arithmetic,
//! a primitive TM2 trace, or an ETH time-bound refinement.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};

/// Exact three-instruction source table (`StackRoutines.clearProgram`).
pub fn clear_program<const R: usize, const S: usize>(
    src: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    Program::new(
        src,
        src,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 0,
                no: 2,
            },
            Instr::Halt,
        ],
    )
}

/// Exact eight-instruction preserving-copy source table.
/// The source requires `src`, `dst`, `tmp` to be distinct and `tmp` empty.
/// We reject invalid port aliases; absence of scratch contents is a caller
/// precondition, rather than silently clearing unrequested data.
pub fn copy_program<const R: usize, const S: usize>(
    src: usize,
    dst: usize,
    tmp: usize,
    value: usize,
    present: usize,
) -> Result<Program<R, S>, Error> {
    if src == dst || src == tmp || dst == tmp || value == present {
        return Err(Error::Invalid(
            "copy requires disjoint ports and read registers".into(),
        ));
    }
    Program::new(
        src,
        dst,
        0,
        vec![
            Instr::Pop {
                stack: src,
                value,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 3,
            },
            Instr::Push {
                stack: tmp,
                src: value,
                next: 0,
            },
            Instr::Pop {
                stack: tmp,
                value,
                present,
                next: 4,
            },
            Instr::Branch {
                test: present,
                yes: 5,
                no: 7,
            },
            Instr::Push {
                stack: src,
                src: value,
                next: 6,
            },
            Instr::Push {
                stack: dst,
                src: value,
                next: 3,
            },
            Instr::Halt,
        ],
    )
}

fn clear_call<const R: usize, const S: usize>(src: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(src, 0, 1)?))
}

/// `BankRoutines.clearCmd`: clears all static ports, then the temporary port.
fn clear_bank<const R: usize, const S: usize>(
    tmp: usize,
    changed: &[usize],
) -> Result<Cmd<R, S>, Error> {
    let mut cmd = clear_call(tmp)?;
    for &port in changed.iter().rev() {
        cmd = Cmd::seq(clear_call(port)?, cmd);
    }
    Ok(cmd)
}

fn set<const R: usize, const S: usize>(dst: usize, value: bool) -> Cmd<R, S> {
    Cmd::Atom(Atom::Set { dst, value })
}

fn push<const R: usize, const S: usize>(port: usize, src: usize) -> Cmd<R, S> {
    Cmd::Atom(Atom::Push { stack: port, src })
}

/// The four-bit record in `Branches.record` is `[true,true,false,false]`.
/// Four source instructions set register 0 and four push to stack 1.
fn branch_record() -> Cmd<2, 2> {
    // Source order: push false, push false, push true, push true;
    // stack top becomes true,true,false,false.
    let mut cmd = Cmd::Skip;
    for bit in [false, false, true, true] {
        cmd = Cmd::seq(cmd, Cmd::seq(set(0, bit), push(1, 0)));
    }
    cmd
}

/// `HighIncidenceProgram.Branches.command`: one seed terminator, then one
/// four-bit record for each true bit of the supplied high-coordinate mask.
pub fn branch_command() -> Cmd<2, 2> {
    let pop = Cmd::Atom(Atom::Pop {
        stack: 0,
        value: 0,
        present: 1,
    });
    Cmd::seq(
        Cmd::seq(set(0, false), push(1, 0)),
        Cmd::seq(
            pop.clone(),
            Cmd::while_(1, Cmd::seq(Cmd::ite(0, branch_record(), Cmd::Skip), pop)),
        ),
    )
}

pub fn branch_program() -> Result<Program<2, 2>, Error> {
    branch_command().compiled(0, 1)
}

/// `HighCountSeed.command` with *physical* register and stack mappings.
/// The 2x2 Branches machine is statically lifted into registers [0,1] and
/// stacks [792,330] of the 40x896 leaf machine.
pub fn seed_command() -> Result<Cmd<40, 896>, Error> {
    let reset = Cmd::seq(clear_call(791)?, clear_bank(791, &[330, 791, 792])?);
    let copy = Cmd::Call(copy_program(338, 792, 791, 0, 1)?);
    let branch = Cmd::Call(branch_program()?.lift::<40, 896>([0, 1], [792, 330])?);
    Ok(Cmd::seq(reset, Cmd::seq(copy, branch)))
}

pub fn seed_program() -> Result<Program<40, 896>, Error> {
    seed_command()?.compiled(338, 330)
}

/// `HighCountInit.command`, clearing stale high-query output and copying the
/// initialized counter from 330 to 789 before setting guard register 21.
pub fn high_count_init_command() -> Result<Cmd<40, 896>, Error> {
    let reset = Cmd::seq(
        clear_call(792)?,
        clear_bank(792, &[788, 789, 790, 323, 791, 792])?,
    );
    let copy = Cmd::Call(copy_program(330, 789, 792, 0, 1)?);
    Ok(Cmd::seq(reset, Cmd::seq(copy, set(21, true))))
}

pub fn high_count_init_program() -> Result<Program<40, 896>, Error> {
    high_count_init_command()?.compiled(330, 788)
}

/// The actual nested source compilation of `HighCountSeed.initializeCmd`:
/// `.seq (.call seed_program) (.call HighCountInit.program)`.
/// The two internal compiled halt instructions become return jumps, not
/// implicit high-level calls.
pub fn initialize_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(seed_program()?),
        Cmd::Call(high_count_init_program()?),
    ))
}

pub fn initialize_program() -> Result<Program<40, 896>, Error> {
    initialize_command()?.compiled(338, 789)
}

/// Exact Lean `Encoding.encodeList id (List.replicate h [false])` payload.
pub fn high_odometer_word(true_count: usize) -> Result<Vec<bool>, Error> {
    let capacity = true_count
        .checked_mul(4)
        .and_then(|v| v.checked_add(1))
        .ok_or(Error::Overflow)?;
    let mut bits = Vec::with_capacity(capacity);
    for _ in 0..true_count {
        bits.extend([true, true, false, false]);
    }
    bits.push(false);
    Ok(bits)
}
