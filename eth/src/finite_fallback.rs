//! Constructive finite-control cutoff scanner from the pinned Lean source.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
//! SqrtLogSpace/FiniteFallback.lean, Scanner.program, cutoffScanner, cutoffCommand.
//! Git blob: 1fc8e1817b4f24d3255ef8fc398fb2127d214284.
//!
//! This is NOT FiniteFallback.countProgram: that program chooses a finite
//! table noncomputably, including tableCount and Fintype.equivFin.
//! The bounded SAT count branch remains unsupported until a source-refined
//! table is independently exhibited. No semantic count oracle is substituted.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::{clear_program, copy_program};

/// Explicit static-table allocation limit, NOT a theorem or Lean cutoff.
/// Rejection is preferred to allocating unbounded instruction vectors.
pub const MAX_CUTOFF_LABELS: usize = 1_000_000;

/// Port of FiniteFallback.cutoffScanner B via Scanner.program 1.
///
/// Each scanner state q is a saturated true-bit count in 0..=B+1.
/// The seven labels per state implement pop, presence branch, bit branch,
/// write the one-bit flag, push it, clear the value register, and halt.
/// The state-major label numbering is a fixed bijective renaming of the
/// Lean Fin (B+2) × Fin 7 label product; steps and physical effects agree.
/// This reads all input bits, not merely their length.
pub fn cutoff_scanner(cutoff: usize) -> Result<Program<2, 1>, Error> {
    let states = cutoff.checked_add(2).ok_or(Error::Overflow)?;
    let labels = states.checked_mul(7).ok_or(Error::Overflow)?;
    if labels > MAX_CUTOFF_LABELS {
        return Err(Error::Capacity(format!(
            "finite cutoff scanner requires {labels} labels; cap is {MAX_CUTOFF_LABELS}"
        )));
    }
    let mut code = Vec::with_capacity(labels);
    let saturated = cutoff + 1;
    for q in 0..states {
        let base = q * 7;
        let incremented = q.saturating_add(1).min(saturated);
        code.extend([
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: base + 1,
            },
            Instr::Branch {
                test: 1,
                yes: base + 2,
                no: base + 3,
            },
            Instr::Branch {
                test: 0,
                yes: incremented * 7,
                no: base,
            },
            Instr::Set {
                dst: 0,
                value: q <= cutoff,
                next: base + 4,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: base + 5,
            },
            Instr::Set {
                dst: 0,
                value: false,
                next: base + 6,
            },
            Instr::Halt,
        ]);
    }
    Program::new(0, 0, 0, code)
}

/// The executable cutoff half of FiniteFallback.dispatchCommand.
///
/// Source port map: stack 258 is a preserved unary header, 270 is the
/// scanner word, 271 is copy scratch; registers 72/73 clear/copy and
/// 75/76 receive the comparison flag/presence. Both scratch stacks are
/// cleared before use, even when initially dirty. This stops before
/// the unsupported conditional dispatch into the finite counting table.
pub fn cutoff_command(cutoff: usize) -> Result<Cmd<80, 1220>, Error> {
    let clear_work = Cmd::Call(clear_program(270, 72, 73)?);
    let clear_scratch = Cmd::Call(clear_program(271, 72, 73)?);
    let copy_header = Cmd::Call(copy_program(258, 270, 271, 72, 73)?);
    let scan = Cmd::Call(cutoff_scanner(cutoff)?.lift::<80, 1220>([75, 76], [270])?);
    let extract_flag = Cmd::Atom(Atom::Pop {
        stack: 270,
        value: 75,
        present: 76,
    });
    Ok(Cmd::seq(
        clear_work,
        Cmd::seq(
            clear_scratch,
            Cmd::seq(copy_header, Cmd::seq(scan, extract_flag)),
        ),
    ))
}

pub fn cutoff_program(cutoff: usize) -> Result<Program<80, 1220>, Error> {
    cutoff_command(cutoff)?.compiled(258, 270)
}
