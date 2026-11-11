//! Direct executable primitive tape transition evaluator for the pinned Lean
//! BitProgramCompile -> StackAdapter -> StackCompiler -> StackMachine path.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! This is finite evidence, NOT a translation of Lean's proof certificate.
//! BitProgram.run counts source instructions, not the primitive transitions
//! counted below. Heap allocations and arbitrary-precision bit costs are not
//! modelled by these counters.

use std::collections::{BTreeMap, BTreeSet};

use crate::Error;
use crate::bit_program::{Config, Instr, Program};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimitiveLimits {
    pub max_source_steps: u64,
    pub max_primitive_steps: u64,
    pub max_visited_cells: usize,
    pub max_encoded_bits: usize,
}

impl Default for PrimitiveLimits {
    fn default() -> Self {
        Self {
            max_source_steps: 100_000,
            max_primitive_steps: 3_000_000,
            max_visited_cells: 1_000_000,
            max_encoded_bits: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrimitiveStats {
    /// Number of complete BitProgram.step transitions.
    pub source_steps: u64,
    /// Actual executed TM2.Stmt constructors (not statementSize bound).
    pub tm2_microsteps: u64,
    /// Transitions of the source's StackCompiler.controller.
    pub primitive_steps: u64,
    pub head_moves: u64,
    pub writes: u64,
    /// Distinct (tape index, relative cell position) visited by a head.
    pub visited_cells: usize,
    pub peak_live_stack_bits: usize,
    pub peak_encoded_bits: usize,
    /// StackAdapter.overhead for this finite program, a per-source-step bound.
    pub source_step_overhead_bound: u64,
}

#[derive(Clone, Debug)]
struct Tape {
    /// A some false is a real, nonblank cell. Absence is Lean's none.
    cells: BTreeMap<i64, bool>,
    head: i64,
    visited: BTreeSet<i64>,
}

impl Tape {
    fn from_bits(bits: &[bool]) -> Result<Self, Error> {
        let cells = bits
            .iter()
            .enumerate()
            .map(|(i, b)| {
                i64::try_from(i)
                    .map(|at| (at, *b))
                    .map_err(|_| Error::Overflow)
            })
            .collect::<Result<_, _>>()?;
        Ok(Self {
            cells,
            head: 0,
            visited: BTreeSet::new(),
        })
    }

    fn read(&self) -> Option<bool> {
        self.cells.get(&self.head).copied()
    }

    fn touch(&mut self, stats: &mut PrimitiveStats, limits: PrimitiveLimits) -> Result<(), Error> {
        if self.visited.insert(self.head) {
            stats.visited_cells = stats.visited_cells.checked_add(1).ok_or(Error::Overflow)?;
            if stats.visited_cells > limits.max_visited_cells {
                return Err(Error::Capacity("primitive visited-cell limit".into()));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Action {
    Write(Option<bool>),
    Left,
    Right,
    Halt,
}

fn primitive_step(
    tape: &mut Tape,
    action: Action,
    stats: &mut PrimitiveStats,
    limits: PrimitiveLimits,
) -> Result<(), Error> {
    if stats.primitive_steps >= limits.max_primitive_steps {
        return Err(Error::Capacity(
            "primitive TM tape-transition budget".into(),
        ));
    }
    tape.touch(stats, limits)?;
    match action {
        Action::Write(bit) => {
            if let Some(value) = bit {
                tape.cells.insert(tape.head, value);
            } else {
                tape.cells.remove(&tape.head);
            }
            stats.writes = stats.writes.checked_add(1).ok_or(Error::Overflow)?;
        }
        Action::Left | Action::Right => {
            tape.head = if matches!(action, Action::Left) {
                tape.head.checked_sub(1)
            } else {
                tape.head.checked_add(1)
            }
            .ok_or(Error::Overflow)?;
            tape.touch(stats, limits)?;
            stats.head_moves = stats.head_moves.checked_add(1).ok_or(Error::Overflow)?;
        }
        Action::Halt => {}
    }
    stats.primitive_steps = stats
        .primitive_steps
        .checked_add(1)
        .ok_or(Error::Overflow)?;
    Ok(())
}

fn width(port: usize, input: usize) -> usize {
    if port == input { 1 } else { 2 }
}

// Boolean is enumerated as false=0/true=1. For non-input tapes, the
// StackEncoding.codeOfEquiv 2-bit chunk is [false, value], with first
// coordinate most significant in the recursively defined chunkEquiv.
fn block(port: usize, input: usize, bit: bool) -> Vec<bool> {
    if port == input {
        vec![bit]
    } else {
        vec![false, bit]
    }
}

fn decode(port: usize, input: usize, bits: &[Option<bool>]) -> Result<Option<bool>, Error> {
    if bits.iter().all(Option::is_none) {
        return Ok(None);
    }
    if port == input {
        return match bits {
            [Some(bit)] => Ok(Some(*bit)),
            _ => Err(Error::Invalid("invalid raw Boolean input block".into())),
        };
    }
    match bits {
        [Some(false), Some(bit)] => Ok(Some(*bit)),
        _ => Err(Error::Invalid(
            "invalid encoded Boolean work-stack block".into(),
        )),
    }
}

fn encoded_stack(port: usize, input: usize, stack: impl IntoIterator<Item = bool>) -> Vec<bool> {
    stack
        .into_iter()
        .flat_map(|bit| block(port, input, bit))
        .collect()
}
