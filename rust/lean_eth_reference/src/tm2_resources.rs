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

/// One executed primitive controller transition. A blank is None, while
/// Some(false) is a physically written zero. Heads use per-tape coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimitiveAction {
    Write(Option<bool>),
    Left,
    Right,
    Halt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimitiveEvent {
    pub source_index: u64,
    pub micro_index: u64,
    pub tape: usize,
    pub action: PrimitiveAction,
    pub head_before: i64,
    pub head_after: i64,
    pub cell_before: Option<bool>,
    pub cell_after: Option<bool>,
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

type Action = PrimitiveAction;

struct Accounting<'a, 'b> {
    stats: &'a mut PrimitiveStats,
    limits: PrimitiveLimits,
    trace: &'a mut Option<&'b mut Vec<PrimitiveEvent>>,
    max_trace_events: usize,
}

fn primitive_step(
    tape: &mut Tape,
    action: Action,
    tape_index: usize,
    ctx: &mut Accounting<'_, '_>,
) -> Result<(), Error> {
    if ctx.trace.as_ref().is_some_and(|v| v.len() >= ctx.max_trace_events) {
        return Err(Error::Capacity("primitive trace event budget".into()));
    }
    if ctx.stats.primitive_steps >= ctx.limits.max_primitive_steps {
        return Err(Error::Capacity("primitive TM tape-transition budget".into()));
    }
    tape.touch(ctx.stats, ctx.limits)?;
    let head_before = tape.head;
    let cell_before = tape.read();
    match action {
        Action::Write(bit) => {
            if let Some(value) = bit {
                tape.cells.insert(tape.head, value);
            } else {
                tape.cells.remove(&tape.head);
            }
            ctx.stats.writes = ctx.stats.writes.checked_add(1).ok_or(Error::Overflow)?;
        }
        Action::Left | Action::Right => {
            tape.head = if matches!(action, Action::Left) {
                tape.head.checked_sub(1)
            } else {
                tape.head.checked_add(1)
            }
            .ok_or(Error::Overflow)?;
            tape.touch(ctx.stats, ctx.limits)?;
            ctx.stats.head_moves = ctx.stats.head_moves.checked_add(1).ok_or(Error::Overflow)?;
        }
        Action::Halt => {}
    }
    if let Some(events) = ctx.trace.as_mut() {
        events.push(PrimitiveEvent {
            source_index: ctx.stats.source_steps,
            micro_index: ctx.stats.tm2_microsteps,
            tape: tape_index,
            action,
            head_before,
            head_after: tape.head,
            cell_before,
            cell_after: tape.read(),
        });
    }
    ctx.stats.primitive_steps = ctx.stats.primitive_steps.checked_add(1).ok_or(Error::Overflow)?;
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

fn snapshot<const R: usize, const S: usize>(
    p: &Program<R, S>,
    pc: Option<usize>,
    regs: [bool; R],
    tapes: &[Tape],
) -> Result<Config<R, S>, Error> {
    let stacks: [std::collections::VecDeque<bool>; S] = (0..S)
        .map(|port| {
            let tape = &tapes[port];
            let mut cells = std::collections::VecDeque::new();
            let mut address = tape.head;
            loop {
                let mut bits = Vec::with_capacity(width(port, p.input_stack()));
                for _ in 0..width(port, p.input_stack()) {
                    bits.push(tape.cells.get(&address).copied());
                    address = address.checked_add(1).ok_or(Error::Overflow)?;
                }
                match decode(port, p.input_stack(), &bits)? {
                    Some(bit) => cells.push_back(bit),
                    None => break,
                }
                // Cannot decode more blocks than physically represented cells.
                if cells.len() > tape.cells.len() {
                    return Err(Error::Invalid("nonterminating physical tape decode".into()));
                }
            }
            Ok::<_, Error>(cells)
        })
        .collect::<Result<Vec<_>, _>>()?
        .try_into()
        .map_err(|_| Error::Invalid("incorrect tape count".into()))?;
    Ok(Config { pc, regs, stacks })
}

#[derive(Clone, Debug)]
enum Micro {
    Halt,
    Goto(usize),
    Load(Instr),
    Branch {
        test: usize,
        yes: usize,
        no: usize,
    },
    Push {
        stack: usize,
        src: usize,
    },
    Peek {
        stack: usize,
        value: usize,
        present: usize,
    },
    Pop {
        stack: usize,
        value: usize,
        present: usize,
    },
}

fn microcode(instruction: &Instr) -> Vec<Micro> {
    match instruction {
        Instr::Halt => vec![Micro::Halt],
        Instr::Goto { next } => vec![Micro::Goto(*next)],
        Instr::Branch { test, yes, no } => vec![
            Micro::Branch {
                test: *test,
                yes: *yes,
                no: *no,
            },
            Micro::Goto(usize::MAX), // replaced with selected branch target
        ],
        Instr::Push { stack, src, next } => vec![
            Micro::Push {
                stack: *stack,
                src: *src,
            },
            Micro::Goto(*next),
        ],
        Instr::Peek {
            stack,
            value,
            present,
            next,
        } => vec![
            Micro::Peek {
                stack: *stack,
                value: *value,
                present: *present,
            },
            Micro::Goto(*next),
        ],
        Instr::Pop {
            stack,
            value,
            present,
            next,
        } => vec![
            Micro::Pop {
                stack: *stack,
                value: *value,
                present: *present,
            },
            Micro::Goto(*next),
        ],
        _ => {
            let next = match instruction {
                Instr::Set { next, .. }
                | Instr::Copy { next, .. }
                | Instr::Not { next, .. }
                | Instr::And { next, .. }
                | Instr::Or { next, .. }
                | Instr::Xor { next, .. } => *next,
                _ => unreachable!(),
            };
            vec![Micro::Load(instruction.clone()), Micro::Goto(next)]
        }
    }
}

fn source_step_overhead<const R: usize, const S: usize>(p: &Program<R, S>) -> Result<u64, Error> {
    let max_width = if S > 1 { 2u64 } else { 1u64 };
    let compiler = max_width * 4 + 3;
    let block = p
        .code()
        .iter()
        .map(|i| match i {
            Instr::Halt | Instr::Goto { .. } => 1u64,
            Instr::Branch { .. } => 3u64, // both branches counted in statementSize
            _ => 2u64,
        })
        .max()
        .ok_or_else(|| Error::Invalid("empty source program".into()))?;
    compiler.checked_mul(block).ok_or(Error::Overflow)
}

/// Directly execute the StackCompiler primitive controller for one TM2
/// constructor. Each write/move is charged as one physical transition.
fn execute_micro<const R: usize, const S: usize>(
    instruction: &Micro,
    p: &Program<R, S>,
    pc: &mut Option<usize>,
    regs: &mut [bool; R],
    tapes: &mut [Tape],
    ctx: &mut Accounting<'_, '_>,
) -> Result<(), Error> {
    let port = match instruction {
        Micro::Push { stack, .. } | Micro::Peek { stack, .. } | Micro::Pop { stack, .. } => *stack,
        Micro::Halt => p.output_stack(),
        _ => p.input_stack(),
    };
    let w = width(port, p.input_stack());
    let tape = &mut tapes[port];

    // Ready -> reading: one write bit (including blank bit) transition.
    let unchanged = tape.read();
    primitive_step(tape, Action::Write(unchanged), port, ctx)?;
    let mut register_bits = Vec::with_capacity(w);
    for _ in 0..w {
        register_bits.push(tape.read());
        primitive_step(tape, Action::Right, port, ctx)?;
    }
    for _ in 0..w {
        primitive_step(tape, Action::Left, port, ctx)?;
    }

    let mut op = None;
    let mut halts = false;
    match instruction {
        Micro::Halt => {
            *pc = None;
            halts = true;
        }
        Micro::Goto(next) => *pc = Some(*next),
        Micro::Load(source) => match source {
            Instr::Set { dst, value, .. } => regs[*dst] = *value,
            Instr::Copy { dst, src, .. } => regs[*dst] = regs[*src],
            Instr::Not { dst, src, .. } => regs[*dst] = !regs[*src],
            Instr::And {
                dst, left, right, ..
            } => regs[*dst] = regs[*left] && regs[*right],
            Instr::Or {
                dst, left, right, ..
            } => regs[*dst] = regs[*left] || regs[*right],
            Instr::Xor {
                dst, left, right, ..
            } => regs[*dst] = regs[*left] ^ regs[*right],
            _ => return Err(Error::Invalid("non-load compiled into TM2 load".into())),
        },
        Micro::Branch { test, yes, no } => {
            *pc = Some(if regs[*test] { *yes } else { *no });
        }
        Micro::Push { src, .. } => op = Some(Some(regs[*src])),
        Micro::Peek { value, present, .. } | Micro::Pop { value, present, .. } => {
            let top = decode(port, p.input_stack(), &register_bits)?;
            regs[*value] = top.unwrap_or(false);
            regs[*present] = top.is_some();
            if matches!(instruction, Micro::Pop { .. }) {
                op = Some(None);
            }
        }
    }

    // Reading -> action state (or halt), one transition. This is a write-self
    // for all non-halting instructions. The halt transition has no action.
    if halts {
        primitive_step(tape, Action::Halt, port, ctx)?;
    } else {
        let unchanged = tape.read();
        primitive_step(tape, Action::Write(unchanged), port, ctx)?;
        match op {
            Some(Some(bit)) => {
                // StackMachine.pushBits recurses on the tail: emit low bits
                // right-to-left, each as move-left followed by write.
                for value in block(port, p.input_stack(), bit).into_iter().rev() {
                    primitive_step(tape, Action::Left, port, ctx)?;
                    primitive_step(tape, Action::Write(Some(value)), port, ctx)?;
                }
            }
            Some(None) => {
                // StackMachine.popBits repeats blank-write, move-right
                // even when the source stack was already empty.
                for _ in 0..w {
                    primitive_step(tape, Action::Write(None), port, ctx)?;
                    primitive_step(tape, Action::Right, port, ctx)?;
                }
            }
            None => {}
        }
        // Acting -> ready: one final write-self transition.
        let unchanged = tape.read();
        primitive_step(tape, Action::Write(unchanged), port, ctx)?;
    }
    ctx.stats.tm2_microsteps = ctx.stats.tm2_microsteps.checked_add(1).ok_or(Error::Overflow)?;
    Ok(())
}

/// Execute the primitive-bit compiler and independently check every completed
/// BitProgram instruction boundary. The caller's config is committed only on
/// success: budget exhaustion and mismatches leave it unchanged.
///
/// The visited-cell count is distinct head positions on each physical tape,
/// including destination positions reached on a head move. It is NOT peak
/// allocated heap memory or a proof of an asymptotic space bound.
pub fn run_primitive<const R: usize, const S: usize>(
    p: &Program<R, S>,
    config: &mut Config<R, S>,
    limits: PrimitiveLimits,
) -> Result<PrimitiveStats, Error> {
    run_primitive_inner(p, config, limits, None, 0)
}

/// Return all primitive transition events for bounded, small fixtures. No
/// partial trace escapes on refusal; the input config is unchanged on error.
pub fn run_primitive_traced<const R: usize, const S: usize>(
    p: &Program<R, S>,
    config: &mut Config<R, S>,
    limits: PrimitiveLimits,
    max_trace_events: usize,
) -> Result<(PrimitiveStats, Vec<PrimitiveEvent>), Error> {
    let mut events = Vec::new();
    let stats = run_primitive_inner(p, config, limits, Some(&mut events), max_trace_events)?;
    debug_assert_eq!(events.len() as u64, stats.primitive_steps);
    Ok((stats, events))
}

fn run_primitive_inner<const R: usize, const S: usize>(
    p: &Program<R, S>,
    config: &mut Config<R, S>,
    limits: PrimitiveLimits,
    mut trace: Option<&mut Vec<PrimitiveEvent>>,
    max_trace_events: usize,
) -> Result<PrimitiveStats, Error> {
    let mut regs = config.regs;
    let mut pc = config.pc;
    let mut tapes = (0..S)
        .map(|port| {
            let encoded = encoded_stack(port, p.input_stack(), config.stacks[port].iter().copied());
            Tape::from_bits(&encoded)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut stats = PrimitiveStats {
        peak_live_stack_bits: config.stack_bits()?,
        source_step_overhead_bound: source_step_overhead(p)?,
        ..PrimitiveStats::default()
    };
    stats.peak_encoded_bits = tapes.iter().try_fold(0usize, |sum, tape| {
        sum.checked_add(tape.cells.len()).ok_or(Error::Overflow)
    })?;
    if stats.peak_encoded_bits > limits.max_encoded_bits {
        return Err(Error::Capacity("initial physical tape bits".into()));
    }
    let mut reference = config.clone();
    while let Some(label) = pc {
        if stats.source_steps >= limits.max_source_steps {
            return Err(Error::Capacity("source instruction budget".into()));
        }
        let instr = p
            .code()
            .get(label)
            .ok_or_else(|| Error::Invalid("invalid program counter".into()))?;
        let mut micro = microcode(instr);
        for operation in &mut micro {
            // A compiled branch evaluates the predicate, then executes a goto
            // chosen by the predicate. No third source instruction is executed.
            if let Micro::Goto(next) = operation
                && *next == usize::MAX
            {
                *next = pc.ok_or_else(|| Error::Invalid("missing branch target".into()))?;
            }
            execute_micro(
                operation,
                p,
                &mut pc,
                &mut regs,
                &mut tapes,
                &mut Accounting {
                    stats: &mut stats,
                    limits,
                    trace: &mut trace,
                    max_trace_events,
                },
            )?;
            let live_encoded = tapes.iter().try_fold(0usize, |sum, tape| {
                sum.checked_add(tape.cells.len()).ok_or(Error::Overflow)
            })?;
            stats.peak_encoded_bits = stats.peak_encoded_bits.max(live_encoded);
            if stats.peak_encoded_bits > limits.max_encoded_bits {
                return Err(Error::Capacity("primitive encoded bit capacity".into()));
            }
        }
        if !p.step(&mut reference)? {
            return Err(Error::Invalid(
                "source unexpectedly halted during primitive step".into(),
            ));
        }
        stats.source_steps = stats.source_steps.checked_add(1).ok_or(Error::Overflow)?;
        let obtained = snapshot(p, pc, regs, &tapes)?;
        if obtained != reference {
            return Err(Error::Invalid(format!(
                "source/TM2 boundary mismatch after {} source instructions",
                stats.source_steps
            )));
        }
        stats.peak_live_stack_bits = stats.peak_live_stack_bits.max(obtained.stack_bits()?);
        if stats.primitive_steps
            > stats
                .source_steps
                .saturating_mul(stats.source_step_overhead_bound)
        {
            return Err(Error::Invalid(
                "source compiler primitive step bound violated".into(),
            ));
        }
    }
    *config = reference;
    Ok(stats)
}
