//! On-demand physical instruction view for shared Lean program composition.
//!
//! This is a prototype backend for a future Lean-elaborated structural IR.
//! No constructor silently replaces physical source steps with semantic #SAT
//! operations. In particular a Call keeps the callee's complete label space:
//! its halt becomes a jump to the caller continuation.

use std::sync::Arc;

use super::{Atom, Config, Instr, Program, RunLimits, RunStats, execute_instr};
use crate::Error;

/// Source instruction view hides only the callee's *finite dimensions*, not
/// its instructions or any machine steps. A lifted program stays on demand.
pub(super) trait PhysicalSource: std::fmt::Debug + Send + Sync {
    fn instruction_at(&self, pc: usize) -> Result<Instr, Error>;
}

impl<const R: usize, const S: usize> PhysicalSource for DeferredProgram<R, S> {
    fn instruction_at(&self, pc: usize) -> Result<Instr, Error> {
        DeferredProgram::instruction_at(self, pc)
    }
}

/// Original ProgramLinking.relocateInstr data-port portion, covering every
/// source opcode. The label map is identity for a lift.
pub fn relocate_ports(instr: Instr, registers: &[usize], stacks: &[usize]) -> Result<Instr, Error> {
    let reg = |i: usize| {
        registers
            .get(i)
            .copied()
            .ok_or_else(|| Error::Invalid(format!("source register {i} outside lift map")))
    };
    let stack = |i: usize| {
        stacks
            .get(i)
            .copied()
            .ok_or_else(|| Error::Invalid(format!("source stack {i} outside lift map")))
    };
    Ok(match instr {
        Instr::Halt => Instr::Halt,
        Instr::Goto { next } => Instr::Goto { next },
        Instr::Set { dst, value, next } => Instr::Set {
            dst: reg(dst)?,
            value,
            next,
        },
        Instr::Copy { dst, src, next } => Instr::Copy {
            dst: reg(dst)?,
            src: reg(src)?,
            next,
        },
        Instr::Not { dst, src, next } => Instr::Not {
            dst: reg(dst)?,
            src: reg(src)?,
            next,
        },
        Instr::And {
            dst,
            left,
            right,
            next,
        } => Instr::And {
            dst: reg(dst)?,
            left: reg(left)?,
            right: reg(right)?,
            next,
        },
        Instr::Or {
            dst,
            left,
            right,
            next,
        } => Instr::Or {
            dst: reg(dst)?,
            left: reg(left)?,
            right: reg(right)?,
            next,
        },
        Instr::Xor {
            dst,
            left,
            right,
            next,
        } => Instr::Xor {
            dst: reg(dst)?,
            left: reg(left)?,
            right: reg(right)?,
            next,
        },
        Instr::Branch { test, yes, no } => Instr::Branch {
            test: reg(test)?,
            yes,
            no,
        },
        Instr::Push {
            stack: port,
            src,
            next,
        } => Instr::Push {
            stack: stack(port)?,
            src: reg(src)?,
            next,
        },
        Instr::Peek {
            stack: port,
            value,
            present,
            next,
        } => Instr::Peek {
            stack: stack(port)?,
            value: reg(value)?,
            present: reg(present)?,
            next,
        },
        Instr::Pop {
            stack: port,
            value,
            present,
            next,
        } => Instr::Pop {
            stack: stack(port)?,
            value: reg(value)?,
            present: reg(present)?,
            next,
        },
    })
}

pub(super) fn check_injective_map(
    map: &[usize],
    dimension: usize,
    port: &str,
) -> Result<(), Error> {
    let mut seen = vec![false; dimension];
    for &to in map {
        let Some(used) = seen.get_mut(to) else {
            return Err(Error::Invalid(format!(
                "{port} lift map outside target dimension"
            )));
        };
        if *used {
            return Err(Error::Invalid(format!("{port} lift map is not injective")));
        }
        *used = true;
    }
    Ok(())
}

#[derive(Clone, Debug)]
enum Body<const R: usize, const S: usize> {
    Table(Program<R, S>),
    Composed(Arc<Block<R, S>>),
    Source(Arc<dyn PhysicalSource>),
    Lift {
        source: Arc<dyn PhysicalSource>,
        registers: Vec<usize>,
        stacks: Vec<usize>,
    },
    Link {
        left: Arc<DeferredProgram<R, S>>,
        right: Arc<DeferredProgram<R, S>>,
    },
}

/// A physical BitProgram that can resolve a label without creating the full
/// instruction vector. In the Composed case label zero is the source halt,
/// matching StructuredCalls.compiled and StructuredProgram.compiled in Lean.
#[derive(Clone, Debug)]
pub struct DeferredProgram<const R: usize, const S: usize> {
    input_stack: usize,
    output_stack: usize,
    entry: usize,
    labels: usize,
    body: Body<R, S>,
}

impl<const R: usize, const S: usize> DeferredProgram<R, S> {
    /// Existing verified finite tables remain valid leaves of the graph.
    pub fn table(program: Program<R, S>) -> Arc<Self> {
        Arc::new(Self {
            input_stack: program.input_stack(),
            output_stack: program.output_stack(),
            entry: program.entry(),
            labels: program.code().len(),
            body: Body::Table(program),
        })
    }

    /// The single native source-graph decoder builds typed, on-demand linked
    /// physical instruction views. This does not flatten or reinterpret calls.
    /// The decoder independently checks all source dimensions and port maps.
    pub(super) fn source_program(
        input_stack: usize,
        output_stack: usize,
        entry: usize,
        labels: usize,
        source: Arc<dyn PhysicalSource>,
    ) -> Result<Arc<Self>, Error> {
        if labels == 0 || input_stack >= S || output_stack >= S || entry >= labels {
            return Err(Error::Invalid(
                "linked source program ABI outside target".into(),
            ));
        }
        Ok(Arc::new(Self {
            input_stack,
            output_stack,
            entry,
            labels,
            body: Body::Source(source),
        }))
    }

    /// Original ProgramLinking.liftProgram, without materializing the source
    /// table. Require injective finite port maps for exact framed traces.
    pub fn lift<const SR: usize, const SS: usize>(
        source: Arc<DeferredProgram<SR, SS>>,
        registers: [usize; SR],
        stacks: [usize; SS],
    ) -> Result<Arc<Self>, Error> {
        check_injective_map(&registers, R, "register")?;
        check_injective_map(&stacks, S, "stack")?;
        let input_stack = stacks[source.input_stack];
        let output_stack = stacks[source.output_stack];
        let entry = source.entry;
        let labels = source.labels;
        let source: Arc<dyn PhysicalSource> = source;
        Ok(Arc::new(Self {
            input_stack,
            output_stack,
            entry,
            labels,
            body: Body::Lift {
                source,
                registers: registers.into(),
                stacks: stacks.into(),
            },
        }))
    }

    /// Original ProgramLinking.link: left halt labels become jumps to the
    /// right entry; right halt labels remain halts, with label offset.
    pub fn link(left: Arc<Self>, right: Arc<Self>) -> Result<Arc<Self>, Error> {
        let labels = left
            .labels
            .checked_add(right.labels)
            .ok_or(Error::Overflow)?;
        let input_stack = left.input_stack;
        let output_stack = right.output_stack;
        let entry = left.entry;
        Ok(Arc::new(Self {
            input_stack,
            output_stack,
            entry,
            labels,
            body: Body::Link { left, right },
        }))
    }

    /// Original ProgramLinking.linkInto with independently mapped source
    /// registers and stacks on both sides. The two sources can have
    /// different finite dimensions, but share one target machine.
    pub fn link_into<const LR: usize, const LS: usize, const RR: usize, const RS: usize>(
        left: Arc<DeferredProgram<LR, LS>>,
        right: Arc<DeferredProgram<RR, RS>>,
        left_registers: [usize; LR],
        left_stacks: [usize; LS],
        right_registers: [usize; RR],
        right_stacks: [usize; RS],
    ) -> Result<Arc<Self>, Error> {
        Self::link(
            Self::lift(left, left_registers, left_stacks)?,
            Self::lift(right, right_registers, right_stacks)?,
        )
    }

    /// Preserve every original StructuredCalls site, without flattening.
    pub fn composed(
        input_stack: usize,
        output_stack: usize,
        root: Arc<Block<R, S>>,
    ) -> Result<Arc<Self>, Error> {
        if input_stack >= S || output_stack >= S {
            return Err(Error::Invalid("deferred program port outside Fin S".into()));
        }
        let labels = root.size.checked_add(1).ok_or(Error::Overflow)?;
        let entry = root.entry_at(1, 0)?;
        if entry >= labels {
            return Err(Error::Invalid(
                "deferred program entry outside labels".into(),
            ));
        }
        Ok(Arc::new(Self {
            input_stack,
            output_stack,
            entry,
            labels,
            body: Body::Composed(root),
        }))
    }

    pub fn labels(&self) -> usize {
        self.labels
    }

    pub fn entry(&self) -> usize {
        self.entry
    }

    /// Exact physical source ABI port indices.
    pub fn input_stack(&self) -> usize {
        self.input_stack
    }

    pub fn output_stack(&self) -> usize {
        self.output_stack
    }

    pub fn initial(&self, input: impl IntoIterator<Item = bool>) -> Config<R, S> {
        let mut config = Config {
            pc: Some(self.entry),
            regs: [false; R],
            stacks: std::array::from_fn(|_| std::collections::VecDeque::new()),
        };
        config.stacks[self.input_stack].extend(input);
        config
    }

    /// Exact physical instruction for an original Lean Fin label.
    /// A rejected or out-of-range address cannot become an implicit halt.
    pub fn instruction_at(&self, pc: usize) -> Result<Instr, Error> {
        if pc >= self.labels {
            return Err(Error::Invalid(format!(
                "deferred configuration pc {pc} outside Fin {}",
                self.labels
            )));
        }
        match &self.body {
            Body::Table(program) => Ok(program.code()[pc].clone()),
            Body::Source(source) => source.instruction_at(pc),
            Body::Composed(_) if pc == 0 => Ok(Instr::Halt),
            Body::Composed(block) => block.instruction_at(1, 0, pc),
            Body::Lift {
                source,
                registers,
                stacks,
            } => relocate_ports(source.instruction_at(pc)?, registers, stacks),
            Body::Link { left, right } if pc < left.labels => {
                let original = left.instruction_at(pc)?;
                match original {
                    Instr::Halt => Ok(Instr::Goto {
                        next: left
                            .labels
                            .checked_add(right.entry)
                            .ok_or(Error::Overflow)?,
                    }),
                    instruction => Ok(instruction),
                }
            }
            Body::Link { left, right } => {
                let original = right.instruction_at(pc - left.labels)?;
                match original {
                    Instr::Halt => Ok(Instr::Halt),
                    instruction => instruction.relocate(left.labels, 0),
                }
            }
        }
    }

    /// Construct the ordinary Program only when its size is explicitly budgeted.
    /// Used for differential testing, not for large production graphs.
    pub fn materialize(&self, max_labels: usize) -> Result<Program<R, S>, Error> {
        if self.labels > max_labels {
            return Err(Error::Capacity(
                "deferred materialization label budget".into(),
            ));
        }
        let instructions = (0..self.labels)
            .map(|pc| self.instruction_at(pc))
            .collect::<Result<Vec<_>, _>>()?;
        Program::new(
            self.input_stack,
            self.output_stack,
            self.entry,
            instructions,
        )
    }

    /// Execute one original physical BitProgram step, not one AST node.
    pub fn step(&self, config: &mut Config<R, S>) -> Result<bool, Error> {
        let Some(pc) = config.pc else {
            return Ok(false);
        };
        let instruction = self.instruction_at(pc)?;
        execute_instr(&instruction, config);
        Ok(true)
    }

    /// Physically faithful bounded execution, without a flat instruction table.
    /// The reported count is source BitProgram steps, not TM2 microsteps.
    pub fn run(&self, config: &mut Config<R, S>, limits: RunLimits) -> Result<RunStats, Error> {
        run_with_instruction_at(config, limits, self.labels, |pc| self.instruction_at(pc))
    }
}

/// Checked scalar analogue of the Lean source live-stack balance law.
///
/// The caller validates all instruction operands first, so any indexed stack
/// access below is safe. No state is mutated on refusal. Under an accurate
/// cached count, a nonempty Pop cannot underflow and an admitted Push cannot
/// overflow usize, but use checked operations anyway so a violated invariant
/// causes an explicit refusal rather than a wrapped or panicking counter.
fn next_live_bit_count<const R: usize, const S: usize>(
    instruction: &Instr,
    config: &Config<R, S>,
    cached: usize,
    limit: usize,
) -> Result<usize, Error> {
    match *instruction {
        Instr::Push { .. } => {
            if cached >= limit {
                Err(Error::Capacity("BitProgram stack-bit limit".into()))
            } else {
                cached.checked_add(1).ok_or(Error::Overflow)
            }
        }
        Instr::Pop { stack, .. } if !config.stacks[stack].is_empty() => {
            cached.checked_sub(1).ok_or(Error::Overflow)
        }
        _ => Ok(cached),
    }
}

/// Execute the exact physical BitProgram machine against an instruction lookup.
/// The caller supplies the finite number of physical labels so both the active PC
/// and every decoded successor must be admitted before any state mutation.
/// Flat, deferred, and generated source graphs share this bounded runner,
/// including instruction and stack-bit limits and readRegs overwrite ordering.
pub fn run_with_instruction_at<const R: usize, const S: usize, F>(
    config: &mut Config<R, S>,
    limits: RunLimits,
    label_count: usize,
    instruction_at: F,
) -> Result<RunStats, Error>
where
    F: FnMut(usize) -> Result<Instr, Error>,
{
    run_with_instruction_at_and_reserve(config, limits, label_count, instruction_at, |stack| {
        stack
            .try_reserve(1)
            .map_err(|_| Error::Capacity("BitProgram host stack allocation".into()))
    })
}

/// A single shared execution loop, with the host's fallible Push reservation
/// made explicit. Production passes VecDeque::try_reserve(1); unit tests can
/// force a refused reservation without exhausting host memory. The callback
/// only observes the target stack after instruction and scalar validation.
/// No source-visible instruction state may change before it returns Ok(()).
fn run_with_instruction_at_and_reserve<const R: usize, const S: usize, F, G>(
    config: &mut Config<R, S>,
    limits: RunLimits,
    label_count: usize,
    mut instruction_at: F,
    mut reserve_push: G,
) -> Result<RunStats, Error>
where
    F: FnMut(usize) -> Result<Instr, Error>,
    G: FnMut(&mut std::collections::VecDeque<bool>) -> Result<(), Error>,
{
    let mut stats = RunStats {
        peak_stack_bits: config.stack_bits()?,
        ..RunStats::default()
    };
    if stats.peak_stack_bits > limits.max_stack_bits {
        return Err(Error::Capacity("initial bit-stack capacity".into()));
    }
    let mut live_bits = stats.peak_stack_bits;
    while let Some(pc) = config.pc {
        if stats.instructions >= limits.max_steps {
            return Err(Error::Capacity("BitProgram instruction limit".into()));
        }
        if pc >= label_count {
            return Err(Error::Invalid(format!(
                "configuration pc {pc} outside Fin {label_count}"
            )));
        }
        let instruction = instruction_at(pc)?;
        // A public callback can supply arbitrary instructions. Validate every
        // operand and *all* successor labels against the actual finite table
        // before indexing any stack or modifying the configuration.
        instruction.validate::<R, S>(label_count)?;
        // Compute all fallible scalar operations *before* mutating the
        // configuration. This makes arithmetic refusal atomic at the
        // instruction boundary, including an inconsistent cached counter.
        let next_live_bits =
            next_live_bit_count(&instruction, config, live_bits, limits.max_stack_bits)?;
        let next_instructions = stats.instructions.checked_add(1).ok_or(Error::Overflow)?;
        // A source Push can grow the host VecDeque even when the logical bit
        // limit admits it. Make this allocation fallible *before* any logical
        // state mutation. Rust's VecDeque::try_reserve(1) preserves contents
        // on failure and guarantees one insertion without further growth.
        if let Instr::Push { stack, .. } = &instruction {
            reserve_push(&mut config.stacks[*stack])?;
        }
        execute_instr(&instruction, config);
        live_bits = next_live_bits;
        stats.instructions = next_instructions;
        stats.peak_stack_bits = stats.peak_stack_bits.max(live_bits);
    }
    Ok(stats)
}

#[cfg(test)]
mod checked_counter_tests {
    use super::*;
    use std::collections::VecDeque;

    #[test]
    fn forced_host_refusal_does_not_commit_an_admitted_push() {
        let original = Config::<1, 1> {
            pc: Some(0),
            regs: [true],
            stacks: [VecDeque::new()],
        };
        let mut current = original.clone();
        let mut reserve_calls = 0;
        let mut fetch_calls = 0;
        let failure = run_with_instruction_at_and_reserve(
            &mut current,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 3,
            },
            1,
            |_| {
                fetch_calls += 1;
                Ok(Instr::Push {
                    stack: 0,
                    src: 0,
                    next: 0,
                })
            },
            |stack| {
                reserve_calls += 1;
                assert!(stack.is_empty());
                Err(Error::Capacity("injected host allocation refusal".into()))
            },
        );
        assert!(matches!(failure, Err(Error::Capacity(_))));
        assert_eq!(reserve_calls, 1);
        assert_eq!(fetch_calls, 1);
        assert_eq!(current, original, "no source step may be committed");
    }

    #[test]
    fn forced_host_refusal_preserves_a_committed_prefix_and_allows_resume() {
        let instruction_at = |pc| {
            Ok(match pc {
                0 => Instr::Push {
                    stack: 0,
                    src: 0,
                    next: 1,
                },
                1 => Instr::Push {
                    stack: 0,
                    src: 0,
                    next: 2,
                },
                2 => Instr::Halt,
                _ => panic!("callback received invalid label"),
            })
        };
        let mut current = Config::<1, 1> {
            pc: Some(0),
            regs: [true],
            stacks: [VecDeque::new()],
        };
        let mut calls = 0;
        let result = run_with_instruction_at_and_reserve(
            &mut current,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 2,
            },
            3,
            instruction_at,
            |stack| {
                calls += 1;
                if calls == 2 {
                    return Err(Error::Capacity("second push cannot allocate".into()));
                }
                stack
                    .try_reserve(1)
                    .map_err(|_| Error::Capacity("host stack allocation".into()))
            },
        );
        assert!(matches!(result, Err(Error::Capacity(_))));
        assert_eq!(calls, 2);
        assert_eq!(current.pc, Some(1));
        assert_eq!(
            current.stacks[0].iter().copied().collect::<Vec<_>>(),
            [true]
        );

        let remaining = run_with_instruction_at_and_reserve(
            &mut current,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 2,
            },
            3,
            instruction_at,
            |stack| {
                stack
                    .try_reserve(1)
                    .map_err(|_| Error::Capacity("host stack allocation".into()))
            },
        )
        .unwrap();
        assert_eq!(remaining.instructions, 2);
        assert_eq!(remaining.peak_stack_bits, 2);
        assert_eq!(current.pc, None);
        assert_eq!(
            current.stacks[0].iter().copied().collect::<Vec<_>>(),
            [true, true]
        );
    }

    #[test]
    fn failure_guards_precede_host_reservation() {
        let original = Config::<1, 1> {
            pc: Some(0),
            regs: [true],
            stacks: [VecDeque::from([false])],
        };
        let push = Instr::Push {
            stack: 0,
            src: 0,
            next: 0,
        };
        for (limits, label_count, instruction, invalid_label) in [
            (
                RunLimits {
                    max_steps: 3,
                    max_stack_bits: 0,
                },
                1,
                push.clone(),
                false,
            ),
            (
                RunLimits {
                    max_steps: 0,
                    max_stack_bits: 2,
                },
                1,
                push.clone(),
                false,
            ),
            (
                RunLimits {
                    max_steps: 3,
                    max_stack_bits: 1,
                },
                1,
                push.clone(),
                false,
            ),
            (
                RunLimits {
                    max_steps: 3,
                    max_stack_bits: 2,
                },
                0,
                push.clone(),
                true,
            ),
            (
                RunLimits {
                    max_steps: 3,
                    max_stack_bits: 2,
                },
                1,
                Instr::Push {
                    stack: 0,
                    src: 0,
                    next: 1,
                },
                true,
            ),
        ] {
            let mut config = original.clone();
            let result = run_with_instruction_at_and_reserve(
                &mut config,
                limits,
                label_count,
                |_| Ok(instruction.clone()),
                |_| panic!("a rejected instruction must not request host reservation"),
            );
            if invalid_label {
                assert!(matches!(result, Err(Error::Invalid(_))));
            } else {
                assert!(matches!(result, Err(Error::Capacity(_))));
            }
            assert_eq!(config, original);
        }
    }

    #[test]
    fn non_push_does_not_request_host_reservation() {
        let mut config = Config::<1, 1> {
            pc: Some(0),
            regs: [false],
            stacks: [VecDeque::new()],
        };
        let stats = run_with_instruction_at_and_reserve(
            &mut config,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 0,
            },
            1,
            |_| Ok(Instr::Halt),
            |_| panic!("Halt must never attempt host reservation"),
        )
        .unwrap();
        assert_eq!(stats.instructions, 1);
        assert_eq!(stats.peak_stack_bits, 0);
        assert_eq!(config.pc, None);
    }

    #[test]
    fn push_preflight_is_exact_up_to_machine_word_maximum() {
        let cfg = Config::<1, 1> {
            pc: Some(0),
            regs: [true],
            stacks: [VecDeque::new()],
        };
        let push = Instr::Push {
            stack: 0,
            src: 0,
            next: 0,
        };
        // All machine-word values are tested without allocating a giant stack.
        assert_eq!(
            next_live_bit_count(&push, &cfg, usize::MAX - 1, usize::MAX),
            Ok(usize::MAX)
        );
        assert!(matches!(
            next_live_bit_count(&push, &cfg, usize::MAX, usize::MAX),
            Err(Error::Capacity(_))
        ));
        assert!(matches!(
            next_live_bit_count(&push, &cfg, 0, 0),
            Err(Error::Capacity(_))
        ));
        assert_eq!(next_live_bit_count(&push, &cfg, 0, 1), Ok(1));
    }

    #[test]
    fn preflight_refusals_do_not_resize_or_mutate_native_stacks() {
        let initial = Config::<1, 1> {
            pc: Some(0),
            regs: [true],
            stacks: [VecDeque::new()],
        };
        let push = Instr::Push {
            stack: 0,
            src: 0,
            next: 0,
        };
        for limits in [
            RunLimits {
                max_steps: 3,
                max_stack_bits: 0,
            },
            RunLimits {
                max_steps: 0,
                max_stack_bits: 3,
            },
        ] {
            let mut config = initial.clone();
            let before_capacity = config.stacks[0].capacity();
            let result = run_with_instruction_at(&mut config, limits, 1, |_| Ok(push.clone()));
            assert!(matches!(result, Err(Error::Capacity(_))));
            assert_eq!(config, initial);
            assert_eq!(
                config.stacks[0].capacity(),
                before_capacity,
                "logical refusal must precede host storage reservation"
            );
        }

        let mut config = initial;
        let stats = run_with_instruction_at(
            &mut config,
            RunLimits {
                max_steps: u64::MAX,
                max_stack_bits: usize::MAX,
            },
            1,
            |_| Ok(Instr::Halt),
        )
        .unwrap();
        assert_eq!(stats.instructions, 1);
        assert_eq!(config.pc, None);
    }

    #[test]
    fn host_deque_reserve_failure_preserves_logical_contents() {
        let mut deque = VecDeque::from([true, false, true]);
        let before = deque.clone();
        // Deterministically exceeds the allocatable usize capacity,
        // without requesting an actual huge allocation.
        assert!(deque.try_reserve(usize::MAX).is_err());
        assert_eq!(deque, before);
    }

    #[test]
    fn nonempty_pop_and_empty_pop_preserve_checked_counter_contract() {
        let pop = Instr::Pop {
            stack: 0,
            value: 0,
            present: 0,
            next: 0,
        };
        let mut cfg = Config::<1, 1> {
            pc: Some(0),
            regs: [false],
            stacks: [VecDeque::new()],
        };
        let before = cfg.clone();
        assert_eq!(next_live_bit_count(&pop, &cfg, 0, 0), Ok(0));
        assert_eq!(cfg, before);
        cfg.stacks[0].push_front(true);
        let before = cfg.clone();
        assert_eq!(next_live_bit_count(&pop, &cfg, 1, 1), Ok(0));
        assert_eq!(
            next_live_bit_count(&pop, &cfg, usize::MAX, usize::MAX),
            Ok(usize::MAX - 1)
        );
        assert_eq!(
            next_live_bit_count(&pop, &cfg, 0, 1),
            Err(Error::Overflow),
            "corrupted cache must refuse instead of underflowing"
        );
        assert_eq!(cfg, before, "scalar refusal must not mutate any state");
    }
}

#[derive(Clone, Debug)]
enum BlockKind<const R: usize, const S: usize> {
    Skip,
    Atom(Atom),
    Call(Arc<DeferredProgram<R, S>>),
    Repeat {
        count: usize,
        body: Arc<Block<R, S>>,
    },
    Seq(Arc<Block<R, S>>, Arc<Block<R, S>>),
    If {
        test: usize,
        yes: Arc<Block<R, S>>,
        no: Arc<Block<R, S>>,
    },
    While {
        test: usize,
        body: Arc<Block<R, S>>,
    },
}

/// A source StructuredCalls command with cached physical site count. Arc nodes
/// retain shared subprograms and repeated subgraphs instead of duplicating code.
#[derive(Clone, Debug)]
pub struct Block<const R: usize, const S: usize> {
    size: usize,
    kind: BlockKind<R, S>,
}

impl<const R: usize, const S: usize> Block<R, S> {
    pub fn skip() -> Arc<Self> {
        Arc::new(Self {
            size: 0,
            kind: BlockKind::Skip,
        })
    }

    pub fn atom(atom: Atom) -> Result<Arc<Self>, Error> {
        // Check all register/stack addresses before any execution.
        atom.instr(0).validate::<R, S>(1)?;
        Ok(Arc::new(Self {
            size: 1,
            kind: BlockKind::Atom(atom),
        }))
    }

    pub fn call(program: Arc<DeferredProgram<R, S>>) -> Arc<Self> {
        Arc::new(Self {
            size: program.labels,
            kind: BlockKind::Call(program),
        })
    }

    /// Preserve n source sequential copies with one stored shared node.
    pub fn repeat(count: usize, body: Arc<Self>) -> Result<Arc<Self>, Error> {
        if count == 0 || body.size == 0 {
            return Ok(Self::skip());
        }
        if count == 1 {
            return Ok(body);
        }
        let size = count.checked_mul(body.size).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self {
            size,
            kind: BlockKind::Repeat { count, body },
        }))
    }

    pub fn seq(first: Arc<Self>, second: Arc<Self>) -> Result<Arc<Self>, Error> {
        let size = first.size.checked_add(second.size).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self {
            size,
            kind: BlockKind::Seq(first, second),
        }))
    }

    pub fn ite(test: usize, yes: Arc<Self>, no: Arc<Self>) -> Result<Arc<Self>, Error> {
        if test >= R {
            return Err(Error::Invalid(
                "deferred branch register outside Fin R".into(),
            ));
        }
        let size = yes
            .size
            .checked_add(no.size)
            .and_then(|n| n.checked_add(1))
            .ok_or(Error::Overflow)?;
        Ok(Arc::new(Self {
            size,
            kind: BlockKind::If { test, yes, no },
        }))
    }

    pub fn while_(test: usize, body: Arc<Self>) -> Result<Arc<Self>, Error> {
        if test >= R {
            return Err(Error::Invalid(
                "deferred while register outside Fin R".into(),
            ));
        }
        let size = body.size.checked_add(1).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self {
            size,
            kind: BlockKind::While { test, body },
        }))
    }

    pub fn size(&self) -> usize {
        self.size
    }

    fn entry_at(&self, base: usize, exit: usize) -> Result<usize, Error> {
        match &self.kind {
            BlockKind::Skip => Ok(exit),
            BlockKind::Atom(_) | BlockKind::If { .. } | BlockKind::While { .. } => Ok(base),
            BlockKind::Call(program) => base.checked_add(program.entry).ok_or(Error::Overflow),
            BlockKind::Repeat { count, body } => {
                if *count == 0 || body.size == 0 {
                    return Ok(exit);
                }
                // Any nonempty block enters at a source site, independent of its exit.
                let following = if *count > 1 {
                    let next_base = base.checked_add(body.size).ok_or(Error::Overflow)?;
                    body.entry_at(next_base, exit)?
                } else {
                    exit
                };
                body.entry_at(base, following)
            }
            BlockKind::Seq(first, second) => {
                let mid = base.checked_add(first.size).ok_or(Error::Overflow)?;
                first.entry_at(base, second.entry_at(mid, exit)?)
            }
        }
    }

    fn instruction_at(&self, base: usize, exit: usize, pc: usize) -> Result<Instr, Error> {
        let end = base.checked_add(self.size).ok_or(Error::Overflow)?;
        if !(base..end).contains(&pc) {
            return Err(Error::Invalid(
                "deferred physical site outside source block".into(),
            ));
        }
        match &self.kind {
            BlockKind::Skip => Err(Error::Invalid("empty block has no instruction".into())),
            BlockKind::Atom(atom) => Ok(atom.instr(exit)),
            BlockKind::Call(program) => {
                let original = program.instruction_at(pc - base)?;
                original.relocate(base, exit)
            }
            BlockKind::Repeat { count, body } => {
                let iteration = (pc - base) / body.size;
                if iteration >= *count {
                    return Err(Error::Invalid("repeat index outside source body".into()));
                }
                let offset = iteration.checked_mul(body.size).ok_or(Error::Overflow)?;
                let iteration_base = base.checked_add(offset).ok_or(Error::Overflow)?;
                let following = if iteration + 1 < *count {
                    let next_base = iteration_base
                        .checked_add(body.size)
                        .ok_or(Error::Overflow)?;
                    body.entry_at(next_base, exit)?
                } else {
                    exit
                };
                body.instruction_at(iteration_base, following, pc)
            }
            BlockKind::Seq(first, second) => {
                let mid = base.checked_add(first.size).ok_or(Error::Overflow)?;
                if pc < mid {
                    first.instruction_at(base, second.entry_at(mid, exit)?, pc)
                } else {
                    second.instruction_at(mid, exit, pc)
                }
            }
            BlockKind::If { test, yes, no } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                let second = first.checked_add(yes.size).ok_or(Error::Overflow)?;
                if pc == base {
                    Ok(Instr::Branch {
                        test: *test,
                        yes: yes.entry_at(first, exit)?,
                        no: no.entry_at(second, exit)?,
                    })
                } else if pc < second {
                    yes.instruction_at(first, exit, pc)
                } else {
                    no.instruction_at(second, exit, pc)
                }
            }
            BlockKind::While { test, body } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                if pc == base {
                    Ok(Instr::Branch {
                        test: *test,
                        yes: body.entry_at(first, base)?,
                        no: exit,
                    })
                } else {
                    body.instruction_at(first, base, pc)
                }
            }
        }
    }
}

#[cfg(test)]
mod linking_tests {
    use super::*;

    #[test]
    fn source_link_into_preserves_ports_and_all_physical_labels() {
        let p = DeferredProgram::table(
            Program::<1, 1>::new(
                0,
                0,
                1,
                vec![
                    Instr::Halt,
                    Instr::Set {
                        dst: 0,
                        value: true,
                        next: 0,
                    },
                ],
            )
            .unwrap(),
        );
        let q = DeferredProgram::table(
            Program::<1, 1>::new(
                0,
                0,
                1,
                vec![
                    Instr::Halt,
                    Instr::Not {
                        dst: 0,
                        src: 0,
                        next: 0,
                    },
                ],
            )
            .unwrap(),
        );
        let linked = DeferredProgram::<3, 2>::link_into(p, q, [2], [1], [2], [1]).unwrap();
        assert_eq!(linked.labels(), 4);
        assert_eq!(linked.entry(), 1);
        assert_eq!(linked.instruction_at(0).unwrap(), Instr::Goto { next: 3 });
        assert_eq!(
            linked.instruction_at(1).unwrap(),
            Instr::Set {
                dst: 2,
                value: true,
                next: 0
            }
        );
        assert_eq!(linked.instruction_at(2).unwrap(), Instr::Halt);
        assert_eq!(
            linked.instruction_at(3).unwrap(),
            Instr::Not {
                dst: 2,
                src: 2,
                next: 2
            }
        );
        let mut state = linked.initial([]);
        let stats = linked
            .run(
                &mut state,
                RunLimits {
                    max_steps: 10,
                    max_stack_bits: 10,
                },
            )
            .unwrap();
        assert_eq!(stats.instructions, 4);
        assert!(state.pc.is_none());
        assert!(!state.regs[2]);
    }

    #[test]
    fn lift_rejects_noninjective_and_out_of_range_maps() {
        let p = DeferredProgram::table(Program::<2, 1>::new(0, 0, 0, vec![Instr::Halt]).unwrap());
        assert!(DeferredProgram::<3, 2>::lift(p.clone(), [0, 0], [1]).is_err());
        assert!(DeferredProgram::<3, 2>::lift(p, [0, 3], [1]).is_err());
    }

    #[test]
    fn lift_does_not_flatten_large_original_composition() {
        let atom = Block::<1, 1>::atom(Atom::Not { dst: 0, src: 0 }).unwrap();
        let repeated = Block::repeat(1_000_000, atom).unwrap();
        let source = DeferredProgram::<1, 1>::composed(0, 0, repeated).unwrap();
        let lifted = DeferredProgram::<3, 2>::lift(source, [2], [1]).unwrap();
        assert_eq!(lifted.labels(), 1_000_001);
        assert_eq!(
            lifted.instruction_at(500_000).unwrap(),
            Instr::Not {
                dst: 2,
                src: 2,
                next: 500_001
            }
        );
        assert_eq!(
            lifted.instruction_at(1_000_000).unwrap(),
            Instr::Not {
                dst: 2,
                src: 2,
                next: 0
            }
        );
        assert_eq!(lifted.instruction_at(0).unwrap(), Instr::Halt);
    }
}
