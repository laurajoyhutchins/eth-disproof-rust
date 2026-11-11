//! On-demand physical instruction view for shared Lean program composition.
//!
//! This is a prototype backend for a future Lean-elaborated structural IR.
//! No constructor silently replaces physical source steps with semantic #SAT
//! operations. In particular a Call keeps the callee's complete label space:
//! its halt becomes a jump to the caller continuation.

use std::sync::Arc;

use super::{Atom, Config, Instr, Program, RunLimits, RunStats, execute_instr};
use crate::Error;

#[derive(Clone, Debug)]
enum Body<const R: usize, const S: usize> {
    Table(Program<R, S>),
    Composed(Arc<Block<R, S>>),
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
            return Err(Error::Invalid("deferred program entry outside labels".into()));
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
            Body::Composed(_) if pc == 0 => Ok(Instr::Halt),
            Body::Composed(block) => block.instruction_at(1, 0, pc),
        }
    }

    /// Construct the ordinary Program only when its size is explicitly budgeted.
    /// Used for differential testing, not for large production graphs.
    pub fn materialize(&self, max_labels: usize) -> Result<Program<R, S>, Error> {
        if self.labels > max_labels {
            return Err(Error::Capacity("deferred materialization label budget".into()));
        }
        let instructions = (0..self.labels)
            .map(|pc| self.instruction_at(pc))
            .collect::<Result<Vec<_>, _>>()?;
        Program::new(self.input_stack, self.output_stack, self.entry, instructions)
    }

    /// Execute one original physical BitProgram step, not one AST node.
    pub fn step(&self, config: &mut Config<R, S>) -> Result<bool, Error> {
        let Some(pc) = config.pc else { return Ok(false) };
        let instruction = self.instruction_at(pc)?;
        execute_instr(&instruction, config);
        Ok(true)
    }

    /// Physically faithful bounded execution, without a flat instruction table.
    /// The reported count is source BitProgram steps, not TM2 microsteps.
    pub fn run(&self, config: &mut Config<R, S>, limits: RunLimits) -> Result<RunStats, Error> {
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
            let instruction = self.instruction_at(pc)?;
            match instruction {
                Instr::Push { .. } => {
                    if live_bits >= limits.max_stack_bits {
                        return Err(Error::Capacity("BitProgram stack-bit limit".into()));
                    }
                    live_bits = live_bits.checked_add(1).ok_or(Error::Overflow)?;
                }
                Instr::Pop { stack, .. } if !config.stacks[stack].is_empty() => {
                    live_bits -= 1;
                }
                _ => {}
            }
            execute_instr(&instruction, config);
            stats.instructions += 1;
            stats.peak_stack_bits = stats.peak_stack_bits.max(live_bits);
        }
        Ok(stats)
    }
}

#[derive(Clone, Debug)]
enum BlockKind<const R: usize, const S: usize> {
    Skip,
    Atom(Atom),
    Call(Arc<DeferredProgram<R, S>>),
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
        Arc::new(Self { size: 0, kind: BlockKind::Skip })
    }

    pub fn atom(atom: Atom) -> Result<Arc<Self>, Error> {
        // Check all register/stack addresses before any execution.
        atom.instr(0).validate::<R, S>(1)?;
        Ok(Arc::new(Self { size: 1, kind: BlockKind::Atom(atom) }))
    }

    pub fn call(program: Arc<DeferredProgram<R, S>>) -> Arc<Self> {
        Arc::new(Self {
            size: program.labels,
            kind: BlockKind::Call(program),
        })
    }

    pub fn seq(first: Arc<Self>, second: Arc<Self>) -> Result<Arc<Self>, Error> {
        let size = first.size.checked_add(second.size).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self { size, kind: BlockKind::Seq(first, second) }))
    }

    pub fn ite(test: usize, yes: Arc<Self>, no: Arc<Self>) -> Result<Arc<Self>, Error> {
        if test >= R {
            return Err(Error::Invalid("deferred branch register outside Fin R".into()));
        }
        let size = yes.size.checked_add(no.size)
            .and_then(|n| n.checked_add(1)).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self { size, kind: BlockKind::If { test, yes, no } }))
    }

    pub fn while_(test: usize, body: Arc<Self>) -> Result<Arc<Self>, Error> {
        if test >= R {
            return Err(Error::Invalid("deferred while register outside Fin R".into()));
        }
        let size = body.size.checked_add(1).ok_or(Error::Overflow)?;
        Ok(Arc::new(Self { size, kind: BlockKind::While { test, body } }))
    }

    pub fn size(&self) -> usize {
        self.size
    }

    fn entry_at(&self, base: usize, exit: usize) -> Result<usize, Error> {
        match &self.kind {
            BlockKind::Skip => Ok(exit),
            BlockKind::Atom(_) | BlockKind::If { .. } | BlockKind::While { .. } => Ok(base),
            BlockKind::Call(program) => base.checked_add(program.entry).ok_or(Error::Overflow),
            BlockKind::Seq(first, second) => {
                let mid = base.checked_add(first.size).ok_or(Error::Overflow)?;
                first.entry_at(base, second.entry_at(mid, exit)?)
            }
        }
    }

    fn instruction_at(&self, base: usize, exit: usize, pc: usize) -> Result<Instr, Error> {
        let end = base.checked_add(self.size).ok_or(Error::Overflow)?;
        if !(base..end).contains(&pc) {
            return Err(Error::Invalid("deferred physical site outside source block".into()));
        }
        match &self.kind {
            BlockKind::Skip => Err(Error::Invalid("empty block has no instruction".into())),
            BlockKind::Atom(atom) => Ok(atom.instr(exit)),
            BlockKind::Call(program) => {
                let original = program.instruction_at(pc - base)?;
                original.relocate(base, exit)
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
