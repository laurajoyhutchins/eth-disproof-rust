//! Exact source-instruction semantics from upstream `BitProgram.lean`, plus
//! `StructuredProgram` / `StructuredCalls` finite-table compilation.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Every instruction changes at most one stack. This is NOT the TM2 microstep
//! implementation or its tape-space accounting from `BitProgramCompile.lean`.

use std::array;
use std::collections::VecDeque;

use crate::Error;

/// An instruction of `BitProgram.Instr`. All indexes are validated when a
/// program is created, corresponding to Lean's `Fin` index types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Halt,
    Goto {
        next: usize,
    },
    Set {
        dst: usize,
        value: bool,
        next: usize,
    },
    Copy {
        dst: usize,
        src: usize,
        next: usize,
    },
    Not {
        dst: usize,
        src: usize,
        next: usize,
    },
    And {
        dst: usize,
        left: usize,
        right: usize,
        next: usize,
    },
    Or {
        dst: usize,
        left: usize,
        right: usize,
        next: usize,
    },
    Xor {
        dst: usize,
        left: usize,
        right: usize,
        next: usize,
    },
    Branch {
        test: usize,
        yes: usize,
        no: usize,
    },
    Push {
        stack: usize,
        src: usize,
        next: usize,
    },
    Peek {
        stack: usize,
        value: usize,
        present: usize,
        next: usize,
    },
    Pop {
        stack: usize,
        value: usize,
        present: usize,
        next: usize,
    },
}

impl Instr {
    /// `ProgramLinking.relocateInstr` with identity register/stack maps.
    /// A subroutine's halt becomes a jump to the caller's continuation.
    fn relocate(&self, base: usize, return_to: usize) -> Result<Self, Error> {
        let offset = |label: usize| label.checked_add(base).ok_or(Error::Overflow);
        Ok(match *self {
            Self::Halt => Self::Goto { next: return_to },
            Self::Goto { next } => Self::Goto {
                next: offset(next)?,
            },
            Self::Set { dst, value, next } => Self::Set {
                dst,
                value,
                next: offset(next)?,
            },
            Self::Copy { dst, src, next } => Self::Copy {
                dst,
                src,
                next: offset(next)?,
            },
            Self::Not { dst, src, next } => Self::Not {
                dst,
                src,
                next: offset(next)?,
            },
            Self::And {
                dst,
                left,
                right,
                next,
            } => Self::And {
                dst,
                left,
                right,
                next: offset(next)?,
            },
            Self::Or {
                dst,
                left,
                right,
                next,
            } => Self::Or {
                dst,
                left,
                right,
                next: offset(next)?,
            },
            Self::Xor {
                dst,
                left,
                right,
                next,
            } => Self::Xor {
                dst,
                left,
                right,
                next: offset(next)?,
            },
            Self::Branch { test, yes, no } => Self::Branch {
                test,
                yes: offset(yes)?,
                no: offset(no)?,
            },
            Self::Push { stack, src, next } => Self::Push {
                stack,
                src,
                next: offset(next)?,
            },
            Self::Peek {
                stack,
                value,
                present,
                next,
            } => Self::Peek {
                stack,
                value,
                present,
                next: offset(next)?,
            },
            Self::Pop {
                stack,
                value,
                present,
                next,
            } => Self::Pop {
                stack,
                value,
                present,
                next: offset(next)?,
            },
        })
    }

    fn validate<const R: usize, const S: usize>(&self, labels: usize) -> Result<(), Error> {
        let reg = |i: usize| {
            if i < R {
                Ok(())
            } else {
                Err(Error::Invalid(format!("register {i} outside Fin {R}")))
            }
        };
        let stack = |i: usize| {
            if i < S {
                Ok(())
            } else {
                Err(Error::Invalid(format!("stack {i} outside Fin {S}")))
            }
        };
        let label = |i: usize| {
            if i < labels {
                Ok(())
            } else {
                Err(Error::Invalid(format!("label {i} outside Fin {labels}")))
            }
        };
        match *self {
            Self::Halt => Ok(()),
            Self::Goto { next } => label(next),
            Self::Set { dst, next, .. } => {
                reg(dst)?;
                label(next)
            }
            Self::Copy { dst, src, next } | Self::Not { dst, src, next } => {
                reg(dst)?;
                reg(src)?;
                label(next)
            }
            Self::And {
                dst,
                left,
                right,
                next,
            }
            | Self::Or {
                dst,
                left,
                right,
                next,
            }
            | Self::Xor {
                dst,
                left,
                right,
                next,
            } => {
                reg(dst)?;
                reg(left)?;
                reg(right)?;
                label(next)
            }
            Self::Branch { test, yes, no } => {
                reg(test)?;
                label(yes)?;
                label(no)
            }
            Self::Push {
                stack: s,
                src,
                next,
            } => {
                stack(s)?;
                reg(src)?;
                label(next)
            }
            Self::Peek {
                stack: s,
                value,
                present,
                next,
            }
            | Self::Pop {
                stack: s,
                value,
                present,
                next,
            } => {
                stack(s)?;
                reg(value)?;
                reg(present)?;
                label(next)
            }
        }
    }
}

/// `BitProgram.Program r s l`, with the finite label type represented by the
/// length of an immutable instruction table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program<const R: usize, const S: usize> {
    input_stack: usize,
    output_stack: usize,
    entry: usize,
    code: Vec<Instr>,
}

impl<const R: usize, const S: usize> Program<R, S> {
    pub fn new(
        input_stack: usize,
        output_stack: usize,
        entry: usize,
        code: Vec<Instr>,
    ) -> Result<Self, Error> {
        if input_stack >= S || output_stack >= S || entry >= code.len() {
            return Err(Error::Invalid(
                "program's input/output port or entry label is out of range".into(),
            ));
        }
        for instr in &code {
            instr.validate::<R, S>(code.len())?;
        }
        Ok(Self {
            input_stack,
            output_stack,
            entry,
            code,
        })
    }
    pub fn code(&self) -> &[Instr] {
        &self.code
    }
    pub fn entry(&self) -> usize {
        self.entry
    }
    pub fn input_stack(&self) -> usize {
        self.input_stack
    }
    pub fn output_stack(&self) -> usize {
        self.output_stack
    }

    /// Lift a concrete finite instruction table through injective register
    /// and stack maps, as in `ProgramLinking.liftProgram`.
    ///
    /// The source label set and step count remain unchanged. In particular,
    /// this is *not* a runtime interpreter of port mappings: instructions
    /// retain their physical mapped register/stack addresses after lifting.
    pub fn lift<const RR: usize, const SS: usize>(
        &self,
        registers: [usize; R],
        stacks: [usize; S],
    ) -> Result<Program<RR, SS>, Error> {
        let unique = |items: &[usize], upper: usize| {
            items.iter().all(|&i| i < upper)
                && items
                    .iter()
                    .enumerate()
                    .all(|(i, x)| !items[i + 1..].contains(x))
        };
        if !unique(&registers, RR) || !unique(&stacks, SS) {
            return Err(Error::Invalid(
                "lift requires injective in-range register/stack maps".into(),
            ));
        }
        let reg = |i: usize| registers[i];
        let stack = |i: usize| stacks[i];
        let code = self
            .code
            .iter()
            .map(|instr| match *instr {
                Instr::Halt => Instr::Halt,
                Instr::Goto { next } => Instr::Goto { next },
                Instr::Set { dst, value, next } => Instr::Set {
                    dst: reg(dst),
                    value,
                    next,
                },
                Instr::Copy { dst, src, next } => Instr::Copy {
                    dst: reg(dst),
                    src: reg(src),
                    next,
                },
                Instr::Not { dst, src, next } => Instr::Not {
                    dst: reg(dst),
                    src: reg(src),
                    next,
                },
                Instr::And {
                    dst,
                    left,
                    right,
                    next,
                } => Instr::And {
                    dst: reg(dst),
                    left: reg(left),
                    right: reg(right),
                    next,
                },
                Instr::Or {
                    dst,
                    left,
                    right,
                    next,
                } => Instr::Or {
                    dst: reg(dst),
                    left: reg(left),
                    right: reg(right),
                    next,
                },
                Instr::Xor {
                    dst,
                    left,
                    right,
                    next,
                } => Instr::Xor {
                    dst: reg(dst),
                    left: reg(left),
                    right: reg(right),
                    next,
                },
                Instr::Branch { test, yes, no } => Instr::Branch {
                    test: reg(test),
                    yes,
                    no,
                },
                Instr::Push {
                    stack: port,
                    src,
                    next,
                } => Instr::Push {
                    stack: stack(port),
                    src: reg(src),
                    next,
                },
                Instr::Peek {
                    stack: port,
                    value,
                    present,
                    next,
                } => Instr::Peek {
                    stack: stack(port),
                    value: reg(value),
                    present: reg(present),
                    next,
                },
                Instr::Pop {
                    stack: port,
                    value,
                    present,
                    next,
                } => Instr::Pop {
                    stack: stack(port),
                    value: reg(value),
                    present: reg(present),
                    next,
                },
            })
            .collect();
        Program::new(
            stack(self.input_stack),
            stack(self.output_stack),
            self.entry,
            code,
        )
    }

    /// `BitProgram.initial`: the input is a list with its first bit at top.
    pub fn initial(&self, input: impl IntoIterator<Item = bool>) -> Config<R, S> {
        let mut config = Config {
            pc: Some(self.entry),
            regs: [false; R],
            stacks: array::from_fn(|_| VecDeque::new()),
        };
        config.stacks[self.input_stack].extend(input);
        config
    }

    pub fn is_canonical_terminal(&self, config: &Config<R, S>, output: &[bool]) -> bool {
        config.pc.is_none()
            && config.regs.iter().all(|bit| !bit)
            && config.stacks.iter().enumerate().all(|(i, stack)| {
                if i == self.output_stack {
                    stack.iter().copied().eq(output.iter().copied())
                } else {
                    stack.is_empty()
                }
            })
    }

    /// Exactly one source instruction, `BitProgram.step`, returning `false`
    /// only when the configuration has already halted.
    pub fn step(&self, config: &mut Config<R, S>) -> Result<bool, Error> {
        let Some(pc) = config.pc else {
            return Ok(false);
        };
        let instr = self.code.get(pc).ok_or_else(|| {
            Error::Invalid(format!(
                "configuration pc {pc} outside Fin {}",
                self.code.len()
            ))
        })?;
        match *instr {
            Instr::Halt => config.pc = None,
            Instr::Goto { next } => config.pc = Some(next),
            Instr::Set { dst, value, next } => {
                config.regs[dst] = value;
                config.pc = Some(next)
            }
            Instr::Copy { dst, src, next } => {
                config.regs[dst] = config.regs[src];
                config.pc = Some(next)
            }
            Instr::Not { dst, src, next } => {
                config.regs[dst] = !config.regs[src];
                config.pc = Some(next)
            }
            Instr::And {
                dst,
                left,
                right,
                next,
            } => {
                config.regs[dst] = config.regs[left] && config.regs[right];
                config.pc = Some(next)
            }
            Instr::Or {
                dst,
                left,
                right,
                next,
            } => {
                config.regs[dst] = config.regs[left] || config.regs[right];
                config.pc = Some(next)
            }
            Instr::Xor {
                dst,
                left,
                right,
                next,
            } => {
                config.regs[dst] = config.regs[left] ^ config.regs[right];
                config.pc = Some(next)
            }
            Instr::Branch { test, yes, no } => {
                config.pc = Some(if config.regs[test] { yes } else { no })
            }
            Instr::Push { stack, src, next } => {
                config.stacks[stack].push_front(config.regs[src]);
                config.pc = Some(next)
            }
            Instr::Peek {
                stack,
                value,
                present,
                next,
            } => {
                read_registers(
                    &mut config.regs,
                    value,
                    present,
                    config.stacks[stack].front().copied(),
                );
                config.pc = Some(next);
            }
            Instr::Pop {
                stack,
                value,
                present,
                next,
            } => {
                let top = config.stacks[stack].pop_front();
                read_registers(&mut config.regs, value, present, top);
                config.pc = Some(next);
            }
        }
        Ok(true)
    }

    /// Refuses before a step that would exceed either limit; never returns an
    /// incomplete execution as a completed answer. Counts *source instructions*,
    /// not primitive TM2 microsteps or heap memory.
    pub fn run(&self, config: &mut Config<R, S>, limits: RunLimits) -> Result<RunStats, Error> {
        let mut stats = RunStats {
            peak_stack_bits: config.stack_bits()?,
            ..RunStats::default()
        };
        if stats.peak_stack_bits > limits.max_stack_bits {
            return Err(Error::Capacity("initial bit-stack capacity".into()));
        }
        // Maintain exact live stack cells incrementally. Re-scanning every
        // stack after each instruction would add an O(S) interpreter tax to
        // Lean's O(1)-stack-operation source machine.
        let mut live_bits = stats.peak_stack_bits;
        while let Some(pc) = config.pc {
            if stats.instructions >= limits.max_steps {
                return Err(Error::Capacity("BitProgram instruction limit".into()));
            }
            let instruction = self.code.get(pc).ok_or_else(|| {
                Error::Invalid(format!(
                    "configuration pc {pc} outside Fin {}",
                    self.code.len()
                ))
            })?;
            match *instruction {
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
            self.step(config)?;
            stats.instructions += 1;
            stats.peak_stack_bits = stats.peak_stack_bits.max(live_bits);
        }
        Ok(stats)
    }
}

/// `BitProgram.readRegs`. The second update overrides the first when the
/// `value` and `present` register indices coincide.
fn read_registers<const R: usize>(
    regs: &mut [bool; R],
    value: usize,
    present: usize,
    top: Option<bool>,
) {
    regs[value] = top.unwrap_or(false);
    regs[present] = top.is_some();
}

/// Direct correspondence to `BitProgram.Cfg`; only Finite program *labels*
/// may appear, and all stack/list tops are at index zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config<const R: usize, const S: usize> {
    pub pc: Option<usize>,
    pub regs: [bool; R],
    pub stacks: [VecDeque<bool>; S],
}
impl<const R: usize, const S: usize> Config<R, S> {
    pub fn stack_bits(&self) -> Result<usize, Error> {
        self.stacks
            .iter()
            .try_fold(0usize, |a, b| a.checked_add(b.len()).ok_or(Error::Overflow))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunLimits {
    pub max_steps: u64,
    pub max_stack_bits: usize,
}
impl Default for RunLimits {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_stack_bits: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RunStats {
    pub instructions: u64,
    pub peak_stack_bits: usize,
}

/// Atom syntax from `StructuredProgram.Atom` (continuation omitted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    Set {
        dst: usize,
        value: bool,
    },
    Copy {
        dst: usize,
        src: usize,
    },
    Not {
        dst: usize,
        src: usize,
    },
    And {
        dst: usize,
        left: usize,
        right: usize,
    },
    Or {
        dst: usize,
        left: usize,
        right: usize,
    },
    Xor {
        dst: usize,
        left: usize,
        right: usize,
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
impl Atom {
    fn instr(&self, next: usize) -> Instr {
        match *self {
            Self::Set { dst, value } => Instr::Set { dst, value, next },
            Self::Copy { dst, src } => Instr::Copy { dst, src, next },
            Self::Not { dst, src } => Instr::Not { dst, src, next },
            Self::And { dst, left, right } => Instr::And {
                dst,
                left,
                right,
                next,
            },
            Self::Or { dst, left, right } => Instr::Or {
                dst,
                left,
                right,
                next,
            },
            Self::Xor { dst, left, right } => Instr::Xor {
                dst,
                left,
                right,
                next,
            },
            Self::Push { stack, src } => Instr::Push { stack, src, next },
            Self::Peek {
                stack,
                value,
                present,
            } => Instr::Peek {
                stack,
                value,
                present,
                next,
            },
            Self::Pop {
                stack,
                value,
                present,
            } => Instr::Pop {
                stack,
                value,
                present,
                next,
            },
        }
    }
}

/// `StructuredCalls.Cmd`, with `StructuredProgram.Cmd` embedded as the subset
/// without `Call`. Unlike a dynamic call, `Call` is expanded into a fixed
/// relocated instruction table at compilation time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cmd<const R: usize, const S: usize> {
    Skip,
    Atom(Atom),
    Call(Program<R, S>),
    Seq(Box<Self>, Box<Self>),
    If {
        test: usize,
        yes: Box<Self>,
        no: Box<Self>,
    },
    While {
        test: usize,
        body: Box<Self>,
    },
}
impl<const R: usize, const S: usize> Cmd<R, S> {
    pub fn seq(first: Self, second: Self) -> Self {
        Self::Seq(Box::new(first), Box::new(second))
    }
    pub fn ite(test: usize, yes: Self, no: Self) -> Self {
        Self::If {
            test,
            yes: Box::new(yes),
            no: Box::new(no),
        }
    }
    pub fn while_(test: usize, body: Self) -> Self {
        Self::While {
            test,
            body: Box::new(body),
        }
    }

    /// `StructuredCalls.size`, used to allocate exactly `size + 1` labels.
    pub fn size(&self) -> Result<usize, Error> {
        match self {
            Self::Skip => Ok(0),
            Self::Atom(_) => Ok(1),
            Self::Call(p) => Ok(p.code.len()),
            Self::Seq(a, b) => a.size()?.checked_add(b.size()?).ok_or(Error::Overflow),
            Self::If { yes, no, .. } => yes
                .size()?
                .checked_add(no.size()?)
                .and_then(|n| n.checked_add(1))
                .ok_or(Error::Overflow),
            Self::While { body, .. } => body.size()?.checked_add(1).ok_or(Error::Overflow),
        }
    }

    fn entry_at(&self, base: usize, exit: usize) -> Result<usize, Error> {
        match self {
            Self::Skip => Ok(exit),
            Self::Atom(_) | Self::If { .. } | Self::While { .. } => Ok(base),
            Self::Call(p) => base.checked_add(p.entry).ok_or(Error::Overflow),
            Self::Seq(a, b) => {
                let mid = base.checked_add(a.size()?).ok_or(Error::Overflow)?;
                a.entry_at(base, b.entry_at(mid, exit)?)
            }
        }
    }

    fn emit(&self, base: usize, exit: usize, code: &mut [Instr]) -> Result<(), Error> {
        match self {
            Self::Skip => Ok(()),
            Self::Atom(a) => {
                code[base] = a.instr(exit);
                Ok(())
            }
            Self::Call(p) => {
                for (i, instruction) in p.code.iter().enumerate() {
                    code[base + i] = instruction.relocate(base, exit)?;
                }
                Ok(())
            }
            Self::Seq(a, b) => {
                let mid = base.checked_add(a.size()?).ok_or(Error::Overflow)?;
                a.emit(base, b.entry_at(mid, exit)?, code)?;
                b.emit(mid, exit, code)
            }
            Self::If { test, yes, no } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                let second = first.checked_add(yes.size()?).ok_or(Error::Overflow)?;
                code[base] = Instr::Branch {
                    test: *test,
                    yes: yes.entry_at(first, exit)?,
                    no: no.entry_at(second, exit)?,
                };
                yes.emit(first, exit, code)?;
                no.emit(second, exit, code)
            }
            Self::While { test, body } => {
                let first = base.checked_add(1).ok_or(Error::Overflow)?;
                code[base] = Instr::Branch {
                    test: *test,
                    yes: body.entry_at(first, base)?,
                    no: exit,
                };
                body.emit(first, base, code)
            }
        }
    }

    /// Fully compiled `BitProgram.Program`, with the additional terminal
    /// `halt` instruction and no runtime call stack.
    pub fn compiled(
        &self,
        input_stack: usize,
        output_stack: usize,
    ) -> Result<Program<R, S>, Error> {
        let size = self.size()?;
        // Original StructuredCalls.compiled uses
        // (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm.
        // The outer None (halt/exit) is physical label 0; each real
        // instruction occupies 1..=size. Our previous 0..size-1 layout
        // was behaviorally equivalent but NOT an exact source-state port.
        //
        // Embed at label 1 and route the command exit to label 0.
        // Direct Program::new imports retain their source-given labels.
        let code_len = size.checked_add(1).ok_or(Error::Overflow)?;
        let mut code = vec![Instr::Halt; code_len];
        self.emit(1, 0, &mut code)?;
        Program::new(input_stack, output_stack, self.entry_at(1, 0)?, code)
    }
}
