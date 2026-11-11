//! Source-instruction port of the *pruned pair DFS controller*.
//!
//! `openai/math@4eaee87548250b2682affda7d05d947c05554bae`,
//! `SqrtLogSpace/DifferencePairsProgram.lean` lines 15–120.
//!
//! This command streams each admissible pair `(E,U)` with `U ⊆ E` and
//! `|E| < J` in the original source order. The callback is a **physical
//! structured command** invoked once at each leaf, not a Rust host closure
//! and not an enumeration of a precomputed pair list. The caller is
//! responsible for the callback's input/output contract and for supplying
//! unary depth/budget stacks. This module does not implement the signed
//! matrix arithmetic in the full query callback.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::clear_program;
use crate::native_pair_setup::expand_caller_command;

/// Injective maps of the four persistent DFS stacks and five registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PairPorts<const R: usize, const S: usize> {
    registers: [usize; 5],
    stacks: [usize; 4],
}

impl<const R: usize, const S: usize> PairPorts<R, S> {
    pub fn new(registers: [usize; 5], stacks: [usize; 4]) -> Result<Self, Error> {
        let unique = |xs: &[usize], bound: usize| {
            xs.iter()
                .enumerate()
                .all(|(i, x)| *x < bound && xs[..i].iter().all(|prev| prev != x))
        };
        if !unique(&registers, R) || !unique(&stacks, S) {
            return Err(Error::Invalid(
                "pair ports must be injective and in range".into(),
            ));
        }
        Ok(Self { registers, stacks })
    }

    pub fn registers(&self) -> [usize; 5] {
        self.registers
    }
    pub fn stacks(&self) -> [usize; 4] {
        self.stacks
    }

    fn set(&self, i: usize, value: bool) -> Cmd<R, S> {
        Cmd::Atom(Atom::Set {
            dst: self.registers[i],
            value,
        })
    }
    fn push(&self, stack: usize, value: bool) -> Cmd<R, S> {
        Cmd::seq(
            self.set(2, value),
            Cmd::Atom(Atom::Push {
                stack: self.stacks[stack],
                src: self.registers[2],
            }),
        )
    }
    fn pop(&self, stack: usize, value: usize) -> Cmd<R, S> {
        Cmd::Atom(Atom::Pop {
            stack: self.stacks[stack],
            value: self.registers[value],
            present: self.registers[3],
        })
    }
    fn peek(&self, stack: usize, value: usize) -> Cmd<R, S> {
        Cmd::Atom(Atom::Peek {
            stack: self.stacks[stack],
            value: self.registers[value],
            present: self.registers[3],
        })
    }
    fn choice(&self, test: usize, yes: Cmd<R, S>, no: Cmd<R, S>) -> Cmd<R, S> {
        Cmd::ite(self.registers[test], yes, no)
    }
    fn enter(&self, e: bool, u: bool) -> Cmd<R, S> {
        Cmd::seq(
            self.push(2, e),
            Cmd::seq(self.push(3, u), self.set(0, true)),
        )
    }
    fn finish_level(&self) -> Cmd<R, S> {
        self.push(0, true)
    }
    fn next_outside(&self) -> Cmd<R, S> {
        Cmd::seq(
            self.pop(1, 2),
            Cmd::seq(
                self.peek(1, 2),
                self.choice(
                    3,
                    self.enter(true, false),
                    Cmd::seq(self.push(1, true), self.finish_level()),
                ),
            ),
        )
    }
    fn backtrack(&self) -> Cmd<R, S> {
        Cmd::seq(
            self.pop(2, 4),
            self.choice(
                3,
                Cmd::seq(
                    self.pop(3, 2),
                    self.choice(
                        4,
                        self.choice(
                            2,
                            Cmd::seq(self.push(1, true), self.finish_level()),
                            self.enter(true, true),
                        ),
                        self.next_outside(),
                    ),
                ),
                self.set(1, false),
            ),
        )
    }
    fn descend(&self, callback: Cmd<R, S>) -> Cmd<R, S> {
        Cmd::seq(
            self.pop(0, 2),
            self.choice(
                3,
                self.enter(false, false),
                Cmd::seq(callback, Cmd::seq(self.set(0, false), self.set(1, true))),
            ),
        )
    }

    /// Exact source `DifferencePairsProgram.command p callback`.
    /// On each callback the outer and inner masks are on stacks 2/3 in
    /// reverse coordinate order, as required by `PairNativeSetup.expandCaller`.
    pub fn command(&self, callback: Cmd<R, S>) -> Cmd<R, S> {
        let init = Cmd::seq(
            self.peek(1, 2),
            Cmd::seq(
                Cmd::Atom(Atom::Copy {
                    dst: self.registers[1],
                    src: self.registers[3],
                }),
                self.set(0, true),
            ),
        );
        let body = self.choice(0, self.descend(callback), self.backtrack());
        Cmd::seq(init, Cmd::while_(self.registers[1], body))
    }

    pub fn program(&self, callback: Cmd<R, S>) -> Result<Program<R, S>, Error> {
        self.command(callback)
            .compiled(self.stacks[0], self.stacks[2])
    }
}

/// `QueryStreamProgram.pairPorts`: regs 0–4 (`Fin.castAddEmb 35`), stacks 832–835.
pub fn query_pair_ports() -> PairPorts<40, 896> {
    PairPorts::new([0, 1, 2, 3, 4], [832, 833, 834, 835])
        .expect("source-defined pair ports are injective")
}

/// The complete source DFS *control*, with the supplied physical callback.
/// `QueryStreamProgram.pairCallback` is not yet fully ported.
pub fn query_pairs_command(callback: Cmd<40, 896>) -> Cmd<40, 896> {
    query_pair_ports().command(callback)
}

pub fn query_pairs_program(callback: Cmd<40, 896>) -> Result<Program<40, 896>, Error> {
    query_pair_ports().program(callback)
}

/// `QueryExecution.PairStart.command`: clear the pair dictionary (stack 851)
/// and physically expand both caller pair masks through `PairNativeSetup`.
pub fn pair_start_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(clear_program(851, 0, 1)?),
        expand_caller_command()?,
    ))
}

/// Composed physical pair traversal with the real source PairStart prefix,
/// followed by a supplied downstream tuple visitor. **Not yet** the complete
/// `QueryStreamProgram.pairCallback`, which still requires the signature
/// tuple, signed accumulation, and reconstruction stages.
pub fn query_pairs_with_pair_start(after_pair_start: Cmd<40, 896>) -> Result<Cmd<40, 896>, Error> {
    Ok(query_pairs_command(Cmd::seq(
        pair_start_command()?,
        after_pair_start,
    )))
}
