//! Source-defined attained-signature tuple controller and physical level initializer.
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Files: SqrtLogSpace/SignatureTupleProgram.lean and SignatureTupleNative.lean.
//!
//! The full native Routines remain unported. This module never substitutes a
//! semantic tuple enumerator or claims the complete QueryStreamProgram runs.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Program};
use crate::native_high::copy_program;

/// Exact source ABI: tuple stacks 836..847 and controller registers
/// active=36, leaf=37, available=38, fresh=39.
pub const TUPLE_STACKS: [usize; 12] = [836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847];
pub const CONTROLLER_REGISTERS: [usize; 4] = [36, 37, 38, 39];

/// Source SignatureTupleProgram.Routines. Each member is an actual finite
/// machine command, never a Rust closure or semantic evaluator.
#[derive(Clone, Debug)]
pub struct TupleRoutines<const R: usize, const S: usize> {
    pub setup: Cmd<R, S>,
    pub probe: Cmd<R, S>,
    pub descend: Cmd<R, S>,
    pub advance: Cmd<R, S>,
    pub ascend: Cmd<R, S>,
    pub visit: Cmd<R, S>,
}

/// Source SignatureTupleProgram.Ports. Lean does not require generic
/// injectivity; the concrete ABI uses disjoint registers 36..39.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TuplePorts<const R: usize> {
    pub active: usize,
    pub leaf: usize,
    pub available: usize,
    pub fresh: usize,
}

impl<const R: usize> TuplePorts<R> {
    pub fn new(active: usize, leaf: usize, available: usize, fresh: usize) -> Result<Self, Error> {
        if [active, leaf, available, fresh].iter().any(|&i| i >= R) {
            return Err(Error::Invalid(
                "signature tuple controller register outside machine".into(),
            ));
        }
        Ok(Self {
            active,
            leaf,
            available,
            fresh,
        })
    }

    /// Literal source body: leaf visit/ascend; otherwise probe and branch on
    /// available/fresh, invoking exactly one of descend/advance/ascend.
    pub fn body<const S: usize>(&self, q: &TupleRoutines<R, S>) -> Cmd<R, S> {
        Cmd::ite(
            self.leaf,
            Cmd::seq(q.visit.clone(), q.ascend.clone()),
            Cmd::seq(
                q.probe.clone(),
                Cmd::ite(
                    self.available,
                    Cmd::ite(self.fresh, q.descend.clone(), q.advance.clone()),
                    q.ascend.clone(),
                ),
            ),
        )
    }

    pub fn loop_command<const S: usize>(&self, q: &TupleRoutines<R, S>) -> Cmd<R, S> {
        Cmd::while_(self.active, self.body(q))
    }

    pub fn command<const S: usize>(&self, q: &TupleRoutines<R, S>) -> Cmd<R, S> {
        Cmd::seq(q.setup.clone(), self.loop_command(q))
    }

    pub fn program<const S: usize>(
        &self,
        q: &TupleRoutines<R, S>,
        input: usize,
        output: usize,
    ) -> Result<Program<R, S>, Error> {
        self.command(q).compiled(input, output)
    }
}

pub fn query_ports() -> TuplePorts<40> {
    TuplePorts::new(36, 37, 38, 39).expect("pinned tuple ABI is in range")
}

/// Exact physical SignatureTupleNative.initializeLevelsCommand:
/// preserving copy 130 -> 842 via scratch 841, then 649 -> 845 via 841,
/// peek 842 into (0, 1), set leaf = not reg1 and active = true.
///
/// Source entry preconditions: stacks 841, 842, and 845 are empty.
/// Source words 130/649 are preserved, scratch 841 is emptied on return.
pub fn initialize_levels_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        Cmd::Call(copy_program(130, TUPLE_STACKS[6], TUPLE_STACKS[5], 0, 1)?),
        Cmd::seq(
            Cmd::Call(copy_program(649, TUPLE_STACKS[9], TUPLE_STACKS[5], 0, 1)?),
            Cmd::seq(
                Cmd::Atom(Atom::Peek {
                    stack: TUPLE_STACKS[6],
                    value: 0,
                    present: 1,
                }),
                Cmd::seq(
                    Cmd::Atom(Atom::Not {
                        dst: CONTROLLER_REGISTERS[1],
                        src: 1,
                    }),
                    Cmd::Atom(Atom::Set {
                        dst: CONTROLLER_REGISTERS[0],
                        value: true,
                    }),
                ),
            ),
        ),
    ))
}

pub fn initialize_levels_program() -> Result<Program<40, 896>, Error> {
    initialize_levels_command()?.compiled(130, TUPLE_STACKS[9])
}
