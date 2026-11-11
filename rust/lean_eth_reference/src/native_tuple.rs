//! Exact finite instruction table from the pinned Lean tuple odometer.
//!
//! Sources (`openai/math@4eaee87548250b2682affda7d05d947c05554bae`):
//! - `ExecCNFTupleOdometer.program` and `bumpWords`
//! - `ExecCNFTupleEnumeration.incrementCmd`, `advanceCmd`, `enumerate`
//! - `CounterForPrograms.Ports` and `HighQueryAdapter.highPorts.counter`
//!
//! This exposes the *real source loop* with an explicit compiled callback.
//! It does not stand in for `HighQueryProgram.conditioned`, which is not ported.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};

/// The complete 18-label machine, including the source's final halt label 17.
/// The scratch stack holds a reversed prefix, restored physically on return.
pub fn odometer_program() -> Result<Program<3, 2>, Error> {
    Program::new(
        0,
        0,
        0,
        vec![
            Instr::Set {
                dst: 2,
                value: true,
                next: 1,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 2,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 13,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 4,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 5,
            },
            Instr::Branch {
                test: 0,
                yes: 6,
                no: 12,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 7,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 8,
            },
            Instr::Not {
                dst: 0,
                src: 0,
                next: 9,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 10,
            },
            Instr::Branch {
                test: 0,
                yes: 11,
                no: 4,
            },
            Instr::Set {
                dst: 2,
                value: false,
                next: 14,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 1,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 14,
            },
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 15,
            },
            Instr::Branch {
                test: 1,
                yes: 16,
                no: 17,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 14,
            },
            Instr::Halt,
        ],
    )
}

/// Source `bumpWord`: one little-endian Boolean word with a carry bit.
pub fn bump_word(word: &[bool]) -> (bool, Vec<bool>) {
    let mut carry = true;
    let mut next = Vec::with_capacity(word.len());
    for &bit in word {
        next.push(bit ^ carry);
        carry &= bit;
    }
    (carry, next)
}

/// Source `bumpWords`: carry propagates across framed component records.
pub fn bump_words(words: &[Vec<bool>]) -> (bool, Vec<Vec<bool>>) {
    let mut carry = true;
    let mut result = Vec::with_capacity(words.len());
    for word in words {
        if carry {
            let (c, updated) = bump_word(word);
            carry = c;
            result.push(updated);
        } else {
            result.push(word.clone());
        }
    }
    (carry, result)
}

/// `Encoding.encodeList id`; no semantic conversion to integer masks.
pub fn encode_words(words: &[Vec<bool>]) -> Result<Vec<bool>, Error> {
    let length = words
        .iter()
        .try_fold(1usize, |total, word| {
            total.checked_add(2usize.checked_mul(word.len())?.checked_add(2)?)
        })
        .ok_or(Error::Overflow)?;
    let mut out = Vec::with_capacity(length);
    for word in words {
        out.push(true);
        for &bit in word {
            out.push(true);
            out.push(bit);
        }
        out.push(false);
    }
    out.push(false);
    Ok(out)
}

/// Physical `CounterForPrograms.Ports`, whose three machine registers are
/// *distinct*. All checks correspond to Lean's finite-index embeddings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CounterPorts {
    pub registers: [usize; 3],
    pub counter: usize,
    pub scratch: usize,
}

impl CounterPorts {
    fn validate<const R: usize, const S: usize>(self) -> Result<(), Error> {
        if self.counter == self.scratch
            || self.counter >= S
            || self.scratch >= S
            || self.registers.iter().any(|&r| r >= R)
            || self.registers[0] == self.registers[1]
            || self.registers[0] == self.registers[2]
            || self.registers[1] == self.registers[2]
        {
            return Err(Error::Invalid(
                "noninjective or out-of-range tuple ports".into(),
            ));
        }
        Ok(())
    }
}

/// `HighQueryAdapter.highPorts.counter`: actual marked-query ABI.
pub const HIGH_QUERY_PORTS: CounterPorts = CounterPorts {
    registers: [19, 20, 21],
    counter: 789,
    scratch: 790,
};

/// Source `ExecCNFTupleEnumeration.incrementCmd`: a *static lifted* call.
pub fn increment_command<const R: usize, const S: usize>(
    ports: CounterPorts,
) -> Result<Cmd<R, S>, Error> {
    ports.validate::<R, S>()?;
    Ok(Cmd::Call(odometer_program()?.lift::<R, S>(
        ports.registers,
        [ports.counter, ports.scratch],
    )?))
}

/// Source `advanceCmd`: run the full increment and complement its carry flag.
pub fn advance_command<const R: usize, const S: usize>(
    ports: CounterPorts,
) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::seq(
        increment_command(ports)?,
        Cmd::Atom(Atom::Not {
            dst: ports.registers[2],
            src: ports.registers[2],
        }),
    ))
}

/// Source `ExecCNFTupleEnumeration.enumerate`: start, while, body, advance.
///
/// The *supplied* callback must preserve the framed counter and scratch and
/// return with the guard restored. This API makes that dependency explicit;
/// it does not pretend that a substitute callback is the actual SAT query.
pub fn enumerate_command<const R: usize, const S: usize>(
    ports: CounterPorts,
    callback: Cmd<R, S>,
) -> Result<Cmd<R, S>, Error> {
    ports.validate::<R, S>()?;
    let start = Cmd::Atom(Atom::Set {
        dst: ports.registers[2],
        value: true,
    });
    Ok(Cmd::seq(
        start,
        Cmd::while_(
            ports.registers[2],
            Cmd::seq(callback, advance_command(ports)?),
        ),
    ))
}

/// Full fixed-control `HighQueryProgram.highLoop` with its callback supplied
/// by the caller. Until `QueryStreamProgram.command` is ported this is only
/// the executable control/odometer portion of that source definition.
pub fn high_loop_command(callback: Cmd<40, 896>) -> Result<Cmd<40, 896>, Error> {
    enumerate_command(HIGH_QUERY_PORTS, callback)
}
