//! Structured finite-program syntax and compile-time instruction-table expansion.
//! This is distinct from the source-instruction interpreter in the parent module.

use super::{Instr, Program};
use crate::Error;

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
        let exit = size;
        let mut code = vec![Instr::Halt; size.checked_add(1).ok_or(Error::Overflow)?];
        self.emit(0, exit, &mut code)?;
        Program::new(input_stack, output_stack, self.entry_at(0, exit)?, code)
    }
}
