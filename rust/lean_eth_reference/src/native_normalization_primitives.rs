//! Exact source-native normalization prerequisites: unary polarity reversal,
//! physical framed-record emission, and reversible record iteration.
//!
//! Pinned original: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! These components are not a complete CNF normalization program.

use crate::Error;
use crate::bit_program::{Atom, Cmd, Instr, Program};
use crate::native_high::clear_program;
use crate::native_record_membership::frame_program;

/// SubexpNormalizeProgram.negateProgram, the original 15-label 2x2 table.
/// On canonical unary code c, emits unary (c xor 1) in precisely
/// 8*(c/2)+10+c%2 source steps, including halt, and preserves the suffix.
pub fn negate_literal_program() -> Result<Program<2, 2>, Error> {
    use Instr as I;
    Program::new(0, 1, 0, vec![
        I::Set { dst: 0, value: false, next: 1 },
        I::Push { stack: 1, src: 0, next: 2 },
        I::Pop { stack: 0, value: 0, present: 1, next: 3 },
        I::Branch { test: 1, yes: 4, no: 12 },
        I::Branch { test: 0, yes: 5, no: 10 },
        I::Pop { stack: 0, value: 0, present: 1, next: 6 },
        I::Branch { test: 1, yes: 7, no: 12 },
        I::Branch { test: 0, yes: 8, no: 12 },
        I::Push { stack: 1, src: 0, next: 9 },
        I::Push { stack: 1, src: 0, next: 2 },
        I::Set { dst: 0, value: true, next: 11 },
        I::Push { stack: 1, src: 0, next: 12 },
        I::Set { dst: 0, value: false, next: 13 },
        I::Set { dst: 1, value: false, next: 14 },
        I::Halt,
    ])
}

/// SubexpNormalizeProgram.emitRecordProgram: the unchanged source 17-label
/// SubexpPostfixControl.literalService table, entered directly at label 7.
/// Source parser labels 0-6 remain part of the table, with the original
/// continuation at 7. Encodes a reversed payload from stack 3 onto stack 2.
pub fn emit_record_program() -> Result<Program<3, 4>, Error> {
    let parser = frame_program()?;
    let mut code = Vec::with_capacity(17);
    for instruction in parser.code() {
        let relocated = match *instruction {
            Instr::Pop { stack, value, present, next } => Instr::Pop {
                stack: if stack == 1 { 3 } else { stack },
                value,
                present,
                next,
            },
            Instr::Push { stack, src, next } => Instr::Push {
                stack: if stack == 1 { 3 } else { stack },
                src,
                next,
            },
            Instr::Halt => Instr::Goto { next: 7 },
            Instr::Branch { test, yes, no } => Instr::Branch { test, yes, no },
            _ => return Err(Error::Invalid("unexpected source frame instruction".into())),
        };
        code.push(relocated);
    }
    code.extend([
        Instr::Set { dst: 0, value: false, next: 8 },
        Instr::Push { stack: 2, src: 0, next: 9 },
        Instr::Pop { stack: 3, value: 0, present: 1, next: 10 },
        Instr::Branch { test: 1, yes: 11, no: 14 },
        Instr::Push { stack: 2, src: 0, next: 12 },
        Instr::Set { dst: 0, value: true, next: 13 },
        Instr::Push { stack: 2, src: 0, next: 9 },
        Instr::Set { dst: 0, value: true, next: 15 },
        Instr::Push { stack: 2, src: 0, next: 16 },
        Instr::Halt,
    ]);
    Program::new(3, 2, 7, code)
}

/// Original SubexpNormalizeProgram.emitIfSelected. The discard branch and
/// register reset both execute as finite physical machine instructions.
pub fn emit_if_selected_command() -> Result<Cmd<3, 4>, Error> {
    let route = Cmd::ite(
        2,
        Cmd::Call(emit_record_program()?),
        Cmd::Call(clear_program(3, 0, 1)?),
    );
    let reset = Cmd::seq(
        Cmd::Atom(Atom::Set { dst: 0, value: false }),
        Cmd::seq(
            Cmd::Atom(Atom::Set { dst: 1, value: true }),
            Cmd::Atom(Atom::Set { dst: 2, value: false }),
        ),
    );
    Ok(Cmd::seq(route, reset))
}

/// SubexpNormalizeProgram.reverseRecordsCmd: exact RecordPrograms.iterate
/// with filterPorts=(tag0,present1,found2,source0,payload3), physically
/// constructing records.reverse in the output stack's encoded list.
pub fn reverse_records_command() -> Result<Cmd<3, 4>, Error> {
    let reader = Cmd::Call(frame_program()?.lift::<3, 4>([0, 1], [0, 3])?);
    let emit_every = Cmd::seq(
        Cmd::Atom(Atom::Set { dst: 2, value: true }),
        emit_if_selected_command()?,
    );
    let advance = Cmd::ite(
        2,
        Cmd::Atom(Atom::Set { dst: 0, value: false }),
        Cmd::Atom(Atom::Pop { stack: 0, value: 0, present: 1 }),
    );
    let body = Cmd::seq(reader, Cmd::seq(emit_every, advance));
    Ok(Cmd::seq(
        Cmd::Atom(Atom::Set { dst: 2, value: false }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop { stack: 0, value: 0, present: 1 }),
            Cmd::while_(0, body),
        ),
    ))
}

pub fn reverse_records_program() -> Result<Program<3, 4>, Error> {
    reverse_records_command()?.compiled(0, 2)
}

/// Exact lift into ExecLiteralDedupProgram.reverseProgram, 10x8.
pub fn literal_dedup_reverse_program() -> Result<Program<10, 8>, Error> {
    reverse_records_program()?.lift::<10, 8>([7, 8, 9], [2, 7, 0, 1])
}

/// Exact lift into ExecCleanLiteralsProgram.reverseProgram, 13x11.
pub fn clean_literals_reverse_program() -> Result<Program<13, 11>, Error> {
    reverse_records_program()?.lift::<13, 11>([10, 11, 12], [2, 10, 0, 1])
}

/// Exact lift into SubexpTautologyFilterProgram.reverseProgram, 13x11.
pub fn tautology_filter_reverse_program() -> Result<Program<13, 11>, Error> {
    reverse_records_program()?.lift::<13, 11>([10, 11, 12], [2, 3, 0, 1])
}

/// Exact lift into ExecClauseFilterReverse.program, 15x16.
pub fn clause_filter_reverse_program() -> Result<Program<15, 16>, Error> {
    reverse_records_program()?.lift::<15, 16>([0, 1, 14], [14, 9, 13, 15])
}
