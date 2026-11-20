//! Canonical physical `BitProgram` record transport for source-graph
//! verification. A single production mapping prints opcode rows;
//! independently derived Serde variants are checked downstream.
//! This module does not emit Lean proofs, interpret source graphs,
//! or claim that serialization refines arbitrary Rust execution.
use serde_json::{Value, json};
use super::{Instr, Program};

/// The 12 physical opcodes use the *existing* source-graph table format.
/// This is a serializer of Rust values, not a second Lean formatter.
/// A new Rust instruction constructor requires an explicit, reviewed case.
pub fn instruction_record(instr: &Instr) -> String {
    match *instr {
        Instr::Halt => "halt".into(),
        Instr::Goto { next } => format!("goto:{next}"),
        Instr::Set { dst, value, next } => {
            format!("set:{dst}:{}:{next}", usize::from(value))
        }
        Instr::Copy { dst, src, next } => format!("copy:{dst}:{src}:{next}"),
        Instr::Not { dst, src, next } => format!("not:{dst}:{src}:{next}"),
        Instr::And {
            dst,
            left,
            right,
            next,
        } => {
            format!("and:{dst}:{left}:{right}:{next}")
        }
        Instr::Or {
            dst,
            left,
            right,
            next,
        } => {
            format!("or:{dst}:{left}:{right}:{next}")
        }
        Instr::Xor {
            dst,
            left,
            right,
            next,
        } => {
            format!("xor:{dst}:{left}:{right}:{next}")
        }
        Instr::Branch { test, yes, no } => format!("branch:{test}:{yes}:{no}"),
        Instr::Push { stack, src, next } => format!("push:{stack}:{src}:{next}"),
        Instr::Peek {
            stack,
            value,
            present,
            next,
        } => {
            format!("peek:{stack}:{value}:{present}:{next}")
        }
        Instr::Pop {
            stack,
            value,
            present,
            next,
        } => {
            format!("pop:{stack}:{value}:{present}:{next}")
        }
    }
}

/// Exactly the established source-graph finite table object. It is parsed
/// with verify_source_graph.parse_program, not a separate JSON schema.
pub fn program_record<const R: usize, const S: usize>(program: &Program<R, S>) -> Value {
    json!({
        "r": R,
        "s": S,
        "labels": program.code().len(),
        "entry": program.entry(),
        "input": program.input_stack(),
        "output": program.output_stack(),
        "code": program.code().iter().map(instruction_record).collect::<Vec<_>>(),
    })
}

