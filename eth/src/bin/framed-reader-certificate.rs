//! Emit actual production Rust physical programs in the existing source-graph
//! finite-table vocabulary. The shared Python certificate engine parses these
//! rows and renders them into Lean. No Lean source or expected table is written
//! here; this executable cannot certify its own output.

use lean_eth_reference::bit_program::frame_programs::frame_program;
use lean_eth_reference::bit_program::{Cmd, Instr, Program};
use serde_json::{Value, json};

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";

/// The 12 physical opcodes use the *existing* source-graph table format.
/// This is a serializer of Rust values, not a second Lean formatter.
/// A new Rust instruction constructor requires an explicit, reviewed case.
fn instruction_record(instr: &Instr) -> String {
    match *instr {
        Instr::Halt => "halt".into(),
        Instr::Goto { next } => format!("goto:{next}"),
        Instr::Set { dst, value, next } => {
            format!("set:{dst}:{}:{next}", usize::from(value))
        }
        Instr::Copy { dst, src, next } => format!("copy:{dst}:{src}:{next}"),
        Instr::Not { dst, src, next } => format!("not:{dst}:{src}:{next}"),
        Instr::And { dst, left, right, next } => {
            format!("and:{dst}:{left}:{right}:{next}")
        }
        Instr::Or { dst, left, right, next } => {
            format!("or:{dst}:{left}:{right}:{next}")
        }
        Instr::Xor { dst, left, right, next } => {
            format!("xor:{dst}:{left}:{right}:{next}")
        }
        Instr::Branch { test, yes, no } => format!("branch:{test}:{yes}:{no}"),
        Instr::Push { stack, src, next } => format!("push:{stack}:{src}:{next}"),
        Instr::Peek { stack, value, present, next } => {
            format!("peek:{stack}:{value}:{present}:{next}")
        }
        Instr::Pop { stack, value, present, next } => {
            format!("pop:{stack}:{value}:{present}:{next}")
        }
    }
}

/// Exactly the established source-graph finite table object. It is parsed
/// with verify_source_graph.parse_program, not a separate JSON schema.
fn program_record<const R: usize, const S: usize>(program: &Program<R, S>) -> Value {
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

#[derive(Clone, Copy)]
struct Ports {
    tag: usize,
    present: usize,
    found: usize,
    source: usize,
    payload: usize,
    input: usize,
    output: usize,
}

impl Ports {
    fn valid<const R: usize, const S: usize>(self) -> bool {
        self.tag < R
            && self.present < R
            && self.found < R
            && self.tag != self.present
            && self.found != self.tag
            && self.found != self.present
            && self.source < S
            && self.payload < S
            && self.source != self.payload
            && self.input < S
            && self.output < S
    }
}

/// Only these six physical source call sites are admitted by the receipt.
/// Their callback policies are intentionally not merged.
fn case<const R: usize, const S: usize>(
    name: &str,
    ports: Ports,
) -> Result<Value, Box<dyn std::error::Error>> {
    if !ports.valid::<R, S>() {
        return Err("invalid original RecordPrograms.Ports or compiled I/O port".into());
    }
    let lifted =
        frame_program()?.lift::<R, S>([ports.tag, ports.present], [ports.source, ports.payload])?;
    let compiled = Cmd::Call(lifted.clone()).compiled(ports.input, ports.output)?;
    Ok(json!({
        "name": name,
        "ports": {
            "tag": ports.tag,
            "present": ports.present,
            "found": ports.found,
            "source": ports.source,
            "payload": ports.payload,
            "input": ports.input,
            "output": ports.output,
        },
        "lifted": program_record(&lifted),
        "compiled": program_record(&compiled),
    }))
}

fn receipt() -> Result<Value, Box<dyn std::error::Error>> {
    Ok(json!({
        "kind": "rust-physical-programs-v1",
        "source_commit": SOURCE_COMMIT,
        "cases": [
            case::<15, 16>("dedup", Ports {
                tag: 0, present: 1, found: 14, source: 13, payload: 15,
                input: 13, output: 13,
            })?,
            case::<15, 16>("filter", Ports {
                tag: 0, present: 1, found: 14, source: 13, payload: 15,
                input: 13, output: 15,
            })?,
            case::<15, 12>("relation", Ports {
                tag: 12, present: 13, found: 14, source: 10, payload: 11,
                input: 10, output: 11,
            })?,
            case::<13, 11>("tautology", Ports {
                tag: 10, present: 11, found: 12, source: 0, payload: 1,
                input: 0, output: 0,
            })?,
            case::<7, 5>("membership", Ports {
                tag: 5, present: 6, found: 4, source: 0, payload: 1,
                input: 0, output: 1,
            })?,
            case::<3, 4>("reversal", Ports {
                tag: 0, present: 1, found: 2, source: 0, payload: 3,
                input: 0, output: 2,
            })?,
        ],
    }))
}

fn main() {
    match receipt() {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("physical program receipt refused: {error}");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_six_actual_programs_have_the_expected_dimensions() {
        let data = receipt().unwrap();
        let cases = data["cases"].as_array().unwrap();
        assert_eq!(cases.len(), 6);
        for case in cases {
            assert_eq!(case["lifted"]["labels"], 7);
            assert_eq!(case["compiled"]["labels"], 8);
            assert_eq!(case["lifted"]["code"][6], "halt");
            assert_eq!(case["compiled"]["code"][0], "halt");
            assert_eq!(case["compiled"]["code"][7], "goto:0");
            assert_eq!(case["compiled"]["entry"], 1);
        }
    }

    #[test]
    fn source_forbidden_found_alias_is_refused_before_receipt_output() {
        assert!(case::<3, 3>("invalid", Ports {
            tag: 0, present: 1, found: 0, source: 0,
            payload: 1, input: 0, output: 1,
        }).is_err());
    }

    #[test]
    fn every_physical_opcode_has_a_canonical_row() {
        let rows = [
            (Instr::Halt, "halt"),
            (Instr::Goto { next: 0 }, "goto:0"),
            (Instr::Set { dst: 0, value: true, next: 1 }, "set:0:1:1"),
            (Instr::Set { dst: 0, value: false, next: 1 }, "set:0:0:1"),
            (Instr::Copy { dst: 0, src: 1, next: 2 }, "copy:0:1:2"),
            (Instr::Not { dst: 0, src: 1, next: 2 }, "not:0:1:2"),
            (Instr::And { dst: 0, left: 1, right: 2, next: 3 }, "and:0:1:2:3"),
            (Instr::Or { dst: 0, left: 1, right: 2, next: 3 }, "or:0:1:2:3"),
            (Instr::Xor { dst: 0, left: 1, right: 2, next: 3 }, "xor:0:1:2:3"),
            (Instr::Branch { test: 0, yes: 1, no: 2 }, "branch:0:1:2"),
            (Instr::Push { stack: 0, src: 1, next: 2 }, "push:0:1:2"),
            (Instr::Peek { stack: 0, value: 1, present: 2, next: 3 }, "peek:0:1:2:3"),
            (Instr::Pop { stack: 0, value: 1, present: 2, next: 3 }, "pop:0:1:2:3"),
        ];
        for (instruction, expected) in rows {
            assert_eq!(instruction_record(&instruction), expected);
        }
    }
}
