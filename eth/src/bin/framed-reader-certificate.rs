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
        // Serde derives this independently from the Rust variants and named
        // fields. The Python gate compares it with every hand-formatted row.
        "structure": {
            "lifted": serde_json::to_value(&lifted)?,
            "compiled": serde_json::to_value(&compiled)?,
        },
    }))
}

/// Check all 12 instruction constructors, with both values of Set,
/// through the hand-written row formatter and independently derived Serde
/// structural serialization. This is not a source-program certificate.
fn encoding_corpus() -> Result<Value, Box<dyn std::error::Error>> {
    let program = Program::<4, 3>::new(
        0, 1, 0,
        vec![
            Instr::Halt,
            Instr::Goto { next: 0 },
            Instr::Set { dst: 0, value: true, next: 1 },
            Instr::Set { dst: 1, value: false, next: 2 },
            Instr::Copy { dst: 0, src: 1, next: 2 },
            Instr::Not { dst: 1, src: 2, next: 3 },
            Instr::And { dst: 0, left: 1, right: 2, next: 4 },
            Instr::Or { dst: 1, left: 2, right: 3, next: 5 },
            Instr::Xor { dst: 2, left: 3, right: 0, next: 6 },
            Instr::Branch { test: 3, yes: 0, no: 12 },
            Instr::Push { stack: 2, src: 3, next: 7 },
            Instr::Peek { stack: 1, value: 2, present: 3, next: 8 },
            Instr::Pop { stack: 2, value: 1, present: 0, next: 9 },
        ],
    )?;
    Ok(json!({
        "physical": program_record(&program),
        "structure": serde_json::to_value(&program)?,
    }))
}

fn receipt() -> Result<Value, Box<dyn std::error::Error>> {
    Ok(json!({
        "kind": "rust-physical-programs-v2",
        "source_commit": SOURCE_COMMIT,
        "encoding_corpus": encoding_corpus()?,
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
        assert!(
            case::<3, 3>(
                "invalid",
                Ports {
                    tag: 0,
                    present: 1,
                    found: 0,
                    source: 0,
                    payload: 1,
                    input: 0,
                    output: 1,
                }
            )
            .is_err()
        );
    }

    #[test]
    fn every_physical_opcode_and_boolean_bit_has_independent_format_evidence() {
        let corpus = encoding_corpus().unwrap();
        assert_eq!(
            corpus["physical"]["code"],
            json!([
                "halt", "goto:0", "set:0:1:1", "set:1:0:2",
                "copy:0:1:2", "not:1:2:3", "and:0:1:2:4",
                "or:1:2:3:5", "xor:2:3:0:6", "branch:3:0:12",
                "push:2:3:7", "peek:1:2:3:8", "pop:2:1:0:9"
            ])
        );
        assert_eq!(corpus["structure"]["code"][2]["Set"]["value"], true);
        assert_eq!(corpus["structure"]["code"][3]["Set"]["value"], false);
        assert_eq!(corpus["structure"]["code"][11]["Peek"]["present"], 3);
        assert_eq!(corpus["structure"]["code"][12]["Pop"]["present"], 0);
    }

}
