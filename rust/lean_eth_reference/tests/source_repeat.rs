//! Physical source repeat must preserve the exact original per-label machine.
 //! Counts are symbolic at compile time; a repeated instruction is never
 //! replaced with a higher-level semantic shortcut.
use lean_eth_reference::bit_program::{DeferredProgram, Instr, RunLimits, SourceGraphBinding};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::sync::Arc;

fn decode(
    command: Value,
    labels: usize,
) -> Result<Arc<DeferredProgram<2, 2>>, lean_eth_reference::Error> {
    let graph = json!({
        "kind": "original-structured-source-v1",
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "source_blob": "0123456789abcdef0123456789abcdef01234567",
        "declaration": "Fixture.RepeatedCommand",
        "id": "repeat_fixture",
        "abi": { "r": 2, "s": 2, "labels": labels, "input": 0, "output": 1 },
        "command": command,
    });
    let mut raw = serde_json::to_vec(&graph).unwrap();
    raw.push(b'\n');
    let digest = format!("{:x}", Sha256::digest(&raw));
    DeferredProgram::<2, 2>::from_original_source_json(
        &raw,
        SourceGraphBinding {
            id: "repeat_fixture",
            declaration: "Fixture.RepeatedCommand",
            source_blob: "0123456789abcdef0123456789abcdef01234567",
            graph_sha256: &digest,
        },
    )
}

#[test]
fn simple_repeat_preserves_every_step_and_halt() {
    let p = decode(
        json!({"kind": "repeat", "count": 3,
               "body": {"kind": "atom", "opcode": "set:0:1"}}),
        4,
    )
    .unwrap();
    assert_eq!(p.entry(), 1);
    assert_eq!(p.instruction_at(0).unwrap(), Instr::Halt);
    for pc in 1..4 {
        assert_eq!(
            p.instruction_at(pc).unwrap(),
            Instr::Set {
                dst: 0,
                value: true,
                next: if pc == 3 { 0 } else { pc + 1 },
            }
        );
    }
    let mut state = p.initial([]);
    let stats = p
        .run(
            &mut state,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 10,
            },
        )
        .unwrap();
    assert_eq!(stats.instructions, 4);
    assert!(state.pc.is_none());
    assert!(state.regs[0]);
}

#[test]
fn repeat_nested_inside_composed_call_retains_source_return_step() {
    let p = decode(
        json!({"kind": "call", "program": {
            "kind": "composed", "r": 2, "s": 2, "input": 0, "output": 1,
            "command": {"kind": "repeat", "count": 3,
                        "body": {"kind": "atom", "opcode": "not:0:0"}}
        }}),
        5,
    )
    .unwrap();
    assert_eq!(p.entry(), 2);
    assert_eq!(p.instruction_at(1).unwrap(), Instr::Goto { next: 0 });
    assert_eq!(
        p.instruction_at(4).unwrap(),
        Instr::Not {
            dst: 0,
            src: 0,
            next: 1,
        }
    );
    let mut state = p.initial([]);
    let stats = p
        .run(
            &mut state,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 10,
            },
        )
        .unwrap();
    assert_eq!(stats.instructions, 5);
    assert!(state.regs[0]);
    assert!(state.pc.is_none());
}

#[test]
fn large_repeat_resolves_random_access_without_flattening() {
    let p = decode(
        json!({"kind": "repeat", "count": 500_000_000_usize,
               "body": {"kind": "atom", "opcode": "not:0:0"}}),
        500_000_001,
    )
    .unwrap();
    assert_eq!((p.entry(), p.labels()), (1, 500_000_001));
    assert_eq!(
        p.instruction_at(250_000_000).unwrap(),
        Instr::Not {
            dst: 0,
            src: 0,
            next: 250_000_001,
        }
    );
    assert_eq!(
        p.instruction_at(500_000_000).unwrap(),
        Instr::Not {
            dst: 0,
            src: 0,
            next: 0,
        }
    );
    assert!(p.materialize(4096).is_err());
}

#[test]
fn zero_repeat_has_only_the_original_halt() {
    let p = decode(
        json!({"kind": "repeat", "count": 0, "body":
               {"kind": "atom", "opcode": "set:0:1"}}),
        1,
    )
    .unwrap();
    assert_eq!(p.entry(), 0);
    assert_eq!(p.instruction_at(0).unwrap(), Instr::Halt);
    let mut state = p.initial([]);
    assert_eq!(
        p.run(
            &mut state,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 1,
            }
        )
        .unwrap()
        .instructions,
        1
    );
}

#[test]
fn bogus_repeat_counts_labels_and_nested_opcodes_refuse() {
    for command in [
        json!({"kind": "repeat", "count": 1_000_000_000_u64,
                "body": {"kind": "atom", "opcode": "not:0:0"}}),
        json!({"kind": "repeat", "count": -1, "body": {"kind": "skip"}}),
        json!({"kind": "repeat", "count": 1.5, "body": {"kind": "skip"}}),
        json!({"kind": "repeat", "count": 2,
                "body": {"kind": "atom", "opcode": "set:99:1"}}),
        json!({"kind": "repeat", "count": 2,
                "body": {"kind": "atom", "opcode": "set:0:1"}, "extra": true}),
    ] {
        assert!(decode(command, 3).is_err());
    }
    assert!(decode(
        json!({"kind": "repeat", "count": 2,
               "body": {"kind": "atom", "opcode": "set:0:1"}}),
        9,
    )
    .is_err());
}
