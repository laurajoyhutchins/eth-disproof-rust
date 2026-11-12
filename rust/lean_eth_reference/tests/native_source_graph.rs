//! Strict native source-graph import. The independent source acceptance suite
//! checks these bytes against the original Lean kernel before invoking Rust.
use std::sync::Arc;

use lean_eth_reference::bit_program::{DeferredProgram, Instr, SourceGraphBinding};
use sha2::{Digest, Sha256};

const SOURCE_BLOB: &str = "1111111111111111111111111111111111111111";
const ID: &str = "fixture_0";
const DECL: &str = "OAI.Algorithms.SubexponentialSAT.Example.fixture";

fn bound<'a>(json: &'a [u8], digest: &'a str) -> SourceGraphBinding<'a> {
    let _ = json;
    SourceGraphBinding {
        id: ID,
        declaration: DECL,
        source_blob: SOURCE_BLOB,
        graph_sha256: digest,
    }
}

fn import<const R: usize, const S: usize>(
    json: &[u8],
) -> Result<Arc<DeferredProgram<R, S>>, lean_eth_reference::Error> {
    let digest = format!("{:x}", Sha256::digest(json));
    DeferredProgram::<R, S>::from_original_source_json(json, bound(json, &digest))
}

fn wrap(command: &str, labels: usize, r: usize, s: usize) -> Vec<u8> {
    format!(
        "{{\"kind\":\"original-structured-source-v1\",\"source_commit\":\"4eaee87548250b2682affda7d05d947c05554bae\",\"source_blob\":\"{SOURCE_BLOB}\",\"declaration\":\"{DECL}\",\"id\":\"{ID}\",\"abi\":{{\"r\":{r},\"s\":{s},\"labels\":{labels},\"input\":0,\"output\":0}},\"command\":{command}}}\n"
    ).into_bytes()
}

#[test]
fn native_source_graph_preserves_entry_halt_branch_and_callee_relocation() {
    // Source physical label 0 is halt. Two callee physical labels become
    // relocated 1 and 2; its halt returns to following source instruction.
    let cmd = r#"{"kind":"seq","first":{"kind":"call","program":{"r":3,"s":3,"labels":3,"entry":2,"input":0,"output":0,"code":["halt","goto:0","set:0:1:1"]}},"second":{"kind":"while","test":0,"body":{"kind":"atom","opcode":"set:1:0"}}}"#;
    let input = wrap(cmd, 6, 3, 3);
    let graph = import::<3, 3>(&input).unwrap();
    assert_eq!(graph.labels(), 6);
    assert_eq!(graph.entry(), 3);
    assert_eq!(graph.instruction_at(0).unwrap(), Instr::Halt);
    assert_eq!(graph.instruction_at(1).unwrap(), Instr::Goto { next: 4 });
    assert_eq!(graph.instruction_at(2).unwrap(), Instr::Goto { next: 1 });
    assert_eq!(
        graph.instruction_at(3).unwrap(),
        Instr::Set {
            dst: 0,
            value: true,
            next: 2
        }
    );
    assert_eq!(
        graph.instruction_at(4).unwrap(),
        Instr::Branch {
            test: 0,
            yes: 5,
            no: 0
        }
    );
    assert_eq!(
        graph.instruction_at(5).unwrap(),
        Instr::Set {
            dst: 1,
            value: false,
            next: 4
        }
    );
}

#[test]
fn all_original_physical_opcodes_parse_with_typed_indices() {
    let codes = [
        "halt",
        "goto:0",
        "set:2:1:0",
        "copy:0:2:0",
        "not:0:2:0",
        "and:0:1:2:0",
        "or:0:1:2:0",
        "xor:0:1:2:0",
        "branch:0:0:1",
        "push:1:2:0",
        "peek:1:2:0:0",
        "pop:1:2:0:0",
    ];
    let rendered = codes
        .iter()
        .map(|s| format!("\"{s}\""))
        .collect::<Vec<_>>()
        .join(",");
    let cmd = format!(
        "{{\"kind\":\"call\",\"program\":{{\"r\":3,\"s\":3,\"labels\":12,\"entry\":1,\"input\":0,\"output\":0,\"code\":[{rendered}]}}}}"
    );
    let graph = import::<3, 3>(&wrap(&cmd, 13, 3, 3)).unwrap();
    assert_eq!(graph.labels(), 13);
    assert_eq!(graph.instruction_at(1).unwrap(), Instr::Goto { next: 0 });
    assert_eq!(
        graph.instruction_at(3).unwrap(),
        Instr::Set {
            dst: 2,
            value: true,
            next: 1
        }
    );
    assert_eq!(
        graph.instruction_at(11).unwrap(),
        Instr::Peek {
            stack: 1,
            value: 2,
            present: 0,
            next: 1,
        }
    );
    assert_eq!(
        graph.instruction_at(12).unwrap(),
        Instr::Pop {
            stack: 1,
            value: 2,
            present: 0,
            next: 1,
        }
    );
}

#[test]
fn fail_closed_on_schema_or_digest_tampering() {
    let src = wrap(r#"{"kind":"atom","opcode":"set:0:1"}"#, 2, 3, 3);
    assert!(import::<3, 3>(&src).is_ok());
    let digest = format!("{:x}", Sha256::digest(&src));
    let altered = String::from_utf8(src.clone())
        .unwrap()
        .replace("set:0:1", "set:0:0");
    assert!(
        DeferredProgram::<3, 3>::from_original_source_json(
            altered.as_bytes(),
            bound(&src, &digest),
        )
        .is_err()
    );

    for malformed in [
        r#"{"kind":"atom","opcode":"set:00:1"}"#,
        r#"{"kind":"atom","opcode":"set:3:1"}"#,
        r#"{"kind":"atom","opcode":"pop:4:1:0"}"#,
        r#"{"kind":"atom","opcode":"set:0:3"}"#,
        r#"{"kind":"oracle","opcode":"set:0:1"}"#,
        r#"{"kind":"skip","extra":"ignored"}"#,
        r#"{"kind":"while","test":3,"body":{"kind":"skip"}}"#,
        r#"{"kind":"atom","kind":"atom","opcode":"set:0:1"}"#,
        r#"{"kind":"atom","opcode":"set:0:1","opcode":"set:0:0"}"#,
    ] {
        assert!(
            import::<3, 3>(&wrap(malformed, 2, 3, 3)).is_err(),
            "{malformed}"
        );
    }
    assert!(import::<3, 3>(&wrap(r#"{"kind":"skip"}"#, 2, 3, 3)).is_err());
    assert!(import::<4, 3>(&src).is_err());
    let mut byte_change = src.clone();
    byte_change.push(b'\n');
    assert!(import::<3, 3>(&byte_change).is_err());
}

#[test]
fn empty_source_and_nested_source_control_flow_are_not_implicit_halts() {
    let empty = import::<3, 3>(&wrap(r#"{"kind":"skip"}"#, 1, 3, 3)).unwrap();
    assert_eq!(empty.entry(), 0);
    assert_eq!(empty.instruction_at(0).unwrap(), Instr::Halt);
    assert!(empty.instruction_at(1).is_err());

    let cmd = r#"{"kind":"if","test":0,"yes":{"kind":"atom","opcode":"peek:0:1:2"},"no":{"kind":"atom","opcode":"pop:0:1:2"}}"#;
    let x = import::<3, 3>(&wrap(cmd, 4, 3, 3)).unwrap();
    assert_eq!(
        x.instruction_at(1).unwrap(),
        Instr::Branch {
            test: 0,
            yes: 2,
            no: 3
        }
    );
    assert_eq!(
        x.instruction_at(2).unwrap(),
        Instr::Peek {
            stack: 0,
            value: 1,
            present: 2,
            next: 0,
        }
    );
    assert_eq!(
        x.instruction_at(3).unwrap(),
        Instr::Pop {
            stack: 0,
            value: 1,
            present: 2,
            next: 0,
        }
    );
}
