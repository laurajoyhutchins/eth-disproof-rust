//! A source-bound physical Program can itself be the root. A spurious
//! StructuredCalls::Call wrapper would add a halt site and change the trace.
//! These are schema/physical semantics tests, not Lean kernel certificates.
use lean_eth_reference::bit_program::{DeferredProgram, Instr, RunLimits, SourceGraphBinding};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn linked() -> Value {
    json!({
        "kind": "original-linked-source-v1",
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "source_blob": "0123456789abcdef0123456789abcdef01234567",
        "declaration": "Fixture.LinkedRoot",
        "id": "linked_root",
        "abi": {"r": 2, "s": 2, "labels": 4, "input": 0, "output": 1},
        "program": {
            "kind": "link",
            "left": {
                "r": 2, "s": 2, "labels": 2, "entry": 1, "input": 0, "output": 0,
                "code": ["halt", "set:0:1:0"]
            },
            "right": {
                "r": 2, "s": 2, "labels": 2, "entry": 1, "input": 0, "output": 1,
                "code": ["halt", "not:0:0:0"]
            }
        }
    })
}

fn compile(
    value: Value,
) -> Result<std::sync::Arc<DeferredProgram<2, 2>>, lean_eth_reference::Error> {
    let mut bytes = serde_json::to_vec(&value).unwrap();
    bytes.push(b'\n');
    let digest = format!("{:x}", Sha256::digest(&bytes));
    DeferredProgram::<2, 2>::from_original_source_json(
        &bytes,
        SourceGraphBinding {
            id: "linked_root",
            declaration: "Fixture.LinkedRoot",
            source_blob: "0123456789abcdef0123456789abcdef01234567",
            graph_sha256: &digest,
        },
    )
}

#[test]
fn direct_linked_root_preserves_all_physical_labels_and_entry() {
    let graph = compile(linked()).unwrap();
    assert_eq!(
        (
            graph.labels(),
            graph.entry(),
            graph.input_stack(),
            graph.output_stack()
        ),
        (4, 1, 0, 1)
    );
    assert_eq!(graph.instruction_at(0).unwrap(), Instr::Goto { next: 3 });
    assert_eq!(
        graph.instruction_at(1).unwrap(),
        Instr::Set {
            dst: 0,
            value: true,
            next: 0
        }
    );
    assert_eq!(graph.instruction_at(2).unwrap(), Instr::Halt);
    assert_eq!(
        graph.instruction_at(3).unwrap(),
        Instr::Not {
            dst: 0,
            src: 0,
            next: 2
        }
    );
    let mut state = graph.initial([]);
    let stats = graph
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
    assert!(!state.regs[0]);
}

#[test]
fn linked_root_rejects_ambiguous_schema_and_false_abi() {
    let mut graph = linked();
    graph["command"] = json!({"kind": "skip"});
    assert!(
        compile(graph).is_err(),
        "a source root cannot be both forms"
    );

    let mut graph = linked();
    graph["abi"]["labels"] = json!(5);
    assert!(compile(graph).is_err(), "incorrect source ABI must refuse");

    let mut graph = linked();
    graph["abi"]["output"] = json!(0);
    assert!(compile(graph).is_err(), "incorrect output port must refuse");

    let mut graph = linked();
    graph["program"]["right"]["code"][1] = json!("not:9:0:0");
    assert!(
        compile(graph).is_err(),
        "out-of-range physical operand must refuse"
    );
}

#[test]
fn structured_root_cannot_silently_use_linked_root_payload() {
    let mut graph = linked();
    graph["kind"] = json!("original-structured-source-v1");
    assert!(compile(graph).is_err());
}
