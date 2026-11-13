//! Execute real rustc code generated from validated source-bound physical IR.
//! Compare every small-program label and the terminal state with the existing
//! independent Rust interpreter. No external Lean certification is implied
//! by these synthetic fixtures.
use lean_eth_reference::bit_program::{
    DeferredProgram, RunLimits, SourceGraphBinding, emit_original_source_rust,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const BLOB: &str = "0123456789abcdef0123456789abcdef01234567";
const ID: &str = "aot_fixture";
const DECL: &str = "Fixture.Compiled";

fn graph(kind: &str, abi: Value, key: &str, body: Value) -> (Vec<u8>, String) {
    let mut object = json!({
        "kind": kind,
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "source_blob": BLOB,
        "id": ID,
        "declaration": DECL,
        "abi": abi
    });
    object[key] = body;
    let mut bytes = serde_json::to_vec(&object).unwrap();
    bytes.push(b'\n');
    let hash = format!("{:x}", Sha256::digest(&bytes));
    (bytes, hash)
}

fn binding(hash: &str) -> SourceGraphBinding<'_> {
    SourceGraphBinding {
        id: ID,
        declaration: DECL,
        source_blob: BLOB,
        graph_sha256: hash,
    }
}

static NEXT: AtomicU64 = AtomicU64::new(0);

fn compile(source: &str) -> (PathBuf, PathBuf) {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "lean-source-aot-test-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&path).unwrap();
    let source_path = path.join("generated.rs");
    let binary_path = path.join("generated");
    fs::write(&source_path, source).unwrap();

    let deps = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let library = fs::read_dir(&deps)
        .unwrap()
        .map(|p| p.unwrap().path())
        .find(|p| {
            p.file_name().and_then(|n| n.to_str()).is_some_and(|name| {
                name.starts_with("liblean_eth_reference-") && name.ends_with(".rlib")
            })
        })
        .expect("cargo must build lean_eth_reference rlib for integration test");
    let compilation = Command::new("rustc")
        .arg("--edition=2024")
        .arg(&source_path)
        .arg("--extern")
        .arg(format!("lean_eth_reference={}", library.display()))
        .arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .arg("-o")
        .arg(&binary_path)
        .output()
        .expect("rustc must be installed");
    assert!(
        compilation.status.success(),
        "generated source failed to compile:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    (path, binary_path)
}

fn run_binary(binary: &PathBuf, args: &[&str]) -> String {
    let result = Command::new(binary).args(args).output().unwrap();
    assert!(
        result.status.success(),
        "generated binary failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout).unwrap().trim().to_string()
}

fn assert_aot_matches(
    bytes: &[u8],
    hash: &str,
    input: &str,
    labels: usize,
    max_steps: u64,
) {
    let original = DeferredProgram::<2, 2>::from_original_source_json(bytes, binding(hash))
        .expect("source graph must decode");
    let emitted = emit_original_source_rust(bytes, binding(hash)).unwrap();
    assert_eq!(
        emitted,
        emit_original_source_rust(bytes, binding(hash)).unwrap(),
        "AOT output must be deterministic"
    );
    assert!(emitted.contains("pub const SOURCE_GRAPH_SHA256"));
    assert!(!emitted.contains("serde_json"));
    assert!(!emitted.contains("include_bytes!"));
    let (directory, binary) = compile(&emitted);
    for pc in 0..labels {
        let expected = format!("{:?}", original.instruction_at(pc).unwrap());
        let actual = run_binary(&binary, &["lookup", &pc.to_string()]);
        assert_eq!(actual, expected, "instruction differs at label {pc}");
    }
    let mut state = original.initial(input.bytes().map(|b| b == b'1'));
    let limits = RunLimits {
        max_steps,
        max_stack_bits: 100,
    };
    let stats = original.run(&mut state, limits).unwrap();
    let expected = format!(
        "steps={};peak={};pc={:?};regs={:?};stacks={:?}",
        stats.instructions, stats.peak_stack_bits, state.pc, state.regs, state.stacks
    );
    assert_eq!(
        run_binary(&binary, &["run", input, &max_steps.to_string(), "100"]),
        expected,
        "terminal state diverged"
    );
    let rejection = Command::new(&binary)
        .args(["lookup", &labels.to_string()])
        .output()
        .unwrap();
    assert!(!rejection.status.success(), "out-of-range label accepted");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn generated_structural_call_branch_and_repeat_match_physical_interpreter() {
    let call = json!({
        "r": 2, "s": 2, "labels": 2, "entry": 0, "input": 0, "output": 1,
        "code": ["set:1:1:1", "halt"]
    });
    let (raw, hash) = graph(
        "original-structured-source-v1",
        json!({"r": 2, "s": 2, "labels": 11, "input": 0, "output": 1}),
        "command",
        json!({"kind": "seq",
            "first": {"kind": "atom", "opcode": "set:0:1"},
            "second": {"kind": "seq",
                "first": {"kind": "if", "test": 0,
                    "yes": {"kind": "atom", "opcode": "not:0:0"},
                    "no": {"kind": "atom", "opcode": "set:1:1"}},
                "second": {"kind": "repeat", "count": 3,
                    "body": {"kind": "call", "program": call}}
            }
        }),
    );
    assert_aot_matches(&raw, &hash, "1010", 11, 30);
}

#[test]
fn generated_linked_lifts_keep_ports_and_right_hand_halt() {
    let left = json!({
        "kind": "lift", "r": 2, "s": 2,
        "registers": [1], "stacks": [0],
        "source": {
            "r": 1, "s": 1, "labels": 2, "entry": 0, "input": 0, "output": 0,
            "code": ["set:0:1:1", "halt"]
        }
    });
    let right = json!({
        "kind": "lift", "r": 2, "s": 2,
        "registers": [0], "stacks": [1],
        "source": {
            "r": 1, "s": 1, "labels": 2, "entry": 0, "input": 0, "output": 0,
            "code": ["not:0:0:1", "halt"]
        }
    });
    let (raw, hash) = graph(
        "original-linked-source-v1",
        json!({"r": 2, "s": 2, "labels": 4, "input": 0, "output": 1}),
        "program",
        json!({"kind": "link", "left": left, "right": right}),
    );
    assert_aot_matches(&raw, &hash, "", 4, 20);
}

#[test]
fn huge_repeat_compiles_without_expansion_and_rejects_step_overrun() {
    let (raw, hash) = graph(
        "original-structured-source-v1",
        json!({"r": 2, "s": 2, "labels": 500_000_001_usize, "input": 0, "output": 1}),
        "command",
        json!({"kind": "repeat", "count": 500_000_000_usize,
                "body": {"kind": "atom", "opcode": "not:0:0"}}),
    );
    let emitted = emit_original_source_rust(&raw, binding(&hash)).unwrap();
    assert!(emitted.len() < 16_000, "symbolic repeat was expanded");
    let (directory, binary) = compile(&emitted);
    assert_eq!(
        run_binary(&binary, &["lookup", "250000000"]),
        "Not { dst: 0, src: 0, next: 250000001 }"
    );
    assert_eq!(
        run_binary(&binary, &["lookup", "500000000"]),
        "Not { dst: 0, src: 0, next: 0 }"
    );
    let limited = Command::new(&binary)
        .args(["run", "", "4", "100"])
        .output()
        .unwrap();
    assert!(!limited.status.success());
    assert!(
        String::from_utf8_lossy(&limited.stderr).contains("instruction limit"),
        "nonterminating source must fail closed at step budget"
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn codegen_refuses_unbound_or_invalid_source() {
    let (raw, hash) = graph(
        "original-structured-source-v1",
        json!({"r": 2, "s": 2, "labels": 2, "input": 0, "output": 1}),
        "command",
        json!({"kind": "atom", "opcode": "set:0:1"}),
    );
    assert!(emit_original_source_rust(&raw, binding("0")).is_err());
    let mut truncated = raw.clone();
    truncated.pop();
    assert!(emit_original_source_rust(&truncated, binding(&hash)).is_err());
    let (wrong_labels, new_hash) = graph(
        "original-structured-source-v1",
        json!({"r": 2, "s": 2, "labels": 3, "input": 0, "output": 1}),
        "command",
        json!({"kind": "atom", "opcode": "set:0:1"}),
    );
    assert!(emit_original_source_rust(&wrong_labels, binding(&new_hash)).is_err());
}
