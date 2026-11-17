//! Contract for the receipt-driven AOT build CLI. The synthetic "certified"
//! receipt here is deliberately NOT evidence of any Lean kernel execution.
//! This tests only receipt parsing, hash binding, cargo building and atomicity.
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const BLOB: &str = "0123456789abcdef0123456789abcdef01234567";
static NEXT: AtomicU64 = AtomicU64::new(0);

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

struct Fixture {
    root: PathBuf,
    graph: PathBuf,
    receipt: PathBuf,
    certificate: PathBuf,
    output: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "original-source-build-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let graph = root.join("graph.json");
        let receipt = root.join("certificate.receipt.json");
        let certificate = root.join("certificate.lean");
        let output = root.join("built");
        // Intentionally NOT a real certificate. This is a mocked receipt
        // proving that the builder must never call hash matching a proof.
        let cert = b"-- synthetic, not a kernel-checked Lean theorem\n";
        fs::write(&certificate, cert).unwrap();
        let source = json!({
            "kind":"original-structured-source-v1",
            "source_commit":SOURCE_COMMIT,
            "source_blob":BLOB,
            "id":"synthetic_build",
            "declaration":"Fixture.SyntheticBuild",
            "abi":{"r":2,"s":2,"labels":4,"input":0,"output":1},
            "command":{"kind":"repeat","count":3,
                       "body":{"kind":"atom","opcode":"not:0:0"}}
        });
        let mut graph_data = serde_json::to_vec(&source).unwrap();
        graph_data.push(b'\n');
        fs::write(&graph, &graph_data).unwrap();
        let evidence = json!({
            "status":"LEAN_KERNEL_CERTIFIED_SOURCE_DERIVED_FIXTURE",
            "lean_version":"Lean (version 4.34.1, synthetic test toolchain)",
            "source_commit":SOURCE_COMMIT,
            "source_blob":BLOB,
            "id":"synthetic_build",
            "declaration":"Fixture.SyntheticBuild",
            "source_graph_sha256":sha256(&graph_data),
            "certificate_sha256":sha256(cert),
            "physical_labels":4,
            "coverage":"synthetic acceptance fixture"
        });
        fs::write(&receipt, serde_json::to_vec(&evidence).unwrap()).unwrap();
        Self {
            root,
            graph,
            receipt,
            certificate,
            output,
        }
    }

    fn cli(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_original-source-build"))
            .args([&self.graph, &self.receipt, &self.certificate, &self.output])
            .output()
            .unwrap()
    }

    fn set_receipt(&self, field: &str, value: Value) {
        let mut data: Value = serde_json::from_slice(&fs::read(&self.receipt).unwrap()).unwrap();
        data[field] = value;
        fs::write(&self.receipt, serde_json::to_vec(&data).unwrap()).unwrap();
    }

    fn assert_refusal(&self) {
        let result = self.cli();
        assert!(
            !result.status.success(),
            "invalid or mismatched receipt accepted"
        );
        assert!(
            !self.output.exists(),
            "incomplete generated binary published"
        );
        let entries = fs::read_dir(&self.root)
            .unwrap()
            .map(|p| p.unwrap().file_name().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert!(
            !entries.iter().any(|name| name.contains(".aot-")),
            "failed build left staging products: {entries:?}"
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}

#[test]
fn build_produces_native_executable_and_source_provenance() {
    let fixture = Fixture::new();
    let built = fixture.cli();
    assert!(
        built.status.success(),
        "receipt-based build failed: {}",
        String::from_utf8_lossy(&built.stderr)
    );
    let exe = fixture.output.join("target/debug/original_lean_aot");
    assert!(exe.is_file(), "compiled native Rust executable missing");
    assert!(
        String::from_utf8(built.stdout)
            .unwrap()
            .trim()
            .ends_with("original_lean_aot")
    );
    let source = fs::read_to_string(fixture.output.join("src/main.rs")).unwrap();
    assert!(!source.contains("serde_json"));
    assert!(source.contains("fn block_"));
    assert!(source.contains("SOURCE_GRAPH_SHA256"));
    let report: Value =
        serde_json::from_slice(&fs::read(fixture.output.join("build.receipt.json")).unwrap())
            .unwrap();
    assert_eq!(report["status"], "GENERATED_AND_NATIVE_BUILT");
    assert_eq!(report["generated_rust_sha256"], sha256(source.as_bytes()));
    assert_eq!(report["binary_sha256"], sha256(&fs::read(&exe).unwrap()));
    assert_eq!(report["physical_labels"], 4);
    assert_eq!(
        report["lean_certificate_sha256"],
        sha256(&fs::read(&fixture.certificate).unwrap())
    );
    for (pc, expected) in [
        (0, "Halt"),
        (1, "Not { dst: 0, src: 0, next: 2 }"),
        (2, "Not { dst: 0, src: 0, next: 3 }"),
        (3, "Not { dst: 0, src: 0, next: 0 }"),
    ] {
        let got = Command::new(&exe)
            .args(["lookup", &pc.to_string()])
            .output()
            .unwrap();
        assert!(got.status.success(), "{pc}: {:?}", got.status);
        assert_eq!(String::from_utf8(got.stdout).unwrap().trim(), expected);
    }
    let executed = Command::new(&exe)
        .args(["run", "101", "10", "10"])
        .output()
        .unwrap();
    assert!(executed.status.success());
    assert!(
        String::from_utf8_lossy(&executed.stdout).contains("steps=4;"),
        "physical halt step was lost"
    );
    let second = fixture.cli();
    assert!(
        !second.status.success(),
        "builder overwrote existing output"
    );
}

#[test]
fn build_rejects_tampered_graph_and_certificate_without_artifacts() {
    let fixture = Fixture::new();
    fs::write(&fixture.graph, b"{}\n").unwrap();
    fixture.assert_refusal();
    fs::write(&fixture.certificate, b"-- replaced theorem\n").unwrap();
    fixture.assert_refusal();
}

#[test]
fn build_rejects_unverified_or_wrong_source_receipts() {
    let fixture = Fixture::new();
    for (field, replacement) in [
        ("status", json!("UNVERIFIED_LEAN_CERTIFICATE_SOURCE")),
        ("source_commit", json!("0".repeat(40))),
        ("lean_version", json!("4.35.0")),
        ("physical_labels", json!(5)),
        ("source_graph_sha256", json!("a".repeat(64))),
        ("source_blob", json!("a".repeat(40))),
        ("id", json!("another_declaration")),
    ] {
        let saved = fs::read(&fixture.receipt).unwrap();
        fixture.set_receipt(field, replacement);
        fixture.assert_refusal();
        fs::write(&fixture.receipt, saved).unwrap();
    }
}

#[test]
fn build_rejects_existing_directory_without_modifying_it() {
    let fixture = Fixture::new();
    fs::create_dir(&fixture.output).unwrap();
    let sentinel = fixture.output.join("do_not_touch");
    fs::write(&sentinel, b"keep").unwrap();
    let refused = fixture.cli();
    assert!(!refused.status.success());
    assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
}
