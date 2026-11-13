//! End-to-end source identity and stale-receipt tests using the installed Git CLI.
use lean_eth_reference::lean_codegen::{Backend, source_identity, validate};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::SystemTime,
};

struct GitFixture {
    root: PathBuf,
    revision: String,
}
impl Drop for GitFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
fn git(path: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(path)
        .args(args)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "git failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap().trim().to_owned()
}
fn fixture() -> GitFixture {
    let stamp = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("eth-rust-git-test-{}-{stamp}", std::process::id()));
    fs::create_dir(&root).unwrap();
    git(&root, &["init", "-q"]);
    git(&root, &["config", "user.name", "Fixture"]);
    git(&root, &["config", "user.email", "fixture@example.org"]);
    fs::write(
        root.join("Demo.lean"),
        "namespace Demo\ndef double (n : Nat) := n + n\nend Demo\n",
    )
    .unwrap();
    fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    git(&root, &["add", "Demo.lean", "lean-toolchain"]);
    git(&root, &["commit", "-qm", "pin source"]);
    let revision = git(&root, &["rev-parse", "HEAD"]);
    GitFixture { root, revision }
}
fn graph() -> Vec<u8> {
    let root = json!({"tag":"str","parent":{"tag":"str","parent":{"tag":"anonymous"},"value":"Demo"},"value":"double"});
    let d = json!({"format":"lean-core-expr-dag-v1","status":"residualized-unverified",
        "source":root,"source_root":0,"reduced_root":0,"nodes":[{"tag":"nat","value":9}],
        "node_count":1,"source_symbols":[],"metadata_dropped":0,
        "lean_defeq_checked":true,"beta_zeta_steps":0,
        "rust_executable":false,"physical_refinement":"not-established"});
    format!("{d}\n").into_bytes()
}

#[test]
fn git_head_blob_and_toolchain_must_remain_pinned() {
    let repo = fixture();
    let id = source_identity(&repo.root, "Demo.lean", "lean-toolchain", &repo.revision).unwrap();
    assert_eq!(id.git_revision, repo.revision);
    assert_eq!(id.lean_toolchain, "leanprover/lean4:v4.35.0");
    assert!(source_identity(&repo.root, "../outside", "lean-toolchain", &repo.revision).is_err());
    assert!(source_identity(&repo.root, "Demo.lean", "lean-toolchain", &"f".repeat(40)).is_err());
    fs::write(repo.root.join("Demo.lean"), "def double := 7\n").unwrap();
    assert!(source_identity(&repo.root, "Demo.lean", "lean-toolchain", &repo.revision).is_err());
    git(&repo.root, &["checkout", "--", "Demo.lean"]);
    fs::write(
        repo.root.join("lean-toolchain"),
        "leanprover/lean4:v4.34.1\n",
    )
    .unwrap();
    assert!(source_identity(&repo.root, "Demo.lean", "lean-toolchain", &repo.revision).is_err());
}

#[test]
fn existing_artifact_verify_never_grants_executable_approval() {
    let repo = fixture();
    let original = graph();
    let id = source_identity(&repo.root, "Demo.lean", "lean-toolchain", &repo.revision).unwrap();
    let accepted = validate(
        Backend::ResidualExpr,
        &original,
        None,
        "Demo",
        &["Demo.double".into()],
        &id,
    )
    .unwrap();
    assert_eq!(accepted["executable_approved"], false);
    let artifact = repo.root.join("out.json");
    let receipt = repo.root.join("receipt.json");
    fs::write(&artifact, original).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_eth-compiler"))
        .args([
            "verify",
            "--backend",
            "residual-expr",
            "--module",
            "Demo",
            "--root",
            "Demo.double",
            "--source-repo",
        ])
        .arg(&repo.root)
        .arg("--source-path")
        .arg("Demo.lean")
        .arg("--source-revision")
        .arg(&repo.revision)
        .arg("--artifact")
        .arg(&artifact)
        .arg("--receipt")
        .arg(&receipt)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "verification refused: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let doc: Value = serde_json::from_slice(&fs::read(&receipt).unwrap()).unwrap();
    assert_eq!(doc["executable_approved"], false);
    fs::write(
        &artifact,
        graph()
            .into_iter()
            .chain(b"\n".iter().copied())
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_eth-compiler"))
        .args([
            "verify",
            "--backend",
            "residual-expr",
            "--module",
            "Demo",
            "--root",
            "Demo.double",
            "--source-repo",
        ])
        .arg(&repo.root)
        .arg("--source-path")
        .arg("Demo.lean")
        .arg("--source-revision")
        .arg(&repo.revision)
        .arg("--artifact")
        .arg(&artifact)
        .arg("--receipt")
        .arg(&receipt)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(
        !receipt.exists(),
        "stale acceptance receipt survived refusal"
    );
}
