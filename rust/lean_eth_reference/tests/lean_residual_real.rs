//! Actual Lean frontend smoke tests. Set LEAN_BIN to run; never mock Lean semantics.
use lean_eth_reference::lean_codegen::validate_residual;
use serde_json::Value;
use std::{env, fs, path::Path, process::Command, time::SystemTime};

struct FixtureDir(std::path::PathBuf);
impl Drop for FixtureDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn run(lean: &str, dir: &Path, file: &str, body: &str) -> std::process::Output {
    fs::write(dir.join(file), format!("import ResidualGraph\n{body}\n")).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .arg(file)
        .output()
        .expect("actual Lean invocation")
}

#[test]
fn real_lean_core_expr_regressions_when_toolchain_is_available() {
    let Ok(lean) = env::var("LEAN_BIN") else {
        // CI cannot claim this test passed against Lean without a real toolchain.
        return;
    };
    let stamp = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = FixtureDir(env::temp_dir().join(format!("eth-lean-expr-{}-{stamp}", std::process::id())));
    fs::create_dir(&dir.0).unwrap();
    let producer = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tools/lean-ir-smoke/ResidualGraph.lean");
    fs::copy(producer, dir.0.join("ResidualGraph.lean")).unwrap();
    let build = Command::new(&lean)
        .current_dir(&dir.0)
        .env("LEAN_PATH", &dir.0)
        .args(["ResidualGraph.lean", "-o", "ResidualGraph.olean"])
        .output()
        .unwrap();
    assert!(build.status.success(), "Lean producer failed: {}", String::from_utf8_lossy(&build.stderr));
    let successes = [
        ("Shared", "Shared.root", "namespace Shared\nnoncomputable def root : Nat → Nat := fun n => (Nat.succ (Nat.succ n)) + (Nat.succ (Nat.succ n))\nend Shared\n#export_residual_graph Shared.root"),
        ("Reduction", "Reduction.root", "namespace Reduction\nnoncomputable def root : Nat := (let f := (fun x : Nat => x + 1); f) 41\nend Reduction\n#export_residual_graph Reduction.root"),
        ("Large", "Large.root", "namespace Large\nnoncomputable def root : Nat := Nat.rec 0 (fun _ acc => acc + 1) 1000000000\nend Large\n#export_residual_graph Large.root"),
        ("Polymorphic", "Polymorphic.root", "namespace Polymorphic\nnoncomputable def root.{u} (α : Sort u) (x : α) : α := x\nend Polymorphic\n#export_residual_graph Polymorphic.root"),
    ];
    for (file, root, body) in successes {
        let output = run(&lean, &dir.0, &format!("{file}.lean"), body);
        assert!(output.status.success(), "{root} failed: {}", String::from_utf8_lossy(&output.stderr));
        validate_residual(&output.stdout, root).expect("typed Rust receipt accepts real Lean expression DAG");
        let doc: Value = serde_json::from_slice(&output.stdout).unwrap();
        if file == "Large" {
            assert!(doc["node_count"].as_u64().unwrap() < 100, "recursor expanded");
        }
        if file == "Reduction" {
            assert_eq!(doc["beta_zeta_steps"], 2);
        }
    }
    let refusals = [
        ("Axiom", "namespace AxiomTest\naxiom oracle : Nat\nnoncomputable def root : Nat := oracle + 1\nend AxiomTest\n#export_residual_graph AxiomTest.root"),
        ("Theorem", "namespace TheoremTest\ntheorem root : True := True.intro\nend TheoremTest\n#export_residual_graph TheoremTest.root"),
        ("Unknown", "#export_residual_graph NoSuchDefinition.ever"),
    ];
    for (file, body) in refusals {
        let output = run(&lean, &dir.0, &format!("{file}.lean"), body);
        assert!(!output.status.success(), "{file} unexpectedly accepted");
        assert!(!output.stdout.starts_with(b"{"), "{file} published a graph on failure");
    }
}
