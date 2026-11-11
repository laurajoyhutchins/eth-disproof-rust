//! CLI refuses self-comparison and incomplete fake "Lean" evidence.
use std::fs;
use std::process::Command;

fn high_fixture() -> String {
    let mut lines = Vec::new();
    for kind in ["branch", "initialize"] {
        for case in ["empty", "zero", "one", "mixed", "alternate", "all"] {
            lines.push(format!("{kind}|{case}|1|0|1|0|1"));
        }
    }
    lines.join("\n") + "\n"
}

#[test]
fn cli_accepts_independent_paths_but_rejects_aliases_and_bad_records() {
    let dir = std::env::temp_dir().join(format!(
        "eth-rust-trace-comparison-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let lean = dir.join("lean.trace");
    let rust = dir.join("rust.trace");
    fs::write(&lean, high_fixture()).unwrap();
    fs::write(&rust, high_fixture()).unwrap();

    let exe = env!("CARGO_BIN_EXE_compare-traces");
    let result = Command::new(exe)
        .args(["--suite", "high", "--lean"])
        .arg(&lean)
        .arg("--rust")
        .arg(&rust)
        .output()
        .unwrap();
    assert!(result.status.success(), "valid distinct input: {result:?}");

    let alias = Command::new(exe)
        .args(["--suite", "high", "--lean"])
        .arg(&lean)
        .arg("--rust")
        .arg(&lean)
        .output()
        .unwrap();
    assert!(!alias.status.success());
    assert!(String::from_utf8_lossy(&alias.stderr).contains("distinct files"));

    fs::write(&rust, high_fixture().lines().skip(1).collect::<Vec<_>>().join("\n")).unwrap();
    let incomplete = Command::new(exe)
        .args(["--suite", "high", "--lean"])
        .arg(&lean)
        .arg("--rust")
        .arg(&rust)
        .output()
        .unwrap();
    assert!(!incomplete.status.success());
    fs::remove_dir_all(dir).unwrap();
}
