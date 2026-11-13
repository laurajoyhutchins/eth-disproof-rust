//! End-to-end CLI smoke: DIMACS -> canonical Lean bits -> physical frontend.
use std::io::Write;
use std::process::{Command, Stdio};

fn run(args: &[&str], dimacs: &str) -> std::process::Output {
    let bin = env!("CARGO_BIN_EXE_eth-frontend");
    let mut p = Command::new(bin)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("eth-frontend binary exists");
    p.stdin
        .as_mut()
        .unwrap()
        .write_all(dimacs.as_bytes())
        .unwrap();
    p.wait_with_output().unwrap()
}

#[test]
fn dimacs_cli_executes_and_reports_real_source_frontend_state() {
    let out = run(&[], "p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let report = String::from_utf8(out.stdout).unwrap();
    assert!(report.contains("status=frontend-completed\n"));
    assert!(report.contains("ambient_unary=1110\n"));
    assert!(report.contains("variables_binary_lsb=11\n"));
    assert!(report.contains("normalized_body="));
    assert!(report.contains("instructions="));
    assert!(report.contains("peak_stack_bits="));
    assert!(
        !report.contains("count="),
        "frontend must not pose as #SAT counter"
    );
}

#[test]
fn dimacs_cli_budget_exhaustion_has_no_success_output() {
    let out = run(&["--max-steps", "4"], "p cnf 2 1\n1 0\n");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("capacity refusal"));
    assert!(
        out.stdout.is_empty(),
        "partial frontend is not a successful run"
    );
}

#[test]
fn dimacs_cli_invalid_formula_is_rejected_before_machine_execution() {
    let out = run(&[], "p cnf 1 1\n2 0\n");
    assert!(!out.status.success());
    assert!(out.stdout.is_empty());
}
