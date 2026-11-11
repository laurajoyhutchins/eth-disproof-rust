//! End-to-end clap CLI contract, with all three claims kept separate.
use std::fs;
use std::io::Write;
use std::process::{Command, Output, Stdio};

fn run(args: &[&str], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_eth"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn help_is_structured_and_tells_the_truth() {
    let output = run(&["--help"], "");
    assert!(output.status.success());
    let help = String::from_utf8(output.stdout).unwrap();
    for command in ["frontend", "terminal-count", "oracle"] {
        assert!(help.contains(command));
    }
    assert!(help.contains("exponential") || help.contains("Exponential"));
    assert!(run(&[], "").status.code() != Some(0));
}

#[test]
fn frontend_subcommand_executes_physical_machine_without_counting() {
    let input = "p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n";
    let modern = run(&["frontend"], input);
    assert!(modern.status.success(), "{modern:?}");
    let stdout = String::from_utf8(modern.stdout).unwrap();
    assert!(stdout.contains("status=frontend-completed"));
    assert!(stdout.contains("ambient_unary=1110\n"));
    assert!(stdout.contains("variables_binary_lsb=11\n"));
    assert!(!stdout.contains("count="));
}

#[test]
fn oracle_is_explicitly_exponential_and_bounded() {
    let input = "p cnf 3 2\n1 2 0\n1 3 0\n";
    let modern = run(&["oracle"], input);
    assert!(modern.status.success(), "{modern:?}");
    assert!(String::from_utf8_lossy(&modern.stdout).contains("count=5"));
    let invalid = run(&["oracle", "--max-variables", "21"], input);
    assert!(!invalid.status.success());
    assert!(invalid.stdout.is_empty());
}

#[test]
fn terminal_count_preserves_source_native_success_and_refusal() {
    let input = "p cnf 3 0\n";
    let modern = run(&["terminal-count"], input);
    assert!(modern.status.success(), "{modern:?}");
    let stdout = String::from_utf8_lossy(&modern.stdout);
    assert!(stdout.contains("status=terminal-count-complete\n"));
    assert!(stdout.contains("count=8\n"));
    assert!(stdout.contains("source_instructions="));
    assert!(stdout.contains("resource_basis=BitProgram_source_instructions_not_TM2_microsteps"));

    let unsupported = run(&["terminal-count"], "p cnf 1 1\n1 0\n");
    assert!(!unsupported.status.success());
    assert!(unsupported.stdout.is_empty());
    assert!(String::from_utf8_lossy(&unsupported.stderr).contains("unimplemented"));
}

#[test]
fn explicit_paths_budgets_and_bad_options_fail_closed() {
    let input = "p cnf 0 0\n";
    let path = std::env::temp_dir().join(format!(
        "eth-clap-{}-{}.cnf",
        std::process::id(),
        "explicit-path"
    ));
    fs::write(&path, input).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_eth"))
        .arg("oracle")
        .arg(&path)
        .output()
        .unwrap();
    fs::remove_file(&path).unwrap();
    assert!(result.status.success(), "{result:?}");
    assert!(String::from_utf8_lossy(&result.stdout).contains("count=1"));

    for flags in [
        vec!["frontend", "--max-steps", "0"],
        vec!["frontend", "--max-stack-bits", "0"],
        vec!["terminal-count", "--max-steps", "0"],
        vec!["oracle", "--unknown-option"],
        vec!["does-not-exist"],
    ] {
        let result = run(&flags, input);
        assert!(!result.status.success(), "{flags:?}");
        assert!(result.stdout.is_empty());
    }
    let refused = run(&["frontend", "--max-steps", "4"], input);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
}
