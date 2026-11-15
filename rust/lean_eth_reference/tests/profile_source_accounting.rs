//! Acceptance of source-defined stage costs and the nonterminal refusal.
//! An executable observer is not a substitute for the absent counting stage.

use std::process::Command;

const HEADER: &str = "case,opcode,transitions,elapsed_ns,allocation_calls,reallocation_calls,requested_bytes,peak_stack_bits,peak_stack_capacity_bits,max_integer_bits";

fn profile(mode: &str) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_profile-full-machine"))
        .arg(mode)
        .output()
        .expect("execute actual source program observer");
    assert!(
        output.status.success(),
        "{mode}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("observer emits UTF-8")
}

fn instruction_totals(csv: &str, case: &str, stage: &str) -> u64 {
    csv.lines()
        .filter(|line| !line.starts_with('#') && !line.starts_with("case,"))
        .map(|line| line.split(',').collect::<Vec<_>>())
        .filter(|row| row.first().copied() == Some(&format!("{case}_{stage}")[..]))
        .map(|row| {
            assert_eq!(row.len(), 10, "each accounting row has a stable schema");
            assert_eq!(
                row[9], "NA",
                "source BitProgram has no integer coefficient observation"
            );
            row[2].parse::<u64>().expect("source instruction tally")
        })
        .sum()
}

#[test]
fn nonterminal_source_accounting_preserves_refusal_and_actual_work() {
    let output = profile("--nonterminal");
    assert!(output.lines().next() == Some(HEADER));
    for case in ["two_unit", "three_two_clause"] {
        let frontend = instruction_totals(&output, case, "frontend");
        let ready = instruction_totals(&output, case, "terminal");
        assert!(frontend > 0 && ready > 0, "source stages must execute");
        let marker = format!(
            "# case={case} status=unsupported_nonterminal_count source_steps={} count=NA",
            frontend + ready
        );
        assert!(output.lines().any(|line| line == marker));
    }
    assert!(!output.contains("status=terminal-count-complete"));
    assert!(!output.contains("status=nonterminal-count-complete"));
    assert!(!output.contains("count=5"));
    assert!(!output.contains("three_two_clause_transfer_adapter"));
    assert!(!output.contains("three_two_clause_answer"));
}

#[test]
fn terminal_source_accounting_replays_all_four_stages() {
    let output = profile("--terminal");
    assert!(output.lines().next() == Some(HEADER));
    for case in [
        "zero_empty",
        "three_empty",
        "three_empty_clause",
        "two_tautology",
    ] {
        for stage in ["frontend", "terminal", "transfer_adapter", "answer"] {
            assert!(
                instruction_totals(&output, case, stage) > 0,
                "{case}/{stage} must execute"
            );
        }
    }
}

#[test]
fn observer_mode_requires_an_explicit_supported_boundary() {
    let output = Command::new(env!("CARGO_BIN_EXE_profile-full-machine"))
        .arg("--source-defined-whole-counter")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains("usage: profile-full-machine"));
}
