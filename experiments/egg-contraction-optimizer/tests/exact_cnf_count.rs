use std::io::Write;
use std::process::{Command, Stdio};

fn run(input: &str, extra: &[&str]) -> (bool, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_exact-cnf-count"));
    cmd.args(extra).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("binary starts");
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let output = child.wait_with_output().unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn closed_dimacs_count_exposes_a_replay_receipt() {
    let (ok, stdout, stderr) = run(
        "c equality plus a unit\np cnf 4 3\n1 -2 0\n-1 2 0\n3 0\n",
        &[],
    );
    assert!(ok, "{stderr}");
    assert!(stdout.contains(r#""status":"exact""#), "{stdout}");
    assert!(stdout.contains(r#""count":"4""#), "{stdout}");
    assert!(stdout.contains(r#""equations":2"#), "{stdout}");
    assert!(stdout.contains(r#""verification":"independent-rust-replay""#));
    assert!(stdout.contains(r#""process_peak_rss_kib":"#));
}

#[test]
fn unsupported_is_nonzero_and_never_masquerades_as_an_answer() {
    let (ok, stdout, stderr) = run("p cnf 3 1\n1 2 3 0\n", &[]);
    assert!(!ok);
    assert!(stdout.is_empty());
    assert!(stderr.contains(r#""status":"refused""#), "{stderr}");
    assert!(stderr.contains(r#""code":"unsupported""#));
    assert!(stderr.contains(r#""stage":"recognize""#));
}

#[test]
fn user_resource_limit_is_observable() {
    let (ok, stdout, stderr) = run("p cnf 4 0\n", &["--max-variables", "2"]);
    assert!(!ok);
    assert!(stdout.is_empty());
    assert!(stderr.contains(r#""code":"resource""#), "{stderr}");
}
