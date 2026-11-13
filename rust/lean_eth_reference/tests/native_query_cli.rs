//! CLI smoke test: physical execution and fail-closed errors, not a real query oracle.
use std::fs;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use lean_eth_reference::native_query_table::{QUERY_SOURCE_BLOB, SOURCE_COMMIT};

static UNIQUE: AtomicUsize = AtomicUsize::new(0);

fn exercise(code: &str, fixture: &str, steps: u64, memory: usize) -> std::process::Output {
    let id = UNIQUE.fetch_add(1, Ordering::Relaxed);
    let temp = std::env::temp_dir().join(format!("lean-query-cli-{}-{id}", std::process::id()));
    fs::create_dir_all(&temp).unwrap();
    let table_path = temp.join("table.txt");
    let fixture_path = temp.join("fixture.txt");
    fs::write(&table_path, code).unwrap();
    fs::write(&fixture_path, fixture).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_native_query"))
        .args([
            table_path.to_str().unwrap(),
            fixture_path.to_str().unwrap(),
            &steps.to_string(),
            &memory.to_string(),
        ])
        .output()
        .unwrap();
    fs::remove_dir_all(&temp).unwrap();
    result
}

fn table() -> String {
    format!(
        "PIN|query|{SOURCE_COMMIT}|{QUERY_SOURCE_BLOB}\nPROGRAM|query|40|896|3|0|330|323\nCODE|query|0|set:0:1:1\nCODE|query|1|push:323:0:2\nCODE|query|2|halt\nEND|query|3\n"
    )
}

#[test]
fn admitted_tiny_machine_executes_with_physical_fixture() {
    let result = exercise(&table(), "STACK|330|101\nSTACK|323|\nREG|1|1\n", 100, 100);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(String::from_utf8(result.stdout).unwrap(), "HALT|3|4|1\n");
}

#[test]
fn malformed_table_and_resource_refusal_never_print_success() {
    let bad_table = table().replace("END|query|3", "END|query|2");
    let cases = [
        exercise(&bad_table, "STACK|330|101\n", 100, 100),
        exercise(&table(), "STACK|330|101\n", 2, 100),
        exercise(&table(), "STACK|330|101\n", 100, 3),
        exercise(&table(), "STACK|330|0\nSTACK|330|1\n", 100, 100),
    ];
    for result in cases {
        assert!(!result.status.success());
        assert!(result.stdout.is_empty(), "refusal must not print a result");
    }
}
