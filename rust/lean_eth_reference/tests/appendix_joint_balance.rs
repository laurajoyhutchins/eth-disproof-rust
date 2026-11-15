//! CLI refuses SAT claims and reports both independent structural
//! conditions for the deterministic joint symbol/orbit labeling.
use serde_json::Value;
use std::process::Command;

fn run(fixture: &str) -> (i32, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-joint-balance"))
        .arg(fixture)
        .output()
        .expect("compiled joint-balancing binary");
    let value: Value = serde_json::from_slice(&output.stdout).unwrap();
    (output.status.code().unwrap(), value)
}

#[test]
fn shifted_matching_recovers_low_waste_without_losing_symbol_balance() {
    let (code, receipt) = run("r4-shifted");
    assert_eq!(code, 2);
    assert_eq!(receipt["real_edges"], 32);
    assert_eq!(receipt["right_coordinate_shifts"], serde_json::json!([3, 3]));
    assert_eq!(receipt["initial_sparse_packet_count"], 32);
    assert_eq!(receipt["final_sparse_packet_count"], 8);
    assert_eq!(receipt["initial_unused_slots"], 96);
    assert_eq!(receipt["final_unused_slots"], 0);
    assert_eq!(receipt["source_uniform_packets_at_final_labels"], "512");
    assert_eq!(receipt["greedy_port_bound_sufficient_for_source"], true);
    assert_eq!(receipt["source_packet_bound_holds"], true);
    assert_eq!(receipt["source_symbol_port_bounds_hold"], true);
    assert_eq!(receipt["structurally_admitted"], true);
    assert_eq!(receipt["source_u0"], 0);
    assert_eq!(receipt["source_tensor_deformation_proved"], false);
    assert_eq!(receipt["source_recursion_executed"], false);
    assert!(receipt["sat_count"].is_null());
}

#[test]
fn large_r_witness_retains_64_packets_instead_of_full_uniform_class_space() {
    let (code, receipt) = run("r64-diagonal");
    assert_eq!(code, 2);
    assert_eq!(receipt["real_edges"], 256);
    assert_eq!(receipt["initial_sparse_packet_count"], 64);
    assert_eq!(receipt["final_sparse_packet_count"], 64);
    assert_eq!(receipt["final_unused_slots"], 0);
    assert_eq!(receipt["source_uniform_packets_at_final_labels"], "16777216");
    assert_eq!(receipt["maximum_actual_row_symbol_ports"], 4);
    assert_eq!(receipt["maximum_actual_column_symbol_ports"], 4);
    assert_eq!(receipt["structurally_admitted"], true);
    assert_eq!(receipt["source_weighted_modes_proved"], false);
    assert!(receipt["sat_count"].is_null());
}

#[test]
fn provable_star_obstruction_fails_before_emitting_success_receipt() {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-joint-balance"))
        .arg("r4-star")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("unavoidable per-symbol port overload"));
}

#[test]
fn invalid_fixture_is_not_an_algorithm_execution() {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-joint-balance"))
        .arg("unknown")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
}
