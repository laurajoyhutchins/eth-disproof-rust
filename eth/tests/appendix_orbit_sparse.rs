//! Confirm that finite orbit-sparse packet receipts do not claim the
//! source-defined recursive counting algorithm.
use serde_json::Value;
use std::process::Command;

fn receipt(fixture: &str) -> (i32, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-orbit-sparse"))
        .arg(fixture)
        .output()
        .expect("compiled orbit-sparse witness binary");
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    (output.status.code().unwrap(), json)
}

#[test]
fn r64_balanced_layout_has_no_global_padding_overhead() {
    let (code, v) = receipt("r64-balanced");
    assert_eq!(code, 2);
    assert_eq!(v["real_edges"], 256);
    assert_eq!(v["groups"], 64);
    assert_eq!(v["a"], 2);
    assert_eq!(v["occupied_orbits"], 64);
    assert_eq!(v["packet_count"], 64);
    assert_eq!(v["padded_slots"], 256);
    assert_eq!(v["unused_slots"], 0);
    assert_eq!(v["maximum_original_degree"], 1);
    assert_eq!(v["maximum_real_symbol_ports"], 4);
    assert_eq!(v["maximum_child_edge_incidences"], 8);
    assert_eq!(v["source_packet_structural_bounds_hold"], true);
    assert_eq!(v["original_source_root_u"], 0);
    assert_eq!(v["source_sparse_tensor_semantics_proved"], false);
    assert_eq!(v["source_precision_and_routing_proved"], false);
    assert_eq!(v["recursion_executed"], false);
    assert!(v["sat_count"].is_null());
}

#[test]
fn counterexamples_separate_packet_and_symbol_balance_obligations() {
    let (_, unequal) = receipt("r2-concentrated-unequal");
    assert_eq!(unequal["source_packet_count_bound_holds"], false);
    assert_eq!(unequal["source_symbol_port_bounds_hold"], true);
    assert_eq!(unequal["orientation_imbalance_slots"], 12);
    assert_eq!(unequal["packet_count"], 4);
    assert_eq!(unequal["real_edges"], 4);
    assert_eq!(unequal["source_packet_structural_bounds_hold"], false);
    assert!(unequal["sat_count"].is_null());

    let (_, equal) = receipt("r4-concentrated-equal");
    assert_eq!(equal["source_packet_count_bound_holds"], true);
    assert_eq!(equal["source_symbol_port_bounds_hold"], false);
    assert_eq!(equal["source_child_edge_bound_holds"], false);
    assert_eq!(equal["source_packet_structural_bounds_hold"], false);
    assert!(equal["sat_count"].is_null());
}

#[test]
fn empty_orbits_are_absent_and_single_orbit_is_preserved() {
    let (_, v) = receipt("r2-one-orbit");
    assert_eq!(v["occupied_orbits"], 1);
    assert_eq!(v["real_edges"], 16);
    assert_eq!(v["packet_count"], 4);
    assert_eq!(v["source_packet_structural_bounds_hold"], true);
    assert_eq!(v["orbit_receipts"].as_array().unwrap().len(), 1);
    assert!(v["sat_count"].is_null());
}

#[test]
fn invalid_fixture_fails_before_emitting_receipt() {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-orbit-sparse"))
        .arg("not-a-fixture")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
}
