//! The sufficient theorem checker and tiny exact conditional-expectation
//! witness cannot be misrepresented as a recursive counting program.
use serde_json::Value;
use std::process::Command;

fn invoke(args: &[&str]) -> (i32, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-joint-potential"))
        .args(args)
        .output()
        .expect("joint potential CLI binary exists");
    let value: Value = serde_json::from_slice(&output.stdout).unwrap();
    (output.status.code().unwrap(), value)
}

#[test]
fn r64_mathematical_sufficient_threshold_is_exact_and_not_an_execution() {
    let (code, value) = invoke(&["audit", "4205841067", "64", "2", "8", "8"]);
    assert_eq!(code, 2);
    assert_eq!(value["minimum_edges_for_joint_sufficiency"], "4205841067");
    assert_eq!(value["minimum_edges_for_port_cap"], "18432");
    assert_eq!(value["minimum_edges_for_packet_cap"], "4205841067");
    assert_eq!(value["joint_sufficient_if_actual_degree_certified"], true);
    assert_eq!(value["degree_bound_verified_from_graph"], false);
    assert_eq!(value["actual_graph_labeled"], false);
    assert_eq!(value["source_recursion_executed"], false);
    assert!(value["sat_count"].is_null());

    let (_, below) = invoke(&["audit", "4205841066", "64", "2", "8", "8"]);
    assert_eq!(below["arithmetic_port_sufficient"], true);
    assert_eq!(below["arithmetic_packet_sufficient"], false);
    assert_eq!(below["joint_sufficient_if_actual_degree_certified"], false);
    assert!(below["sat_count"].is_null());
}

#[test]
fn exact_bounded_joint_potential_derandomization_emits_real_witness() {
    for mask in 1..16 {
        let name = mask.to_string();
        let (code, value) = invoke(&["tiny-mask", &name]);
        assert_eq!(code, 2);
        assert_eq!(value["mask"], mask);
        assert_eq!(value["conditional_average_identities_verified"], true);
        assert_eq!(value["pair_load_bound_verified"], true);
        assert_eq!(value["source_recursion_executed"], false);
        assert!(value["sat_count"].is_null());
        let initial = value["exact_initial_potential_numerator"]
            .as_str()
            .unwrap()
            .parse::<u128>()
            .unwrap();
        let final_value = value["exact_final_potential_numerator"]
            .as_str()
            .unwrap()
            .parse::<u128>()
            .unwrap();
        let denominator = value["positive_common_denominator"]
            .as_str()
            .unwrap()
            .parse::<u128>()
            .unwrap();
        assert_eq!(initial, 2 * denominator);
        assert!(final_value <= initial);
    }
}

#[test]
fn malformed_and_unrepresentable_inputs_refuse_before_receipt() {
    for args in [
        vec!["audit", "0", "64", "2", "8", "8"],
        vec!["audit", "100", "64", "2", "101", "101"],
        vec!["audit", "100", "64", "2", "8", "7"],
        vec!["audit", "100", "invalid", "2", "8", "8"],
        vec!["tiny-mask", "0"],
        vec!["tiny-mask", "16"],
        vec!["tiny-mask", "garbage"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_appendix-joint-potential"))
            .args(&args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}
