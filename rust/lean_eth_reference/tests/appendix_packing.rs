//! Ensure an arithmetic candidate can never be mistaken for an executed
//! original-source contraction.
use serde_json::Value;
use std::process::Command;

fn observe(arguments: &[&str]) -> (i32, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-packing"))
        .args(arguments)
        .output()
        .expect("compiled appendix-packing binary");
    let receipt: Value = serde_json::from_slice(&output.stdout).unwrap();
    (output.status.code().unwrap(), receipt)
}

#[test]
fn degree_bounded_candidate_is_a_nonterminal_refusal() {
    let (code, value) = observe(&["4503599627370496", "64", "1", "8"]);
    assert_eq!(code, 2);
    assert_eq!(value["status"], "unsupported_full_recursion");
    assert_eq!(value["packing_arithmetic_holds"], true);
    assert_eq!(value["original_child_shrink_bound_holds"], true);
    assert_eq!(value["source_asymptotic_u_bound_holds"], false);
    assert_eq!(value["published_degree_envelope_obstructed"], true);
    assert_eq!(value["required_collision_edges"], "4503599627370496");
    assert_eq!(value["unavoidable_minimum_root_edges"], "4503599627370496");
    assert_eq!(value["source_degree_invariant_verified"], false);
    assert_eq!(value["active_recursion_executed"], false);
    assert!(value["sat_count"].is_null());
}

#[test]
fn published_envelope_cannot_be_bypassed_with_an_optimistic_cap() {
    let (_, value) = observe(&["1000000", "64", "1", "8"]);
    assert_eq!(value["packing_arithmetic_holds"], false);
    assert_eq!(value["published_degree_envelope_obstructed"], true);
    assert!(value["sat_count"].is_null());
}

#[test]
fn invalid_inputs_are_not_json_success() {
    for args in [
        ["0", "64", "1", "8"],
        ["1", "1", "1", "8"],
        ["1", "64", "0", "8"],
        ["1", "64", "1", "0"],
        ["abc", "64", "1", "8"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_appendix-packing"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}
