//! End-to-end CLI receipts for a deliberately optimistic replacement
//! leaf budget. A mathematical arithmetic gate is never a SAT count.
use serde_json::Value;
use std::process::Command;

fn observe(edges: &str, groups: &str, budget: &str) -> (i32, Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_appendix-basecase-gap"))
        .args([edges, groups, budget])
        .output()
        .expect("compiled appendix-basecase-gap binary");
    let parsed: Value = serde_json::from_slice(&output.stdout).unwrap();
    (output.status.code().unwrap(), parsed)
}

#[test]
fn improved_root_condition_does_not_certify_next_level() {
    let (code, value) = observe("6106906624", "64", "64");
    assert_eq!(code, 2);
    assert_eq!(value["status"], "unsupported_full_recursion");
    assert_eq!(value["published_root_width_u"], 0);
    assert_eq!(value["optimistic_packing_prefix_stages"], 1);
    assert_eq!(value["first_uncovered_active_depth"], 1);
    assert_eq!(value["hypothetical_guaranteed_leaf_depth"], 8);
    assert_eq!(
        value["stages"][0]["minimum_matching_required_edges"],
        "6106906624"
    );
    assert_eq!(value["stages"][1]["optimistic_upper_edges"], "572522496");
    assert_eq!(
        value["minimum_matching_required_edges_at_first_gap"],
        "855683929200394240"
    );
    assert_eq!(value["source_recursion_admitted"], false);
    assert_eq!(value["tensor_contraction_executed"], false);
    assert!(value["sat_count"].is_null());
}

#[test]
fn original_and_smaller_group_counts_have_opposing_depth_costs() {
    let (_, large) = observe("10000000000", "64", "64");
    let (_, small) = observe("10000000000", "7", "64");
    assert_eq!(large["first_uncovered_active_depth"], 1);
    assert_eq!(large["hypothetical_guaranteed_leaf_depth"], 8);
    assert_eq!(small["first_uncovered_active_depth"], 2);
    assert_eq!(small["hypothetical_guaranteed_leaf_depth"], 123);
    assert_eq!(
        small["stages"][0]["minimum_matching_required_edges"],
        "441784"
    );
    assert_eq!(
        small["stages"][1]["minimum_matching_required_edges"],
        "8445433465"
    );
    assert_eq!(
        small["stages"][2]["could_meet_sufficient_packing_arithmetic"],
        false
    );
    assert!(small["sat_count"].is_null());
}

#[test]
fn maximum_128_bit_graph_still_has_an_uncovered_depth() {
    let max = u128::MAX.to_string();
    let (_, large) = observe(&max, "64", "128");
    let (_, small) = observe(&max, "7", "128");
    assert_eq!(large["first_uncovered_active_depth"], 4);
    assert_eq!(large["hypothetical_guaranteed_leaf_depth"], 36);
    assert_eq!(small["first_uncovered_active_depth"], 8);
    assert_eq!(small["hypothetical_guaranteed_leaf_depth"], 544);
    assert_eq!(small["optimistic_packing_prefix_stages"], 8);
    assert_eq!(small["source_recursion_admitted"], false);
    assert!(small["sat_count"].is_null());
}

#[test]
fn already_small_root_is_zero_depth_with_no_executed_counter() {
    let (code, receipt) = observe("10000", "64", "10000");
    assert_eq!(code, 2);
    assert_eq!(receipt["hypothetical_guaranteed_leaf_depth"], 0);
    assert!(receipt["first_uncovered_active_depth"].is_null());
    assert_eq!(receipt["stages"].as_array().unwrap().len(), 0);
    assert!(receipt["sat_count"].is_null());
}

#[test]
fn malformed_arguments_fail_without_an_apparent_success_receipt() {
    let cases = [
        ["1", "64", "64"],
        ["100", "6", "64"],
        ["100", "64", "0"],
        ["abc", "64", "64"],
        ["100", "abc", "64"],
    ];
    for args in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_appendix-basecase-gap"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}
