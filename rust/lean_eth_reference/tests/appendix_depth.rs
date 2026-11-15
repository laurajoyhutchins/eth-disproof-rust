//! Regressions for a hypothetical schedule receipt. None of the
//! cases is permitted to report a SAT count.
use serde_json::Value;
use std::process::Command;

fn run(edges: &str, groups: &str, cap: &str, widths: &str) -> (i32, Value) {
    let result = Command::new(env!("CARGO_BIN_EXE_appendix-depth"))
        .args([edges, groups, cap, widths])
        .output()
        .expect("appendix-depth binary");
    let receipt: Value = serde_json::from_slice(&result.stdout).unwrap();
    (result.status.code().unwrap(), receipt)
}

#[test]
fn improved_root_packing_still_produces_only_leaf_children() {
    let (status, receipt) = run("6106906624", "64", "8", "1,1,1");
    assert_eq!(status, 2);
    assert_eq!(receipt["lambda"], 33);
    assert_eq!(receipt["leaf_edge_exponent"], "1221381325");
    assert_eq!(receipt["stages"][0]["matching_arithmetic_possible"], true);
    assert_eq!(receipt["stages"][1]["reason"], "guaranteed_leaf");
    assert_eq!(receipt["stages"][2]["reason"], "guaranteed_leaf");
    assert_eq!(receipt["stages"][0]["published_width_u"], 0);
    assert_eq!(receipt["status"], "unsupported_full_recursion");
    assert_eq!(receipt["tensor_contraction_executed"], false);
    assert!(receipt["sat_count"].is_null());
}

#[test]
fn second_active_level_requires_far_larger_root_even_after_packing_change() {
    let just_above_power = ((1u128 << 120) + 1).to_string();
    let (_, after) = run(&just_above_power, "64", "32", "1,1,1");
    assert_eq!(after["lambda"], 121);
    assert_eq!(after["stages"][1]["could_be_active"], true);
    assert_eq!(after["stages"][2]["reason"], "guaranteed_leaf");

    let power = (1u128 << 120).to_string();
    let (_, before) = run(&power, "64", "32", "1,1,1");
    assert_eq!(before["lambda"], 120);
    assert_eq!(before["stages"][1]["reason"], "guaranteed_leaf");
}

#[test]
fn maximum_u128_still_cannot_produce_third_active_stage() {
    let (code, receipt) = run(&u128::MAX.to_string(), "64", "32", "1,1,1");
    assert_eq!(code, 2);
    assert_eq!(receipt["stages"][0]["matching_arithmetic_possible"], true);
    assert_eq!(receipt["stages"][1]["matching_arithmetic_possible"], true);
    assert_eq!(receipt["stages"][2]["reason"], "guaranteed_leaf");
    assert_eq!(
        receipt["leaf_edge_exponent"],
        "30934760629176223951215873402888019224"
    );
    assert_eq!(receipt["full_recursion_admitted"], false);
    assert!(receipt["sat_count"].is_null());
}

#[test]
fn rejects_invalid_without_printing_success() {
    for args in [
        ["1", "64", "8", "1,1"],
        ["100", "6", "8", "1,1"],
        ["100", "64", "0", "1,1"],
        ["100", "64", "8", ""],
        ["100", "64", "8", "1,-1"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_appendix-depth"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}
