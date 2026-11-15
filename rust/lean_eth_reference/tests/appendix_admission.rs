//! Integration test: impossible fixed-schedule root must never be reported
//! as a successful recursive count or as measured contraction work.
use serde_json::Value;
use std::process::Command;

#[test]
fn reported_million_edge_refusal_is_exact_and_not_a_count() {
    let out = Command::new(env!("CARGO_BIN_EXE_appendix-admission"))
        .arg("1000000")
        .output()
        .expect("appendix admission executable");
    assert_eq!(out.status.code(), Some(2));
    assert!(out.stderr.is_empty());
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(report["status"], "refused");
    assert_eq!(report["reason"], "root_packet_width_zero");
    assert_eq!(report["edges"], "1000000");
    assert_eq!(report["lambda"], 20);
    assert_eq!(report["root_u"], 0);
    assert_eq!(report["extension_degree"], 80);
    assert_eq!(report["leaf_edge_exponent"], "250000");
    assert_eq!(report["active_recursion_executed"], false);
    assert!(report["sat_count"].is_null());
}

#[test]
fn no_large_integer_rounding_and_no_invalid_success() {
    let max_edges = u128::MAX.to_string();
    let out = Command::new(env!("CARGO_BIN_EXE_appendix-admission"))
        .arg(&max_edges)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    let report: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(report["edges"].as_str(), Some(max_edges.as_str()));
    assert_eq!(report["lambda"], 128);
    assert_eq!(report["root_u"], 0);
    assert!(report["sat_count"].is_null());

    for bad in ["0", "-1", "abc"] {
        let out = Command::new(env!("CARGO_BIN_EXE_appendix-admission"))
            .arg(bad)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
        assert!(out.stdout.is_empty());
    }
}
