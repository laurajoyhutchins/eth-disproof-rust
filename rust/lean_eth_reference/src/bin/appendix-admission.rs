//! Fail-closed preflight for the paper's fixed appendix recursion schedule.
//! Exit 2 denotes refusal; the output never contains a #SAT count.
use lean_eth_reference::two_adic_admission::{NECESSARY_ROOT_LAMBDA, ScheduleAudit};
use serde_json::json;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: appendix-admission <positive tensor-network edge count>");
        return ExitCode::from(2);
    }
    let edges = match args[1].parse::<u128>() {
        Ok(edges) => edges,
        Err(_) => {
            eprintln!("invalid positive tensor-network edge count");
            return ExitCode::from(2);
        }
    };
    let audit = match ScheduleAudit::new(edges) {
        Ok(audit) => audit,
        Err(err) => {
            eprintln!("{err}");
            return ExitCode::from(2);
        }
    };
    // Decimal strings preserve exactness for counts above JavaScript's
    // 53-bit integer range. This is an admission audit, not execution.
    println!(
        "{}",
        json!({
            "method": "fixed_appendix_two_adic_schedule",
            "role": "necessary_condition_preflight",
            "status": "refused",
            "reason": audit.refusal_reason(),
            "edges": audit.edges.to_string(),
            "lambda": audit.lambda,
            "root_u": audit.root_u,
            "extension_degree": audit.extension_degree,
            "leaf_edge_exponent": audit.leaf_threshold.map(|n| n.to_string()),
            "necessary_root_lambda": NECESSARY_ROOT_LAMBDA.to_string(),
            "active_recursion_executed": false,
            "sat_count": null
        })
    );
    ExitCode::from(2)
}
