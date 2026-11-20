//! Fail-closed preflight for the paper's fixed appendix recursion schedule.
//! Exit 2 denotes refusal; the output never contains a #SAT count.

use std::process::ExitCode;

use lean_eth_reference::two_adic_admission::{NECESSARY_ROOT_LAMBDA, ScheduleAudit};
use serde_json::json;

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        return Err("usage: appendix-admission <positive tensor-network edge count>".into());
    }
    let edges = args[1]
        .parse::<u128>()
        .map_err(|_| "invalid positive tensor-network edge count".to_owned())?;
    let audit = ScheduleAudit::new(edges).map_err(|error| error.to_string())?;
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
    Ok(())
}

fn main() -> ExitCode {
    if let Err(error) = run() {
        eprintln!("{error}");
    }
    // An arithmetic receipt is not an execution of the original algorithm.
    ExitCode::from(2)
}
