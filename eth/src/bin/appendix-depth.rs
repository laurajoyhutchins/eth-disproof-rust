//! Fail-closed exact multi-level arithmetic receipt for hypothetical
//! appendix tensor schedules. No SAT count or tensor computation.
use lean_eth_reference::two_adic_depth::DepthAudit;
use serde_json::json;
use std::process::ExitCode;

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 {
        return Err(
            "usage: appendix-depth <root-edges> <groups> <candidate-degree-cap> <u0,u1,...>".into(),
        );
    }
    let edges = args[1]
        .parse::<u128>()
        .map_err(|_| "invalid edges".to_owned())?;
    let groups = args[2]
        .parse::<u32>()
        .map_err(|_| "invalid groups".to_owned())?;
    let degree = args[3]
        .parse::<u128>()
        .map_err(|_| "invalid degree cap".to_owned())?;
    let widths = args[4]
        .split(',')
        .map(|part| {
            part.parse::<u32>()
                .map_err(|_| "invalid packet width".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let audit =
        DepthAudit::new(edges, groups, degree, &widths).map_err(|error| error.to_string())?;
    let stages = audit
        .stages
        .iter()
        .map(|s| {
            json!({
                "depth": s.depth,
                "candidate_width_u": s.width_u,
                "published_width_u": s.source_fixed_width_u,
                "a": s.cumulative_a,
                "slots_l": s.slots_l.map(|v| v.to_string()),
                "label_classes_d": s.label_classes_d.map(|v| v.to_string()),
                "max_possible_edges_if_ancestors_pack": s.maximum_possible_edges.to_string(),
                "matching_required_edges": s.matching_required_edges.map(|v| v.to_string()),
                "packet_degree_bound_holds": s.degree_cap_sufficient_for_packet_vertices,
                "could_be_active": s.potentially_active,
                "matching_arithmetic_possible": s.matching_arithmetic_possible,
                "reason": s.reason
            })
        })
        .collect::<Vec<_>>();
    println!(
        "{}",
        json!({
            "method": "hypothetical_two_adic_depth_gate",
            "status": "unsupported_full_recursion",
            "root_edges": audit.root_edges.to_string(),
            "lambda": audit.lambda,
            "leaf_edge_exponent": audit.root_leaf_threshold.to_string(),
            "groups": audit.groups,
            "candidate_degree_cap": audit.proposed_maximum_degree.to_string(),
            "child_fraction_numerator": 6,
            "child_fraction_denominator": audit.groups,
            "child_upper_bounds_conditional_on_packing": true,
            "stages": stages,
            "full_recursion_admitted": false,
            "degree_invariant_verified": false,
            "precision_schedule_verified": false,
            "tensor_contraction_executed": false,
            "sat_count": null
        })
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::from(2),
        Err(message) => {
            eprintln!("{message}");
            ExitCode::from(2)
        }
    }
}
