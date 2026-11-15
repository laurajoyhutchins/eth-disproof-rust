//! Inspect an intentionally optimistic *replacement* direct-leaf cutoff.
//! This never executes a tensor contraction or returns a SAT count.
use lean_eth_reference::two_adic_basecase_gap::BasecaseGapAudit;
use serde_json::json;
use std::process::ExitCode;

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        return Err(
            "usage: appendix-basecase-gap <root-edges> <groups> <direct-leaf-edge-budget>".into(),
        );
    }
    let edges = args[1]
        .parse::<u128>()
        .map_err(|_| "invalid root edge count".to_owned())?;
    let groups = args[2]
        .parse::<u32>()
        .map_err(|_| "invalid group count".to_owned())?;
    let budget = args[3]
        .parse::<u128>()
        .map_err(|_| "invalid direct-leaf budget".to_owned())?;
    let audit = BasecaseGapAudit::new(edges, groups, budget).map_err(|err| err.to_string())?;
    let stages = audit
        .stages
        .iter()
        .map(|s| {
            json!({
                "depth": s.depth,
                "optimistic_upper_edges": s.largest_possible_edges.to_string(),
                "minimum_positive_width_u": 1,
                "minimum_cumulative_a": s.cumulative_a,
                "minimum_packet_slots_l": s.minimum_packet_slots_l.map(|v| v.to_string()),
                "minimum_label_pair_classes_d": s.label_pair_classes_d.map(|v| v.to_string()),
                "minimum_degree_cap": s.minimum_degree_cap.map(|v| v.to_string()),
                "minimum_matching_required_edges": s.minimum_matching_required_edges.map(|v| v.to_string()),
                "minimum_uniform_padding_edges": s.minimum_uniform_padding_edges.map(|v| v.to_string()),
                "could_fit_source_uniform_padding": s.could_fit_source_uniform_padding,
                "could_meet_sufficient_packing_arithmetic": s.could_meet_matching_sufficient_condition
            })
        })
        .collect::<Vec<_>>();
    println!(
        "{}",
        json!({
            "method": "optimistic_two_adic_basecase_gap",
            "status": "unsupported_full_recursion",
            "root_edges": audit.root_edges.to_string(),
            "groups": audit.groups,
            "candidate_direct_leaf_edge_budget": audit.proposed_leaf_edge_budget.to_string(),
            "lambda": audit.lambda,
            "published_root_width_u": audit.published_root_width_u,
            "hypothetical_guaranteed_leaf_depth": audit.hypothetical_guaranteed_leaf_depth,
            "optimistic_packing_prefix_stages": audit.optimistic_prefix_stages,
            "first_uniform_padding_gap_depth": audit.first_uniform_padding_gap_depth,
            "optimistic_uniform_padding_prefix_stages": audit.optimistic_uniform_padding_prefix_stages,
            "upper_edges_at_first_padding_gap": audit.upper_edges_at_first_padding_gap.map(|v| v.to_string()),
            "minimum_uniform_padding_edges_at_first_gap": audit.minimum_uniform_padding_edges_at_first_gap.map(|v| v.to_string()),
            "first_uncovered_active_depth": audit.first_uncovered_active_depth,
            "upper_edges_at_first_gap": audit.upper_edges_at_first_gap.map(|v| v.to_string()),
            "minimum_matching_required_edges_at_first_gap": audit.minimum_required_edges_at_first_gap.map(|v| v.to_string()),
            "minimum_degree_cap_at_first_gap": audit.minimum_degree_cap_at_first_gap.map(|v| v.to_string()),
            "displayed_stage_limit": 12,
            "stages": stages,
            "assumptions": {
                "every_active_width_u_is_one": true,
                "degree_cap_equals_minimum_new_packet_vertex_cap_at_each_depth": true,
                "actual_child_edges_are_no_larger_than_conditional_upper_bound": true,
                "actual_child_graphs_and_degree_caps_verified": false,
                "uniform_all_label_pair_class_padding": true,
                "original_precision_and_complexity_proof_transferred": false
            },
            "source_recursion_admitted": false,
            "tensor_contraction_executed": false,
            "sat_count": null
        })
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::from(2),
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}
