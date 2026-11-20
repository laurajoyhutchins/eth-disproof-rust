//! Inspect exact *necessary* packing inequalities of a hypothetical
//! root schedule. This never executes recursion or reports a #SAT count.

use std::process::ExitCode;

use lean_eth_reference::two_adic_packing::RootPackingAudit;
use serde_json::json;

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 {
        return Err("usage: appendix-packing <edges> <groups> <root-u> <degree-cap>".into());
    }
    let edges = args[1]
        .parse::<u128>()
        .map_err(|_| "invalid edges".to_owned())?;
    let groups = args[2]
        .parse::<u32>()
        .map_err(|_| "invalid groups".to_owned())?;
    let u = args[3]
        .parse::<u32>()
        .map_err(|_| "invalid root-u".to_owned())?;
    let cap = args[4]
        .parse::<u128>()
        .map_err(|_| "invalid degree-cap".to_owned())?;
    let audit = RootPackingAudit::new(edges, groups, u, cap)
        .map_err(|error| error.to_string())?;

    println!(
        "{}",
        json!({
            "method": "hypothetical_appendix_root_packing",
            "status": "unsupported_full_recursion",
            "root_edges": audit.edges.to_string(),
            "lambda": audit.lambda,
            "groups": audit.groups,
            "root_u": audit.u,
            "candidate_degree_cap": audit.degree_cap.to_string(),
            "a": audit.a,
            "slots_l": audit.slots_l.map(|v| v.to_string()),
            "label_classes_d": audit.label_classes_d.map(|v| v.to_string()),
            "required_collision_edges": audit.required_edges_collision.map(|v| v.to_string()),
            "matching_potential_required_edges": audit.matching_potential_required_edges().map(|v| v.to_string()),
            "matching_potential_packing_holds": audit.matching_potential_packing_holds(),
            "matching_potential_uses_certified_degree": false,
            "matching_packing_arithmetic_holds": audit.matching_potential_packing_holds(),
            "unavoidable_minimum_root_edges": audit.minimum_root_edges_any_degree_cap().map(|v| v.to_string()),
            "required_slot_edges": audit.required_edges_slots.map(|v| v.to_string()),
            "required_packet_degree": audit.required_new_degree.map(|v| v.to_string()),
            "packing_arithmetic_holds": audit.packet_inequalities_hold(),
            "original_child_shrink_bound_holds": audit.original_child_shrink_bound_holds(),
            "source_asymptotic_u_bound_holds": audit.source_asymptotic_u_bound_holds(),
            "published_degree_envelope_obstructed": audit.published_degree_envelope_obstructed(),
            "published_degree_envelope_obstructs_matching_lemma": audit.published_envelope_obstructs_matching_lemma(),
            "source_degree_invariant_verified": false,
            "interpolation_precision_verified": false,
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
