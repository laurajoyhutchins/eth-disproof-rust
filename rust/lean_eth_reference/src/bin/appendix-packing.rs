//! Inspect exact *necessary* packing inequalities of a hypothetical
//! root schedule. This never executes recursion or reports a #SAT count.
use lean_eth_reference::two_adic_packing::RootPackingAudit;
use serde_json::json;
use std::process::ExitCode;

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
    let a = RootPackingAudit::new(edges, groups, u, cap).map_err(|e| e.to_string())?;

    println!(
        "{}",
        json!({
            "method": "hypothetical_appendix_root_packing",
            "status": "unsupported_full_recursion",
            "root_edges": a.edges.to_string(),
            "lambda": a.lambda,
            "groups": a.groups,
            "root_u": a.u,
            "candidate_degree_cap": a.degree_cap.to_string(),
            "a": a.a,
            "slots_l": a.slots_l.map(|v| v.to_string()),
            "label_classes_d": a.label_classes_d.map(|v| v.to_string()),
            "required_collision_edges": a.required_edges_collision.map(|v| v.to_string()),
            "unavoidable_minimum_root_edges": a.minimum_root_edges_any_degree_cap().map(|v| v.to_string()),
            "required_slot_edges": a.required_edges_slots.map(|v| v.to_string()),
            "required_packet_degree": a.required_new_degree.map(|v| v.to_string()),
            "packing_arithmetic_holds": a.packet_inequalities_hold(),
            "original_child_shrink_bound_holds": a.original_child_shrink_bound_holds(),
            "source_asymptotic_u_bound_holds": a.source_asymptotic_u_bound_holds(),
            "published_degree_envelope_obstructed": a.published_degree_envelope_obstructed(),
            "source_degree_invariant_verified": false,
            "interpolation_precision_verified": false,
            "active_recursion_executed": false,
            "sat_count": null
        })
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::from(2), // An arithmetic pass is never an algorithm pass.
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(2)
        }
    }
}
