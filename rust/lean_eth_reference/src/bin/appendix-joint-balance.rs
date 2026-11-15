//! Fail-closed simultaneous port + orbit-label balancing receipt.
//! No SAT count, field tensors, or source recursion is executed.
use lean_eth_reference::two_adic_joint_balance::construct_joint_balanced_bounded;
use lean_eth_reference::two_adic_packet_layout::BipartiteEdge;
use serde_json::json;
use std::process::ExitCode;

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        return Err("usage: appendix-joint-balance <r4-shifted|r64-diagonal|r4-star>".into());
    }
    let (edges, left_count, right_count, r, a, cap, passes) = match args[1].as_str() {
        "r4-shifted" => (
            (0..32)
                .map(|left| BipartiteEdge {
                    left,
                    right: (left / 4) * 4 + ((left + 1) % 4),
                })
                .collect::<Vec<_>>(),
            32,
            32,
            4,
            2,
            8,
            3,
        ),
        "r64-diagonal" => (
            (0..256)
                .map(|i| BipartiteEdge { left: i, right: i })
                .collect::<Vec<_>>(),
            256,
            256,
            64,
            2,
            8,
            2,
        ),
        "r4-star" => (
            (0..16)
                .map(|right| BipartiteEdge { left: 0, right })
                .collect::<Vec<_>>(),
            1,
            16,
            4,
            2,
            16,
            3,
        ),
        _ => return Err("unsupported joint balance fixture".into()),
    };
    let receipt = construct_joint_balanced_bounded(
        &edges, left_count, right_count, r, a, cap, passes,
    )
    .map_err(|error| error.to_string())?;
    let lambda = usize::BITS - (edges.len() - 1).leading_zeros();
    let layout = &receipt.final_layout;
    println!(
        "{}",
        json!({
            "method": "deterministic_joint_orbit_port_balancing",
            "fixture": args[1],
            "status": "unsupported_full_source_recursion",
            "groups": r,
            "a": a,
            "real_edges": edges.len(),
            "maximum_original_degree": receipt.maximum_degree,
            "greedy_max_symbol_port_bound_numerator": receipt.greedy_port_bound_numerator,
            "greedy_max_symbol_port_bound_denominator": r,
            "greedy_port_bound_sufficient_for_source": receipt.greedy_port_sufficient_for_source_limit,
            "necessary_max_degree_port_bound": receipt.vertex_degree_necessary_port_bound,
            "maximum_actual_row_symbol_ports": receipt.maximum_row_port,
            "maximum_actual_column_symbol_ports": receipt.maximum_column_port,
            "right_coordinate_shifts": receipt.right_coordinate_shifts,
            "layouts_evaluated": receipt.layouts_evaluated,
            "coordinate_passes": receipt.coordinate_passes,
            "initial_sparse_packet_count": receipt.initial_packets,
            "final_sparse_packet_count": receipt.final_packets,
            "initial_unused_slots": receipt.initial_unused_slots,
            "final_unused_slots": layout.unused_slots,
            "orientation_imbalance_slots": layout.orientation_imbalance_slots,
            "copy_rounding_slots": layout.rounding_slots,
            "source_uniform_packets_at_final_labels": receipt.uniform_packets_at_final_labels.map(|v| v.to_string()),
            "source_packet_bound_holds": layout.packet_count_bound_holds,
            "source_symbol_port_bounds_hold": layout.symbol_port_bounds_hold,
            "source_child_edge_bound_holds": layout.child_edge_bound_holds,
            "structurally_admitted": receipt.structurally_admitted(),
            "source_u0": lambda / 131_072,
            "source_tensor_deformation_proved": false,
            "source_weighted_modes_proved": false,
            "source_precision_schedule_proved": false,
            "source_recursion_executed": false,
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
