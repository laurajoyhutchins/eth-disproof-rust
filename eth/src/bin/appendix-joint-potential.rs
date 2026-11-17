//! Fail-closed quantitative audit and tiny exact joint-potential witness.
//! No original source schedule, tensor recursion or SAT count is executed.
use lean_eth_reference::matching_packing::BipartiteGraph;
use lean_eth_reference::two_adic_joint_derandomize::construct_joint_potential_labels_small;
use lean_eth_reference::two_adic_joint_potential::JointPotentialArithmetic;
use serde_json::json;
use std::process::ExitCode;

fn parse_u128(s: &str, name: &str) -> Result<u128, String> {
    s.parse::<u128>().map_err(|_| format!("invalid {name}"))
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    match args.as_slice() {
        [_, mode, edges, r, a, degree, cap] if mode == "audit" => {
            let m = parse_u128(edges, "edges")?;
            let r = r.parse::<u32>().map_err(|_| "invalid groups")?;
            let a = a.parse::<u32>().map_err(|_| "invalid coordinates")?;
            let delta = parse_u128(degree, "actual degree bound")?;
            let cap = parse_u128(cap, "packet degree cap")?;
            let audit = JointPotentialArithmetic::new(m, r, a, delta, cap)
                .map_err(|e| e.to_string())?;
            println!(
                "{}",
                json!({
                    "method": "combined_matching_and_port_potential_sufficient_threshold",
                    "status": "arithmetic_hypothesis_only",
                    "edges": audit.root_edges.to_string(),
                    "groups": audit.groups,
                    "coordinates": audit.coordinates,
                    "proposed_actual_maximum_degree": audit.proposed_actual_maximum_degree.to_string(),
                    "degree_bound_verified_from_graph": false,
                    "packet_degree_cap": audit.proposed_maximum_degree_cap.to_string(),
                    "alphabet_per_side": audit.labels_per_shore.map(|v| v.to_string()),
                    "pair_classes_d": audit.ordered_label_classes_d.map(|v| v.to_string()),
                    "slots_l": audit.packet_slots_l.map(|v| v.to_string()),
                    "unordered_orbits_o": audit.all_coordinate_orbits_o.map(|v| v.to_string()),
                    "matching_bound_k": audit.greedy_matching_count_bound_k.map(|v| v.to_string()),
                    "pair_log_ceiling": audit.pair_log_ceiling,
                    "port_log_ceiling": audit.port_log_ceiling,
                    "minimum_edges_for_packet_cap": audit.minimum_edges_for_packet_cap.map(|v| v.to_string()),
                    "minimum_edges_for_port_cap": audit.minimum_edges_for_port_cap.map(|v| v.to_string()),
                    "minimum_edges_for_joint_sufficiency": audit.minimum_edges_for_both.map(|v| v.to_string()),
                    "source_degree_cap_holds": audit.degree_cap_covers_source_packets,
                    "arithmetic_packet_sufficient": audit.source_packet_arithmetic_possible,
                    "arithmetic_port_sufficient": audit.source_port_arithmetic_possible,
                    "joint_sufficient_if_actual_degree_certified": audit.simultaneous_sufficient_arithmetic,
                    "actual_graph_labeled": false,
                    "source_tensor_deformation_verified": false,
                    "source_weighted_modes_verified": false,
                    "source_recursion_executed": false,
                    "sat_count": null
                })
            );
            Ok(())
        }
        [_, mode, mask] if mode == "tiny-mask" => {
            let bits = mask.parse::<usize>().map_err(|_| "invalid tiny mask")?;
            if !(1..16).contains(&bits) {
                return Err("tiny mask must be between 1 and 15".into());
            }
            let edges = (0..4)
                .filter(|&i| bits & (1usize << i) != 0)
                .map(|i| (i / 2, i % 2))
                .collect::<Vec<_>>();
            let graph = BipartiteGraph {
                left_vertices: 2,
                right_vertices: 2,
                edges,
            };
            let witness = construct_joint_potential_labels_small(&graph, 2, 2)
                .map_err(|e| e.to_string())?;
            let sparse = &witness.orbit_sparse_layout;
            println!(
                "{}",
                json!({
                    "method": "exact_bounded_joint_conditional_expectation",
                    "status": "finite_structural_witness_only",
                    "mask": bits,
                    "edges": graph.edges.len(),
                    "groups": 2,
                    "coordinates": 2,
                    "maximum_actual_degree": witness.maximum_degree,
                    "proper_matching_colors": witness.matching_count,
                    "chosen_left_labels": witness.left_labels,
                    "chosen_right_labels": witness.right_labels,
                    "exact_initial_potential_numerator": witness.initial_potential_numerator.to_string(),
                    "exact_final_potential_numerator": witness.final_potential_numerator.to_string(),
                    "positive_common_denominator": witness.common_positive_denominator.to_string(),
                    "conditional_average_identities_verified": witness.all_conditional_average_identities_verified,
                    "candidates_evaluated": witness.choices_evaluated,
                    "maximum_pair_class_load": witness.maximum_pair_class_load,
                    "pair_load_bound_verified": witness.pair_class_bound_verified,
                    "max_row_symbol_ports": witness.maximum_row_symbol_load,
                    "max_column_symbol_ports": witness.maximum_column_symbol_load,
                    "sparse_packet_count": sparse.packets.len(),
                    "sparse_padded_slots": sparse.padded_slots,
                    "sparse_waste": sparse.unused_slots,
                    "source_packet_structural_bounds_hold": witness.structurally_admitted(),
                    "source_full_recursion_admitted": false,
                    "source_cauchy_mode_routing_verified": false,
                    "source_recursion_executed": false,
                    "sat_count": null
                })
            );
            Ok(())
        }
        _ => Err(
            "usage: appendix-joint-potential audit <M> <r> <a> <actual-max-degree> <degree-cap> | tiny-mask <1..15>"
                .into(),
        ),
    }
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
