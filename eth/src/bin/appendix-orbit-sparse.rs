//! Reproducible bounded orbit-sparse packet *structure* receipts.
//! This CLI does not run tensor coefficients, modes, interpolation or #SAT.

use std::process::ExitCode;

use lean_eth_reference::two_adic_orbit_sparse::construct_orbit_sparse_bounded;
use lean_eth_reference::two_adic_packet_layout::BipartiteEdge;
use serde_json::json;

type Fixture = (
    Vec<BipartiteEdge>,
    Vec<usize>,
    Vec<usize>,
    usize,
    u32,
    usize,
);

fn fixture(name: &str) -> Result<Fixture, String> {
    match name {
        "r64-balanced" => {
            let edges = (0..256)
                .map(|i| BipartiteEdge { left: i, right: i })
                .collect::<Vec<_>>();
            let labels = (0..256).map(|i| (i / 4) * 65).collect::<Vec<_>>();
            Ok((edges, labels.clone(), labels, 64, 2, 8))
        }
        "r2-one-orbit" => {
            let edges = (0..16)
                .map(|i| BipartiteEdge { left: i, right: i })
                .collect::<Vec<_>>();
            Ok((edges, vec![0; 16], vec![0; 16], 2, 2, 8))
        }
        "r2-concentrated-unequal" => {
            let edges = (0..4)
                .map(|i| BipartiteEdge { left: i, right: i })
                .collect::<Vec<_>>();
            Ok((edges, vec![0; 4], vec![3; 4], 2, 2, 8))
        }
        "r4-concentrated-equal" => {
            let edges = (0..16)
                .map(|i| BipartiteEdge { left: i, right: i })
                .collect::<Vec<_>>();
            Ok((edges, vec![0; 16], vec![0; 16], 4, 2, 8))
        }
        _ => Err("fixture must be r64-balanced, r2-one-orbit, r2-concentrated-unequal, or r4-concentrated-equal".into()),
    }
}

fn run() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        return Err("usage: appendix-orbit-sparse <fixture>".into());
    }
    let (edges, left, right, r, a, degree_cap) = fixture(&args[1])?;
    let layout = construct_orbit_sparse_bounded(&edges, &left, &right, r, a, degree_cap)
        .map_err(|error| error.to_string())?;
    let max_ports = layout
        .row_ports
        .iter()
        .chain(&layout.column_ports)
        .flat_map(|row| row.iter())
        .copied()
        .max()
        .unwrap_or(0);
    let max_child_edges = layout
        .child_edge_upper_counts
        .iter()
        .flat_map(|row| row.iter())
        .copied()
        .max()
        .unwrap_or(0);
    let orbit_receipts = layout
        .occupied_orbits
        .iter()
        .map(|orbit| {
            json!({
                "signature": orbit.unordered_pairs,
                "real_edges": orbit.real_edges,
                "class_count": orbit.ordered_classes_in_orbit,
                "copy_slots_per_class": orbit.copies_per_class_per_packet,
                "maximum_class_load": orbit.maximum_class_load,
                "packets": orbit.packets,
                "orientation_imbalance_slots": orbit.orientation_imbalance_slots,
                "rounding_slots": orbit.rounding_slots
            })
        })
        .collect::<Vec<_>>();
    let lambda = usize::BITS - (edges.len() - 1).leading_zeros();
    println!(
        "{}",
        json!({
            "method": "source_slot_preserving_orbit_sparse_layout",
            "fixture": args[1],
            "status": "unsupported_source_recursion",
            "groups": r,
            "a": a,
            "slots_per_packet": layout.slots_per_packet,
            "real_edges": layout.real_edges,
            "occupied_orbits": layout.occupied_orbits.len(),
            "packet_count": layout.packets.len(),
            "padded_slots": layout.padded_slots,
            "unused_slots": layout.unused_slots,
            "orientation_imbalance_slots": layout.orientation_imbalance_slots,
            "rounding_slots": layout.rounding_slots,
            "maximum_original_degree": layout.original_maximum_degree,
            "verified_degree_cap": layout.asserted_degree_cap,
            "maximum_real_symbol_ports": max_ports,
            "maximum_child_edge_incidences": max_child_edges,
            "source_packet_count_bound_holds": layout.packet_count_bound_holds,
            "source_symbol_port_bounds_hold": layout.symbol_port_bounds_hold,
            "source_child_edge_bound_holds": layout.child_edge_bound_holds,
            "source_packet_structural_bounds_hold": layout.original_packet_bounds_hold(),
            "original_source_root_u": lambda / 131_072,
            "orbit_receipts": orbit_receipts,
            "source_sparse_tensor_semantics_proved": false,
            "source_precision_and_routing_proved": false,
            "recursion_executed": false,
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
