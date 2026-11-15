//! Independent tests of simultaneous finite port balancing and orbit
//! packet minimization. No source-defined tensor counting.
use lean_eth_reference::two_adic_joint_balance::{
    JointBalanceReceipt, construct_joint_balanced_admitted,
    construct_joint_balanced_bounded,
};
use lean_eth_reference::two_adic_orbit_sparse::construct_orbit_sparse_bounded;
use lean_eth_reference::two_adic_packet_layout::BipartiteEdge;

fn shifted_edges() -> Vec<BipartiteEdge> {
    (0..32)
        .map(|left| BipartiteEdge {
            left,
            right: (left / 4) * 4 + ((left + 1) % 4),
        })
        .collect()
}

fn port_loads(labels: &[usize], edges: &[BipartiteEdge], left: bool, r: usize, a: u32) -> Vec<Vec<usize>> {
    let mut ports = vec![vec![0usize; r]; a as usize];
    for edge in edges {
        let mut label = labels[if left { edge.left } else { edge.right }];
        for row in &mut ports {
            row[label % r] += 1;
            label /= r;
        }
    }
    ports
}

fn assert_certified(edges: &[BipartiteEdge], r: usize, a: u32, receipt: &JointBalanceReceipt) {
    let m = edges.len();
    let max_degree = receipt.maximum_degree;
    let lhs = m + (r - 1) * max_degree;
    assert_eq!(receipt.greedy_port_bound_numerator, lhs);
    assert_eq!(receipt.vertex_degree_necessary_port_bound, r * max_degree <= 3 * m);
    assert_eq!(
        receipt.greedy_port_sufficient_for_source_limit,
        (r - 1) * max_degree <= 2 * m
    );
    assert!(receipt.layouts_evaluated <= 1 + a as usize * (r - 1) * 3);
    assert!(receipt.final_packets <= receipt.initial_packets);
    assert_eq!(receipt.final_packets, receipt.final_layout.packets.len());
    assert!(receipt.final_layout.padded_slots <= receipt.initial_packets * (1usize << a));
    assert_eq!(
        receipt.final_layout.unused_slots,
        receipt.final_layout.orientation_imbalance_slots + receipt.final_layout.rounding_slots
    );
    let initial_row = port_loads(&receipt.initial_left_labels, edges, true, r, a);
    let initial_col = port_loads(&receipt.initial_right_labels, edges, false, r, a);
    let final_row = port_loads(&receipt.left_labels, edges, true, r, a);
    let final_col = port_loads(&receipt.right_labels, edges, false, r, a);
    for (old, new) in initial_row.iter().zip(&final_row) {
        let mut before = old.clone();
        let mut after = new.clone();
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after);
    }
    for (old, new) in initial_col.iter().zip(&final_col) {
        let mut before = old.clone();
        let mut after = new.clone();
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after);
    }
    assert_eq!(final_row, receipt.final_layout.row_ports);
    assert_eq!(final_col, receipt.final_layout.column_ports);
    assert!(
        r * receipt.maximum_row_port <= lhs,
        "greedy weighted row bound must hold exactly"
    );
    assert!(
        r * receipt.maximum_column_port <= lhs,
        "greedy weighted column bound must hold exactly"
    );
    if receipt.greedy_port_sufficient_for_source_limit {
        assert!(receipt.final_layout.symbol_port_bounds_hold);
        assert!(receipt.final_layout.child_edge_bound_holds);
    }
    let independently_replayed = construct_orbit_sparse_bounded(
        edges,
        &receipt.left_labels,
        &receipt.right_labels,
        r,
        a,
        receipt.final_layout.asserted_degree_cap,
    )
    .unwrap();
    assert_eq!(receipt.final_layout, independently_replayed);
    assert_eq!(
        receipt.structurally_admitted(),
        receipt.final_layout.original_packet_bounds_hold()
    );
    let uniform = receipt.uniform_packets_at_final_labels.unwrap();
    assert!(uniform >= receipt.final_packets as u128);
}

#[test]
fn coordinate_descent_repairs_two_different_symbol_rotations_without_port_loss() {
    let edges = shifted_edges();
    let receipt = construct_joint_balanced_admitted(&edges, 32, 32, 4, 2, 8, 3).unwrap();
    assert_eq!(receipt.maximum_degree, 1);
    assert_eq!(receipt.initial_packets, 32);
    assert_eq!(receipt.initial_unused_slots, 96);
    assert_eq!(receipt.final_packets, 8);
    assert_eq!(receipt.final_layout.unused_slots, 0);
    assert_eq!(receipt.right_coordinate_shifts, vec![3, 3]);
    assert!(receipt.greedy_port_sufficient_for_source_limit);
    assert!(receipt.structurally_admitted());
    assert_eq!(receipt.maximum_row_port, 8);
    assert_eq!(receipt.maximum_column_port, 8);
    assert_eq!(receipt.uniform_packets_at_final_labels, Some(512));
    assert_certified(&edges, 4, 2, &receipt);
    assert_eq!(
        receipt,
        construct_joint_balanced_admitted(&edges, 32, 32, 4, 2, 8, 3).unwrap()
    );
}

#[test]
fn source_group_count_has_a_sparse_diagonal_witness_without_d_classes() {
    let edges = (0..256)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let receipt = construct_joint_balanced_admitted(&edges, 256, 256, 64, 2, 8, 2).unwrap();
    assert_eq!(receipt.maximum_degree, 1);
    assert_eq!(receipt.initial_packets, 64);
    assert_eq!(receipt.final_packets, 64);
    assert_eq!(receipt.final_layout.unused_slots, 0);
    assert_eq!(receipt.uniform_packets_at_final_labels, Some(16_777_216));
    assert_eq!(receipt.maximum_row_port, 4);
    assert_eq!(receipt.maximum_column_port, 4);
    assert_eq!(receipt.final_layout.occupied_orbits.len(), 64);
    assert!(receipt.structurally_admitted());
    assert_certified(&edges, 64, 2, &receipt);
}

#[test]
fn star_degree_is_a_provable_no_go_before_label_search() {
    let edges = (0..16)
        .map(|right| BipartiteEdge { left: 0, right })
        .collect::<Vec<_>>();
    // r*Delta=64 >3M=48; whichever symbol labels the star
    // center, that row symbol necessarily carries 16 real ports.
    let err = construct_joint_balanced_bounded(&edges, 1, 16, 4, 2, 16, 3).unwrap_err();
    assert!(err.to_string().contains("unavoidable per-symbol port overload"));
}

#[test]
fn bounded_search_keeps_explicit_failure_instead_of_calling_it_a_counter() {
    // All 2x2 simple graphs, with both positive and unbalanced degree
    // patterns, have deterministic explicit structural receipts whenever
    // the necessary maximum-degree condition holds.
    for mask in 1..16usize {
        let edges = (0..4)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| BipartiteEdge {
                left: i / 2,
                right: i % 2,
            })
            .collect::<Vec<_>>();
        let delta = (0..2)
            .map(|v| {
                let row = edges.iter().filter(|e| e.left == v).count();
                let col = edges.iter().filter(|e| e.right == v).count();
                row.max(col)
            })
            .max()
            .unwrap();
        if 2 * delta > 3 * edges.len() {
            assert!(construct_joint_balanced_bounded(&edges, 2, 2, 2, 2, 8, 2).is_err());
            continue;
        }
        let receipt = construct_joint_balanced_bounded(&edges, 2, 2, 2, 2, 8, 2).unwrap();
        assert_certified(&edges, 2, 2, &receipt);
        if !receipt.structurally_admitted() {
            assert!(construct_joint_balanced_admitted(&edges, 2, 2, 2, 2, 8, 2).is_err());
        }
        assert_eq!(
            receipt,
            construct_joint_balanced_bounded(&edges, 2, 2, 2, 2, 8, 2).unwrap()
        );
    }
}

#[test]
fn parallel_edges_weight_one_vertex_without_losing_port_certificate() {
    let edges = vec![BipartiteEdge { left: 0, right: 0 }; 8];
    let receipt = construct_joint_balanced_admitted(&edges, 1, 1, 2, 2, 8, 2).unwrap();
    assert_eq!(receipt.maximum_degree, 8);
    assert_eq!(receipt.final_packets, 2);
    assert_eq!(receipt.final_layout.padded_slots, 8);
    assert!(receipt.greedy_port_sufficient_for_source_limit);
    assert_certified(&edges, 2, 2, &receipt);
}

#[test]
fn invalid_graph_degree_and_search_budget_fail_closed() {
    let edge = [BipartiteEdge { left: 0, right: 0 }];
    assert!(construct_joint_balanced_bounded(&edge, 0, 1, 2, 2, 8, 1).is_err());
    assert!(construct_joint_balanced_bounded(&edge, 1, 1, 1, 2, 8, 1).is_err());
    assert!(construct_joint_balanced_bounded(&edge, 1, 1, 2, 0, 8, 1).is_err());
    assert!(construct_joint_balanced_bounded(&edge, 1, 1, 2, 2, 7, 1).is_err());
    assert!(construct_joint_balanced_bounded(&edge, 1, 1, 2, 2, 8, 0).is_err());
    assert!(construct_joint_balanced_bounded(&edge, 1, 1, 2, 2, 8, 4).is_err());
    assert!(construct_joint_balanced_bounded(&[], 1, 1, 2, 2, 8, 1).is_err());
}
