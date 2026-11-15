//! Independent source-slot tests for sparse versus uniformly padded
//! packet layouts. No #SAT evaluator, field entries or recursive count.
use lean_eth_reference::two_adic_orbit_sparse::{
    OrbitSparsePacketLayout, construct_orbit_sparse_admitted,
    construct_orbit_sparse_bounded,
};
use lean_eth_reference::two_adic_packet_layout::{BipartiteEdge, pack_bounded};
use std::collections::BTreeMap;

fn edges_from_pairs(pairs: &[(usize, usize)]) -> Vec<BipartiteEdge> {
    pairs
        .iter()
        .map(|&(left, right)| BipartiteEdge { left, right })
        .collect()
}

fn verify_independently(
    edges: &[BipartiteEdge],
    left: &[usize],
    right: &[usize],
    layout: &OrbitSparsePacketLayout,
) {
    let a = usize::try_from(layout.a).unwrap();
    let l = 1usize << layout.a;
    assert_eq!(layout.slots_per_packet, l);
    assert_eq!(layout.real_edges, edges.len());
    assert_eq!(layout.padded_slots, layout.packets.len() * l);
    assert_eq!(layout.padded_slots, edges.len() + layout.unused_slots);
    assert_eq!(
        layout.unused_slots,
        layout.orientation_imbalance_slots + layout.rounding_slots
    );
    assert_eq!(layout.packets.len(), layout.occupied_orbits.iter().map(|o| o.packets).sum());
    assert_eq!(
        edges.len(),
        layout.occupied_orbits.iter().map(|o| o.real_edges).sum()
    );
    assert!(layout.occupied_orbits.iter().all(|o| o.real_edges > 0));

    let mut saw = vec![0usize; edges.len()];
    let mut independent_row = vec![vec![0usize; layout.r]; a];
    let mut independent_col = vec![vec![0usize; layout.r]; a];
    let mut independent_classes = BTreeMap::<Vec<(usize, usize)>, BTreeMap<(usize, usize), usize>>::new();
    let b = layout.r.pow(layout.a);
    for (index, edge) in edges.iter().enumerate() {
        let rl = left[edge.left];
        let cl = right[edge.right];
        assert!(rl < b && cl < b);
        let mut sig = Vec::new();
        let mut x = rl;
        let mut y = cl;
        for coordinate in 0..a {
            let row_digit = x % layout.r;
            let col_digit = y % layout.r;
            independent_row[coordinate][row_digit] += 1;
            independent_col[coordinate][col_digit] += 1;
            sig.push((row_digit.min(col_digit), row_digit.max(col_digit)));
            x /= layout.r;
            y /= layout.r;
        }
        *independent_classes.entry(sig).or_default().entry((rl, cl)).or_default() += 1;
        assert!(index < edges.len());
    }
    assert_eq!(layout.row_ports, independent_row);
    assert_eq!(layout.column_ports, independent_col);
    let expected_packet_count: usize = independent_classes
        .iter()
        .map(|(sig, classes)| {
            let q = 1usize << sig.iter().filter(|&&(x, y)| x == y).count();
            classes.values().copied().max().unwrap().div_ceil(q)
        })
        .sum();
    assert_eq!(layout.packets.len(), expected_packet_count);
    assert_eq!(layout.occupied_orbits.len(), independent_classes.len());
    for orbit in &layout.occupied_orbits {
        let classes = &independent_classes[&orbit.unordered_pairs];
        let q = 1usize << orbit.equal_coordinates;
        let c = 1usize << (a - orbit.equal_coordinates);
        let m: usize = classes.values().sum();
        let x = classes.values().copied().max().unwrap();
        let p = x.div_ceil(q);
        assert_eq!(orbit.copies_per_class_per_packet, q);
        assert_eq!(orbit.ordered_classes_in_orbit, c);
        assert_eq!(orbit.real_edges, m);
        assert_eq!(orbit.maximum_class_load, x);
        assert_eq!(orbit.packets, p);
        assert_eq!(orbit.padded_slots, p * l);
        assert_eq!(orbit.orientation_imbalance_slots, c * x - m);
        assert_eq!(orbit.rounding_slots, p * l - c * x);
    }

    for packet in &layout.packets {
        assert_eq!(packet.slots.len(), l);
        for (slot, maybe_idx) in packet.slots.iter().enumerate() {
            let Some(index) = maybe_idx else { continue };
            saw[*index] += 1;
            let edge = edges[*index];
            let mut row = left[edge.left];
            let mut col = right[edge.right];
            for coord in 0..a {
                let x = row % layout.r;
                let y = col % layout.r;
                let (lo, hi) = packet.unordered_pairs[coord];
                assert_eq!((x.min(y), x.max(y)), (lo, hi));
                if lo != hi {
                    let expected = if (slot >> coord) & 1 == 0 {
                        (lo, hi)
                    } else {
                        (hi, lo)
                    };
                    assert_eq!((x, y), expected);
                }
                row /= layout.r;
                col /= layout.r;
            }
        }
    }
    assert!(saw.iter().all(|&count| count == 1));

    let within_packet_bound = layout.packets.len() * l <= 3 * edges.len();
    let within_symbol_bound = independent_row.iter().zip(&independent_col).all(|(rows, cols)| {
        rows.iter().zip(cols).all(|(&x, &y)| {
            x * layout.r <= 3 * edges.len() && y * layout.r <= 3 * edges.len()
        })
    });
    assert_eq!(layout.packet_count_bound_holds, within_packet_bound);
    assert_eq!(layout.symbol_port_bounds_hold, within_symbol_bound);
    assert_eq!(layout.original_packet_bounds_hold(), within_packet_bound && within_symbol_bound);
}

#[test]
fn skips_empty_orbits_and_defeats_uniform_padding_floor() {
    // One all-equal orbit: q=L=4; every packet can carry four real edges.
    // The old source layout enumerates 16 ordered classes and refuses.
    let edges = (0..16)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let left = vec![0; 16];
    let right = vec![0; 16];
    let layout = construct_orbit_sparse_admitted(&edges, &left, &right, 2, 2, 8).unwrap();
    assert_eq!(layout.occupied_orbits.len(), 1);
    assert_eq!(layout.packets.len(), 4);
    assert_eq!(layout.unused_slots, 0);
    assert!(pack_bounded(&edges, &left, &right, 2, 2, 8).is_err());
    verify_independently(&edges, &left, &right, &layout);
}

#[test]
fn dense_balanced_classes_match_original_uniform_packets() {
    // r=2,a=1: each ordered class has exactly two edges.
    let mut pairs = Vec::new();
    for left in 0..2 {
        for right in 0..2 {
            for _ in 0..2 {
                pairs.push((left, right));
            }
        }
    }
    let edges = edges_from_pairs(&pairs);
    let labels = [0, 1];
    let uniform = pack_bounded(&edges, &labels, &labels, 2, 1, 4).unwrap();
    let sparse = construct_orbit_sparse_admitted(&edges, &labels, &labels, 2, 1, 4).unwrap();
    assert_eq!(sparse.packets, uniform.packets);
    assert_eq!(sparse.packets.len(), 4);
    assert_eq!(sparse.unused_slots, 0);
    verify_independently(&edges, &labels, &labels, &sparse);
}

#[test]
fn preserves_two_coordinate_unequal_orientations() {
    let edges = (0..4)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let row = [0, 1, 2, 3];
    let col = [3, 2, 1, 0];
    let layout = construct_orbit_sparse_admitted(&edges, &row, &col, 2, 2, 8).unwrap();
    assert_eq!(layout.occupied_orbits.len(), 1);
    assert_eq!(layout.occupied_orbits[0].equal_coordinates, 0);
    assert_eq!(layout.packets.len(), 1);
    assert_eq!(layout.packets[0].slots, vec![Some(0), Some(1), Some(2), Some(3)]);
    verify_independently(&edges, &row, &col, &layout);
}

#[test]
fn uses_equal_coordinate_bits_for_copy_index() {
    // The first symbol is unequal, the second is equal. Each class
    // appears twice, once at each copy bit.
    let edges = (0..4)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let row = [0, 1, 0, 1];
    let col = [1, 0, 1, 0];
    let layout = construct_orbit_sparse_admitted(&edges, &row, &col, 2, 2, 8).unwrap();
    assert_eq!(layout.occupied_orbits[0].equal_coordinates, 1);
    assert_eq!(layout.occupied_orbits[0].copies_per_class_per_packet, 2);
    assert_eq!(layout.packets[0].slots, vec![Some(0), Some(1), Some(2), Some(3)]);
    verify_independently(&edges, &row, &col, &layout);
}

#[test]
fn zero_slots_and_parallel_edges_preserve_exact_source_edge_ids() {
    let edges = vec![BipartiteEdge { left: 0, right: 0 }; 3];
    let layout = construct_orbit_sparse_admitted(&edges, &[0], &[0], 2, 2, 8).unwrap();
    assert_eq!(layout.packets.len(), 1);
    assert_eq!(layout.packets[0].slots, vec![Some(0), Some(1), Some(2), None]);
    assert_eq!(layout.rounding_slots, 1);
    assert_eq!(layout.orientation_imbalance_slots, 0);
    verify_independently(&edges, &[0], &[0], &layout);
}

#[test]
fn concentrated_unequal_orbit_can_pass_port_balance_but_fail_packets() {
    // All coordinates unequal, q=1, so each edge needs one entire
    // four-slot packet. Port balance alone never proves the 3M/L cap.
    let edges = (0..4)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let row = [0; 4];
    let col = [3; 4];
    let layout = construct_orbit_sparse_bounded(&edges, &row, &col, 2, 2, 8).unwrap();
    assert_eq!(layout.packets.len(), 4);
    assert_eq!(layout.padded_slots, 16);
    assert_eq!(layout.orientation_imbalance_slots, 12);
    assert!(!layout.packet_count_bound_holds);
    assert!(layout.symbol_port_bounds_hold);
    assert!(construct_orbit_sparse_admitted(&edges, &row, &col, 2, 2, 8).is_err());
    verify_independently(&edges, &row, &col, &layout);
}

#[test]
fn concentrated_equal_orbit_can_pass_packets_but_fail_symbol_ports() {
    let edges = (0..16)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let row = [0; 16];
    let col = [0; 16];
    let layout = construct_orbit_sparse_bounded(&edges, &row, &col, 4, 2, 8).unwrap();
    assert_eq!(layout.packets.len(), 4);
    assert!(layout.packet_count_bound_holds);
    assert!(!layout.symbol_port_bounds_hold);
    assert!(!layout.child_edge_bound_holds);
    assert!(construct_orbit_sparse_admitted(&edges, &row, &col, 4, 2, 8).is_err());
    verify_independently(&edges, &row, &col, &layout);
}

#[test]
fn exhaustive_two_by_two_graphs_and_labelings_replay_exact_packet_counts() {
    // Independently enumerate 15 nonempty 2x2 edge subsets and all
    // 4^4 assignments of labels for a=2,r=2.
    for mask in 1..16usize {
        let pairs = (0..4)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| (i / 2, i % 2))
            .collect::<Vec<_>>();
        let edges = edges_from_pairs(&pairs);
        for label_mask in 0..256usize {
            let row = [label_mask & 3, (label_mask >> 2) & 3];
            let col = [(label_mask >> 4) & 3, (label_mask >> 6) & 3];
            let layout = construct_orbit_sparse_bounded(&edges, &row, &col, 2, 2, 8).unwrap();
            verify_independently(&edges, &row, &col, &layout);
            assert_eq!(
                layout,
                construct_orbit_sparse_bounded(&edges, &row, &col, 2, 2, 8).unwrap()
            );
        }
    }
}

#[test]
fn source_r64_positive_width_succeeds_structurally_without_uniform_d_classes() {
    // u=1 -> a=2, L=4, D=64^4. Choose 64 distinct diagonal
    // symbol-labels, each with four independent edges.
    // There are 64 occupied orbits, 256 real edges, zero padding.
    // The uniform construction would have to pad all 2^24 classes.
    let edges = (0..256)
        .map(|i| BipartiteEdge { left: i, right: i })
        .collect::<Vec<_>>();
    let labels = (0..256).map(|i| (i / 4) * 65).collect::<Vec<_>>();
    let receipt = construct_orbit_sparse_admitted(&edges, &labels, &labels, 64, 2, 8).unwrap();
    assert_eq!(receipt.packets.len(), 64);
    assert_eq!(receipt.occupied_orbits.len(), 64);
    assert_eq!(receipt.padded_slots, 256);
    assert_eq!(receipt.unused_slots, 0);
    assert!(receipt.original_packet_bounds_hold());
    assert_eq!(receipt.original_maximum_degree, 1);
    for symbol_counts in &receipt.child_edge_upper_counts {
        assert_eq!(symbol_counts.len(), 64);
        assert!(symbol_counts.iter().all(|&count| count == 8));
    }
    // Some children have at most 8 original edge incidences; there
    // is still no tensor coefficient, signed mode or source-u proof.
    verify_independently(&edges, &labels, &labels, &receipt);
}

#[test]
fn validates_labels_endpoints_degrees_and_capacity() {
    let small = [BipartiteEdge { left: 0, right: 0 }];
    assert!(construct_orbit_sparse_bounded(&small, &[4], &[0], 2, 2, 8).is_err());
    assert!(construct_orbit_sparse_bounded(&small, &[0], &[0], 2, 2, 7).is_err());
    assert!(construct_orbit_sparse_bounded(&small, &[], &[0], 2, 2, 8).is_err());
    assert!(construct_orbit_sparse_bounded(&small, &[0], &[0], 2, 0, 8).is_err());
    assert!(construct_orbit_sparse_bounded(&small, &[0], &[0], 1, 2, 8).is_err());
    assert!(construct_orbit_sparse_bounded(&[], &[0], &[0], 2, 2, 8).is_err());

    let repeated = vec![BipartiteEdge { left: 0, right: 0 }; 9];
    assert!(construct_orbit_sparse_bounded(&repeated, &[0], &[0], 2, 2, 8).is_err());
    let oversized = vec![BipartiteEdge { left: 0, right: 0 }; 257];
    assert!(construct_orbit_sparse_bounded(&oversized, &[0], &[0], 2, 2, 300).is_err());
}
