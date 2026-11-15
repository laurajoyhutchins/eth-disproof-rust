//! Independent finite-graph checks of the deterministic matching
//! labeling constructor. These tests do not run a SAT counter.

use lean_eth_reference::matching_packing::{
    BipartiteGraph, MatchingLabelCertificate, construct_matching_labels,
};

fn verify(graph: &BipartiteGraph, cert: &MatchingLabelCertificate) {
    assert_eq!(cert.edge_colors.len(), graph.edges.len());
    assert_eq!(cert.left_labels.len(), graph.left_vertices);
    assert_eq!(cert.right_labels.len(), graph.right_vertices);
    assert!(cert.final_potential <= cert.initial_potential);
    for &label in cert.left_labels.iter().chain(&cert.right_labels) {
        assert!(label < cert.labels_per_side);
    }
    let q = usize::try_from(cert.labels_per_side).unwrap();
    let mut class_loads = vec![0usize; q * q];
    for (i, &(left, right)) in graph.edges.iter().enumerate() {
        let label = usize::try_from(cert.left_labels[left]).unwrap() * q
            + usize::try_from(cert.right_labels[right]).unwrap();
        class_loads[label] += 1;
        for (j, &(other_left, other_right)) in graph.edges.iter().enumerate() {
            if i != j && cert.edge_colors[i] == cert.edge_colors[j] {
                assert_ne!(left, other_left, "one matching repeats left endpoint");
                assert_ne!(right, other_right, "one matching repeats right endpoint");
            }
        }
    }
    assert_eq!(
        class_loads.into_iter().max().unwrap_or(0),
        cert.maximum_pair_class_load
    );
    let left_degree = (0..graph.left_vertices)
        .map(|v| graph.edges.iter().filter(|&&(left, _)| left == v).count())
        .max()
        .unwrap_or(0);
    let right_degree = (0..graph.right_vertices)
        .map(|v| graph.edges.iter().filter(|&&(_, right)| right == v).count())
        .max()
        .unwrap_or(0);
    assert_eq!(cert.maximum_degree, left_degree.max(right_degree));
    if !graph.edges.is_empty() {
        assert!(cert.matching_count < 2 * cert.maximum_degree);
    }
    assert!(
        u128::try_from(cert.maximum_pair_class_load).unwrap() * cert.exact_load_bound_denominator
            <= cert.exact_load_bound_numerator,
        "reported load violates rational potential bound"
    );
}

#[test]
fn greedy_coloring_and_exact_labels_work_on_complete_bipartite_graph() {
    let graph = BipartiteGraph {
        left_vertices: 4,
        right_vertices: 4,
        edges: (0..4).flat_map(|l| (0..4).map(move |r| (l, r))).collect(),
    };
    let a = construct_matching_labels(&graph, 4).unwrap();
    let b = construct_matching_labels(&graph, 4).unwrap();
    assert_eq!(a, b, "deterministic replay");
    verify(&graph, &a);
    assert_eq!(a.maximum_degree, 4);
}

#[test]
fn multiedges_and_stars_keep_colors_proper() {
    let graph = BipartiteGraph {
        left_vertices: 3,
        right_vertices: 7,
        edges: vec![
            (0, 0),
            (0, 0),
            (0, 1),
            (0, 2),
            (0, 3),
            (0, 4),
            (0, 5),
            (0, 6),
            (1, 0),
            (1, 3),
            (2, 2),
            (2, 6),
        ],
    };
    let receipt = construct_matching_labels(&graph, 4).unwrap();
    verify(&graph, &receipt);
    assert_eq!(receipt.maximum_degree, 8);
}

#[test]
fn exhaustive_small_graph_instances_replay() {
    // All 2x2 simple bipartite edge subsets, including the empty graph.
    for bits in 0..16u32 {
        let edges = (0..4)
            .filter(|index| bits & (1 << index) != 0)
            .map(|index| (index / 2, index % 2))
            .collect();
        let graph = BipartiteGraph {
            left_vertices: 2,
            right_vertices: 2,
            edges,
        };
        verify(&graph, &construct_matching_labels(&graph, 4).unwrap());
    }
}

#[test]
fn refuses_malformed_graph_or_excessive_exact_arithmetic() {
    let invalid = BipartiteGraph {
        left_vertices: 1,
        right_vertices: 1,
        edges: vec![(2, 0)],
    };
    assert!(construct_matching_labels(&invalid, 4).is_err());
    let valid = BipartiteGraph {
        left_vertices: 1,
        right_vertices: 1,
        edges: vec![(0, 0)],
    };
    assert!(construct_matching_labels(&valid, 1).is_err());
    let too_many_classes = BipartiteGraph {
        left_vertices: 100,
        right_vertices: 100,
        edges: (0..100).map(|v| (v, v)).collect(),
    };
    assert!(construct_matching_labels(&too_many_classes, 64).is_err());
}
