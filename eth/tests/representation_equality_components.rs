use lean_eth_reference::Error;
use lean_eth_reference::representation_equality_components::EqualityComponentRegion;

fn brute_force(region: &EqualityComponentRegion) -> i128 {
    assert!(region.len() <= 6);
    (0..(1usize << region.len()))
        .map(|mask| {
            let bits: Vec<_> = (0..region.len()).map(|i| ((mask >> i) & 1) == 1).collect();
            region.value_at(&bits).expect("small independent oracle")
        })
        .sum()
}

#[test]
fn all_simple_equality_graphs_to_five_vertices_match_full_truth_tables() {
    for n in 0..=5usize {
        let edges: Vec<_> = (0..n)
            .flat_map(|a| (a + 1..n).map(move |b| (a, b)))
            .collect();
        let unary: Vec<_> = (0..n)
            .map(|i| [i as i128 % 3 - 1, (i as i128 * 3) % 5 - 2])
            .collect();
        for mask in 0..(1usize << edges.len()) {
            let mut region = EqualityComponentRegion::new(unary.clone());
            for (k, &(a, b)) in edges.iter().enumerate() {
                if (mask >> k) & 1 == 1 {
                    region.apply_equality(a, b).unwrap();
                }
            }
            let receipt = region.contract().unwrap();
            assert_eq!(receipt.value, brute_force(&region), "n={n}, graph={mask}");
            assert_eq!(receipt.variable_count, n);
            assert_eq!(receipt.edge_count, mask.count_ones() as usize);
            assert_eq!(receipt.component_count, n - receipt.successful_unions);
            assert_eq!(receipt.checked_additions, receipt.component_count);
            assert_eq!(
                receipt.checked_multiplications,
                2 * n + receipt.component_count
            );
        }
    }
}

#[test]
fn overlapping_edges_and_cycles_are_supported_exactly() {
    let mut region = EqualityComponentRegion::new(vec![[1, 2], [3, 4], [5, 6], [7, 8]]);
    for (a, b) in [(0, 1), (1, 2), (2, 0), (3, 3)] {
        region.apply_equality(a, b).unwrap();
    }
    assert_eq!(region.component_count(), 2);
    assert_eq!(region.edge_count(), 4);
    assert_eq!(
        region.contract().unwrap().value,
        (3 * 5 + 2 * 4 * 6) * (7 + 8)
    );
    assert_eq!(region.contract().unwrap().value, brute_force(&region));
    assert!(region.as_unary_product_if_unconstrained().is_err());
}

#[test]
fn large_chain_with_cycles_stays_linear_in_storage_and_arithmetic() {
    let n = 2000;
    let mut region = EqualityComponentRegion::new(vec![[1, 1]; n]);
    for i in 1..n {
        region.apply_equality(i - 1, i).unwrap();
    }
    region.apply_equality(0, n - 1).unwrap(); // Redundant cycle.
    let receipt = region.contract().unwrap();
    assert_eq!(receipt.value, 2);
    assert_eq!(receipt.component_count, 1);
    assert_eq!(receipt.successful_unions, n - 1);
    assert_eq!(receipt.checked_additions, 1);
    assert_eq!(receipt.checked_multiplications, 2 * n + 1);
    assert!(receipt.logical_payload_bytes < 210_000);
}

#[test]
fn invalid_ports_refuse_before_any_mutation() {
    let mut region = EqualityComponentRegion::new(vec![[2, 3], [4, 5]]);
    let before = region.clone();
    assert!(matches!(
        region.apply_equality(0, 2),
        Err(Error::Invalid(_))
    ));
    assert_eq!(region, before);
    assert!(matches!(region.value_at(&[true]), Err(Error::Invalid(_))));
}

#[test]
fn overflow_refuses_without_a_modular_or_saturated_count() {
    let mut region = EqualityComponentRegion::new(vec![[i128::MAX, i128::MAX], [2, 3]]);
    region.apply_equality(0, 1).unwrap();
    assert!(matches!(region.contract(), Err(Error::Overflow)));
    assert_eq!(region.value_at(&[true, false]).unwrap(), 0);
    assert!(matches!(
        region.value_at(&[false, false]),
        Err(Error::Overflow)
    ));
}

#[test]
fn empty_and_unconstrained_components_have_correct_identity() {
    let empty = EqualityComponentRegion::new(vec![]);
    assert!(empty.is_empty());
    assert_eq!(empty.contract().unwrap().value, 1);
    assert_eq!(empty.contract().unwrap().component_count, 0);

    let unconstrained = EqualityComponentRegion::new(vec![[2, 3], [4, 5]]);
    assert_eq!(
        unconstrained.as_unary_product_if_unconstrained().unwrap(),
        &[[2, 3], [4, 5]]
    );
    assert_eq!(unconstrained.contract().unwrap().value, (2 + 3) * (4 + 5));
}

/// Completely independent reachability reference: repeated edge relaxation.
/// Unlike union-find it never reads or updates the production parent array.
fn reachable(n: usize, edges: &[(usize, usize)], start: usize, target: usize) -> bool {
    let mut seen = vec![false; n];
    seen[start] = true;
    for _ in 0..n {
        for &(a, b) in edges {
            if seen[a] || seen[b] {
                seen[a] = true;
                seen[b] = true;
            }
        }
    }
    seen[target]
}

#[test]
fn component_labels_are_surjective_and_match_independent_paths() {
    for n in 1..=5 {
        let possible_edges: Vec<_> = (0..n)
            .flat_map(|a| (a + 1..n).map(move |b| (a, b)))
            .collect();
        for mask in 0..(1usize << possible_edges.len()) {
            let edges: Vec<_> = possible_edges
                .iter()
                .enumerate()
                .filter_map(|(k, &edge)| ((mask >> k) & 1 == 1).then_some(edge))
                .collect();
            for reverse in [false, true] {
                let mut region = EqualityComponentRegion::new(vec![[1, 1]; n]);
                if reverse {
                    for &(a, b) in edges.iter().rev() {
                        region.apply_equality(b, a).unwrap();
                    }
                } else {
                    for &(a, b) in &edges {
                        region.apply_equality(a, b).unwrap();
                    }
                }
                let labels = region.component_labels().unwrap();
                assert_eq!(labels.len(), n);
                assert_eq!(
                    labels
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>(),
                    (0..region.component_count()).collect(),
                    "surjective labels: n={n} graph={mask}"
                );
                for a in 0..n {
                    for b in 0..n {
                        assert_eq!(
                            labels[a] == labels[b],
                            reachable(n, &edges, a, b),
                            "n={n} graph={mask}, reversed={reverse}, ports=({a},{b})"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn duplicates_self_edges_and_reordered_insertions_preserve_partition() {
    let mut region = EqualityComponentRegion::new(vec![[2, 3]; 6]);
    let edges = [(2, 3), (1, 2), (2, 3), (0, 0), (3, 4), (4, 1)];
    for (a, b) in edges {
        region.apply_equality(a, b).unwrap();
    }
    assert_eq!(region.component_labels().unwrap(), vec![0, 1, 1, 1, 1, 2]);
    assert_eq!(region.component_count(), 3);
    let expected = region.contract().unwrap().value;
    let mut reversed = EqualityComponentRegion::new(vec![[2, 3]; 6]);
    for &(a, b) in edges.iter().rev() {
        reversed.apply_equality(b, a).unwrap();
    }
    assert_eq!(
        reversed.component_labels().unwrap(),
        region.component_labels().unwrap()
    );
    assert_eq!(reversed.contract().unwrap().value, expected);
}

#[test]
fn empty_partition_has_no_fictitious_component_label() {
    let empty = EqualityComponentRegion::new(vec![]);
    assert!(empty.component_labels().unwrap().is_empty());
    assert_eq!(empty.component_count(), 0);
}
