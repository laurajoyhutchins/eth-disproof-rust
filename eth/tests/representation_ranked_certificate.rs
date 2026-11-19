use lean_eth_reference::Error;
use lean_eth_reference::representation_equality_components::EqualityComponentRegion;
use lean_eth_reference::representation_ranked_certificate::{
    RankedComponentCertificate, contract_checked_ranked_weights,
    verify_ranked_component_certificate,
};

fn direct_oracle(n: usize, edges: &[(usize, usize)], weights: &[[i128; 2]]) -> i128 {
    assert!(n <= 6);
    (0..(1usize << n))
        .filter(|&bits| {
            edges
                .iter()
                .all(|&(a, b)| ((bits >> a) & 1) == ((bits >> b) & 1))
        })
        .map(|bits| {
            weights.iter().enumerate().fold(1i128, |acc, (i, w)| {
                acc * w[(bits >> i) & 1]
            })
        })
        .sum()
}

#[test]
fn all_simple_graphs_to_five_vertices_verify_ranked_witness_and_count() {
    for n in 0..=5usize {
        let possible: Vec<_> = (0..n)
            .flat_map(|a| (a + 1..n).map(move |b| (a, b)))
            .collect();
        let weights: Vec<_> = (0..n)
            .map(|i| [(i as i128) % 3 - 1, (i as i128 * 2) % 5 - 2])
            .collect();
        for mask in 0..(1usize << possible.len()) {
            let mut region = EqualityComponentRegion::new(weights.clone());
            for (bit, &(a, b)) in possible.iter().enumerate() {
                if mask & (1usize << bit) != 0 {
                    region.apply_equality(a, b).unwrap();
                }
            }
            let (receipt, certificate) = region.contract_with_ranked_certificate().unwrap();
            let verified =
                verify_ranked_component_certificate(n, region.source_edges(), &certificate)
                    .unwrap();
            assert_eq!(verified.components, region.component_count());
            assert_eq!(verified.parent_links, n - verified.components);
            assert_eq!(
                receipt.value,
                direct_oracle(n, region.source_edges(), &weights),
                "n={n}, mask={mask}"
            );
            assert_eq!(receipt.value, region.contract().unwrap().value);
            assert_eq!(receipt.checked_additions, verified.components);
            assert_eq!(receipt.checked_multiplications, 2 * n + verified.components);
        }
    }
}

#[test]
fn duplicate_reversed_and_self_edges_do_not_change_certified_count() {
    let edges = [(2, 3), (1, 2), (2, 3), (0, 0), (3, 4), (4, 1)];
    let weights = vec![[2, 1], [3, -4], [1, 1], [-1, 2], [0, 5], [7, 8]];
    let mut region = EqualityComponentRegion::new(weights.clone());
    for (a, b) in edges {
        region.apply_equality(a, b).unwrap();
    }
    let (receipt, certificate) = region.contract_with_ranked_certificate().unwrap();
    assert_eq!(receipt.value, direct_oracle(6, region.source_edges(), &weights));
    assert_eq!(certificate.roots.len(), 3);
    assert_eq!(certificate.rank[certificate.roots[0]], 0);
    assert_eq!(certificate.rank[certificate.roots[1]], 0);
    assert_eq!(certificate.rank[certificate.roots[2]], 0);

    let mut reversed = EqualityComponentRegion::new(weights);
    for &(a, b) in edges.iter().rev() {
        reversed.apply_equality(b, a).unwrap();
    }
    let (reverse_receipt, reverse_certificate) =
        reversed.contract_with_ranked_certificate().unwrap();
    assert_eq!(reverse_receipt.value, receipt.value);
    assert_eq!(reverse_certificate.labels, certificate.labels);
}

#[test]
fn strictly_decreasing_rank_forbids_parent_cycles() {
    let source = [(0, 1), (1, 2), (2, 1)];
    let forged = RankedComponentCertificate {
        labels: vec![0, 0, 0],
        roots: vec![0],
        parent_edge_indices: vec![None, Some(1), Some(2)],
        rank: vec![0, 2, 1],
    };
    // 1 must be above 2, while 2 must be above 1.
    assert!(verify_ranked_component_certificate(3, &source, &forged).is_err());
}

#[test]
fn malformed_roots_labels_parent_links_and_ranks_refuse() {
    let source = [(0, 1), (1, 2)];
    let good = RankedComponentCertificate {
        labels: vec![0, 0, 0],
        roots: vec![0],
        parent_edge_indices: vec![None, Some(0), Some(1)],
        rank: vec![0, 1, 2],
    };
    assert!(verify_ranked_component_certificate(3, &source, &good).is_ok());

    let mut mutated = good.clone();
    mutated.roots[0] = 1;
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.parent_edge_indices[2] = None;
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.parent_edge_indices[2] = Some(0);
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.parent_edge_indices[2] = Some(90);
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.rank[2] = 1;
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.rank[0] = 7;
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.labels[2] = 2;
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());

    let mut mutated = good.clone();
    mutated.labels.pop();
    assert!(verify_ranked_component_certificate(3, &source, &mutated).is_err());
}

#[test]
fn source_change_invalidates_certificate_without_reusable_receipt() {
    let good = RankedComponentCertificate {
        labels: vec![0, 0, 1],
        roots: vec![0, 2],
        parent_edge_indices: vec![None, Some(0), None],
        rank: vec![0, 1, 0],
    };
    let weights = vec![[1, 2]; 3];
    let edges = [(0, 1)];
    assert_eq!(
        contract_checked_ranked_weights(&weights, &edges, &good)
            .unwrap()
            .value,
        (1 + 1 * 1 * 2) * (1 + 2)
    );
    assert!(contract_checked_ranked_weights(&weights, &[(1, 2)], &good).is_err());

    let mut forged = good.clone();
    forged.parent_edge_indices[1] = Some(9);
    assert!(contract_checked_ranked_weights(&weights, &edges, &forged).is_err());
}

#[test]
fn verified_labels_count_refuses_overflow_instead_of_truncation() {
    let cert = RankedComponentCertificate {
        labels: vec![0, 0],
        roots: vec![0],
        parent_edge_indices: vec![None, Some(0)],
        rank: vec![0, 1],
    };
    let edges = [(0, 1)];
    let weights = [[i128::MAX, i128::MAX], [2, 3]];
    assert!(matches!(
        contract_checked_ranked_weights(&weights, &edges, &cert),
        Err(Error::Overflow)
    ));
}

#[test]
fn large_ranked_chain_has_linear_certificate_size() {
    let n = 2000usize;
    let mut region = EqualityComponentRegion::new(vec![[1, 0]; n]);
    for i in 1..n {
        region.apply_equality(i - 1, i).unwrap();
    }
    region.apply_equality(0, n - 1).unwrap();
    let (receipt, certificate) = region.contract_with_ranked_certificate().unwrap();
    assert_eq!(receipt.value, 1);
    assert_eq!(receipt.component_count, 1);
    assert_eq!(receipt.checked_multiplications, 2 * n + 1);
    assert_eq!(receipt.checked_additions, 1);
    assert_eq!(certificate.parent_edge_indices.iter().flatten().count(), n - 1);
    assert_eq!(
        verify_ranked_component_certificate(n, region.source_edges(), &certificate)
            .unwrap()
            .parent_links,
        n - 1
    );
}

#[test]
fn empty_certificate_has_zero_fake_components() {
    let region = EqualityComponentRegion::new(vec![]);
    let (receipt, certificate) = region.contract_with_ranked_certificate().unwrap();
    assert_eq!(receipt.value, 1);
    assert!(certificate.labels.is_empty());
    assert!(certificate.roots.is_empty());
    assert_eq!(
        verify_ranked_component_certificate(0, &[], &certificate)
            .unwrap()
            .components,
        0
    );
}
