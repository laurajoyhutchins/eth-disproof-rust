//! Adversarial acceptance tests for independently checked partition evidence.

use lean_eth_reference::representation_component_certificate::{
    ComponentCertificate, verify_component_certificate,
};
use lean_eth_reference::representation_equality_components::EqualityComponentRegion;

#[test]
fn every_small_simple_graph_produces_a_verified_spanning_forest() {
    for n in 0..=5usize {
        let candidates: Vec<(usize, usize)> = (0..n)
            .flat_map(|a| (a + 1..n).map(move |b| (a, b)))
            .collect();
        for graph in 0..(1usize << candidates.len()) {
            let mut region = EqualityComponentRegion::new(vec![[1, 1]; n]);
            for (i, &(a, b)) in candidates.iter().enumerate() {
                if graph & (1 << i) != 0 {
                    region.apply_equality(a, b).unwrap();
                }
            }
            let (receipt, certificate) = region.contract_with_certificate().unwrap();
            let verified =
                verify_component_certificate(region.len(), region.source_edges(), &certificate)
                    .unwrap();
            assert_eq!(verified.variables, n);
            assert_eq!(verified.original_edges, region.edge_count());
            assert_eq!(verified.components, region.component_count());
            assert_eq!(verified.forest_edges, n - region.component_count());
            assert_eq!(receipt.value, 1i128 << verified.components);
        }
    }
}

#[test]
fn overlap_duplicates_self_edges_and_reversal_still_certify() {
    let mut region = EqualityComponentRegion::new(vec![[2, 3]; 6]);
    for (a, b) in [(2, 3), (1, 2), (2, 3), (0, 0), (3, 4), (4, 1)] {
        region.apply_equality(a, b).unwrap();
    }
    let (_, certificate) = region.contract_with_certificate().unwrap();
    assert_eq!(certificate.labels, vec![0, 1, 1, 1, 1, 2]);
    assert_eq!(certificate.forest_edge_indices.len(), 3);
    assert_eq!(
        verify_component_certificate(6, region.source_edges(), &certificate)
            .unwrap()
            .components,
        3
    );
    let mut reversed = EqualityComponentRegion::new(vec![[2, 3]; 6]);
    for &(a, b) in region.source_edges().iter().rev() {
        reversed.apply_equality(b, a).unwrap();
    }
    let (_, reverse_certificate) = reversed.contract_with_certificate().unwrap();
    assert_eq!(reverse_certificate.labels, certificate.labels);
}

#[test]
fn forged_splits_are_rejected_by_source_edge_closure() {
    let edges = [(0, 1), (1, 2), (2, 3)];
    let certificate = ComponentCertificate {
        labels: vec![0, 0, 1, 1],
        forest_edge_indices: vec![0, 2],
    };
    assert!(verify_component_certificate(4, &edges, &certificate).is_err());
}

#[test]
fn forged_merges_are_rejected_by_missing_forest_paths() {
    let edges = [(0, 1), (1, 2), (2, 0)];
    // The claimed class merges the triangle with disconnected vertex 3.
    // Three genuine source edges give the right count but form a cycle,
    // not a spanning tree. Only independent reachability detects this.
    let certificate = ComponentCertificate {
        labels: vec![0, 0, 0, 0],
        forest_edge_indices: vec![0, 1, 2],
    };
    assert!(verify_component_certificate(4, &edges, &certificate).is_err());
}

#[test]
fn incomplete_witness_and_forged_edge_references_are_rejected() {
    let edges = [(0, 1), (1, 2)];
    let good = ComponentCertificate {
        labels: vec![0, 0, 0],
        forest_edge_indices: vec![0, 1],
    };
    assert!(verify_component_certificate(3, &edges, &good).is_ok());

    let missing = ComponentCertificate {
        forest_edge_indices: vec![0],
        ..good.clone()
    };
    assert!(verify_component_certificate(3, &edges, &missing).is_err());

    let foreign = ComponentCertificate {
        forest_edge_indices: vec![0, 99],
        ..good.clone()
    };
    assert!(verify_component_certificate(3, &edges, &foreign).is_err());

    let duplicate = ComponentCertificate {
        forest_edge_indices: vec![0, 0],
        ..good
    };
    assert!(verify_component_certificate(3, &edges, &duplicate).is_err());
}

#[test]
fn malformed_labels_and_untrusted_source_endpoints_are_rejected() {
    let source = [(0, 1), (2, 3)];
    for labels in [
        vec![0, 0, 1],
        vec![0, 0, 2, 2],
        vec![0, 0, usize::MAX, usize::MAX],
    ] {
        let cert = ComponentCertificate {
            labels,
            forest_edge_indices: vec![0, 1],
        };
        assert!(verify_component_certificate(4, &source, &cert).is_err());
    }
    let correct = ComponentCertificate {
        labels: vec![0, 0, 1, 1],
        forest_edge_indices: vec![0, 1],
    };
    assert!(verify_component_certificate(4, &source, &correct).is_ok());
    // A certificate for the original source is not evidence for this
    // changed graph. Its crossing edge must be rejected.
    assert!(verify_component_certificate(4, &[(0, 2), (2, 3)], &correct).is_err());
    assert!(verify_component_certificate(4, &[(0, 8), (2, 3)], &correct).is_err());
}

#[test]
fn empty_graph_and_thousand_pair_witness() {
    let empty = EqualityComponentRegion::new(vec![]);
    let (_, cert) = empty.contract_with_certificate().unwrap();
    assert!(cert.labels.is_empty());
    assert!(cert.forest_edge_indices.is_empty());
    assert_eq!(
        verify_component_certificate(0, &[], &cert)
            .unwrap()
            .components,
        0
    );

    let mut region = EqualityComponentRegion::new(vec![[1, 0]; 2000]);
    for i in (0..2000).step_by(2) {
        region.apply_equality(i, i + 1).unwrap();
    }
    for i in (0..2000).step_by(2) {
        region.apply_equality(i + 1, i).unwrap();
    }
    let (receipt, certificate) = region.contract_with_certificate().unwrap();
    let verified = verify_component_certificate(2000, region.source_edges(), &certificate).unwrap();
    assert_eq!(receipt.value, 1);
    assert_eq!(verified.components, 1000);
    assert_eq!(verified.forest_edges, 1000);
    assert_eq!(receipt.checked_additions, 1000);
}
