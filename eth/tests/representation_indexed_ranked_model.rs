//! Model-based differential tests for the source-indexed ranked guard.
//!
//! The model below states all guards independently as Boolean predicates
//! over read-only arrays. The implementation under test uses early-refusal
//! loops, and must accept exactly the same finite test cases. This is
//! evidence, not a machine-checked Lean-to-Rust refinement.

use lean_eth_reference::representation_ranked_certificate::{
    RankedComponentCertificate, verify_ranked_component_certificate,
};

fn indexed_guard_model(
    n: usize,
    edges: &[(usize, usize)],
    cert: &RankedComponentCertificate,
) -> bool {
    let c = cert.roots.len();
    if c > n
        || cert.labels.len() != n
        || cert.parent_edge_indices.len() != n
        || cert.rank.len() != n
        || edges.iter().any(|&(a, b)| a >= n || b >= n)
        || cert.labels.iter().any(|&label| label >= c)
    {
        return false;
    }
    let source_closed = edges.iter().all(|&(a, b)| cert.labels[a] == cert.labels[b]);
    let root_guards = cert.roots.iter().enumerate().all(|(class, &root)| {
        root < n
            && cert.labels[root] == class
            && cert.parent_edge_indices[root].is_none()
            && cert.rank[root] == 0
    });
    let vertex_guards =
        cert.parent_edge_indices
            .iter()
            .enumerate()
            .all(|(i, parent)| match parent {
                None => i == cert.roots[cert.labels[i]] && cert.rank[i] == 0,
                Some(index) => edges.get(*index).is_some_and(|&(a, b)| {
                    let neighbor = if a == i {
                        Some(b)
                    } else if b == i {
                        Some(a)
                    } else {
                        None
                    };
                    neighbor.is_some_and(|p| {
                        cert.labels[p] == cert.labels[i] && cert.rank[p] < cert.rank[i]
                    })
                }),
            });
    source_closed && root_guards && vertex_guards
}

fn digits(mut code: usize, radix: usize, count: usize) -> Vec<usize> {
    (0..count)
        .map(|_| {
            let digit = code % radix;
            code /= radix;
            digit
        })
        .collect()
}

#[test]
fn indexed_model_and_early_refusal_loops_agree_on_small_certificates() {
    let n = 3usize;
    let sources: [&[(usize, usize)]; 4] =
        [&[], &[(0, 1)], &[(0, 1), (1, 2)], &[(0, 1), (1, 2), (2, 0)]];
    for source in sources {
        let parent_radix = source.len() + 2; // None, valid indices, one invalid index.
        let parent_combinations = parent_radix.pow(n as u32);
        for classes in 0..=2usize {
            let labels_combinations = classes.pow(n as u32);
            for label_code in 0..labels_combinations {
                let labels = digits(label_code, classes, n);
                for root_code in 0..n.pow(classes as u32) {
                    let roots = digits(root_code, n, classes);
                    for parent_code in 0..parent_combinations {
                        let parent_edge_indices: Vec<Option<usize>> = digits(parent_code, parent_radix, n)
                            .into_iter()
                            .map(|digit| (digit != 0).then(|| digit - 1))
                            .collect();
                        for rank_code in 0..3usize.pow(n as u32) {
                            let cert = RankedComponentCertificate {
                                labels: labels.clone(),
                                roots: roots.clone(),
                                parent_edge_indices: parent_edge_indices.clone(),
                                rank: digits(rank_code, 3, n),
                            };
                            assert_eq!(
                                verify_ranked_component_certificate(n, source, &cert).is_ok(),
                                indexed_guard_model(n, source, &cert),
                                "source={source:?}, cert={cert:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn exact_lean_fixture_translation_and_nonincident_refusal() {
    let source = [(0, 1)];
    let positive = RankedComponentCertificate {
        labels: vec![0, 0, 1],
        roots: vec![0, 2],
        parent_edge_indices: vec![None, Some(0), None],
        rank: vec![0, 1, 0],
    };
    assert!(indexed_guard_model(3, &source, &positive));
    assert!(verify_ranked_component_certificate(3, &source, &positive).is_ok());

    let malformed = RankedComponentCertificate {
        parent_edge_indices: vec![None, Some(0), Some(0)],
        ..positive
    };
    assert!(!indexed_guard_model(3, &source, &malformed));
    assert!(verify_ranked_component_certificate(3, &source, &malformed).is_err());
}
