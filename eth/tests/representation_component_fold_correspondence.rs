//! The production vertex-major accumulator versus an independent grouped oracle.
//!
//! The oracle first collects separate 0/1 weight lists per certified class
//! and contracts them in class-major order. Production instead updates its
//! dense class product table in vertex order. Both must agree on success,
//! refusal, and exact value for the tested certificates.
//!
//! This differential test is not a formal verification of Rust i128 machine
//! instructions or the producer's DSU.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::{
    RankedComponentCertificate, contract_checked_ranked_weights,
    verify_ranked_component_certificate,
};

fn star_certificate(labels: Vec<usize>, classes: usize) -> (
    Vec<(usize, usize)>,
    RankedComponentCertificate,
) {
    let n = labels.len();
    let mut edges = Vec::new();
    let mut roots = vec![usize::MAX; classes];
    let mut parent_edge_indices = vec![None; n];
    let mut rank = vec![0usize; n];
    for (i, &class) in labels.iter().enumerate() {
        if roots[class] == usize::MAX {
            roots[class] = i;
        } else {
            parent_edge_indices[i] = Some(edges.len());
            edges.push((roots[class], i));
            rank[i] = 1;
        }
    }
    (
        edges,
        RankedComponentCertificate {
            labels,
            roots,
            parent_edge_indices,
            rank,
        },
    )
}

/// Independent class-major specification. It deliberately does not update
/// products in the vertex-major order of the implementation under test.
fn grouped_reference(
    weights: &[[i128; 2]],
    labels: &[usize],
    classes: usize,
) -> Option<i128> {
    if weights.len() != labels.len() {
        return None;
    }
    let mut groups = vec![(Vec::<i128>::new(), Vec::<i128>::new()); classes];
    for (&class, &pair) in labels.iter().zip(weights.iter()) {
        let (zeros, ones) = groups.get_mut(class)?;
        zeros.push(pair[0]);
        ones.push(pair[1]);
    }
    let mut answer = 1i128;
    for (zeros, ones) in groups {
        let mut zero = 1i128;
        let mut one = 1i128;
        for value in zeros {
            zero = zero.checked_mul(value)?;
        }
        for value in ones {
            one = one.checked_mul(value)?;
        }
        answer = answer.checked_mul(zero.checked_add(one)?)?;
    }
    Some(answer)
}

fn digits(mut code: usize, base: usize, n: usize) -> Vec<usize> {
    (0..n)
        .map(|_| {
            let digit = code % base;
            code /= base;
            digit
        })
        .collect()
}

#[test]
fn independently_grouped_oracle_matches_vertex_major_accumulator() {
    for n in 0..=5usize {
        for classes in 0..=n.min(3) {
            if classes == 0 && n != 0 {
                continue;
            }
            let base = classes.max(1);
            for code in 0..base.pow(n as u32) {
                let labels = digits(code, base, n);
                if (0..classes).any(|k| !labels.contains(&k)) {
                    continue;
                }
                let (edges, certificate) = star_certificate(labels, classes);
                let verified =
                    verify_ranked_component_certificate(n, &edges, &certificate).unwrap();
                assert_eq!(verified.components, classes);
                assert_eq!(verified.parent_links, n - classes);

                for seed in 0..5i128 {
                    let weights: Vec<[i128; 2]> = (0..n)
                        .map(|i| {
                            let x = i as i128;
                            [((x * 7 + seed * 3) % 7) - 3, ((x * 5 + seed) % 9) - 4]
                        })
                        .collect();
                    let actual =
                        contract_checked_ranked_weights(&weights, &edges, &certificate).unwrap();
                    let expected = grouped_reference(&weights, &certificate.labels, classes);
                    assert_eq!(Some(actual.value), expected);
                    assert_eq!(actual.checked_additions, classes);
                    assert_eq!(actual.checked_multiplications, 2 * n + classes);
                }
            }
        }
    }
}

#[test]
fn grouped_oracle_matches_refusal_and_success_near_i128_boundaries() {
    const BOUNDS: [i128; 8] = [
        i128::MIN,
        i128::MIN + 1,
        -3,
        -1,
        0,
        1,
        3,
        i128::MAX,
    ];
    for n in 1..=4usize {
        let classes = 2usize.min(n);
        for code in 0..classes.pow(n as u32) {
            let labels = digits(code, classes, n);
            if (0..classes).any(|k| !labels.contains(&k)) {
                continue;
            }
            let (edges, certificate) = star_certificate(labels, classes);
            for seed in 0..64usize {
                let weights: Vec<[i128; 2]> = (0..n)
                    .map(|i| {
                        [
                            BOUNDS[(seed + 3 * i) % BOUNDS.len()],
                            BOUNDS[(seed * 3 + 5 * i) % BOUNDS.len()],
                        ]
                    })
                    .collect();
                let actual = contract_checked_ranked_weights(&weights, &edges, &certificate);
                let expected = grouped_reference(&weights, &certificate.labels, classes);
                match (actual, expected) {
                    (Ok(receipt), Some(value)) => assert_eq!(receipt.value, value),
                    (Err(Error::Overflow), None) => {}
                    (other, reference) => {
                        panic!("mismatch: {other:?}, grouped reference: {reference:?}");
                    }
                }
            }
        }
    }
}

#[test]
fn source_certificate_is_rechecked_before_any_arithmetic() {
    let (edges, certificate) = star_certificate(vec![0, 0, 1, 1], 2);
    let weights = [[2, 3], [5, 7], [11, 13], [17, 19]];
    assert!(contract_checked_ranked_weights(&weights, &edges, &certificate).is_ok());

    let mut corrupt = certificate.clone();
    corrupt.labels[1] = 1;
    assert!(contract_checked_ranked_weights(&weights, &edges, &corrupt).is_err());

    let mut forged_edges = edges;
    forged_edges[0] = (0, 2);
    assert!(contract_checked_ranked_weights(&weights, &forged_edges, &certificate).is_err());
}
