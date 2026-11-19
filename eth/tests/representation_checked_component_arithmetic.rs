//! Machine-boundary tests for the checked signed component fold.
//! These cases complement the Lean Option-valued arithmetic interpreter;
//! they do not constitute a Rust-to-Lean machine-code refinement.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::{
    RankedComponentCertificate, contract_checked_ranked_weights,
};

fn singleton() -> RankedComponentCertificate {
    RankedComponentCertificate {
        labels: vec![0],
        roots: vec![0],
        parent_edge_indices: vec![None],
        rank: vec![0],
    }
}

fn connected_pair() -> RankedComponentCertificate {
    RankedComponentCertificate {
        labels: vec![0, 0],
        roots: vec![0],
        parent_edge_indices: vec![None, Some(0)],
        rank: vec![0, 1],
    }
}

#[test]
fn asymmetric_minimum_is_a_representable_exact_answer() {
    let receipt =
        contract_checked_ranked_weights(&[[i128::MIN, 0]], &[], &singleton()).unwrap();
    assert_eq!(receipt.value, i128::MIN);
    assert_eq!(receipt.checked_multiplications, 3);
    assert_eq!(receipt.checked_additions, 1);
}

#[test]
fn positive_limit_and_negative_overflow_both_refuse() {
    assert!(matches!(
        contract_checked_ranked_weights(&[[i128::MAX, 1]], &[], &singleton()),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        contract_checked_ranked_weights(
            &[[i128::MIN, 0], [-1, 0]],
            &[(0, 1)],
            &connected_pair(),
        ),
        Err(Error::Overflow)
    ));
}

#[test]
fn negative_weights_preserve_integer_semantics() {
    let receipt =
        contract_checked_ranked_weights(&[[-3, 5], [7, -2]], &[(0, 1)], &connected_pair())
            .unwrap();
    assert_eq!(receipt.value, -31);
    assert_eq!(receipt.checked_multiplications, 5);
    assert_eq!(receipt.checked_additions, 1);
}

#[test]
fn intermediate_overflow_refuses_even_when_later_zero_would_cancel() {
    let cert = RankedComponentCertificate {
        labels: vec![0, 0, 0],
        roots: vec![0],
        parent_edge_indices: vec![None, Some(0), Some(1)],
        rank: vec![0, 1, 2],
    };
    let edges = [(0, 1), (1, 2)];
    let weights = [[i128::MAX, 1], [2, 1], [0, 0]];
    // The unbounded mathematical answer is zero, but an earlier checked
    // product overflows; the implementation must refuse, not wrap.
    assert!(matches!(
        contract_checked_ranked_weights(&weights, &edges, &cert),
        Err(Error::Overflow)
    ));
}
