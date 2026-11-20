//! Multi-step differential evidence for the actual vertex-major scan helper.
//!
//! The oracle is a separate indexed array loop. A failed *step* leaves its
//! target unchanged; a failed *scan* retains all successful earlier steps.
//! This distinction is deliberate and part of the test contract.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::checked_component_product_scan;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ModelFailure {
    Width,
    Class,
    Overflow,
}

fn reference_scan(
    products: &mut [[i128; 2]],
    labels: &[usize],
    weights: &[[i128; 2]],
) -> Result<(), ModelFailure> {
    if labels.len() != weights.len() {
        return Err(ModelFailure::Width);
    }
    for (i, &label) in labels.iter().enumerate() {
        let Some(&[before_zero, before_one]) = products.get(label) else {
            return Err(ModelFailure::Class);
        };
        let Some(next_zero) = before_zero.checked_mul(weights[i][0]) else {
            return Err(ModelFailure::Overflow);
        };
        let Some(next_one) = before_one.checked_mul(weights[i][1]) else {
            return Err(ModelFailure::Overflow);
        };
        products[label] = [next_zero, next_one];
    }
    Ok(())
}

fn digits(mut code: usize, radix: usize, len: usize) -> Vec<usize> {
    (0..len)
        .map(|_| {
            let digit = code % radix;
            code /= radix;
            digit
        })
        .collect()
}

#[test]
fn all_small_scans_match_reference_state_and_refusal() {
    for classes in 0..=3usize {
        let radix = classes + 1; // One additional invalid label for each width.
        for len in 0..=4usize {
            for code in 0..radix.pow(len as u32) {
                let labels = digits(code, radix, len);
                for seed in 0..17i128 {
                    let mut model = vec![[1i128, 1]; classes];
                    let mut actual = model.clone();
                    let weights: Vec<[i128; 2]> = (0..len)
                        .map(|i| {
                            let x = i as i128;
                            [((x * 5 + seed * 3) % 13) - 6, ((x * 7 + seed) % 11) - 5]
                        })
                        .collect();
                    let expected = reference_scan(&mut model, &labels, &weights);
                    let result = checked_component_product_scan(&mut actual, &labels, &weights);
                    assert_eq!(
                        actual, model,
                        "classes={classes} labels={labels:?} seed={seed}"
                    );
                    match (expected, result) {
                        (Ok(()), Ok(())) => {}
                        (Err(ModelFailure::Class), Err(Error::Invalid(_))) => {}
                        (Err(ModelFailure::Overflow), Err(Error::Overflow)) => {}
                        (other, actual) => panic!("expected {other:?}, actual {actual:?}"),
                    }
                }
            }
        }
    }
}

#[test]
fn a_later_overflow_keeps_prior_prefix_but_not_failing_step() {
    let weights = [[2, 3], [5, 7], [4, 2], [1, 1]];
    let labels = [0, 1, 0, 1];
    let mut products = vec![[1, 1], [i128::MAX, 1]];
    let result = checked_component_product_scan(&mut products, &labels, &weights);
    assert!(matches!(result, Err(Error::Overflow)));
    // The first vertex commits, the second overflows in its first product.
    assert_eq!(products, vec![[2, 3], [i128::MAX, 1]]);

    let mut products = vec![[1, 1], [2, i128::MAX]];
    let result = checked_component_product_scan(&mut products, &labels, &weights);
    assert!(matches!(result, Err(Error::Overflow)));
    // The first multiplication of the failing step fits (2*5);
    // its second multiplication fails, so neither term commits.
    assert_eq!(products, vec![[2, 3], [2, i128::MAX]]);
}

#[test]
fn mismatched_widths_refuse_without_writing_any_prefix() {
    let mut products = vec![[2i128, 3], [5, 7]];
    let original = products.clone();
    assert!(matches!(
        checked_component_product_scan(&mut products, &[0, 1], &[[13, 17]]),
        Err(Error::Invalid(_))
    ));
    assert_eq!(products, original);
    assert!(matches!(
        checked_component_product_scan(&mut products, &[0], &[[1, 1], [2, 2]]),
        Err(Error::Invalid(_))
    ));
    assert_eq!(products, original);
}

#[test]
fn empty_scan_is_the_identity_for_zero_or_nonzero_classes() {
    for classes in 0..=4usize {
        let mut products = vec![[11i128, -9]; classes];
        let old = products.clone();
        checked_component_product_scan(&mut products, &[], &[]).unwrap();
        assert_eq!(products, old);
    }
}

#[test]
fn zero_and_extreme_weights_match_reference_scan() {
    let special = [i128::MIN, i128::MAX, -1, 0, 1, 2, -2];
    for classes in 1..=3usize {
        for seed in 0..special.len() {
            let labels = [0usize, classes - 1, 0, classes - 1];
            let weights = [
                [special[seed], 1],
                [special[(seed + 1) % special.len()], -1],
                [0, special[(seed + 2) % special.len()]],
                [special[(seed + 3) % special.len()], 2],
            ];
            let mut model = vec![[1i128, 1]; classes];
            let mut actual = model.clone();
            let expected = reference_scan(&mut model, &labels, &weights);
            let outcome = checked_component_product_scan(&mut actual, &labels, &weights);
            assert_eq!(actual, model);
            match (expected, outcome) {
                (Ok(()), Ok(())) => {}
                (Err(ModelFailure::Overflow), Err(Error::Overflow)) => {}
                (other, actual) => panic!("expected {other:?}, actual {actual:?}"),
            }
        }
    }
}
