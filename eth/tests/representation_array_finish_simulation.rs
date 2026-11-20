//! Independent checks of the production class-major checked finalizer.
//!
//! The oracle uses iterator folds rather than the production loop. It
//! preserves intermediate-overflow refusal, including overflowing class
//! sums before subsequent zero factors. The input is immutable.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::checked_component_product_finish;

const SMALL: [i128; 5] = [-2, -1, 0, 1, 2];

fn reference_finish(products: &[[i128; 2]]) -> Option<i128> {
    products.iter().try_fold(1i128, |acc, pair| {
        let local = pair.iter().try_fold(0i128, |sum, x| sum.checked_add(*x))?;
        acc.checked_mul(local)
    })
}

fn decode(mut value: usize, classes: usize) -> Vec<[i128; 2]> {
    (0..classes)
        .map(|_| {
            let zero = SMALL[value % SMALL.len()];
            value /= SMALL.len();
            let one = SMALL[value % SMALL.len()];
            value /= SMALL.len();
            [zero, one]
        })
        .collect()
}

#[test]
fn exhaustive_small_classes_match_checked_reference() {
    for classes in 0..=3usize {
        for code in 0..(SMALL.len() * SMALL.len()).pow(classes as u32) {
            let products = decode(code, classes);
            let original = products.clone();
            let expected = reference_finish(&products);
            let actual = checked_component_product_finish(&products);
            match (expected, actual) {
                (Some(reference), Ok(value)) => assert_eq!(value, reference),
                (None, Err(Error::Overflow)) => {}
                (reference, other) => panic!("expected {reference:?}, got {other:?}"),
            }
            assert_eq!(products, original, "finalization must not mutate source");
        }
    }
}

#[test]
fn signed_boundaries_and_zero_classes() {
    assert_eq!(checked_component_product_finish(&[]).unwrap(), 1);
    assert_eq!(checked_component_product_finish(&[[0, 0]]).unwrap(), 0);
    assert_eq!(
        checked_component_product_finish(&[[i128::MIN, 0]]).unwrap(),
        i128::MIN
    );
    assert_eq!(
        checked_component_product_finish(&[[i128::MAX, 0]]).unwrap(),
        i128::MAX
    );
    assert_eq!(
        checked_component_product_finish(&[[5, -7], [-3, 4]]).unwrap(),
        -2
    );
}

#[test]
fn rejects_early_addition_overflow_even_if_later_zero() {
    let products = [[i128::MAX, 1], [0, 0]];
    assert!(matches!(
        checked_component_product_finish(&products),
        Err(Error::Overflow)
    ));
    assert_eq!(products, [[i128::MAX, 1], [0, 0]]);

    let products = [[-1, 0], [i128::MIN, -1], [0, 0]];
    assert!(matches!(
        checked_component_product_finish(&products),
        Err(Error::Overflow)
    ));
}

#[test]
fn rejects_running_multiplication_overflow_but_not_after_early_zero() {
    let products = [[i128::MAX, 0], [2, 0]];
    assert!(matches!(
        checked_component_product_finish(&products),
        Err(Error::Overflow)
    ));
    assert_eq!(
        checked_component_product_finish(&[[0, 0], [i128::MAX, 0], [2, 0]]).unwrap(),
        0
    );
    // Even after the zero has made the running count zero, each subsequent
    // local sum is checked independently and may still fail.
    assert!(matches!(
        checked_component_product_finish(&[[0, 0], [i128::MAX, 1]]),
        Err(Error::Overflow)
    ));
}

#[test]
fn short_boundary_sequences_match_reference() {
    const BOUNDS: [i128; 8] = [i128::MIN, i128::MAX, i128::MIN + 1, -2, -1, 0, 1, 2];
    for classes in 0..=5usize {
        for seed in 0..128usize {
            let products: Vec<_> = (0..classes)
                .map(|k| {
                    [
                        BOUNDS[(seed + 3 * k) % BOUNDS.len()],
                        BOUNDS[(seed * 5 + 7 * k) % BOUNDS.len()],
                    ]
                })
                .collect();
            let expected = reference_finish(&products);
            match (expected, checked_component_product_finish(&products)) {
                (Some(value), Ok(actual)) => assert_eq!(actual, value),
                (None, Err(Error::Overflow)) => {}
                (expected, actual) => panic!("expected {expected:?}, got {actual:?}"),
            }
        }
    }
}
