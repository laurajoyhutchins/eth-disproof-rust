//! One-step array transition correspondence tests.
//!
//! The production contraction now calls the same checked array-update
//! primitive exercised here. The tests use an independent whole-array
//! mathematical model to check target selection and preservation of every
//! off-target slot; they are not a Lean-to-Rust refinement proof.

use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::checked_component_product_step;

fn reference_step(
    slots: &[[i128; 2]],
    class: usize,
    weights: [i128; 2],
) -> Option<Vec<[i128; 2]>> {
    let old = *slots.get(class)?;
    let zero = old[0].checked_mul(weights[0])?;
    let one = old[1].checked_mul(weights[1])?;
    let mut out = slots.to_vec();
    out[class] = [zero, one];
    Some(out)
}

#[test]
fn every_small_array_update_matches_independent_model() {
    for len in 0..=5usize {
        for class in 0..=len {
            for seed in 0..63i128 {
                let original: Vec<_> = (0..len)
                    .map(|i| {
                        let x = i as i128;
                        [((x * 13 + seed * 7) % 17) - 8, ((x * 5 + seed * 3) % 19) - 9]
                    })
                    .collect();
                let weights = [((seed * 3) % 13) - 6, ((seed * 7) % 11) - 5];
                let expected = reference_step(&original, class, weights);
                let mut actual = original.clone();
                let result = checked_component_product_step(&mut actual, class, weights);
                match expected {
                    Some(reference) => {
                        result.unwrap();
                        assert_eq!(actual, reference, "len={len}, class={class}, seed={seed}");
                        for i in 0..len {
                            if i != class {
                                assert_eq!(actual[i], original[i]);
                            }
                        }
                    }
                    None => {
                        assert!(matches!(result, Err(Error::Invalid(_))));
                        assert_eq!(actual, original);
                    }
                }
            }
        }
    }
}

#[test]
fn both_checked_products_are_atomic_on_second_product_overflow() {
    let original = vec![[9, 7], [3, i128::MAX], [-2, 11]];
    let mut actual = original.clone();
    assert!(matches!(
        checked_component_product_step(&mut actual, 1, [4, 2]),
        Err(Error::Overflow)
    ));
    // The first product (3 * 4) fits. The second one overflows.
    // Neither component-product slot may be mutated.
    assert_eq!(actual, original);

    let mut first_overflow = original.clone();
    assert!(matches!(
        checked_component_product_step(&mut first_overflow, 1, [i128::MAX, 0]),
        Err(Error::Overflow)
    ));
    assert_eq!(first_overflow, original);
}

#[test]
fn single_step_accepts_exact_signed_minimum_and_rejects_out_of_range() {
    let mut products = [[-1i128, 1]];
    checked_component_product_step(&mut products, 0, [i128::MAX, i128::MIN]).unwrap();
    assert_eq!(products, [[-i128::MAX, i128::MIN]]);

    let mut underflow = [[i128::MIN, 4]];
    assert!(matches!(
        checked_component_product_step(&mut underflow, 0, [-1, 3]),
        Err(Error::Overflow)
    ));
    assert_eq!(underflow, [[i128::MIN, 4]]);
}

#[test]
fn duplicate_component_updates_preserve_the_source_order_semantics() {
    let mut products = vec![[1, 1]; 3];
    let items = [
        (2usize, [2, -1]),
        (0usize, [3, 4]),
        (2usize, [5, 0]),
        (1usize, [-3, 7]),
        (0usize, [-2, 2]),
    ];
    for (class, weights) in items {
        checked_component_product_step(&mut products, class, weights).unwrap();
    }
    assert_eq!(products, vec![[-6, 8], [-3, 7], [10, 0]]);
}
