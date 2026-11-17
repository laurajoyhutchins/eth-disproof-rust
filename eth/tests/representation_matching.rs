use lean_eth_reference::Error;
use lean_eth_reference::representation_matching::MatchingRegion;

fn enumerate(region: &MatchingRegion) -> i128 {
    assert!(region.len() <= 8, "bounded independent oracle");
    (0..(1usize << region.len()))
        .map(|mask| {
            let bits: Vec<bool> = (0..region.len()).map(|i| (mask >> i) & 1 != 0).collect();
            region.value_at(&bits).expect("small exact oracle")
        })
        .sum()
}

#[test]
fn every_small_disjoint_matching_agrees_with_full_enumeration() {
    for n in 0..=8 {
        let unary: Vec<[i128; 2]> = (0..n)
            .map(|i| [i as i128 % 3 - 1, (i as i128 * 2) % 5 - 2])
            .collect();
        for start in 0..=2 {
            let mut region = MatchingRegion::new(unary.clone());
            let mut i = start;
            while i + 1 < n {
                region.apply_equality(i, i + 1).unwrap();
                i += 2;
            }
            let receipt = region.contract().unwrap();
            assert_eq!(receipt.value, enumerate(&region), "n={n}, start={start}");
            assert_eq!(receipt.variable_count, n);
            assert_eq!(receipt.additions, n - receipt.equality_pairs);
            assert_eq!(receipt.multiplications, n + receipt.equality_pairs);
        }
    }
}

#[test]
fn crossing_or_repeated_edges_refuse_without_mutation() {
    let mut region = MatchingRegion::new(vec![[1, 2]; 4]);
    region.apply_equality(0, 1).unwrap();
    let original = region.clone();
    for (left, right) in [(1, 2), (0, 1), (1, 3)] {
        assert!(matches!(
            region.apply_equality(left, right),
            Err(Error::Capacity(_))
        ));
        assert_eq!(region, original);
    }
    assert!(matches!(
        region.apply_equality(2, 2),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(
        region.apply_equality(2, 4),
        Err(Error::Invalid(_))
    ));
    assert!(region.as_unary_product_if_unconstrained().is_err());
}

#[test]
fn product_conversion_is_exact_only_for_certified_unconstrained_case() {
    let mut region = MatchingRegion::new(vec![[2, 3], [4, 5]]);
    assert_eq!(
        region.as_unary_product_if_unconstrained().unwrap(),
        &[[2, 3], [4, 5]]
    );
    assert_eq!(region.contract().unwrap().value, (2 + 3) * (4 + 5));
    region.apply_equality(0, 1).unwrap();
    assert_eq!(region.contract().unwrap().value, 2 * 4 + 3 * 5);
    assert!(region.as_unary_product_if_unconstrained().is_err());
}

#[test]
fn large_matching_is_processed_without_materializing_the_boolean_cube() {
    let mut region = MatchingRegion::new(vec![[1, 0]; 2000]);
    for i in (0..2000).step_by(2) {
        region.apply_equality(i, i + 1).unwrap();
    }
    let receipt = region.contract().unwrap();
    assert_eq!(receipt.value, 1);
    assert_eq!(receipt.equality_pairs, 1000);
    assert_eq!(receipt.additions, 1000);
    assert_eq!(receipt.multiplications, 3000);
}

#[test]
fn bounded_arithmetic_refuses_overflow_and_invalid_assignments() {
    let region = MatchingRegion::new(vec![[i128::MAX, 1]]);
    assert!(matches!(region.contract(), Err(Error::Overflow)));
    assert!(matches!(region.value_at(&[]), Err(Error::Invalid(_))));
    let mut constrained = MatchingRegion::new(vec![[i128::MAX, 2], [i128::MAX, 3]]);
    constrained.apply_equality(0, 1).unwrap();
    assert_eq!(constrained.value_at(&[false, true]).unwrap(), 0);
    assert!(matches!(constrained.contract(), Err(Error::Overflow)));
}

#[test]
fn empty_region_has_the_multiplicative_identity() {
    let region = MatchingRegion::new(vec![]);
    assert!(region.is_empty());
    let receipt = region.contract().unwrap();
    assert_eq!(receipt.value, 1);
    assert_eq!(receipt.additions, 0);
    assert_eq!(receipt.multiplications, 0);
}
