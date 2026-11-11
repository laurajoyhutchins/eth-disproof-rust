use lean_eth_reference::Error;
use lean_eth_reference::valuation_modes::{CrossingMode, Policy, count_tuples, visit_tuples};

#[test]
fn stronger_precision_budget_is_a_subset_and_counts_match_visits() {
    for p in 1..=15 {
        let modes = [
            CrossingMode { a: 5, i: 4, b: 0 },
            CrossingMode { a: 5, i: 3, b: 1 },
            CrossingMode { a: 5, i: 5, b: 0 },
        ];
        let mut original = Vec::new();
        let mut stronger = Vec::new();
        let n0 = visit_tuples(&modes, p, Policy::Original, 100_000, |x| {
            original.push(x.to_vec())
        })
        .unwrap();
        let n1 = visit_tuples(&modes, p, Policy::Stronger, 100_000, |x| {
            stronger.push(x.to_vec())
        })
        .unwrap();
        assert_eq!(n0, count_tuples(&modes, p, Policy::Original).unwrap());
        assert_eq!(n1, count_tuples(&modes, p, Policy::Stronger).unwrap());
        assert!(stronger.iter().all(|x| original.contains(x)));
        assert!(n1 <= n0);
    }
}

#[test]
fn every_removed_mode_monomial_is_zero_modulo_required_precision() {
    for p in 1..=13 {
        let modes = [
            CrossingMode { a: 6, i: 3, b: 0 },
            CrossingMode { a: 6, i: 5, b: 1 },
            CrossingMode { a: 6, i: 6, b: 0 },
        ];
        let modulus = 1u128 << p;
        let coefs = modes.map(|m| (1u128 << m.stronger_weight().unwrap()) * 3);
        let eval = |exponents: &[usize]| -> u128 {
            exponents.iter().zip(coefs).fold(1u128, |product, (&e, c)| {
                let mut part = 1u128;
                for _ in 0..e {
                    part = (part * c) % modulus;
                }
                (product * part) % modulus
            })
        };
        let mut old = 0u128;
        let mut new = 0u128;
        let mut surviving = Vec::new();
        visit_tuples(&modes, p, Policy::Stronger, 100_000, |x| {
            surviving.push(x.to_vec());
            new = (new + eval(x)) % modulus;
        })
        .unwrap();
        visit_tuples(&modes, p, Policy::Original, 100_000, |x| {
            let term = eval(x);
            if !surviving.contains(&x.to_vec()) {
                assert_eq!(term, 0, "removed tuple survives modulo 2^{p}: {x:?}");
            }
            old = (old + term) % modulus;
        })
        .unwrap();
        assert_eq!(new, old);
    }
}

#[test]
fn useful_example_is_exactly_counted_without_enumerating_sixty_million_tuples() {
    let modes = [CrossingMode { a: 20, i: 7, b: 0 }; 8];
    assert_eq!(
        count_tuples(&modes, 32, Policy::Original).unwrap(),
        61_523_748
    );
    assert_eq!(count_tuples(&modes, 32, Policy::Stronger).unwrap(), 45);
}

#[test]
fn rejects_invalid_sources_overflow_and_unbounded_branch_requests() {
    let invalid = [CrossingMode { a: 2, i: 3, b: 1 }];
    assert!(matches!(
        count_tuples(&invalid, 5, Policy::Stronger),
        Err(Error::Invalid(_))
    ));
    let high = [CrossingMode {
        a: usize::MAX,
        i: 0,
        b: 1,
    }];
    assert_eq!(
        count_tuples(&high, 5, Policy::Stronger),
        Err(Error::Overflow)
    );
    let modes = [CrossingMode { a: 2, i: 2, b: 0 }; 4];
    assert!(matches!(
        visit_tuples(&modes, 15, Policy::Original, 2, |_| {}),
        Err(Error::Capacity(_))
    ));
    assert_eq!(count_tuples(&modes, 0, Policy::Stronger).unwrap(), 0);
    assert!(matches!(
        count_tuples(&modes, 1_000_001, Policy::Stronger),
        Err(Error::Capacity(_))
    ));
    assert_eq!(
        visit_tuples(&[], 8, Policy::Stronger, 1, |_| {}).unwrap(),
        1
    );
}
