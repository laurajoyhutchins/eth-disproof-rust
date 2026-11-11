use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::deferred_power::{DeferredPower, finish_standalone_power};
use lean_eth_reference::native_integer_cache::{make_power_program, power_program};

#[test]
fn deferred_power_matches_every_final_source_machine_field() {
    let original = power_program().unwrap();
    for q in 0..=96 {
        for bits in [false, true] {
            for suffix in [vec![], vec![true], vec![false, true, false]] {
                let mut literal = original.initial(vec![bits; q]);
                literal.regs = [true, true];
                literal.stacks[1] = VecDeque::from(suffix);
                let mut candidate = literal.clone();
                original.run(&mut literal, RunLimits::default()).unwrap();
                finish_standalone_power(&mut candidate, 1_000_000).unwrap();
                assert_eq!(candidate, literal, "q={q}, input={bits}");
            }
        }
    }
}

#[test]
fn make_power_suffix_matches_symbolic_exponent_for_clean_scratch() {
    let source = make_power_program().unwrap();
    for q in 0..=64 {
        let mut full = source.initial([]);
        full.stacks[21] = VecDeque::from(vec![true; q]);
        source.run(&mut full, RunLimits::default()).unwrap();
        let candidate = DeferredPower::from_make_power_input_len(q);
        assert_eq!(full.stacks[2].len(), candidate.source_word_bits().unwrap());
        for (pos, bit) in full.stacks[2].iter().enumerate() {
            assert_eq!(*bit, candidate.bit(pos), "q={q}, bit={pos}");
        }
    }
}

#[test]
fn symbols_compose_without_intermediate_bit_words() {
    let a = DeferredPower::new(500_000);
    let b = DeferredPower::new(400_000);
    let product = a.checked_mul(b).unwrap();
    assert_eq!(product.exponent(), 900_000);
    assert_eq!(product.source_word_bits().unwrap(), 900_001);
    assert!(!product.bit(100_000));
    assert!(product.bit(900_000));
    assert!(!product.bit(900_001));
    assert_eq!(
        std::mem::size_of::<DeferredPower>(),
        std::mem::size_of::<usize>()
    );
    assert_eq!(
        DeferredPower::new(usize::MAX).source_word_bits(),
        Err(Error::Overflow)
    );
    assert_eq!(
        DeferredPower::new(usize::MAX).checked_mul(DeferredPower::new(1)),
        Err(Error::Overflow)
    );
}

#[test]
fn refuses_materialization_without_a_partial_mutation() {
    let mut suffix = VecDeque::from(vec![false, true, false]);
    let before = suffix.clone();
    assert!(matches!(
        DeferredPower::new(5).prepend_to(&mut suffix, 8),
        Err(Error::Capacity(_))
    ));
    assert_eq!(suffix, before);

    let original = power_program().unwrap();
    let mut config = original.initial(vec![false; 5]);
    config.stacks[1] = VecDeque::from(vec![true, false, true]);
    let before = config.clone();
    assert!(matches!(
        finish_standalone_power(&mut config, 8),
        Err(Error::Capacity(_))
    ));
    assert_eq!(config, before);
    finish_standalone_power(&mut config, 9).unwrap();
    assert_eq!(
        config.stacks[1],
        VecDeque::from(vec![
            false, false, false, false, false, true, true, false, true
        ])
    );
}
