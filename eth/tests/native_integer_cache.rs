use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_integer_cache::{
    binary_add_program, cache_cell_local_program, cache_cell_program, cache_copies_program,
    little_endian_add_program, make_power_program, power_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(a: &mut Config<R, S>, port: usize, bits: &[bool]) {
    a.stacks[port] = VecDeque::from(bits.to_vec());
}
fn bits<const R: usize, const S: usize>(a: &Config<R, S>, port: usize) -> Vec<bool> {
    a.stacks[port].iter().copied().collect()
}
fn binary(n: u64) -> Vec<bool> {
    if n == 0 {
        return vec![];
    }
    (0..(64 - n.leading_zeros()))
        .map(|i| (n >> i) & 1 != 0)
        .collect()
}
fn value(bits: &[bool]) -> u128 {
    bits.iter()
        .enumerate()
        .fold(0u128, |n, (i, &b)| if b { n + (1u128 << i) } else { n })
}

#[test]
fn adder_is_original_13_labels_and_linked_17_labels() {
    let inner = binary_add_program().unwrap();
    let linked = little_endian_add_program().unwrap();
    assert_eq!(inner.code().len(), 13);
    assert_eq!(linked.code().len(), 17);
    assert_eq!(
        inner.code()[12],
        lean_eth_reference::bit_program::Instr::Halt
    );
    assert_eq!(
        linked.code()[12],
        lean_eth_reference::bit_program::Instr::Goto { next: 13 }
    );
    for x in 0..=63u64 {
        for y in 0..=63u64 {
            let mut a = linked.initial(binary(x));
            put(&mut a, 1, &binary(y));
            linked.run(&mut a, RunLimits::default()).unwrap();
            assert_eq!(value(&bits(&a, 0)), (x + y) as u128, "x={x} y={y}");
            assert!(a.stacks[1].is_empty());
            assert!(a.stacks[2].is_empty());
        }
    }
}

#[test]
fn linked_adder_handles_noncanonical_words_and_original_carry() {
    let p = little_endian_add_program().unwrap();
    for n in 0..=5 {
        for m in 0..=5 {
            let mut a = p.initial(vec![false; n]);
            put(&mut a, 1, &vec![false; m]);
            p.run(&mut a, RunLimits::default()).unwrap();
            assert_eq!(bits(&a, 0), vec![false; n.max(m)]);
        }
    }
    let mut a = p.initial(vec![true, false, true]);
    put(&mut a, 1, &[true, true]);
    a.regs[0] = true;
    p.run(&mut a, RunLimits::default()).unwrap();
    assert_eq!(value(&bits(&a, 0)), 5 + 3 + 1);
}

#[test]
fn cache_cell_performs_real_shift_then_binary_addition() {
    let low = cache_cell_local_program().unwrap();
    let mapped = cache_cell_program().unwrap();
    assert_eq!(low.code().len(), 20); // 2 atoms + 17 linked labels + halt
    for x in 0..=31u64 {
        for y in 0..=31u64 {
            let mut a = low.initial(binary(x));
            put(&mut a, 1, &binary(y));
            low.run(&mut a, RunLimits::default()).unwrap();
            assert_eq!(value(&bits(&a, 0)), 2 * x as u128 + y as u128);
            assert!(a.stacks[1].is_empty());
            assert!(a.stacks[2].is_empty());
            let mut b = mapped.initial([]);
            put(&mut b, 0, &binary(x));
            put(&mut b, 2, &binary(y));
            put(&mut b, 12, &[true, false, true]);
            mapped.run(&mut b, RunLimits::default()).unwrap();
            assert_eq!(bits(&b, 0), bits(&a, 0));
            assert_eq!(bits(&b, 12), vec![true, false, true]);
            assert!(b.stacks[2].is_empty() && b.stacks[4].is_empty());
        }
    }
}

#[test]
fn fixed_cache_copies_keep_source_words_and_preserve_unrelated_stacks() {
    let p = cache_copies_program().unwrap();
    for a in 0..=5 {
        let mut d = p.initial([]);
        put(&mut d, 20, &vec![true; a]);
        put(&mut d, 21, &[false, true]);
        put(&mut d, 22, &[true, false, false]);
        put(&mut d, 17, &[false]);
        put(&mut d, 4, &[true]);
        let before = d.clone();
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, (7 * (a + 2 + 3) + 15 + 1) as u64);
        assert_eq!(bits(&d, 17), [vec![true; a], vec![false]].concat());
        assert_eq!(bits(&d, 18), vec![false, true]);
        assert_eq!(bits(&d, 19), vec![true, false, false]);
        for port in 0..24 {
            if [17, 18, 19].contains(&port) {
                continue;
            }
            assert_eq!(d.stacks[port], before.stacks[port], "port {port}");
        }
    }
}

#[test]
fn power_machine_consumes_unary_exponent_and_constructs_little_endian_power() {
    let p = power_program().unwrap();
    for exponent in 0..=65 {
        let mut d = p.initial(vec![true; exponent]);
        put(&mut d, 1, &[false, true]);
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, (4 * exponent + 5) as u64);
        assert!(d.stacks[0].is_empty());
        assert_eq!(
            bits(&d, 1),
            [vec![false; exponent], vec![true, false, true]].concat()
        );
    }
}

#[test]
fn make_power_preserves_flat_cache_and_runtime_inputs() {
    let p = make_power_program().unwrap();
    for exponent in 0..=25 {
        let mut d = p.initial([]);
        put(&mut d, 21, &vec![true; exponent]);
        put(&mut d, 0, &[true, false]);
        put(&mut d, 1, &[false, false, true]);
        put(&mut d, 19, &[true]);
        put(&mut d, 22, &[true, true]);
        put(&mut d, 8, &[false, true, false]);
        d.regs = [true, true, true, true, true, true, true, true];
        let before = d.clone();
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(&d.regs[6..8], &before.regs[6..8]);
        assert_eq!(
            stats.instructions,
            (7 * exponent + 4 * exponent.saturating_sub(1) + 12) as u64
        );
        assert_eq!(
            bits(&d, 2),
            [vec![false; exponent.saturating_sub(1)], vec![true]].concat()
        );
        assert!(d.stacks[23].is_empty());
        for port in 0..24 {
            if [2, 23].contains(&port) {
                continue;
            }
            assert_eq!(d.stacks[port], before.stacks[port], "port {port}");
        }
    }
}

#[test]
fn initial_h_row_consumes_runtime_unary_length_and_builds_framed_ones() {
    use lean_eth_reference::native_integer_cache::{initial_h_build_program, initial_h_program};
    let low = initial_h_program().unwrap();
    let high = initial_h_build_program().unwrap();
    for n in 0..=32 {
        let mut a = low.initial([]);
        put(&mut a, 17, &vec![false; n]); // contents ignored, only length matters
        let steps = low.run(&mut a, RunLimits::default()).unwrap();
        assert_eq!(steps.instructions, (12 * n + 5) as u64);
        let expected = [[true, true, true, false, false].repeat(n), vec![false]].concat();
        assert_eq!(bits(&a, 15), expected);
        assert!(a.stacks[17].is_empty());

        let mut b = high.initial([]);
        put(&mut b, 17, &[false, true, false]); // preserved H height word
        put(&mut b, 18, &vec![false; n]);
        put(&mut b, 12, &[false, true]);
        let before = b.clone();
        let steps_high = high.run(&mut b, RunLimits::default()).unwrap();
        assert_eq!(steps_high.instructions, (12 * n + 6) as u64);
        assert_eq!(bits(&b, 15), expected);
        assert_eq!(bits(&b, 17), bits(&before, 17));
        assert_eq!(bits(&b, 12), bits(&before, 12));
        assert!(b.stacks[18].is_empty());
    }
}
