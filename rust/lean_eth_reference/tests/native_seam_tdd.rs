//! Executable composition seam preceding the unported head and pair evaluator.
//! Independent Boolean and word oracles, not an alternative arithmetic backend.

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Cmd, Config, RunLimits};
use lean_eth_reference::native_layout::{self, HIGH_START, LOW_START, MASTER_COUNT};
use lean_eth_reference::native_pair_setup;
use std::collections::VecDeque;

fn bits(width: usize, salt: usize) -> Vec<bool> {
    (0..width).map(|i| (i * 13 + salt * 19) % 7 <= 2).collect()
}

fn put(d: &mut Config<40, 896>, port: usize, value: &[bool]) {
    d.stacks[port] = VecDeque::from(value.to_vec());
}

fn read(d: &Config<40, 896>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}

fn combined() -> lean_eth_reference::bit_program::Program<40, 896> {
    Cmd::seq(
        native_layout::command().unwrap(),
        native_pair_setup::setup_caller_command().unwrap(),
    )
    .compiled(338, 833)
    .unwrap()
}

#[test]
fn layout_then_pair_setup_preserves_sources_and_materializes_derived_words() {
    let p = combined();
    for width in 0..=5usize {
        for rank in 0..(1usize << width) {
            let mask = (0..width).map(|i| (rank >> i) & 1 != 0).collect::<Vec<_>>();
            let free = mask.iter().filter(|&&b| !b).count();
            let mut d = p.initial(mask.clone());
            let meta = bits(rank % 7, rank + width);
            put(&mut d, 243, &meta);
            put(&mut d, 789, &[true, true, false]);
            let mut masters = Vec::new();
            for i in 0..MASTER_COUNT {
                let v = bits((i + rank + width) % 6, i + rank);
                put(&mut d, HIGH_START + i, &v);
                masters.push(v);
                put(&mut d, LOW_START + i, &[false, true, true]);
            }
            for port in [660, 665, 684, 325, 326, 327, 328, 329, 832, 833, 834, 835] {
                put(&mut d, port, &[false, true]);
            }
            for i in 0..40 {
                d.regs[i] = (i + rank) % 2 == 0;
            }
            let before = d.clone();
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            assert!(stats.instructions > 0);
            assert_eq!(d.pc, None);
            assert_eq!(read(&d, 338), mask);
            assert_eq!(read(&d, 243), meta);
            assert_eq!(read(&d, 832), vec![true; free]);
            assert_eq!(read(&d, 833), meta);
            assert_eq!(read(&d, 789), vec![true, true, false]);
            for (index, expected) in masters.iter().enumerate() {
                assert_eq!(read(&d, LOW_START + index), *expected);
                assert_eq!(read(&d, HIGH_START + index), *expected);
            }
            for scratch in [660, 665, 684, 325, 326, 327, 328, 329, 834, 835] {
                assert!(d.stacks[scratch].is_empty(), "scratch stack {scratch}");
            }
            for i in 9..40 {
                assert_eq!(d.regs[i], before.regs[i], "register {i}");
            }
            for i in 0..896 {
                if (LOW_START..LOW_START + MASTER_COUNT).contains(&i)
                    || [660, 665, 684, 325, 326, 327, 328, 329, 832, 833, 834, 835].contains(&i)
                {
                    continue;
                }
                assert_eq!(d.stacks[i], before.stacks[i], "unexpected stack write {i}");
            }
        }
    }
}

#[test]
fn composition_requires_the_complete_instruction_budget() {
    let p = combined();
    let mut initial = p.initial([true, false, true, false]);
    put(&mut initial, 243, &[true, false, true]);
    for i in 0..MASTER_COUNT {
        put(&mut initial, HIGH_START + i, &bits(i % 4, i));
    }
    let mut done = initial.clone();
    let stats = p.run(&mut done, RunLimits::default()).unwrap();
    assert_eq!(done.pc, None);
    let mut refused = initial.clone();
    assert!(matches!(
        p.run(
            &mut refused,
            RunLimits {
                max_steps: stats.instructions - 1,
                max_stack_bits: 100_000
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert!(
        refused.pc.is_some(),
        "incomplete computation must not be accepted"
    );
    let mut exact = initial.clone();
    let steps = p
        .run(
            &mut exact,
            RunLimits {
                max_steps: stats.instructions,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
    assert_eq!(steps.instructions, stats.instructions);
    assert_eq!(exact, done);
}

#[test]
fn capacity_refusal_before_first_step_is_state_preserving() {
    let p = combined();
    let mut d = p.initial([true, false, true, false]);
    let before = d.clone();
    assert!(matches!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: 0,
                max_stack_bits: 3
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert_eq!(d, before);
    assert!(matches!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: 0,
                max_stack_bits: 4
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert_eq!(d, before);
}
