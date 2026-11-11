//! Independent bit-value and physical-state checks of Native.answerCommand.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_answer::{
    ANSWER_STACK, COUNT_STACK, SCRATCH_STACK, answer_program, zero_program,
};

fn put<const R: usize, const S: usize>(state: &mut Config<R, S>, port: usize, bits: &[bool]) {
    state.stacks[port] = bits.iter().copied().collect::<VecDeque<_>>();
}
fn take<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}

#[test]
fn zero_program_is_exact_ten_label_table() {
    let machine = zero_program().unwrap();
    assert_eq!(machine.code().len(), 10);
    assert_eq!(
        machine.code()[0],
        Instr::Set {
            dst: 2,
            value: true,
            next: 1
        }
    );
    assert_eq!(
        machine.code()[5],
        Instr::And {
            dst: 2,
            left: 2,
            right: 0,
            next: 1
        }
    );
    assert_eq!(machine.code()[9], Instr::Halt);
    for len in 0..=9 {
        for mask in 0..1usize << len {
            let bits: Vec<bool> = (0..len).map(|i| (mask >> i) & 1 == 1).collect();
            let mut state = machine.initial(bits.clone());
            state.regs = [true, true, false];
            let stats = machine.run(&mut state, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, (8 * len + 6) as u64);
            assert_eq!(take(&state, 0), bits);
            assert!(state.stacks[1].is_empty());
            assert_eq!(state.regs, [false, false, mask == 0]);
            assert_eq!(state.pc, None);
        }
    }
}

#[test]
fn source_answer_suffix_exhaustive_binary_and_dirty_scratch() {
    let machine = answer_program().unwrap();
    assert_eq!(machine.input_stack(), COUNT_STACK);
    assert_eq!(machine.output_stack(), ANSWER_STACK);
    for len in 0..=8 {
        for mask in 0..1usize << len {
            let bits: Vec<bool> = (0..len).map(|i| (mask >> i) & 1 == 1).collect();
            for (old_answer, old_scratch) in [(0, 0), (2, 3), (4, 1)] {
                let mut state = machine.initial([]);
                put(&mut state, COUNT_STACK, &bits);
                put(&mut state, ANSWER_STACK, &vec![true; old_answer]);
                put(&mut state, SCRATCH_STACK, &vec![false; old_scratch]);
                put(&mut state, 1215, &[true, false, false, true]);
                put(&mut state, 1108, &[false, true, true]);
                state.regs[21] = true;
                state.regs[79] = true;
                state.regs[74] = mask == 0;
                let stats = machine.run(&mut state, RunLimits::default()).unwrap();
                // Lean Native.answerSteps, including the final compiled halt.
                let expected = 2 * old_answer + 2 * old_scratch + 8 * len + 15;
                assert_eq!(stats.instructions, expected as u64, "mask={mask} len={len}");
                assert_eq!(take(&state, COUNT_STACK), bits);
                assert_eq!(take(&state, ANSWER_STACK), vec![mask != 0]);
                assert!(state.stacks[SCRATCH_STACK].is_empty());
                assert_eq!(take(&state, 1215), vec![true, false, false, true]);
                assert_eq!(take(&state, 1108), vec![false, true, true]);
                assert!(state.regs[21] && state.regs[79]);
                assert_eq!(state.regs[74], mask != 0);
                assert!(!state.regs[72] && !state.regs[73]);
                assert_eq!(state.pc, None);
            }
        }
    }
}

#[test]
fn a_high_order_one_is_not_confused_with_zero_or_lsb_sat() {
    let machine = answer_program().unwrap();
    let mut state = machine.initial([]);
    put(
        &mut state,
        COUNT_STACK,
        &[false, false, false, true, false, false],
    );
    machine.run(&mut state, RunLimits::default()).unwrap();
    assert_eq!(take(&state, ANSWER_STACK), vec![true]);
    assert_eq!(
        take(&state, COUNT_STACK),
        vec![false, false, false, true, false, false]
    );
}

#[test]
fn refuse_incomplete_suffix_without_reporting_answer() {
    let machine = answer_program().unwrap();
    let mut state = machine.initial([]);
    put(&mut state, COUNT_STACK, &[false, false, true]);
    put(&mut state, ANSWER_STACK, &[false, true]);
    let err = machine
        .run(
            &mut state,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 1000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(state.pc.is_some());
    assert_ne!(take(&state, ANSWER_STACK), vec![true]);
}
