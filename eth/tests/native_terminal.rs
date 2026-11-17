//! Physical source-boundary tests, not semantic SAT shortcuts.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_terminal::{
    power_program, terminal_power_program, terminal_zero_program,
};

fn put<const R: usize, const S: usize>(state: &mut Config<R, S>, port: usize, bits: &[bool]) {
    state.stacks[port] = bits.iter().copied().collect::<VecDeque<_>>();
}
fn take<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}
fn unary(n: usize) -> Vec<bool> {
    let mut word = vec![true; n];
    word.push(false);
    word
}
fn two_power(n: usize) -> Vec<bool> {
    let mut word = vec![false; n];
    word.push(true);
    word
}

#[test]
fn source_local_power_is_a_fixed_finite_machine() {
    let program = power_program().unwrap();
    assert_eq!(program.code().len(), 8);
    assert_eq!(program.input_stack(), 0);
    assert_eq!(program.output_stack(), 1);
    for n in 0..=128 {
        let mut state = program.initial(unary(n));
        state.regs = [n % 2 == 0, n % 3 == 0];
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, (4 * n + 5) as u64);
        assert_eq!(take(&state, 1), two_power(n));
        assert!(state.stacks[0].is_empty());
        assert_eq!(state.regs, [false, true]);
        assert_eq!(state.pc, None);
    }
}

#[test]
fn terminal_power_physically_preserves_ambient_and_abi_frames() {
    let program = terminal_power_program().unwrap();
    assert_eq!(program.input_stack(), 258);
    assert_eq!(program.output_stack(), 263);
    for n in 0..=128 {
        let mut state = program.initial(unary(n));
        put(&mut state, 13, &[false, true, false, true]);
        put(&mut state, 267, &[true, false, true]);
        put(&mut state, 1216, &[false, true]);
        state.regs[12] = true;
        state.regs[74] = true;
        state.regs[72] = n % 2 == 0;
        state.regs[73] = n % 2 == 1;
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        // Lean NativeTerminal.power_eval = 11*n + 17, then compiled halt.
        assert_eq!(stats.instructions, (11 * n + 18) as u64);
        assert_eq!(take(&state, 258), unary(n));
        assert_eq!(take(&state, 263), two_power(n));
        assert!(state.stacks[268].is_empty());
        assert!(state.stacks[269].is_empty());
        assert_eq!(take(&state, 13), vec![false, true, false, true]);
        assert_eq!(take(&state, 267), vec![true, false, true]);
        assert_eq!(take(&state, 1216), vec![false, true]);
        assert!(state.regs[12] && state.regs[74]);
        assert!(!state.regs[72] && state.regs[73]);
        assert_eq!(state.pc, None);
    }
}

#[test]
fn terminal_zero_writes_the_actual_zero_count_not_an_empty_word() {
    let program = terminal_zero_program().unwrap();
    for n in 0..=8 {
        let mut state = program.initial(unary(n));
        put(&mut state, 265, &[false, true, false]);
        state.regs[72] = true;
        state.regs[6] = true;
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, 3);
        assert_eq!(take(&state, 263), vec![false]);
        assert_eq!(take(&state, 258), unary(n));
        assert_eq!(take(&state, 265), vec![false, true, false]);
        assert!(!state.regs[72]);
        assert!(state.regs[6]);
    }
}

#[test]
fn terminal_power_capacity_refuses_before_a_count_is_complete() {
    let program = terminal_power_program().unwrap();
    let mut state = program.initial(unary(20));
    let err = program
        .run(
            &mut state,
            RunLimits {
                max_steps: 9,
                max_stack_bits: 1000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(state.pc.is_some());
    assert!(state.stacks[263].is_empty());

    let mut state = program.initial(unary(20));
    let err = program
        .run(
            &mut state,
            RunLimits {
                max_steps: 10000,
                max_stack_bits: 21,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(state.pc.is_some());
}

#[test]
fn no_integer_width_saturation_in_ambient_power() {
    let program = terminal_power_program().unwrap();
    let mut state = program.initial(unary(256));
    let stats = program.run(&mut state, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 11 * 256 + 18);
    assert_eq!(take(&state, 263), two_power(256));
    assert_eq!(take(&state, 258), unary(256));
}
