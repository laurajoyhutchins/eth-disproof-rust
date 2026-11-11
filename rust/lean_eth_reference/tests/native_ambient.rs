//! Real finite parser and physical ambient frontend prefix, no SAT oracle.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_ambient::{ambient_program, nat_program};

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

#[test]
fn source_five_label_nat_parser_and_malformed_end() {
    let program = nat_program().unwrap();
    assert_eq!(program.code().len(), 5);
    assert_eq!(
        program.code()[0],
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 1,
            next: 1
        }
    );
    assert_eq!(program.code()[4], Instr::Halt);
    for n in 0..=9 {
        for tail_mask in 0..16usize {
            let tail: Vec<bool> = (0..4).map(|i| (tail_mask >> i) & 1 == 1).collect();
            let mut input = unary(n);
            input.extend_from_slice(&tail);
            let mut state = program.initial(input);
            state.regs = [true, false];
            let stats = program.run(&mut state, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, (4 * n + 4) as u64);
            assert_eq!(take(&state, 0), tail);
            assert_eq!(take(&state, 1), vec![true; n]);
            assert_eq!(state.regs, [false, true]);
        }
    }
    let mut truncated = program.initial([]);
    let stats = program.run(&mut truncated, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 3);
    assert!(!truncated.regs[1]);
}

#[test]
fn ambient_frontend_preserves_raw_input_and_extracts_unary_dimension() {
    let program = ambient_program().unwrap();
    assert_eq!(program.input_stack(), 256);
    assert_eq!(program.output_stack(), 258);
    for n in 0..=8 {
        for tail_mask in 0..16usize {
            let tail: Vec<bool> = (0..4).map(|i| (tail_mask >> i) & 1 == 1).collect();
            let mut input = unary(n);
            input.extend_from_slice(&tail);
            let mut state = program.initial([]);
            put(&mut state, 256, &input);
            put(&mut state, 801, &[true, false, true]);
            state.regs[40] = true;
            state.regs[72] = true;
            let stats = program.run(&mut state, RunLimits::default()).unwrap();
            // Lean Native.ambient_eval + the outer compiled halt.
            let expected = 7 * input.len() + 4 * n + 2 * tail.len() + 15;
            assert_eq!(stats.instructions, expected as u64);
            assert_eq!(take(&state, 256), input);
            assert_eq!(take(&state, 258), unary(n));
            assert!(state.stacks[1218].is_empty());
            assert!(state.stacks[1219].is_empty());
            assert_eq!(take(&state, 801), vec![true, false, true]);
            assert!(state.regs[40]);
            assert!(!state.regs[72] && !state.regs[73]);
            assert_eq!(state.pc, None);
        }
    }
}

#[test]
fn incomplete_frontend_budget_refuses_before_a_header_is_accepted() {
    let program = ambient_program().unwrap();
    let mut state = program.initial([]);
    put(&mut state, 256, &unary(5));
    let err = program
        .run(
            &mut state,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 1024,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(state.pc.is_some());
    assert!(state.stacks[258].is_empty());
}
