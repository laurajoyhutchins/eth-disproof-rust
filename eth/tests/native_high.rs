//! End-to-end source-command tests for the marked high-assignment initializer.
//! These compare *actual compiled instructions* to separate source-definition
//! formulas, including exact stack layout and source instruction counts.
//! No Lean executable is invoked here; that remains a differential obligation.
use std::collections::VecDeque;

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_high::{
    branch_program, high_count_init_program, high_odometer_word, initialize_program, seed_program,
};

fn bits(mask: u64, len: usize) -> Vec<bool> {
    (0..len).map(|i| (mask >> i) & 1 != 0).collect()
}

fn write_stack<const R: usize, const S: usize>(
    cfg: &mut Config<R, S>,
    stack: usize,
    word: &[bool],
) {
    cfg.stacks[stack] = word.iter().copied().collect::<VecDeque<_>>();
}

fn stack<const R: usize, const S: usize>(cfg: &Config<R, S>, stack: usize) -> Vec<bool> {
    cfg.stacks[stack].iter().copied().collect()
}

#[test]
fn native_branches_matches_source_bit_word_and_exact_trace_cost() {
    let program = branch_program().unwrap();
    for size in 0..=8 {
        for mask in 0..1_u64 << size {
            let input = bits(mask, size);
            let count = input.iter().filter(|b| **b).count();
            for regs in [[false, false], [true, true], [false, true], [true, false]] {
                let mut state = program.initial(input.clone());
                state.regs = regs;
                let stats = program.run(&mut state, RunLimits::default()).unwrap();
                // Lean: Branches.command_eval costs 3*length + 8*trueCount + 4;
                // StructuredCalls.compiled_halt_trace pays one more instruction.
                assert_eq!(stats.instructions, (3 * size + 8 * count + 5) as u64);
                assert_eq!(stack(&state, 1), high_odometer_word(count).unwrap());
                assert!(state.stacks[0].is_empty());
                assert_eq!(state.regs, [false, false]);
            }
        }
    }
}

#[test]
fn source_high_seed_resets_scratch_and_keeps_input_mask_and_bystanders() {
    let machine = seed_program().unwrap();
    for size in 0..=7 {
        for mask in 0..1_u64 << size {
            let word = bits(mask, size);
            let count = word.iter().filter(|b| **b).count();
            let mut state = machine.initial(word.clone());
            state.regs[21] = true;
            state.regs[37] = true;
            write_stack(&mut state, 330, &[false]);
            write_stack(&mut state, 791, &[true, true]);
            write_stack(&mut state, 792, &[true, false, true]);
            write_stack(&mut state, 790, &[false, true, true]);
            let initial_len = state.stack_bits().unwrap();
            let stats = machine.run(&mut state, RunLimits::default()).unwrap();
            let reset_cost = 2 * 2 + 3 + 2 * (1 + 3) + 12;
            let expected = reset_cost + 10 * size + 8 * count + 10 + 1;
            assert_eq!(
                stats.instructions, expected as u64,
                "mask={mask} size={size}"
            );
            assert_eq!(stack(&state, 338), word);
            assert_eq!(stack(&state, 330), high_odometer_word(count).unwrap());
            assert!(state.stacks[791].is_empty());
            assert!(state.stacks[792].is_empty());
            assert_eq!(stack(&state, 790), vec![false, true, true]);
            assert!(state.regs[21] && state.regs[37]);
            assert!(stats.peak_stack_bits >= initial_len);
        }
    }
}

#[test]
fn high_count_init_preserves_seed_counter_sets_guard_and_clears_stale_words() {
    let machine = high_count_init_program().unwrap();
    for h in 0..=7 {
        let counter = high_odometer_word(h).unwrap();
        let mut state = machine.initial(counter.clone());
        state.regs[37] = true;
        state.regs[21] = false;
        write_stack(&mut state, 788, &[true]);
        write_stack(&mut state, 789, &[true, false]);
        write_stack(&mut state, 790, &[true, true, false]);
        write_stack(&mut state, 323, &[false]);
        write_stack(&mut state, 791, &[true, false, false]);
        write_stack(&mut state, 792, &[true, true, false, true]);
        write_stack(&mut state, 338, &[true, false, true]);
        let stats = machine.run(&mut state, RunLimits::default()).unwrap();
        // HighCountInit.resetCost + 7*len(counter) + 6 + compiled halt.
        let reset_cost = 2 * 4 + 3 + 2 * (1 + 2 + 3 + 1 + 3) + 21;
        let cost = reset_cost + 7 * counter.len() + 6 + 1;
        assert_eq!(stats.instructions, cost as u64);
        assert_eq!(stack(&state, 789), counter);
        assert_eq!(stack(&state, 330), high_odometer_word(h).unwrap());
        for port in [788, 790, 323, 791, 792] {
            assert!(state.stacks[port].is_empty(), "dirty output port {port}");
        }
        assert_eq!(stack(&state, 338), vec![true, false, true]);
        assert!(state.regs[21] && state.regs[37]);
        assert!(!state.regs[0] && !state.regs[1]);
    }
}

#[test]
fn entire_nested_seed_and_init_preserves_physical_words_and_halting() {
    let program = initialize_program().unwrap();
    for size in 0..=7 {
        for mask in 0..1_u64 << size {
            let word = bits(mask, size);
            let count = word.iter().filter(|b| **b).count();
            let mut state = program.initial(word.clone());
            state.regs[37] = true;
            state.regs[21] = false;
            write_stack(&mut state, 330, &[true, false]);
            write_stack(&mut state, 791, &[true]);
            write_stack(&mut state, 792, &[true, false, true]);
            write_stack(&mut state, 788, &[true, true]);
            write_stack(&mut state, 789, &[false]);
            write_stack(&mut state, 790, &[true, false, true]);
            write_stack(&mut state, 323, &[true, true, true]);
            write_stack(&mut state, 265, &[true, false, false, true]);
            let cost_seed = (2 + 3 + 2 * (2 + 3) + 12) + 10 * size + 8 * count + 10;
            let seed_word = high_odometer_word(count).unwrap();
            // At the HighCountInit boundary the seed call has cleared 791/792
            // and replaced 330 with its canonical high-coordinate word.
            let cost_init = (2 * (2 + 1 + 3 + 3) + 24) + 7 * seed_word.len() + 6;
            let stats = program.run(&mut state, RunLimits::default()).unwrap();
            // Two nested compiled halt→return instructions plus outer halt.
            assert_eq!(stats.instructions, (cost_seed + cost_init + 3) as u64);
            assert_eq!(stack(&state, 330), seed_word);
            assert_eq!(stack(&state, 789), seed_word);
            assert_eq!(stack(&state, 338), word);
            assert_eq!(stack(&state, 265), vec![true, false, false, true]);
            assert_eq!(state.pc, None);
            assert!(state.regs[21] && state.regs[37]);
            for port in [323, 788, 790, 791, 792] {
                assert!(state.stacks[port].is_empty(), "port {port}");
            }
        }
    }
}

#[test]
fn lifted_branch_program_preserves_unmapped_ports_and_rejects_aliases() {
    let source = branch_program().unwrap();
    assert!(source.lift::<3, 3>([0, 0], [0, 1]).is_err());
    assert!(source.lift::<3, 3>([0, 1], [0, 0]).is_err());
    assert!(source.lift::<3, 3>([0, 3], [0, 1]).is_err());
    let program = source.lift::<10, 12>([7, 9], [5, 8]).unwrap();
    for mask in 0..=15u64 {
        let input = bits(mask, 4);
        let mut state = program.initial(input.clone());
        state.regs[0] = true;
        state.regs[4] = true;
        write_stack(&mut state, 2, &[false, true]);
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(
            stats.instructions,
            (3 * 4 + 8 * input.iter().filter(|b| **b).count() + 5) as u64
        );
        assert_eq!(
            stack(&state, 8),
            high_odometer_word(input.iter().filter(|b| **b).count()).unwrap()
        );
        assert!(state.stacks[5].is_empty());
        assert_eq!(stack(&state, 2), vec![false, true]);
        assert!(state.regs[0] && state.regs[4]);
    }
}

#[test]
fn source_initializer_refuses_incomplete_execution() {
    let machine = initialize_program().unwrap();
    let mut state = machine.initial([true, false, true]);
    let e = machine
        .run(
            &mut state,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 1_000_000,
            },
        )
        .unwrap_err();
    assert!(e.to_string().contains("capacity refusal"));
    assert!(
        state.pc.is_some(),
        "a budget refusal must not return a completed result"
    );
}
