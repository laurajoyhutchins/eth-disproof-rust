//! Milestone 2 #108: the scanner is physical; the noncomputable count table
//! is deliberately absent. These oracles check only the source cutoff test.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::finite_fallback::{
    MAX_CUTOFF_LABELS, cutoff_command, cutoff_program, cutoff_scanner,
};

fn word<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}

#[test]
fn scanner_exhaustive_boolean_words_and_state_table() {
    for bound in 0..=6 {
        let scanner = cutoff_scanner(bound).unwrap();
        assert_eq!(scanner.code().len(), (bound + 2) * 7);
        assert_eq!(scanner.entry(), 0);
        for q in 0..bound + 2 {
            let base = 7 * q;
            assert_eq!(
                scanner.code()[base + 3],
                Instr::Set {
                    dst: 0,
                    value: q <= bound,
                    next: base + 4
                }
            );
        }
        for len in 0..=8 {
            for bits in 0..1usize << len {
                let input: Vec<bool> = (0..len).map(|i| bits & (1 << i) != 0).collect();
                let count = input.iter().filter(|b| **b).count();
                let mut state = scanner.initial(input);
                state.regs = [true, true]; // arbitrary old flags must not leak
                let stats = scanner.run(&mut state, RunLimits::default()).unwrap();
                assert_eq!(stats.instructions, (3 * len + 6) as u64);
                assert_eq!(word(&state, 0), vec![count <= bound]);
                assert_eq!(state.regs, [false, false]);
                assert!(state.pc.is_none());
            }
        }
    }
}

#[test]
fn source_cutoff_command_keeps_header_and_frames_and_clears_dirty_scratch() {
    for bound in 0..=5 {
        let program = cutoff_program(bound).unwrap();
        for n in 0..=9 {
            let mut unary = vec![true; n];
            unary.push(false);
            let mut state = program.initial([]);
            state.stacks[258] = unary.iter().copied().collect::<VecDeque<_>>();
            state.stacks[270] = VecDeque::from([true, false, true]);
            state.stacks[271] = VecDeque::from([false, true]);
            state.stacks[777] = VecDeque::from([true, false, false]);
            state.regs[17] = true;
            state.regs[75] = n > bound;
            state.regs[76] = false;
            let stats = program.run(&mut state, RunLimits::default()).unwrap();
            // Lean cutoffCommand_eval steps + one compiled halt.
            assert_eq!(stats.instructions, (2 * 3 + 2 * 2 + 10 * n + 29) as u64);
            assert_eq!(word(&state, 258), unary);
            assert_eq!(word(&state, 777), vec![true, false, false]);
            assert!(word(&state, 270).is_empty());
            assert!(word(&state, 271).is_empty());
            assert!(state.regs[17]);
            assert_eq!(state.regs[75], n <= bound);
            assert!(state.regs[76]);
            assert!(!state.regs[72] && !state.regs[73]);
            assert!(state.pc.is_none());
        }
    }
}

#[test]
fn scanner_allocation_and_runtime_refuse_instead_of_returning_a_flag() {
    assert!(matches!(cutoff_scanner(usize::MAX), Err(Error::Overflow)));
    assert!(matches!(
        cutoff_command(MAX_CUTOFF_LABELS),
        Err(Error::Capacity(_))
    ));
    let program = cutoff_program(2).unwrap();
    let mut state = program.initial([]);
    state.stacks[258] = VecDeque::from([true, true, true, false]);
    assert!(matches!(
        program.run(
            &mut state,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 1000
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert!(
        state.pc.is_some(),
        "budget refusal is not a completed answer"
    );
}

#[test]
fn noncomputable_finite_table_and_outer_entry_stay_explicitly_unsupported() {
    use lean_eth_reference::bit_program::Cmd;
    use lean_eth_reference::remaining::outer;
    for cutoff in 0..=6 {
        assert!(matches!(
            outer::finite_fallback(cutoff, Cmd::<80, 1220>::Skip),
            Err(Error::NotImplemented(_))
        ));
        assert!(matches!(
            outer::entry(cutoff, Cmd::<80, 1220>::Skip),
            Err(Error::NotImplemented(_))
        ));
    }
}
