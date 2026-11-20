//! Independent fixed-table and physical-state controls for the canonical StackRoutines port.
//! Assertions describe the original four-label transfer, not an output-only oracle.

use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::stack_routines::{
    clear_program, copy_program, transfer_program,
};
use lean_eth_reference::bit_program::{Instr, RunLimits};
use lean_eth_reference::{native_clause_dedup, native_clause_relation_scan};
use lean_eth_reference::{native_high, native_query_prefix};

#[test]
fn transfer_aliases_retain_the_original_four_labels() {
    let direct = transfer_program::<15, 16>(11, 8, 0, 1).unwrap();
    let table = [
        Instr::Pop {
            stack: 11,
            value: 0,
            present: 1,
            next: 1,
        },
        Instr::Branch {
            test: 1,
            yes: 2,
            no: 3,
        },
        Instr::Push {
            stack: 8,
            src: 0,
            next: 0,
        },
        Instr::Halt,
    ];
    assert_eq!(direct.code(), &table);
    assert_eq!((direct.input_stack(), direct.output_stack(), direct.entry()), (11, 8, 0));
    assert_eq!(native_query_prefix::transfer_program::<15, 16>(11, 8, 0, 1).unwrap().code(), &table);
    assert_eq!(native_clause_dedup::transfer(11, 8).unwrap().code(), &table);

    let candidate = native_clause_relation_scan::transfer_candidate().unwrap();
    assert_eq!(candidate.code(), &table);
    assert_eq!((candidate.input_stack(), candidate.output_stack(), candidate.entry()), (11, 8, 0));
}

#[test]
fn original_stack_routines_keep_port_order_and_source_cost() {
    let transfer = transfer_program::<2, 3>(0, 1, 0, 1).unwrap();
    let clear = clear_program::<2, 3>(0, 0, 1).unwrap();
    let copy = copy_program::<2, 3>(0, 1, 2, 0, 1).unwrap();
    assert_eq!(native_high::clear_program::<2, 3>(0, 0, 1).unwrap().code(), clear.code());
    assert_eq!(native_high::copy_program::<2, 3>(0, 1, 2, 0, 1).unwrap().code(), copy.code());

    for len in 0..=7 {
        let word: Vec<bool> = (0..len).map(|i| i % 3 == 0).collect();

        let mut transfer_state = transfer.initial(word.iter().copied());
        transfer_state.stacks[1] = VecDeque::from([false, true]);
        let transfer_stats = transfer.run(&mut transfer_state, RunLimits::default()).unwrap();
        let mut expected = word.clone();
        expected.reverse();
        expected.extend([false, true]);
        assert_eq!(transfer_state.stacks[1], VecDeque::from(expected));
        assert!(transfer_state.stacks[0].is_empty());
        assert!(transfer_state.pc.is_none());
        assert_eq!(transfer_stats.instructions, 3 * len as u64 + 3);

        let mut clear_state = clear.initial(word.iter().copied());
        let clear_stats = clear.run(&mut clear_state, RunLimits::default()).unwrap();
        assert!(clear_state.stacks[0].is_empty());
        assert!(clear_state.pc.is_none());
        assert_eq!(clear_stats.instructions, 2 * len as u64 + 3);

        let mut copy_state = copy.initial(word.iter().copied());
        copy_state.stacks[1] = VecDeque::from([false, true]);
        copy.run(&mut copy_state, RunLimits::default()).unwrap();
        let mut expected = word.clone();
        expected.extend([false, true]);
        assert_eq!(copy_state.stacks[0], VecDeque::from(word));
        assert_eq!(copy_state.stacks[1], VecDeque::from(expected));
        assert!(copy_state.stacks[2].is_empty());
        assert!(copy_state.pc.is_none());
    }
}

#[test]
fn invalid_port_aliases_remain_explicit_refusals() {
    assert_eq!(
        transfer_program::<2, 3>(0, 0, 0, 1).unwrap_err(),
        Error::Invalid("transfer requires disjoint ports".into())
    );
    assert_eq!(
        native_clause_dedup::transfer(0, 0).unwrap_err(),
        Error::Invalid("transfer ports must differ".into())
    );
    assert_eq!(
        transfer_program::<2, 3>(0, 1, 0, 0).unwrap_err(),
        Error::Invalid("transfer requires disjoint ports".into())
    );
    assert_eq!(
        copy_program::<2, 3>(0, 1, 0, 0, 1).unwrap_err(),
        Error::Invalid("copy requires disjoint ports and read registers".into())
    );
    assert!(transfer_program::<2, 2>(0, 2, 0, 1).is_err());
    assert!(clear_program::<2, 2>(0, 0, 2).is_err());
}
