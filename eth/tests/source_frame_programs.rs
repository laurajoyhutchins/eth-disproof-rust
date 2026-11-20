//! Independently copied baseline instruction tables and physical-frame tests.
//! These are source-machine checks, not a Lean-to-Rust refinement theorem.

use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::frame_programs::{emit_record_program, frame_program};
use lean_eth_reference::bit_program::{Instr, Program, RunLimits};
use lean_eth_reference::{
    native_cache_iteration, native_normalization_primitives, native_query_prefix,
    native_record_membership,
};

/// Baseline seven-label table, copied from the former membership module
/// without calling the new shared parser.
fn baseline_frame_program() -> Result<Program<2, 2>, Error> {
    Program::new(
        0,
        1,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Branch {
                test: 1,
                yes: 2,
                no: 6,
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 6,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 4,
            },
            Instr::Branch {
                test: 1,
                yes: 5,
                no: 6,
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0,
            },
            Instr::Halt,
        ],
    )
}

/// Baseline seventeen-label constructor, copied from the former normalization
/// module. Its manual relocation is independent of the new lift-based one.
fn baseline_record_emitter() -> Result<Program<3, 4>, Error> {
    let parser = baseline_frame_program()?;
    let mut code = Vec::with_capacity(17);
    for instruction in parser.code() {
        let relocated = match *instruction {
            Instr::Pop {
                stack,
                value,
                present,
                next,
            } => Instr::Pop {
                stack: if stack == 1 { 3 } else { stack },
                value,
                present,
                next,
            },
            Instr::Push { stack, src, next } => Instr::Push {
                stack: if stack == 1 { 3 } else { stack },
                src,
                next,
            },
            Instr::Halt => Instr::Goto { next: 7 },
            Instr::Branch { test, yes, no } => Instr::Branch { test, yes, no },
            _ => return Err(Error::Invalid("unexpected source frame instruction".into())),
        };
        code.push(relocated);
    }
    code.extend([
        Instr::Set {
            dst: 0,
            value: false,
            next: 8,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Pop {
            stack: 3,
            value: 0,
            present: 1,
            next: 10,
        },
        Instr::Branch {
            test: 1,
            yes: 11,
            no: 14,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 12,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 13,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 9,
        },
        Instr::Set {
            dst: 0,
            value: true,
            next: 15,
        },
        Instr::Push {
            stack: 2,
            src: 0,
            next: 16,
        },
        Instr::Halt,
    ]);
    Program::new(3, 2, 7, code)
}

fn frame(bits: &[bool]) -> Vec<bool> {
    let mut result = Vec::with_capacity(2 * bits.len() + 1);
    for &bit in bits {
        result.extend([true, bit]);
    }
    result.push(false);
    result
}

#[test]
fn both_old_parser_entry_points_retain_exact_source_program() {
    let expected = baseline_frame_program().unwrap();
    assert_eq!(frame_program().unwrap(), expected);
    assert_eq!(native_query_prefix::frame_program().unwrap(), expected);
    assert_eq!(native_record_membership::frame_program().unwrap(), expected);
    assert_eq!(expected.code().len(), 7);
    assert_eq!(
        (
            expected.input_stack(),
            expected.output_stack(),
            expected.entry()
        ),
        (0, 1, 0)
    );
}

#[test]
fn both_old_emitter_entry_points_retain_all_seventeen_source_labels() {
    let expected = baseline_record_emitter().unwrap();
    assert_eq!(emit_record_program().unwrap(), expected);
    assert_eq!(
        native_cache_iteration::emit_record_program().unwrap(),
        expected
    );
    assert_eq!(
        native_normalization_primitives::emit_record_program().unwrap(),
        expected
    );
    assert_eq!(expected.code().len(), 17);
    assert_eq!(expected.code()[6], Instr::Goto { next: 7 });
    assert_eq!(
        (
            expected.input_stack(),
            expected.output_stack(),
            expected.entry()
        ),
        (3, 2, 7)
    );
}

#[test]
fn parser_preserves_unread_suffix_and_reverses_payload_at_original_cost() {
    let parser = frame_program().unwrap();
    for n in 0..=7usize {
        for mask in 0..(1usize << n) {
            let word = (0..n).map(|i| (mask >> i) & 1 == 1).collect::<Vec<_>>();
            let mut input = frame(&word);
            input.extend([true, false, true]);
            let mut state = parser.initial(input);
            state.stacks[1] = VecDeque::from([true, false]);
            let stats = parser.run(&mut state, RunLimits::default()).unwrap();
            let mut expected = word;
            expected.reverse();
            expected.extend([true, false]);
            assert_eq!(state.stacks[1], VecDeque::from(expected));
            assert_eq!(state.stacks[0], VecDeque::from([true, false, true]));
            assert_eq!(stats.instructions, (6 * n + 4) as u64);
            assert!(state.pc.is_none());
        }
    }
}

#[test]
fn emitter_writes_a_framed_record_at_the_original_entry_and_cost() {
    let emitter = emit_record_program().unwrap();
    for n in 0..=7usize {
        for mask in 0..(1usize << n) {
            let word = (0..n).map(|i| (mask >> i) & 1 == 1).collect::<Vec<_>>();
            let mut state = emitter.initial(word.iter().rev().copied());
            state.stacks[2] = VecDeque::from([false, true]);
            let stats = emitter.run(&mut state, RunLimits::default()).unwrap();
            let mut expected = vec![true];
            expected.extend(frame(&word));
            expected.extend([false, true]);
            assert_eq!(state.stacks[2], VecDeque::from(expected));
            assert!(state.stacks[3].is_empty());
            assert_eq!(stats.instructions, (5 * n + 7) as u64);
            assert!(state.pc.is_none());
        }
    }
}
