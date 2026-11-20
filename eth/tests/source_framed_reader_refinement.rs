//! Rust-side witness for the pinned Lean RecordPrograms.reader boundary.
//!
//! The expected seven-label table is written independently of frame_program
//! and Program::lift. Lean's FramedRecordReaderRefinement.lean proves this
//! same parameterized table equals the actual original Lean source for every
//! valid RecordPrograms.Ports. The Rust check covers the six real caller maps;
//! it does not formally refine the Rust interpreter or compiler.

use std::collections::VecDeque;

use lean_eth_reference::bit_program::frame_programs::frame_program;
use lean_eth_reference::bit_program::{Instr, Program, RunLimits};

/// Exact Lean-mapped table, with each physical instruction spelled out.
/// This must not call the production frame constructor or the Rust lifter.
fn source_reader<const R: usize, const S: usize>(
    tag: usize,
    present: usize,
    source: usize,
    payload: usize,
) -> Program<R, S> {
    Program::new(
        source,
        payload,
        0,
        vec![
            Instr::Pop {
                stack: source,
                value: tag,
                present,
                next: 1,
            },
            Instr::Branch {
                test: present,
                yes: 2,
                no: 6,
            },
            Instr::Branch {
                test: tag,
                yes: 3,
                no: 6,
            },
            Instr::Pop {
                stack: source,
                value: tag,
                present,
                next: 4,
            },
            Instr::Branch {
                test: present,
                yes: 5,
                no: 6,
            },
            Instr::Push {
                stack: payload,
                src: tag,
                next: 0,
            },
            Instr::Halt,
        ],
    )
    .unwrap()
}

fn framed(bits: &[bool]) -> Vec<bool> {
    let mut result = Vec::with_capacity(bits.len() * 2 + 1);
    for &bit in bits {
        result.extend([true, bit]);
    }
    result.push(false);
    result
}

fn verify_reader<const R: usize, const S: usize>(
    tag: usize,
    present: usize,
    found: usize,
    source: usize,
    payload: usize,
) {
    assert_ne!(tag, present);
    assert_ne!(found, tag);
    assert_ne!(found, present);
    assert_ne!(source, payload);
    let source_table = source_reader::<R, S>(tag, present, source, payload);
    let lifted = frame_program()
        .unwrap()
        .lift::<R, S>([tag, present], [source, payload])
        .unwrap();
    assert_eq!(lifted, source_table);
    assert_eq!(lifted.code().len(), 7);
    assert_eq!(
        (lifted.input_stack(), lifted.output_stack(), lifted.entry()),
        (source, payload, 0)
    );

    // A nonempty suffix, preexisting payload tail and found=true stress
    // exactly what the frame reader must leave untouched.
    for length in 0..=5usize {
        for mask in 0..(1usize << length) {
            let word = (0..length)
                .map(|i| (mask >> i) & 1 == 1)
                .collect::<Vec<_>>();
            let mut encoded = framed(&word);
            encoded.extend([true, false]);
            let mut state = lifted.initial(encoded);
            state.regs[found] = true;
            state.stacks[payload] = VecDeque::from([false, true]);
            let stats = lifted.run(&mut state, RunLimits::default()).unwrap();

            let mut output = word;
            output.reverse();
            output.extend([false, true]);
            assert_eq!(state.stacks[source], VecDeque::from([true, false]));
            assert_eq!(state.stacks[payload], VecDeque::from(output));
            assert!(state.regs[found]);
            assert!(!state.regs[tag]);
            assert!(state.regs[present]);
            assert!(state.pc.is_none());
            assert_eq!(stats.instructions, (6 * length + 4) as u64);
        }
    }
}

#[test]
fn all_six_original_source_scanner_port_maps_match_the_explicit_lean_table() {
    // Clause deduplication and all fixed-master filter modes share ports.
    verify_reader::<15, 16>(0, 1, 14, 13, 15);
    verify_reader::<15, 16>(0, 1, 14, 13, 15);
    // Three relation modes share these different physical register/stack maps.
    verify_reader::<15, 12>(12, 13, 14, 10, 11);
    // Tautology, encoded membership, record reversal.
    verify_reader::<13, 11>(10, 11, 12, 0, 1);
    verify_reader::<7, 5>(5, 6, 4, 0, 1);
    verify_reader::<3, 4>(0, 1, 2, 0, 3);
}

#[test]
fn the_frame_lift_refuses_colliding_read_registers_and_stacks() {
    let base = frame_program().unwrap();
    assert!(base.lift::<3, 3>([0, 0], [0, 1]).is_err());
    assert!(base.lift::<3, 3>([0, 1], [0, 0]).is_err());
    assert!(base.lift::<3, 3>([0, 3], [0, 1]).is_err());
    assert!(base.lift::<3, 3>([0, 1], [0, 3]).is_err());
}
