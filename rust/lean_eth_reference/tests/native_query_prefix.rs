//! Independent, bounded end-to-end tests for the actual query-stream prefix.
//! In particular, expected aligned vectors are constructed from mask/assignment
//! pairs, not from the Rust parser, flattener, or merger under test.

use std::collections::VecDeque;

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_query_prefix::{
    copy_high_counter_command, flatten_program, frame_program, local_high_context_program,
    mask_program, prepare_high_program, query_stream_prefix_command, restriction_program,
    transfer_program,
};
use lean_eth_reference::native_tuple::encode_words;

fn bits<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}

fn mask_from_rank(width: usize, rank: usize) -> Vec<bool> {
    (0..width).map(|i| rank & (1 << i) != 0).collect()
}

fn high_bits(width: usize, rank: usize) -> Vec<bool> {
    mask_from_rank(width, rank)
}

fn aligned(mask: &[bool], assignment: &[bool]) -> Vec<bool> {
    let mut high = assignment.iter().copied();
    mask.iter()
        .map(|&selected| {
            if selected {
                high.next().unwrap()
            } else {
                false
            }
        })
        .collect()
}

fn assignment_records(high: &[bool]) -> Vec<Vec<bool>> {
    high.iter().copied().map(|bit| vec![bit]).collect()
}

fn state_with<const R: usize, const S: usize>(
    program: &lean_eth_reference::bit_program::Program<R, S>,
    port: usize,
    bits: &[bool],
) -> Config<R, S> {
    let mut c = program.initial(Vec::new());
    c.stacks[port] = VecDeque::from(bits.to_vec());
    c
}

#[test]
fn primitive_transfer_and_frame_parser_match_the_pinned_instruction_tables() {
    let transfer = transfer_program::<2, 2>(0, 1, 0, 1).unwrap();
    assert_eq!(transfer.code().len(), 4);
    let frame = frame_program().unwrap();
    assert_eq!(frame.code().len(), 7);
    assert!(transfer_program::<2, 2>(0, 0, 0, 1).is_err());
    assert!(transfer_program::<2, 2>(0, 1, 0, 0).is_err());
    for n in 0..=6 {
        for rank in 0..(1 << n) {
            let word = mask_from_rank(n, rank);
            let mut d = transfer.initial(word.clone());
            let report = transfer.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(report.instructions, 3 * n as u64 + 3);
            assert_eq!(bits(&d, 1), word.iter().rev().copied().collect::<Vec<_>>());
            assert!(d.stacks[0].is_empty());
            let framed = encode_words(std::slice::from_ref(&word)).unwrap();
            // encodeWords adds the outer record tag + terminator, and the
            // inner frame begins immediately after the first tag.
            let mut d = frame.initial(framed[1..].to_vec());
            let report = frame.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(report.instructions, 6 * n as u64 + 4);
            assert_eq!(bits(&d, 1), word.iter().rev().copied().collect::<Vec<_>>());
            assert_eq!(bits(&d, 0), [false]);
            assert_eq!(d.regs, [false, true]);
        }
    }
}

#[test]
fn native_mask_flattener_and_merger_have_exact_step_counts() {
    let mask_source = mask_program().unwrap();
    let flatten = flatten_program().unwrap();
    let merge = restriction_program().unwrap();
    let local = local_high_context_program().unwrap();
    assert_eq!(local.input_stack(), 0);
    assert_eq!(local.output_stack(), 3);
    for width in 0..=5 {
        for mask_rank in 0..(1 << width) {
            let mask = mask_from_rank(width, mask_rank);
            let high = mask.iter().filter(|&&b| b).count();
            let mut d = state_with(&mask_source, 0, &mask);
            let stats = mask_source.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, 10 * width as u64 + 9);
            assert_eq!(bits(&d, 0), mask);
            assert_eq!(bits(&d, 2), mask.iter().rev().copied().collect::<Vec<_>>());
            for rank in 0..(1 << high) {
                let assignment = high_bits(high, rank);
                let encoded = encode_words(&assignment_records(&assignment)).unwrap();
                let mut d = flatten.initial(encoded.clone());
                let stats = flatten.run(&mut d, RunLimits::default()).unwrap();
                assert_eq!(stats.instructions, 9 * high as u64 + 6 * high as u64 + 7);
                assert_eq!(bits(&d, 2), assignment);
                assert!(d.stacks[0].is_empty());
                assert!(d.stacks[1].is_empty());
                let mut d = state_with(&merge, 0, &mask);
                d.stacks[1] = VecDeque::from(assignment.clone());
                let stats = merge.run(&mut d, RunLimits::default()).unwrap();
                assert_eq!(stats.instructions, 5 * width as u64 + 3);
                let expected: Vec<bool> = aligned(&mask, &assignment);
                assert_eq!(bits(&d, 3), expected.into_iter().rev().collect::<Vec<_>>());
                assert!(d.stacks[0].is_empty());
                assert!(d.stacks[1].is_empty());
                assert!(d.stacks[2].is_empty());
            }
        }
    }
}

#[test]
fn physical_prepare_high_handles_dirty_scratch_and_preserves_frame() {
    let program = prepare_high_program().unwrap();
    let local = local_high_context_program().unwrap();
    assert_eq!(program.input_stack(), 330);
    assert_eq!(program.output_stack(), 703);
    for width in 0..=6 {
        for mask_rank in 0..(1 << width) {
            let mask = mask_from_rank(width, mask_rank);
            let high = mask.iter().filter(|&&b| b).count();
            for rank in 0..(1 << high) {
                let assignment = high_bits(high, rank);
                let encoded = encode_words(&assignment_records(&assignment)).unwrap();
                let mut d = state_with(&program, 330, &encoded);
                d.regs[21] = true;
                d.regs[39] = true;
                d.stacks[338] = VecDeque::from(mask.clone());
                d.stacks[799] = VecDeque::from(vec![true, false, true]);
                for stack in [702, 703, 680, 681, 682, 683, 684, 685] {
                    d.stacks[stack] = VecDeque::from(vec![false, true, false]);
                }
                let stats = program.run(&mut d, RunLimits::default()).unwrap();
                assert!(stats.instructions > local.code().len() as u64);
                assert_eq!(bits(&d, 330), encoded);
                assert_eq!(bits(&d, 338), mask);
                assert_eq!(
                    bits(&d, 702),
                    mask.iter().rev().copied().collect::<Vec<_>>()
                );
                assert_eq!(
                    bits(&d, 703),
                    aligned(&mask, &assignment)
                        .into_iter()
                        .rev()
                        .collect::<Vec<_>>()
                );
                for port in [680, 681, 682, 683, 684, 685] {
                    assert!(d.stacks[port].is_empty(), "stale scratch on {port}");
                }
                assert_eq!(bits(&d, 799), [true, false, true]);
                assert!(d.regs[21] && d.regs[39]);
                assert!(d.pc.is_none());
            }
        }
    }
}

#[test]
fn conditioned_query_prefix_uses_actual_persistent_counter_and_mask() {
    let prefix = query_stream_prefix_command()
        .unwrap()
        .compiled(789, 703)
        .unwrap();
    let source_copy = copy_high_counter_command().unwrap();
    assert_eq!(
        prefix.code().len(),
        source_copy.size().unwrap() + prepare_high_program().unwrap().code().len()
    );
    for width in 0..=6 {
        for mask_rank in 0..(1 << width) {
            let mask = mask_from_rank(width, mask_rank);
            let high = mask.iter().filter(|&&b| b).count();
            for rank in 0..(1 << high) {
                let assignment = high_bits(high, rank);
                let encoded = encode_words(&assignment_records(&assignment)).unwrap();
                let mut d = prefix.initial(encoded.clone());
                d.regs[21] = true;
                d.stacks[789] = VecDeque::from(encoded.clone());
                d.stacks[338] = VecDeque::from(mask.clone());
                d.stacks[330] = VecDeque::from(vec![true, false]);
                d.stacks[792] = VecDeque::from(vec![true, true]);
                let _stats = prefix.run(&mut d, RunLimits::default()).unwrap();
                assert_eq!(bits(&d, 789), encoded);
                assert_eq!(bits(&d, 330), encoded);
                assert_eq!(bits(&d, 338), mask);
                assert_eq!(
                    bits(&d, 703),
                    aligned(&mask, &assignment)
                        .into_iter()
                        .rev()
                        .collect::<Vec<_>>()
                );
                assert!(d.stacks[792].is_empty());
                assert!(d.regs[21]);
            }
        }
    }
}

#[test]
fn prefix_program_is_static_in_input_width_and_assignment() {
    // The program table contains no mask bits or assignments. Its source size
    // is fixed by the parsed Lean command tree, not runtime data.
    let program = prepare_high_program().unwrap();
    let count = program.code().len();
    assert_eq!(count, 85); // 10*3 clear labels + 54 local labels + final halt
    let other = query_stream_prefix_command()
        .unwrap()
        .compiled(330, 703)
        .unwrap();
    assert_eq!(
        other.code().len(),
        count + copy_high_counter_command().unwrap().size().unwrap()
    );
    assert!(other.code().len() > count);
}

#[test]
fn high_loop_executes_the_physical_query_prefix_for_every_assignment() {
    use lean_eth_reference::native_tuple::{encode_words, high_loop_command};

    let callback = query_stream_prefix_command().unwrap();
    let callback_size = callback.size().unwrap();
    let program = high_loop_command(callback)
        .unwrap()
        .compiled(789, 703)
        .unwrap();
    // `ExecCNFTupleEnumeration`: start label 0, guard label 1, callback
    // begins at 2; the actual odometer follows callback's final instruction.
    let after_prefix = 2 + callback_size;
    for width in 0..=4 {
        for mask_rank in 0..(1 << width) {
            let mask = mask_from_rank(width, mask_rank);
            let high = mask.iter().filter(|&&b| b).count();
            let empty = encode_words(&assignment_records(&vec![false; high])).unwrap();
            let mut state = program.initial(empty.clone());
            state.stacks[338] = VecDeque::from(mask.clone());
            state.stacks[330] = VecDeque::from(vec![false, true, true]);
            state.stacks[792] = VecDeque::from(vec![true]);
            let mut visits = 0usize;
            let mut steps = 0usize;
            while state.pc.is_some() {
                assert!(steps < 100_000, "unexpected infinite loop");
                if state.pc == Some(after_prefix) {
                    let assignment = high_bits(high, visits);
                    assert_eq!(
                        bits(&state, 789),
                        encode_words(&assignment_records(&assignment)).unwrap()
                    );
                    assert_eq!(bits(&state, 330), bits(&state, 789));
                    assert_eq!(
                        bits(&state, 703),
                        aligned(&mask, &assignment)
                            .into_iter()
                            .rev()
                            .collect::<Vec<_>>()
                    );
                    assert_eq!(
                        bits(&state, 702),
                        mask.iter().rev().copied().collect::<Vec<_>>()
                    );
                    assert!(state.regs[21]);
                    assert!(state.stacks[790].is_empty());
                    visits += 1;
                }
                program.step(&mut state).unwrap();
                steps += 1;
            }
            assert_eq!(visits, 1 << high, "wrong number of physical callbacks");
            assert_eq!(bits(&state, 789), empty, "final overflow did not wrap");
            assert!(!state.regs[21], "final overflow guard not cleared");
        }
    }
}
