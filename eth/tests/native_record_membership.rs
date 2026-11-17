//! Independent result oracle in tests only; execution is physical finite code.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_record_membership::{
    frame_program, membership_program, raw_membership_program,
};

fn put<const R: usize, const S: usize>(state: &mut Config<R, S>, port: usize, word: &[bool]) {
    state.stacks[port] = VecDeque::from(word.to_vec());
}
fn take<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}
fn frame(word: &[bool]) -> Vec<bool> {
    let mut out = Vec::with_capacity(2 * word.len() + 1);
    for bit in word {
        out.push(true);
        out.push(*bit);
    }
    out.push(false);
    out
}
fn encode_list(words: &[Vec<bool>]) -> Vec<bool> {
    let mut out = Vec::new();
    for word in words {
        out.push(true);
        out.extend(frame(word));
    }
    out.push(false);
    out
}
fn bits(n: usize, mask: usize) -> Vec<bool> {
    (0..n).map(|i| (mask >> i) & 1 == 1).collect()
}

#[test]
fn exact_source_frame_table_and_exhaustive_payloads() {
    let p = frame_program().unwrap();
    assert_eq!(p.code().len(), 7);
    assert_eq!(
        p.code()[0],
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 1,
            next: 1
        }
    );
    assert_eq!(p.code()[6], Instr::Halt);
    for len in 0..=8 {
        for mask in 0..1usize << len {
            let word = bits(len, mask);
            let tail = [true, true, false, true];
            let mut input = frame(&word);
            input.extend(tail);
            let mut c = p.initial(input);
            let steps = p.run(&mut c, RunLimits::default()).unwrap();
            assert_eq!(steps.instructions, (6 * len + 4) as u64);
            assert_eq!(take(&c, 0), tail);
            assert_eq!(take(&c, 1), word.iter().rev().copied().collect::<Vec<_>>());
            assert_eq!(&c.regs, &[false, true]);
        }
    }
}

#[test]
fn source_record_membership_all_single_payload_pairs_and_dirty_frames() {
    let p = membership_program().unwrap();
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 1);
    for n in 0..=5 {
        for m in 0..1usize << n {
            let query = bits(n, m);
            for k in 0..=5 {
                for t in 0..1usize << k {
                    let candidate = bits(k, t);
                    let source = encode_list(std::slice::from_ref(&candidate));
                    let mut c = p.initial(source);
                    let reversed: Vec<_> = query.iter().copied().rev().collect();
                    put(&mut c, 2, &reversed);
                    c.regs[3] = true;
                    c.regs[6] = true;
                    let steps = p.run(&mut c, RunLimits::default()).unwrap();
                    assert_eq!(take(&c, 1), vec![candidate == query]);
                    assert_eq!(take(&c, 2), reversed);
                    assert!(c.stacks[3].is_empty() && c.stacks[4].is_empty());
                    // Register 3 is comparator work; register 6 is the outer presence bit.
                    assert!(c.regs[6]);
                    assert!(steps.instructions > 0);
                }
            }
        }
    }
}

#[test]
fn full_raw_record_membership_lists_first_middle_last_absent_empty_and_duplicates() {
    let p = raw_membership_program().unwrap();
    let words = [
        vec![],
        vec![false],
        vec![true],
        vec![true, false],
        vec![false, true],
    ];
    let fixtures: Vec<Vec<Vec<bool>>> = vec![
        vec![],
        vec![vec![]],
        vec![vec![true]],
        vec![vec![], vec![false]],
        vec![vec![false], vec![true], vec![false, true]],
        vec![vec![true], vec![false], vec![true]],
    ];
    for records in fixtures {
        for query in words.clone() {
            let mut input = frame(&query);
            input.extend(encode_list(&records));
            let mut c = p.initial(input);
            c.regs = [true; 7];
            let stats = p.run(&mut c, RunLimits::default()).unwrap();
            assert_eq!(
                take(&c, 1),
                vec![records.contains(&query)],
                "records={records:?} query={query:?}"
            );
            assert!(c.stacks[0].is_empty());
            assert!(c.stacks[2].is_empty());
            assert!(c.stacks[3].is_empty());
            assert!(c.stacks[4].is_empty());
            assert_eq!(c.regs, [false; 7]);
            assert_eq!(c.pc, None);
            assert!(stats.instructions > 0);
        }
    }
}

#[test]
fn callback_short_circuits_only_after_real_member_found() {
    let p = membership_program().unwrap();
    let records = vec![vec![true], vec![false], vec![false, true]];
    let source = encode_list(&records);
    let mut c = p.initial(source.clone());
    put(&mut c, 2, &[false]);
    p.run(&mut c, RunLimits::default()).unwrap();
    assert_eq!(take(&c, 1), vec![true]);
    assert!(
        !c.stacks[0].is_empty(),
        "true member should retain unread suffix"
    );
    assert_eq!(take(&c, 2), vec![false]);
    assert!(c.regs[4]);
}

#[test]
fn full_raw_member_protects_resource_limits() {
    let p = raw_membership_program().unwrap();
    let records = vec![vec![true; 12]; 15];
    let mut input = frame(&[false; 8]);
    input.extend(encode_list(&records));
    let mut c = p.initial(input);
    let err = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 10_000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(c.pc.is_some());
}
