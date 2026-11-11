//! Independently checked original machine header parsing, never a host parser.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_frontend_header::{header_program, initialize_program};
use std::collections::VecDeque;
fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, p: usize, v: &[bool]) {
    c.stacks[p] = VecDeque::from(v.to_vec());
}
fn take<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn unary(n: usize) -> Vec<bool> {
    let mut s = vec![true; n];
    s.push(false);
    s
}
fn binary(mut n: usize) -> Vec<bool> {
    let mut b = vec![];
    while n > 0 {
        b.push(n & 1 != 0);
        n >>= 1;
    }
    b
}
fn word(n: usize, mask: usize) -> Vec<bool> {
    (0..n).map(|i| ((mask >> i) & 1) != 0).collect()
}

#[test]
fn nineteen_labels_match_source_link_and_read_correct_n_binary() {
    let p = initialize_program().unwrap();
    assert_eq!(p.code().len(), 19);
    assert_eq!(p.code()[4], Instr::Goto { next: 5 });
    assert_eq!(p.code()[18], Instr::Halt);
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 2);
    for n in 0..=96 {
        for pat in 0..4 {
            let tail = word(6, pat);
            let mut input = unary(n);
            input.extend(&tail);
            let mut c = p.initial(input);
            let stats = p.run(&mut c, RunLimits::default()).unwrap();
            assert_eq!(take(&c, 0), tail);
            assert!(c.stacks[1].is_empty() && c.stacks[3].is_empty());
            assert_eq!(take(&c, 2), binary(n));
            assert_eq!(c.regs, [false, false, false]);
            assert!(stats.instructions <= (4 * n + 4 + n * (8 * n + 10) + 3) as u64);
            assert_eq!(c.pc, None);
        }
    }
}

#[test]
fn source_header_command_preserves_input_and_physical_abi_frame() {
    let p = header_program().unwrap();
    for n in 0..=32 {
        for m in 0..=8 {
            let original = word(m, 5);
            let mut input = unary(n);
            input.extend(&original);
            let mut c = p.initial(input.clone());
            put(&mut c, 1216, &[false, true]);
            put(&mut c, 1217, &[true, false, true]);
            put(&mut c, 265, &[false, false]);
            c.regs[5] = true;
            c.regs[79] = true;
            let stats = p.run(&mut c, RunLimits::default()).unwrap();
            assert_eq!(take(&c, 256), input);
            assert_eq!(take(&c, 1218), original);
            assert_eq!(take(&c, 267), binary(n));
            assert!(
                c.stacks[268].is_empty() && c.stacks[269].is_empty() && c.stacks[1219].is_empty()
            );
            assert_eq!(take(&c, 1216), vec![false, true]);
            assert_eq!(take(&c, 1217), vec![true, false, true]);
            assert_eq!(take(&c, 265), vec![false, false]);
            assert!(c.regs[5] && c.regs[79]);
            for reg in 72..=74 {
                assert!(!c.regs[reg]);
            }
            assert!(
                stats.instructions
                    <= (7 * (n + 1 + m) + 5 + 4 * n + 4 + n * (8 * n + 10) + 3 + 1) as u64
            );
            assert_eq!(c.pc, None);
        }
    }
}

#[test]
fn header_capacity_refusal_is_not_a_parsed_header() {
    let p = header_program().unwrap();
    let mut c = p.initial(unary(70));
    let err = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 2000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(c.pc.is_some());
    assert!(c.stacks[267].is_empty());
}
