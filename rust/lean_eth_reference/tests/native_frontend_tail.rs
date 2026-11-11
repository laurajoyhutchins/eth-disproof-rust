//! Physical original frontend suffix; host oracle is used only in assertions.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_frontend_tail::{frontend_tail_program, place_body_program};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, p: usize, v: &[bool]) {
    c.stacks[p] = VecDeque::from(v.to_vec());
}
fn take<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn unary(n: usize) -> Vec<bool> {
    let mut v = vec![true; n];
    v.push(false);
    v
}
fn bits(n: usize, pattern: usize) -> Vec<bool> {
    (0..n).map(|i| ((pattern >> i) & 1) != 0).collect()
}

#[test]
fn body_placement_is_paid_preserving_copy_and_clear() {
    let p = place_body_program().unwrap();
    for n in 0..=18 {
        for pat in 0..4 {
            let body = bits(n, pat);
            let old = vec![true, false, true];
            let mut c = p.initial([]);
            put(&mut c, 1218, &body);
            put(&mut c, 265, &old);
            put(&mut c, 256, &[true, false, true, false]);
            put(&mut c, 1216, &[false, true]);
            c.regs[5] = true;
            c.regs[74] = true;
            let stats = p.run(&mut c, RunLimits::default()).unwrap();
            let mut expected = body.clone();
            expected.extend(old);
            assert_eq!(take(&c, 265), expected);
            assert!(c.stacks[1218].is_empty() && c.stacks[1219].is_empty());
            assert_eq!(take(&c, 256), vec![true, false, true, false]);
            assert_eq!(take(&c, 1216), vec![false, true]);
            assert!(c.regs[5] && c.regs[74]);
            assert_eq!(stats.instructions, (9 * n + 9) as u64);
            assert_eq!(c.pc, None);
        }
    }
}

#[test]
fn tail_composes_real_ambient_header_and_normalized_body() {
    let p = frontend_tail_program().unwrap();
    for n in 0..=12 {
        for m in 0..=9 {
            for pat in 0..4 {
                let original_body = bits(m, pat);
                let normalized = bits(m + 2, pat ^ 3);
                let mut input = unary(n);
                input.extend(&original_body);
                let mut c = p.initial(input.clone());
                put(&mut c, 1218, &normalized);
                put(&mut c, 267, &[true, false]);
                put(&mut c, 1216, &[false, true, false]);
                c.regs[7] = true;
                c.regs[79] = true;
                let stats = p.run(&mut c, RunLimits::default()).unwrap();
                assert_eq!(take(&c, 256), input);
                assert_eq!(take(&c, 265), normalized);
                assert_eq!(take(&c, 258), unary(n));
                assert!(c.stacks[1218].is_empty() && c.stacks[1219].is_empty());
                assert_eq!(take(&c, 267), vec![true, false]);
                assert_eq!(take(&c, 1216), vec![false, true, false]);
                assert!(c.regs[7] && c.regs[79]);
                let expected = 9 * (m + 2) + 8 + 7 * (n + 1 + m) + 4 * n + 2 * m + 14 + 1;
                assert_eq!(stats.instructions, expected as u64);
                assert_eq!(c.pc, None);
            }
        }
    }
}

#[test]
fn finite_capacity_refuses_without_false_completion() {
    let p = frontend_tail_program().unwrap();
    let mut c = p.initial(unary(20));
    put(&mut c, 1218, &[true; 12]);
    let err = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 4,
                max_stack_bits: 1000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(c.pc.is_some());
    assert!(c.stacks[258].is_empty());
}
