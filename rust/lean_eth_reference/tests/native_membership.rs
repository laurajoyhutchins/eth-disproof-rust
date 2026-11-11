//! Exact small bit-machine comparator and encoded-record callback tests.
use std::collections::VecDeque;

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_membership::{
    bit_equality_program, membership_callback_program, membership_eq_program,
};

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, p: usize, bits: &[bool]) {
    c.stacks[p] = bits.iter().copied().collect::<VecDeque<_>>();
}
fn take<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn bits(len: usize, mask: usize) -> Vec<bool> {
    (0..len).map(|i| ((mask >> i) & 1) == 1).collect()
}

#[test]
fn original_ten_label_bit_comparator_exact_table_and_all_small_words() {
    let p = bit_equality_program().unwrap();
    assert_eq!(p.code().len(), 10);
    assert_eq!(
        p.code()[0],
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 1,
            next: 1
        }
    );
    assert_eq!(
        p.code()[2],
        Instr::Xor {
            dst: 4,
            left: 1,
            right: 3,
            next: 3
        }
    );
    assert_eq!(p.code()[9], Instr::Halt);
    for lx in 0..=5 {
        for ly in 0..=5 {
            for mx in 0..(1 << lx) {
                for my in 0..(1 << ly) {
                    let xs = bits(lx, mx);
                    let ys = bits(ly, my);
                    let mut c = p.initial(xs.clone());
                    put(&mut c, 1, &ys);
                    c.regs[4] = mx % 2 == 1;
                    let stats = p.run(&mut c, RunLimits::default()).unwrap();
                    assert_eq!(c.regs[4], xs == ys, "xs={xs:?} ys={ys:?}");
                    assert!(stats.instructions <= (9 * (lx + 1)) as u64);
                    assert_eq!(c.pc, None);
                    if xs == ys {
                        assert!(c.stacks[0].is_empty() && c.stacks[1].is_empty());
                        assert_eq!(stats.instructions, (7 * (lx + 1)) as u64);
                    }
                }
            }
        }
    }
}

#[test]
fn comparator_is_really_lifted_to_membership_ports_and_preserves_frames() {
    let p = membership_eq_program().unwrap();
    assert_eq!(p.code().len(), 10);
    assert_eq!(p.input_stack(), 1);
    for lx in 0..=4 {
        for ly in 0..=4 {
            for mx in 0..1usize << lx {
                for my in 0..1usize << ly {
                    let xs = bits(lx, mx);
                    let ys = bits(ly, my);
                    let mut c = p.initial([]);
                    put(&mut c, 1, &xs);
                    put(&mut c, 3, &ys);
                    put(&mut c, 0, &[true, false]);
                    put(&mut c, 2, &[false, true]);
                    put(&mut c, 4, &[true, true]);
                    c.regs[0] = true;
                    c.regs[6] = true;
                    p.run(&mut c, RunLimits::default()).unwrap();
                    assert_eq!(c.regs[4], xs == ys);
                    assert!(c.regs[6]);
                    assert_eq!(take(&c, 0), vec![true, false]);
                    assert_eq!(take(&c, 2), vec![false, true]);
                    assert_eq!(take(&c, 4), vec![true, true]);
                }
            }
        }
    }
}

#[test]
fn source_callback_executes_copy_comparison_and_real_cleanup() {
    let p = membership_callback_program().unwrap();
    assert_eq!(p.input_stack(), 1);
    for lx in 0..=5 {
        for ly in 0..=5 {
            for mx in 0..1usize << lx {
                for my in 0..1usize << ly {
                    let query = bits(lx, mx);
                    let payload = bits(ly, my);
                    let mut c = p.initial([]);
                    // Two already-reversed words, as in the source iterator.
                    put(&mut c, 1, &payload);
                    put(&mut c, 2, &query);
                    put(&mut c, 0, &[false, true, false]);
                    c.regs[5] = true;
                    c.regs[6] = true;
                    let stats = p.run(&mut c, RunLimits::default()).unwrap();
                    assert_eq!(c.regs[4], query == payload);
                    assert_eq!(take(&c, 2), query);
                    assert!(c.stacks[1].is_empty());
                    assert!(c.stacks[3].is_empty());
                    assert!(c.stacks[4].is_empty());
                    assert_eq!(take(&c, 0), vec![false, true, false]);
                    assert!(c.regs[5]);
                    assert!(c.regs[6]);
                    assert_eq!(c.pc, None);
                    assert!(stats.instructions > 0);
                    if query == payload {
                        assert_eq!(stats.instructions, (14 * lx + 19) as u64);
                    }
                }
            }
        }
    }
}

#[test]
fn early_mismatch_keeps_tails_until_explicit_clear() {
    let p = membership_callback_program().unwrap();
    let mut c = p.initial([]);
    put(&mut c, 1, &[false, true, true, true, true]);
    put(&mut c, 2, &[true, false, false, false, false]);
    p.run(&mut c, RunLimits::default()).unwrap();
    assert!(!c.regs[4]);
    assert!(c.stacks[1].is_empty() && c.stacks[3].is_empty());
    assert_eq!(take(&c, 2), vec![true, false, false, false, false]);
}

#[test]
fn callback_enforces_finite_machine_resource_refusal() {
    let p = membership_callback_program().unwrap();
    let mut c = p.initial([]);
    put(&mut c, 1, &[true; 10]);
    put(&mut c, 2, &[true; 10]);
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
}
