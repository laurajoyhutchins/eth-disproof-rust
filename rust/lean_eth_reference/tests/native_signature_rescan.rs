//! TDD oracle for the exact source key-equality comparator and freshness latch.
//! Independent reference for equality is Rust slice equality; machine behavior
//! uses only the pinned ten-instruction program and compiled source calls.

use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_signature_rescan::{
    RESCAN_STACKS, bit_equality_program, cleanup, cleanup_caller, duplicate_key_gate_caller,
    equality_call, equality_caller, equality_caller_via_two_stage_lift, key_equality_program,
    setup, setup_caller, store_fresh, update_fresh,
};

fn write<const R: usize, const S: usize>(s: &mut Config<R, S>, i: usize, xs: &[bool]) {
    s.stacks[i] = xs.iter().copied().collect();
}
fn word<const R: usize, const S: usize>(s: &Config<R, S>, i: usize) -> Vec<bool> {
    s.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, state: &mut Config<R, S>) -> u64 {
    state.pc = Some(p.entry());
    let stats = p
        .run(
            state,
            RunLimits {
                max_steps: 2_000_000,
                max_stack_bits: 80_000,
            },
        )
        .unwrap();
    assert_eq!(state.pc, None);
    stats.instructions
}
fn decode_word(bits: usize, length: usize) -> Vec<bool> {
    (0..length).map(|i| ((bits >> i) & 1) == 1).collect()
}

#[test]
fn bit_equality_has_exact_pinned_instructions_and_exhaustive_outcomes() {
    let p = bit_equality_program().unwrap();
    assert_eq!(p.code().len(), 10);
    assert_eq!((p.input_stack(), p.output_stack()), (0, 0));
    for a_len in 0..=4 {
        for b_len in 0..=4 {
            for a_bits in 0..(1usize << a_len) {
                for b_bits in 0..(1usize << b_len) {
                    let a = decode_word(a_bits, a_len);
                    let b = decode_word(b_bits, b_len);
                    let mut state = p.initial(a.iter().copied());
                    write(&mut state, 1, &b);
                    state.regs[4] = a != b; // poison old equality result
                    run(&p, &mut state);
                    assert_eq!(state.regs[4], a == b, "a={a:?} b={b:?}");
                    assert!(word(&state, 0).len() <= a.len());
                    assert!(word(&state, 1).len() <= b.len());
                }
            }
        }
    }
}

#[test]
fn key_equality_preserves_both_operands_and_frame_for_all_short_words() {
    let p = key_equality_program().unwrap();
    for left_len in 0..=4 {
        for right_len in 0..=4 {
            for left_bits in 0..(1usize << left_len) {
                for right_bits in 0..(1usize << right_len) {
                    let left = decode_word(left_bits, left_len);
                    let right = decode_word(right_bits, right_len);
                    let mut s = p.initial(left.iter().copied());
                    write(&mut s, 2, &right);
                    write(&mut s, 5, &[true, false, false, true]);
                    s.regs[4] = left != right;
                    run(&p, &mut s);
                    assert_eq!(s.regs[4], left == right, "left={left:?} right={right:?}");
                    assert_eq!(word(&s, 0), left);
                    assert_eq!(word(&s, 2), right);
                    assert_eq!(word(&s, 5), [true, false, false, true]);
                    for i in [1, 3, 4] {
                        assert!(word(&s, i).is_empty(), "scratch {i} remains allocated");
                    }
                }
            }
        }
    }
}

#[test]
fn source_16x24_equality_call_preserves_unmapped_ports_and_returns_full_key_answer() {
    let p = equality_call().unwrap().compiled(14, 17).unwrap();
    for (left, right) in [
        (vec![], vec![]),
        (vec![false, true], vec![false, true]),
        (vec![false, true], vec![true, true]),
        (vec![true], vec![true, false]),
    ] {
        let mut s = p.initial(vec![]);
        write(&mut s, 14, &left);
        write(&mut s, 17, &right);
        write(&mut s, 16, &[true, false, true]);
        write(&mut s, 18, &[false, false]);
        write(&mut s, 22, &[true]);
        s.regs[13] = true;
        run(&p, &mut s);
        assert_eq!(s.regs[4], left == right);
        assert!(s.regs[13]);
        assert_eq!(word(&s, 14), left);
        assert_eq!(word(&s, 17), right);
        assert_eq!(word(&s, 16), [true, false, true]);
        assert_eq!(word(&s, 18), [false, false]);
        assert_eq!(word(&s, 22), [true]);
        for i in [1, 3, 4] {
            assert!(word(&s, i).is_empty());
        }
    }
}

#[test]
fn two_stage_physical_lift_is_instruction_identical_to_direct_lift() {
    assert_eq!(RESCAN_STACKS.len(), 24);
    for (i, &port) in RESCAN_STACKS.iter().enumerate() {
        assert!(port < 896);
        for &other in RESCAN_STACKS.iter().take(i) {
            assert_ne!(other, port);
        }
    }
    let a = equality_caller().unwrap().compiled(838, 839).unwrap();
    let b = equality_caller_via_two_stage_lift()
        .unwrap()
        .compiled(838, 839)
        .unwrap();
    assert_eq!(a.code(), b.code());
}

#[test]
fn physical_freshness_gate_handles_duplicate_long_keys_and_prefix_conflicts() {
    let p = duplicate_key_gate_caller()
        .unwrap()
        .compiled(354, 839)
        .unwrap();
    let key = (0..192).map(|i| i % 5 <= 1).collect::<Vec<_>>();
    for (candidate, saved) in [
        (key.clone(), key.clone()),
        (key[..191].to_vec(), key.clone()),
        (key.clone(), key[..191].to_vec()),
        (key.clone(), {
            let mut k = key.clone();
            k[100] = !k[100];
            k
        }),
        (vec![], vec![]),
    ] {
        let mut s = p.initial(vec![]);
        write(&mut s, 354, &candidate);
        write(&mut s, 839, &saved);
        write(&mut s, 362, &[true]);
        write(&mut s, 895, &[false, true]);
        s.regs[34] = true;
        run(&p, &mut s);
        assert_eq!(s.regs[4], candidate == saved);
        assert_eq!(word(&s, 362), [candidate != saved]);
        assert_eq!(word(&s, 354), candidate);
        assert_eq!(word(&s, 839), saved);
        assert_eq!(word(&s, 895), [false, true]);
        assert!(s.regs[34]);
        for i in [341, 343, 344] {
            assert!(word(&s, i).is_empty());
        }
    }
}

#[test]
fn freshness_is_monotone_false_across_successive_predecessors() {
    let p = duplicate_key_gate_caller()
        .unwrap()
        .compiled(354, 839)
        .unwrap();
    let mut s = p.initial(vec![]);
    write(&mut s, 839, &[true, false, true]);
    write(&mut s, 362, &[true]);
    for (candidate, latch) in [
        (vec![false, false, true], true),
        (vec![true, false, true], false),
        (vec![true, true, true], false),
    ] {
        write(&mut s, 354, &candidate);
        run(&p, &mut s);
        assert_eq!(word(&s, 362), [latch]);
    }
}

#[test]
fn store_fresh_and_conditional_update_are_real_paid_stack_operations() {
    let store = store_fresh(false).unwrap().compiled(22, 22).unwrap();
    let mut s = store.initial(vec![true, true, false]);
    assert_eq!(run(&store, &mut s), 2 * 3 + 6);
    assert_eq!(word(&s, 22), [false]);

    let update = update_fresh().unwrap().compiled(22, 22).unwrap();
    let mut absent = update.initial(vec![true]);
    absent.regs[4] = false;
    assert_eq!(run(&update, &mut absent), 2); // conditional guard + halt
    assert_eq!(word(&absent, 22), [true]);
    let mut present = update.initial(vec![true]);
    present.regs[4] = true;
    assert_eq!(run(&update, &mut present), 1 + 2 + 2 + 3 + 1); // guarded clear + set/push + halt
    assert_eq!(word(&present, 22), [false]);
}

#[test]
fn source_setup_and_cleanup_restore_zero_predecessor_with_preserved_candidate() {
    let setup = setup().unwrap().compiled(16, 19).unwrap();
    let finish = cleanup().unwrap().compiled(19, 18).unwrap();
    for h in [0, 1, 2, 3, 8, 64] {
        let candidate = (0..h).map(|i| i % 2 == 0).collect::<Vec<_>>();
        let mut s = setup.initial(vec![]);
        write(&mut s, 16, &candidate);
        write(&mut s, 18, &vec![true; h]);
        write(&mut s, 22, &[false]);
        assert_eq!(run(&setup, &mut s), (7 * h + 13) as u64);
        assert_eq!(word(&s, 19), candidate);
        assert_eq!(word(&s, 22), [true]);
        assert_eq!(word(&s, 16), candidate);
        assert!(word(&s, 21).is_empty());
        // The absent predecessor loop is a separate stage; simulate its
        // verified postcondition: a fixed-width all-zero countdown word.
        write(&mut s, 19, &vec![false; h]);
        assert_eq!(run(&finish, &mut s), (2 * h + 3 * h + 7) as u64);
        assert_eq!(word(&s, 18), vec![false; h]);
        assert!(word(&s, 19).is_empty());
        assert_eq!(word(&s, 16), candidate);
        assert_eq!(word(&s, 22), [true]);
    }
}

#[test]
fn physical_setup_cleanup_preserve_the_nonlocal_tuple_frame() {
    let setup = setup_caller().unwrap().compiled(838, 359).unwrap();
    let finish = cleanup_caller().unwrap().compiled(359, 844).unwrap();
    let mut s = setup.initial(vec![]);
    write(&mut s, 838, &[true, false, true, true]);
    write(&mut s, 844, &[true, true, false]);
    write(&mut s, 836, &[false, true, true]);
    write(&mut s, 850, &[true, false, false, true]);
    s.regs[36] = true;
    run(&setup, &mut s);
    assert_eq!(word(&s, 359), [true, false, true, true]);
    assert_eq!(word(&s, 362), [true]);
    write(&mut s, 359, &[false; 4]);
    run(&finish, &mut s);
    assert_eq!(word(&s, 844), [false; 4]);
    assert_eq!(word(&s, 836), [false, true, true]);
    assert_eq!(word(&s, 850), [true, false, false, true]);
    assert_eq!(word(&s, 838), [true, false, true, true]);
    assert!(s.regs[36]);
}

#[test]
fn maliciously_low_step_budget_refuses_without_reporting_a_result() {
    let p = key_equality_program().unwrap();
    let mut s = p.initial(vec![true; 64]);
    write(&mut s, 2, &[true; 64]);
    let outcome = p.run(
        &mut s,
        RunLimits {
            max_steps: 8,
            max_stack_bits: 2000,
        },
    );
    assert!(outcome.is_err());
    assert_ne!(s.pc, None);
}
