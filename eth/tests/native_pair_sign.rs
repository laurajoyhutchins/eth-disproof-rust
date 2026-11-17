//! Exact source parity sign in the 3x4 local machine and 40x896 pair ABI.
//! The expected sign is independently obtained from Boolean mask cardinality.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, Instr, Program, RunLimits};
use lean_eth_reference::native_difference_pairs::query_pairs_command;
use lean_eth_reference::native_pair_sign::{
    PAIR_SIGN_REGISTERS, PAIR_SIGN_STACKS, pair_sign_call, pair_sign_call_program,
    pair_sign_program, parity_program,
};

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, word: &[bool]) {
    d.stacks[port] = word.iter().copied().collect();
}
fn got<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: 2_000_000,
            max_stack_bits: 500_000,
        },
    )
    .unwrap()
    .instructions
}
fn word(n: usize, mask: usize) -> Vec<bool> {
    (0..n).map(|j| mask & (1 << j) != 0).collect()
}
fn expected_sign(e: &[bool], u: &[bool]) -> bool {
    (e.iter().filter(|&&b| b).count() + u.iter().filter(|&&b| b).count()) % 2 == 1
}

#[test]
fn original_four_label_parity_table_is_literal() {
    let p = parity_program().unwrap();
    assert_eq!(p.code().len(), 4);
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 0);
    assert!(matches!(
        p.code()[0],
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 1,
            next: 1
        }
    ));
    assert!(matches!(
        p.code()[1],
        Instr::Branch {
            test: 1,
            yes: 2,
            no: 3
        }
    ));
    assert!(matches!(
        p.code()[2],
        Instr::Xor {
            dst: 2,
            left: 2,
            right: 0,
            next: 0
        }
    ));
    assert!(matches!(p.code()[3], Instr::Halt));
    for n in 0..8 {
        for mask in 0..(1 << n) {
            for initial in [false, true] {
                let bits = word(n, mask);
                let mut d = p.initial(bits.clone());
                d.regs[2] = initial;
                assert_eq!(run(&p, &mut d), (3 * n + 3) as u64);
                assert!(got(&d, 0).is_empty());
                assert_eq!(
                    d.regs[2],
                    initial ^ (bits.iter().filter(|&&b| b).count() % 2 == 1)
                );
            }
        }
    }
}

#[test]
fn exhaustive_small_masks_are_signed_by_two_physical_parity_scans() {
    let p = pair_sign_program().unwrap();
    for n in 0..=5 {
        for e in 0..(1 << n) {
            for u in 0..(1 << n) {
                let eword = word(n, e);
                let uword = word(n, u);
                let mut d = p.initial(eword.clone());
                put(&mut d, 1, &uword);
                d.regs = [true, false, true];
                let steps = run(&p, &mut d);
                assert_eq!(steps, (10 * (eword.len() + uword.len()) + 19) as u64);
                assert_eq!(got(&d, 0), eword);
                assert_eq!(got(&d, 1), uword);
                assert!(got(&d, 3).is_empty());
                let sign = expected_sign(&eword, &uword);
                assert_eq!(got(&d, 2), [sign]);
                assert_eq!(d.regs, [false, false, sign]);
            }
        }
    }
}

#[test]
fn strict_subset_pairs_have_the_correct_finite_difference_sign() {
    let p = pair_sign_program().unwrap();
    for n in 0..=7 {
        for e in 0..(1 << n) {
            for u in 0..(1 << n) {
                if u & !e != 0 {
                    continue;
                }
                let eword = word(n, e);
                let uword = word(n, u);
                let mut d = p.initial(eword.clone());
                put(&mut d, 1, &uword);
                run(&p, &mut d);
                let exponent = e.count_ones() - u.count_ones();
                assert_eq!(got(&d, 2), [exponent % 2 != 0]);
            }
        }
    }
}

#[test]
fn lifted_pair_call_preserves_ambient_dictionary_tuple_and_accumulator() {
    assert_eq!(PAIR_SIGN_STACKS, [834, 835, 848, 849]);
    assert_eq!(PAIR_SIGN_REGISTERS, [0, 1, 2]);
    let p = pair_sign_call_program().unwrap();
    for n in [0, 1, 4, 9, 17] {
        let e: Vec<bool> = (0..n).map(|j| j % 3 != 1).collect();
        let u: Vec<bool> = (0..n).map(|j| j % 4 == 0).collect();
        let mut d = p.initial([]);
        put(&mut d, 834, &e);
        put(&mut d, 835, &u);
        let guards = [
            (837, vec![true, true, false]),
            (850, vec![false, true]),
            (851, vec![false, true, true]),
            (842, vec![true]),
            (649, vec![true, true]),
            (194, vec![false, false, true]),
        ];
        for (port, w) in &guards {
            put(&mut d, *port, w);
        }
        d.regs[24] = true;
        d.regs[36] = true;
        assert_eq!(run(&p, &mut d), (10 * (e.len() + u.len()) + 20) as u64);
        assert_eq!(got(&d, 834), e);
        assert_eq!(got(&d, 835), u);
        assert_eq!(got(&d, 848), [expected_sign(&e, &u)]);
        assert!(got(&d, 849).is_empty());
        for (port, w) in &guards {
            assert_eq!(got(&d, *port), *w);
        }
        assert!(d.regs[24] && d.regs[36]);
    }
}

#[test]
fn repeated_sign_calls_require_consuming_the_previous_one_bit_cell() {
    let sign = pair_sign_call().unwrap();
    let clear = Cmd::Atom(Atom::Pop {
        stack: 848,
        value: 0,
        present: 1,
    });
    let p = Cmd::seq(sign, clear).compiled(834, 848).unwrap();
    let mut d = p.initial([]);
    for (e, u) in [
        ([true, false, true], [true, false, false]),
        ([true, true, true], [false, true, false]),
        ([false, false, false], [false, false, false]),
    ] {
        put(&mut d, 834, &e);
        put(&mut d, 835, &u);
        d.pc = Some(p.entry());
        run(&p, &mut d);
        assert_eq!(d.regs[0], expected_sign(&e, &u));
        assert!(d.regs[1]);
        assert!(got(&d, 848).is_empty());
        assert!(got(&d, 849).is_empty());
    }
}

#[test]
fn source_pair_sign_refuses_insufficient_step_budget_without_halting() {
    let p = pair_sign_call_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 834, &[true, false, true, true]);
    put(&mut d, 835, &[true, false, false, true]);
    assert!(matches!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 100_000
            }
        ),
        Err(Error::Capacity(_)),
    ));
    assert!(d.pc.is_some());
    assert!(got(&d, 848).is_empty());
    // Input is not a completed result while the program counter is still live.
}

#[test]
fn source_tuple_dfs_calls_pair_sign_only_as_a_test_stage_not_numeric_commit() {
    // The pair controller consumes its own inputs and invokes a finite sign
    // instruction table. This verifies staging, not signed accumulation.
    let visit = Cmd::seq(
        pair_sign_call().unwrap(),
        Cmd::Atom(Atom::Pop {
            stack: 848,
            value: 0,
            present: 1,
        }),
    );
    let program = query_pairs_command(visit).compiled(832, 833).unwrap();
    let mut d = program.initial([true, true]);
    put(&mut d, 833, &[true, true]); // n=2, J=2 => E=0 or singleton
    run(&program, &mut d);
    assert!(got(&d, 848).is_empty());
    assert!(got(&d, 849).is_empty());
    assert!(got(&d, 834).is_empty());
    assert!(got(&d, 835).is_empty());
}
