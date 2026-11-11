//! Independent host predicates appear only in test assertions.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_terminal_classifier::{
    empty_clause_program, ready_program, trivial_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, p: usize, bits: &[bool]) {
    c.stacks[p] = VecDeque::from(bits.to_vec());
}
fn take<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.push(true);
        out.push(*x);
    }
    out.push(false);
    out
}
fn encoded(xs: &[Vec<bool>]) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.push(true);
        out.extend(frame(x));
    }
    out.push(false);
    out
}
fn unary(n: usize) -> Vec<bool> {
    let mut a = vec![true; n];
    a.push(false);
    a
}
fn two_power(n: usize) -> Vec<bool> {
    let mut a = vec![false; n];
    a.push(true);
    a
}

fn records() -> Vec<Vec<Vec<bool>>> {
    vec![
        vec![],
        vec![vec![]],
        vec![vec![false]],
        vec![vec![true]],
        vec![vec![true], vec![]],
        vec![vec![false], vec![false]],
        vec![vec![true], vec![false, true], vec![false]],
        vec![vec![true], vec![false, true], vec![false]],
        vec![vec![false, true], vec![], vec![true]],
    ]
}

#[test]
fn physical_clause_classifier_preserves_full_encoded_body_and_work_stacks() {
    let p = empty_clause_program().unwrap();
    for rs in records() {
        let bits = encoded(&rs);
        let mut c = p.initial(bits.clone());
        c.regs[7] = true;
        c.regs[9] = true;
        let t = p.run(&mut c, RunLimits::default()).unwrap();
        assert_eq!(c.regs[0], rs.contains(&vec![false]), "records={rs:?}");
        assert_eq!(take(&c, 9), bits);
        for i in 0..=4 {
            assert!(c.stacks[i].is_empty(), "work stack {i}");
        }
        assert!(c.stacks[8].is_empty());
        for i in 1..=6 {
            assert!(!c.regs[i]);
        }
        assert!(c.regs[7] && c.regs[9]);
        assert_eq!(c.pc, None);
        assert!(t.instructions > 0);
    }
}

#[test]
fn trivial_classifier_has_distinct_empty_clause_and_empty_formula_flags() {
    let p = trivial_program().unwrap();
    for rs in records() {
        let bits = encoded(&rs);
        let mut c = p.initial(bits.clone());
        p.run(&mut c, RunLimits::default()).unwrap();
        assert_eq!(c.regs[0], rs.contains(&vec![false]));
        assert_eq!(c.regs[7], !rs.is_empty());
        assert_eq!(take(&c, 9), bits);
    }
}

#[test]
fn outer_ready_command_emits_full_terminal_counts_and_rejects_nonterminal_count() {
    let p = ready_program().unwrap();
    for n in 0..=8 {
        for rs in records() {
            let body = encoded(&rs);
            let mut c = p.initial(body.clone());
            put(&mut c, 258, &unary(n));
            put(&mut c, 263, &[true, false, true]);
            put(&mut c, 268, &[false, true]);
            put(&mut c, 269, &[true, true, true, true]);
            put(&mut c, 256, &[true, false, true]);
            put(&mut c, 267, &[false, true, false]);
            put(&mut c, 1216, &[true]);
            c.regs[43] = true;
            c.regs[79] = true;
            let stats = p.run(&mut c, RunLimits::default()).unwrap();
            let expected = if rs.contains(&vec![false]) {
                vec![false]
            } else if rs.is_empty() {
                two_power(n)
            } else {
                vec![]
            };
            assert_eq!(take(&c, 263), expected, "records={rs:?} n={n}");
            assert_eq!(c.regs[0], rs.contains(&vec![false]));
            assert_eq!(c.regs[7], !rs.is_empty());
            assert_eq!(take(&c, 265), body);
            assert_eq!(take(&c, 258), unary(n));
            assert_eq!(take(&c, 256), vec![true, false, true]);
            assert_eq!(take(&c, 267), vec![false, true, false]);
            assert_eq!(take(&c, 1216), vec![true]);
            assert!(c.regs[43] && c.regs[79]);
            assert!(c.stacks[268].is_empty() && c.stacks[269].is_empty());
            for i in 0..=4 {
                assert!(c.stacks[i].is_empty());
            }
            assert_eq!(c.pc, None);
            assert!(stats.instructions > 0);
        }
    }
}

#[test]
fn nonterminal_never_receives_a_fabricated_zero_count() {
    let p = ready_program().unwrap();
    let mut c = p.initial(encoded(&[vec![true]]));
    put(&mut c, 258, &unary(9));
    p.run(&mut c, RunLimits::default()).unwrap();
    assert!(c.stacks[263].is_empty());
    assert!(!c.regs[0]);
    assert!(c.regs[7]);
}

#[test]
fn classifier_budget_refusal_is_not_terminal_success() {
    let p = ready_program().unwrap();
    let mut c = p.initial(encoded(&[vec![true; 15], vec![]]));
    put(&mut c, 258, &unary(15));
    let e = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 6,
                max_stack_bits: 10000,
            },
        )
        .unwrap_err();
    assert!(matches!(e, Error::Capacity(_)));
    assert!(c.pc.is_some());
}
