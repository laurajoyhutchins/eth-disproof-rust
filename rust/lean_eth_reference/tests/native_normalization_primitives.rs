//! Independent test-only oracles; production behavior is finite BitProgram.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, RunLimits};
use lean_eth_reference::native_normalization_primitives::{
    clause_filter_reverse_program, clean_literals_reverse_program, emit_if_selected_command,
    emit_record_program, literal_dedup_reverse_program, negate_literal_program,
    reverse_records_program, tautology_filter_reverse_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, xs: &[bool]) {
    d.stacks[i] = VecDeque::from(xs.to_vec());
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn bits(n: usize, k: usize) -> Vec<bool> {
    (0..n).map(|i| (k >> i) & 1 == 1).collect()
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut out = vec![];
    for b in xs {
        out.extend([true, *b]);
    }
    out.push(false);
    out
}
fn encoded(xs: &[Vec<bool>]) -> Vec<bool> {
    let mut a = vec![];
    for x in xs {
        a.push(true);
        a.extend(frame(x));
    }
    a.push(false);
    a
}

#[test]
fn literal_polarity_exact_source_table_and_cost() {
    let p = negate_literal_program().unwrap();
    assert_eq!(p.code().len(), 15);
    assert_eq!(p.code()[14], Instr::Halt);
    for n in 0..=256 {
        let mut input = vec![true; n];
        input.extend([false, false, true]);
        let mut d = p.initial(input);
        put(&mut d, 1, &[true, false]);
        let s = p.run(&mut d, RunLimits::default()).unwrap();
        let mut expected = vec![true; n ^ 1];
        expected.extend([false, true, false]);
        assert_eq!(get(&d, 1), expected);
        assert_eq!(get(&d, 0), vec![false, true]);
        assert_eq!(d.regs, [false, false]);
        assert_eq!(s.instructions, (8 * (n / 2) + 10 + n % 2) as u64);
    }
}

#[test]
fn physical_frame_writer_and_selected_discard_branches() {
    let writer = emit_record_program().unwrap();
    assert_eq!(writer.code().len(), 17);
    assert_eq!(writer.code()[6], Instr::Goto { next: 7 });
    let branch = emit_if_selected_command().unwrap().compiled(3, 2).unwrap();
    for n in 0..=8 {
        for k in 0..1usize << n {
            let word = bits(n, k);
            let mut d = writer.initial(word.iter().rev().copied());
            put(&mut d, 2, &[false]);
            assert_eq!(
                writer
                    .run(&mut d, RunLimits::default())
                    .unwrap()
                    .instructions,
                (5 * n + 7) as u64
            );
            let mut expected = vec![true];
            expected.extend(frame(&word));
            expected.push(false);
            assert_eq!(get(&d, 2), expected);
            for selected in [false, true] {
                let mut x = branch.initial(word.iter().rev().copied());
                put(&mut x, 2, &[false]);
                x.regs[2] = selected;
                let s = branch.run(&mut x, RunLimits::default()).unwrap();
                let expected = if selected {
                    expected.clone()
                } else {
                    vec![false]
                };
                assert_eq!(get(&x, 2), expected);
                assert!(x.stacks[3].is_empty());
                assert_eq!(x.regs, [false, true, false]);
                assert_eq!(
                    s.instructions,
                    (if selected { 5 * n + 11 } else { 2 * n + 7 } + 1) as u64
                );
            }
        }
    }
}

#[test]
fn real_record_reversal_preserves_payloads_and_unread_suffix() {
    let p = reverse_records_program().unwrap();
    let cases = vec![
        vec![],
        vec![vec![]],
        vec![vec![true]],
        vec![
            vec![true, false],
            vec![],
            vec![false, true],
            vec![true, false],
        ],
    ];
    for records in cases {
        let mut input = encoded(&records);
        input.extend([true, false, true]);
        let mut d = p.initial(input);
        put(&mut d, 2, &[false]);
        put(&mut d, 1, &[true, false]);
        let steps = p.run(&mut d, RunLimits::default()).unwrap();
        let expected = records.into_iter().rev().collect::<Vec<_>>();
        assert_eq!(get(&d, 2), encoded(&expected));
        assert_eq!(get(&d, 0), vec![true, false, true]);
        assert_eq!(get(&d, 1), vec![true, false]);
        assert!(d.stacks[3].is_empty());
        assert_eq!(d.regs, [false, true, false]);
        assert!(steps.instructions > 0);
    }
}

#[test]
fn all_source_lifts_preserve_neighboring_registers_and_stacks() {
    let input = encoded(&[vec![true], vec![], vec![false, true]]);
    let expected = encoded(&[vec![false, true], vec![], vec![true]]);
    let p = literal_dedup_reverse_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 2, &input);
    put(&mut d, 0, &[false]);
    put(&mut d, 3, &[true, false]);
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 0), expected);
    assert_eq!(get(&d, 3), vec![true, false]);
    let p = clean_literals_reverse_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 2, &input);
    put(&mut d, 0, &[false]);
    put(&mut d, 6, &[true]);
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 0), expected);
    assert_eq!(get(&d, 6), vec![true]);
    let p = tautology_filter_reverse_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 2, &input);
    put(&mut d, 0, &[false]);
    put(&mut d, 5, &[true]);
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 0), expected);
    assert_eq!(get(&d, 5), vec![true]);
    let p = clause_filter_reverse_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 14, &input);
    put(&mut d, 13, &[false]);
    put(&mut d, 8, &[true]);
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 13), expected);
    assert_eq!(get(&d, 8), vec![true]);
}

#[test]
fn exhausted_budget_never_returns_completed_reversal() {
    let p = reverse_records_program().unwrap();
    let mut d = p.initial(encoded(&[vec![true; 20], vec![false; 20]]));
    put(&mut d, 2, &[false]);
    let e = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 10_000,
            },
        )
        .unwrap_err();
    assert!(matches!(e, Error::Capacity(_)));
    assert!(d.pc.is_some());
}
