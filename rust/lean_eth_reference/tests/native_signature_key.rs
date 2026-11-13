//! Source-machine regression for `BucketProgramSignature` and the positive
//! counter normalizer. A *test* row callback deliberately emits a constant
//! finite word, so these tests do not claim that source row arithmetic runs.

use lean_eth_reference::bit_program::{Atom, Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_high::clear_program;
use lean_eth_reference::native_signature_key::{
    attained_signature_program, canonical_row_normalize_call, counter_normalize_program,
    prepare_log_program, rescan_key_call, signature_program, trim_program,
};

fn write<const R: usize, const S: usize>(state: &mut Config<R, S>, port: usize, bits: &[bool]) {
    state.stacks[port] = bits.iter().copied().collect();
}
fn word<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, state: &mut Config<R, S>) -> u64 {
    state.pc = Some(p.entry());
    let result = p
        .run(
            state,
            RunLimits {
                max_steps: 2_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
    assert!(state.pc.is_none());
    result.instructions
}
fn bits(value: usize, width: usize) -> Vec<bool> {
    (0..width).map(|i| (value & (1 << i)) != 0).collect()
}
fn frame(bits: &[bool]) -> Vec<bool> {
    let mut out = Vec::with_capacity(2 * bits.len() + 1);
    for bit in bits {
        out.push(true);
        out.push(*bit);
    }
    out.push(false);
    out
}
fn words(records: &[Vec<bool>]) -> Vec<bool> {
    records.iter().flat_map(|r| frame(r)).collect()
}
fn matrix(rows: &[Vec<Vec<bool>>]) -> Vec<bool> {
    let raw: Vec<_> = rows.iter().map(|r| words(r)).collect();
    words(&raw)
}
fn toy_row_program() -> Program<8, 12> {
    // The pinned inner row source has not been ported. This is a controlled,
    // visibly distinct *finite* callback used to test the outer syntax.
    // It cleans local row 9 and assignment 10, retaining seed [true] on 2.
    Cmd::seq(
        Cmd::Call(clear_program(9, 0, 1).unwrap()),
        Cmd::Call(clear_program(10, 0, 1).unwrap()),
    )
    .compiled(9, 2)
    .unwrap()
}

#[test]
fn prepare_log_has_the_pinned_ten_labels_and_trims_high_zeros() {
    let p = prepare_log_program().unwrap();
    assert_eq!(p.code().len(), 10);
    assert_eq!((p.input_stack(), p.output_stack()), (0, 1));
    for width in 0..=11 {
        for v in 0..(1usize << width) {
            let x = bits(v, width);
            let mut s = p.initial(x);
            run(&p, &mut s);
            let want = if v == 0 {
                vec![]
            } else {
                let highest = (usize::BITS - v.leading_zeros()) as usize - 1;
                bits(v, highest).into_iter().rev().collect()
            };
            assert_eq!(word(&s, 1), want, "v={v}, width={width}");
            assert!(word(&s, 0).is_empty());
        }
    }
}

#[test]
fn trim_source_program_keeps_reversed_tail_below_first_true() {
    let p = trim_program().unwrap();
    assert_eq!(p.code().len(), 6);
    for width in 0..=9 {
        for v in 0..(1usize << width) {
            let x = bits(v, width);
            let want: Vec<_> = x.iter().skip_while(|&&b| !b).skip(1).copied().collect();
            let mut s = p.initial([]);
            write(&mut s, 1, &x);
            run(&p, &mut s);
            assert_eq!(word(&s, 1), want, "input={x:?}");
        }
    }
}

#[test]
fn normalizer_uses_twenty_labels_and_preserves_all_positive_values() {
    let p = counter_normalize_program().unwrap();
    assert_eq!(p.code().len(), 20);
    for width in 1..=11 {
        for value in 1..(1usize << width) {
            let mut s = p.initial(bits(value, width));
            s.regs = [true, false, true];
            let steps = run(&p, &mut s);
            let canonical_len = (usize::BITS - value.leading_zeros()) as usize;
            assert_eq!(
                word(&s, 0),
                bits(value, canonical_len),
                "value={value} width={width}"
            );
            assert_eq!(s.regs, [false; 3]);
            assert!(word(&s, 1).is_empty());
            assert!(word(&s, 2).is_empty());
            assert!(
                steps <= 9 * width as u64 + 21,
                "source bound, steps={steps}"
            );
        }
    }
}

#[test]
fn row_normalizer_uses_unchanged_low_register_indices() {
    let p = canonical_row_normalize_call()
        .unwrap()
        .compiled(2, 2)
        .unwrap();
    for (input, want) in [
        (vec![true, false, false, false], vec![true]),
        (
            vec![false, false, true, false, false],
            vec![false, false, true],
        ),
        (vec![true, true], vec![true, true]),
    ] {
        let mut s = p.initial([]);
        write(&mut s, 2, &input);
        s.regs[3] = true;
        s.regs[7] = true;
        write(&mut s, 11, &[true, false, true]);
        run(&p, &mut s);
        assert_eq!(word(&s, 2), want);
        assert!(word(&s, 3).is_empty());
        assert!(word(&s, 4).is_empty());
        assert!(s.regs[3]);
        assert!(s.regs[7]);
        assert_eq!(word(&s, 11), [true, false, true]);
    }
}

#[test]
fn signature_scanner_visits_each_framed_row_once_in_source_order() {
    let toy = toy_row_program();
    let p = signature_program(&toy).unwrap();
    let rows = [
        vec![vec![true, false], vec![true]],
        vec![],
        vec![vec![], vec![false, false, true]],
    ];
    for n in 0..=rows.len() {
        let prefix = &rows[..n];
        let raw = matrix(prefix);
        let mut s = p.initial(raw.clone());
        write(&mut s, 12, &[true, false, true]);
        write(&mut s, 0, &[false, false]);
        write(&mut s, 14, &[true, false]); // already accumulated key suffix
        run(&p, &mut s);
        let expected: Vec<bool> = std::iter::repeat_n(frame(&[true]), n)
            .flatten()
            .chain([true, false])
            .collect();
        assert_eq!(word(&s, 14), expected, "n={n}");
        assert!(word(&s, 13).is_empty());
        assert_eq!(word(&s, 12), [true, false, true]);
        assert_eq!(word(&s, 0), [false, false]);
        for i in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] {
            assert!(word(&s, i).is_empty(), "uncleared scratch {i}");
        }
    }
}

/// Finite testing callback: emit one bit recording whether a row has any
/// framed coefficients. This deliberately does NOT evaluate row arithmetic.
fn toy_row_presence_program() -> Program<8, 12> {
    Cmd::seq(
        Cmd::Atom(Atom::Peek {
            stack: 9,
            value: 2,
            present: 3,
        }),
        Cmd::seq(
            Cmd::Call(clear_program(2, 0, 1).unwrap()),
            Cmd::seq(
                Cmd::Call(clear_program(9, 0, 1).unwrap()),
                Cmd::seq(
                    Cmd::Call(clear_program(10, 0, 1).unwrap()),
                    Cmd::Atom(Atom::Push { stack: 2, src: 3 }),
                ),
            ),
        ),
    )
    .compiled(9, 2)
    .unwrap()
}

#[test]
fn signatures_are_emitted_in_reverse_row_order_with_distinct_key_values() {
    let rows = vec![
        vec![vec![false, true]], // present: true
        vec![vec![true]],        // present: true
        vec![],                  // present: false
    ];
    let p = signature_program(&toy_row_presence_program()).unwrap();
    let mut s = p.initial(matrix(&rows));
    write(&mut s, 12, &[true, false, true]);
    run(&p, &mut s);
    assert_eq!(
        word(&s, 14),
        [frame(&[false]), frame(&[true]), frame(&[true])].concat()
    );
    assert_eq!(word(&s, 12), [true, false, true]);
    assert!(word(&s, 13).is_empty());
}

#[test]
fn full_attained_signature_scanner_preserves_original_matrix() {
    let toy = toy_row_program();
    let p = attained_signature_program(&toy).unwrap();
    for rows in [
        vec![],
        vec![vec![vec![false], vec![]]],
        vec![vec![], vec![vec![true, false]]],
    ] {
        let raw = matrix(&rows);
        let mut s = p.initial([true, false, true]);
        write(&mut s, 15, &raw);
        write(&mut s, 12, &[true, false]);
        run(&p, &mut s);
        assert_eq!(word(&s, 15), raw);
        assert_eq!(word(&s, 12), [true, false]);
        assert!(word(&s, 13).is_empty());
        let expected: Vec<bool> = std::iter::repeat_n(frame(&[true]), rows.len())
            .flatten()
            .collect();
        assert_eq!(word(&s, 14), expected);
    }
}

#[test]
fn rescan_key_call_uses_source_identity_ports_and_cannot_modify_caller_frame() {
    let toy = toy_row_program();
    let p = rescan_key_call(&toy).unwrap().compiled(12, 14).unwrap();
    let rows = vec![vec![], vec![vec![true, false]]];
    let raw = matrix(&rows);
    let mut s = p.initial([true]);
    write(&mut s, 15, &raw);
    write(&mut s, 12, &[true, false]);
    write(&mut s, 22, &[false]);
    s.regs[15] = true;
    run(&p, &mut s);
    assert_eq!(word(&s, 15), raw);
    assert_eq!(word(&s, 14), [frame(&[true]), frame(&[true])].concat());
    assert_eq!(word(&s, 22), [false]);
    assert!(s.regs[15]);
}

#[test]
fn scanner_refuses_insufficient_instruction_budget_without_faking_halt() {
    let p = attained_signature_program(&toy_row_program()).unwrap();
    let raw = matrix(&[vec![vec![false]], vec![vec![true]]]);
    let mut s = p.initial([]);
    write(&mut s, 15, &raw);
    let e = p.run(
        &mut s,
        RunLimits {
            max_steps: 5,
            max_stack_bits: 1000,
        },
    );
    assert!(matches!(e, Err(lean_eth_reference::Error::Capacity(_))));
    assert!(s.pc.is_some());
}

#[test]
fn row_callback_injection_rejects_invalid_port_mappings() {
    let toy = toy_row_program();
    let e = toy.lift::<8, 15>(
        [0, 1, 2, 3, 4, 5, 6, 7],
        [0, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    );
    assert!(matches!(e, Err(lean_eth_reference::Error::Invalid(_))));
}

#[test]
fn normalizer_is_literal_finite_machine_not_a_host_arithmetic_operator() {
    let p = counter_normalize_program().unwrap();
    assert!(
        p.code()
            .iter()
            .any(|i| matches!(i, lean_eth_reference::bit_program::Instr::Pop { .. }))
    );
    assert!(
        p.code()
            .iter()
            .any(|i| matches!(i, lean_eth_reference::bit_program::Instr::Push { .. }))
    );
    assert!(
        !p.code()
            .iter()
            .any(|i| matches!(i, lean_eth_reference::bit_program::Instr::And { .. }))
    );
    let direct = Cmd::<8, 12>::Atom(Atom::Set {
        dst: 3,
        value: true,
    })
    .compiled(0, 0)
    .unwrap();
    assert_eq!(direct.code().len(), 2);
}
