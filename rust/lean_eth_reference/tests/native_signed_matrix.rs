//! Independent semantics and exact trace gates for the source-defined
//! signed incidence readout, including full matrix frames and physical ABI.
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_matrix_preprocess::{
    emit_frame_command, pre_matrix_program, pre_reverse_program, pre_row_program,
    read_word_command, signature_shift_and_clear_program, signature_shift_program,
};
use lean_eth_reference::native_signed_arithmetic::{
    padding_le_program, saturating_subtract_program, shift_program, subtract_le_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, bits: &[bool]) {
    d.stacks[i] = VecDeque::from(bits.to_vec());
}
fn take<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(
    p: &Program<R, S>,
    d: &mut Config<R, S>,
    step_limit: u64,
) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: step_limit,
            max_stack_bits: 150_000,
        },
    )
    .unwrap()
    .instructions
}
fn little(mut n: usize) -> Vec<bool> {
    let mut bits = vec![];
    while n > 0 {
        bits.push(n % 2 == 1);
        n >>= 1;
    }
    bits
}
fn bits_fixed(n: usize, len: usize) -> Vec<bool> {
    (0..len)
        .map(|i| i < usize::BITS as usize && ((n >> i) & 1 == 1))
        .collect()
}
fn value(bits: &[bool]) -> usize {
    bits.iter()
        .enumerate()
        .map(|(i, b)| {
            if *b {
                1usize.checked_shl(i as u32).unwrap_or(0)
            } else {
                0
            }
        })
        .sum()
}
fn frame(word: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for b in word {
        out.extend([true, *b]);
    }
    out.push(false);
    out
}
fn words(ws: &[Vec<bool>]) -> Vec<bool> {
    ws.iter().flat_map(|w| frame(w)).collect()
}
fn signed(row: &[(Vec<bool>, Vec<bool>)]) -> Vec<bool> {
    row.iter()
        .flat_map(|(p, n)| [frame(p), frame(n)].concat())
        .collect()
}
fn matrix(rows: &[Vec<(Vec<bool>, Vec<bool>)>]) -> Vec<bool> {
    words(&rows.iter().map(|r| signed(r)).collect::<Vec<_>>())
}
fn read_frame(stream: &mut &[bool]) -> Vec<bool> {
    let mut r = Vec::new();
    loop {
        let Some((&head, tail)) = stream.split_first() else {
            panic!("unterminated frame")
        };
        *stream = tail;
        if !head {
            return r;
        }
        let Some((&payload, tail)) = stream.split_first() else {
            panic!("truncated escaped frame")
        };
        *stream = tail;
        r.push(payload);
    }
}
fn read_words(mut input: &[bool]) -> Vec<Vec<bool>> {
    let mut out = Vec::new();
    while !input.is_empty() {
        out.push(read_frame(&mut input));
    }
    out
}
fn read_matrix(input: &[bool]) -> Vec<Vec<Vec<bool>>> {
    read_words(input)
        .iter()
        .map(|row| read_words(row))
        .collect()
}
#[test]
fn little_endian_padding_and_subtraction_are_literal_linked_finite_tables() {
    let pad = padding_le_program().unwrap();
    let sub = subtract_le_program().unwrap();
    assert_eq!(pad.code().len(), 9);
    assert_eq!(sub.code().len(), 17);
    for width in 0..=6 {
        for n in 0..=width {
            let inp = bits_fixed((1usize << n).saturating_sub(1) ^ 0x53, n);
            let shape = vec![true; width];
            let mut c = pad.initial(shape.clone());
            put(&mut c, 1, &inp);
            let steps = run(&pad, &mut c, 20_000);
            assert_eq!(steps, 7 * width as u64 + 6);
            assert_eq!(take(&c, 0), [inp.clone(), vec![false; width - n]].concat());
            assert!(take(&c, 1).is_empty() && take(&c, 2).is_empty());
        }
        for a in 0..(1 << width) {
            for b in 0..(1 << width) {
                let mut c = sub.initial(bits_fixed(a, width));
                put(&mut c, 1, &bits_fixed(b, width));
                c.regs[0] = false;
                let steps = run(&sub, &mut c, 20_000);
                assert_eq!(steps, 15 * width as u64 + 6);
                let expected = (a.wrapping_sub(b)) & ((1 << width) - 1);
                assert_eq!(value(&take(&c, 0)), expected, "width={width} a={a} b={b}");
                assert_eq!(c.regs[0], a < b, "borrow width={width} a={a} b={b}");
            }
        }
    }
}
#[test]
fn saturating_subtraction_preserves_operands_and_clears_all_registers() {
    let p = saturating_subtract_program().unwrap();
    for w in 0..=30 {
        for n in 0..=30 {
            let mut d = p.initial(little(w));
            put(&mut d, 1, &little(n));
            d.regs = [true; 8];
            run(&p, &mut d, 120_000);
            assert_eq!(value(&take(&d, 2)), w.saturating_sub(n), "W={w} N={n}");
            assert_eq!(take(&d, 0), little(w));
            assert_eq!(take(&d, 1), little(n));
            assert_eq!(d.regs, [false; 8]);
            for at in [3, 4, 5, 6, 7] {
                assert!(take(&d, at).is_empty(), "dirty {at}");
            }
        }
    }
}
#[test]
fn complete_shift_is_source_instruction_arithmetic_not_host_integer_subtraction() {
    let p = shift_program().unwrap();
    for w in 0..=15 {
        for n in 0..=15 {
            for positive in [0, 1, 2, 3, 8, 15] {
                let mut d = p.initial(little(w));
                put(&mut d, 1, &little(n));
                put(&mut d, 8, &little(positive));
                let stats = run(&p, &mut d, 180_000);
                assert!(stats > 25);
                assert_eq!(
                    value(&take(&d, 9)),
                    w.saturating_sub(n) + positive,
                    "W={w} N={n} P={positive}"
                );
                for (at, expected) in [(0, w), (1, n), (8, positive)] {
                    assert_eq!(value(&take(&d, at)), expected);
                }
                for at in [3, 4, 5, 6, 7] {
                    assert!(take(&d, at).is_empty(), "scratch {at}");
                }
            }
        }
    }
}
#[test]
fn paid_framed_word_reader_and_emitter_are_inverses() {
    let read = read_word_command::<14>(10, 8, 12)
        .unwrap()
        .compiled(10, 8)
        .unwrap();
    let emit = emit_frame_command::<14>(8, 11, 12)
        .unwrap()
        .compiled(8, 11)
        .unwrap();
    for len in 0..=12 {
        for seed in 0..=8 {
            let word = bits_fixed(seed * 3 + 1, len);
            let suffix = vec![false, true, true];
            let mut a = read.initial([frame(&word), suffix.clone()].concat());
            put(&mut a, 10, &[frame(&word), suffix.clone()].concat());
            let ticks = run(&read, &mut a, 20_000);
            assert_eq!(ticks, 9 * len as u64 + 8);
            assert_eq!(take(&a, 8), word);
            assert_eq!(take(&a, 10), suffix);
            let mut b = emit.initial([]);
            put(&mut b, 8, &word);
            let ticks = run(&emit, &mut b, 20_000);
            assert_eq!(ticks, 8 * len as u64 + 9);
            assert_eq!(take(&b, 11), frame(&word));
            assert!(take(&b, 8).is_empty());
            assert!(take(&b, 12).is_empty());
        }
    }
}
#[test]
fn physical_order_repair_reverses_frames_and_matches_lean_cost() {
    let p = pre_reverse_program().unwrap();
    for count in 0..=7 {
        for seed in 0..=5 {
            let records = (0..count)
                .map(|i| bits_fixed((i + 1) * 17 + seed, i % 5))
                .collect::<Vec<_>>();
            let mut d = p.initial(words(&records));
            let ticks = run(&p, &mut d, 350_000);
            let expected = records.iter().map(|r| 17 * r.len() + 17).sum::<usize>() + 3;
            assert_eq!(ticks, expected as u64);
            assert_eq!(
                read_words(&take(&d, 3)),
                records.into_iter().rev().collect::<Vec<_>>()
            );
            for at in [0, 1, 2] {
                assert!(take(&d, at).is_empty());
            }
        }
    }
}
#[test]
fn full_signed_row_preprocessor_preserves_coefficient_order() {
    let p = pre_row_program().unwrap();
    for w in [0, 1, 3, 7, 15] {
        for len in 0..=5 {
            for seed in 0..=5 {
                let row = (0..len)
                    .map(|i| (little((i * 3 + seed) % 24), little((i * 5 + seed) % 20)))
                    .collect::<Vec<_>>();
                let mut d = p.initial([]);
                put(&mut d, 0, &little(w));
                put(&mut d, 10, &signed(&row));
                run(&p, &mut d, 2_000_000);
                let observed = read_words(&take(&d, 11));
                assert_eq!(observed.len(), row.len());
                for ((pos, neg), coeff) in row.iter().zip(&observed) {
                    assert_eq!(value(coeff), w.saturating_sub(value(neg)) + value(pos));
                    assert!(coeff.len() <= little(w).len() + pos.len() + neg.len() + 1);
                }
                for i in 1..14 {
                    if i != 11 {
                        assert!(take(&d, i).is_empty(), "row scratch {i}");
                    }
                }
            }
        }
    }
}
#[test]
fn full_signed_matrix_preprocessor_preserves_both_row_and_coefficient_order() {
    let p = pre_matrix_program().unwrap();
    for h in 0..=4 {
        for width in [0, 3, 10] {
            for seed in 0..=6 {
                let data = (0..h)
                    .map(|row| {
                        (0..row % 4 + 1)
                            .map(|col| {
                                let pos = (row * 7 + col * 2 + seed) % 25;
                                let neg = (row * 3 + col + seed) % 17;
                                (little(pos), little(neg))
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                let mut d = p.initial([]);
                put(&mut d, 0, &little(width));
                put(&mut d, 14, &matrix(&data));
                run(&p, &mut d, 4_000_000);
                let got = read_matrix(&take(&d, 15));
                assert_eq!(got.len(), data.len());
                for (row, out) in data.iter().zip(&got) {
                    assert_eq!(out.len(), row.len());
                    for ((pos, neg), word) in row.iter().zip(out) {
                        assert_eq!(value(word), width.saturating_sub(value(neg)) + value(pos));
                    }
                }
                for i in 1..17 {
                    if i != 15 {
                        assert!(take(&d, i).is_empty(), "matrix scratch {i}");
                    }
                }
            }
        }
    }
}
#[test]
fn signature_shift_uses_correct_physical_bank_and_preserves_master_stacks() {
    let p = signature_shift_program().unwrap();
    let data = vec![
        vec![(little(2), little(0)), (little(0), little(2))],
        vec![(little(4), little(1)), (little(3), little(7))],
    ];
    let input = matrix(&data);
    let mut d = p.initial([]);
    put(&mut d, 141, &little(11));
    put(&mut d, 669, &input);
    for (at, word) in [
        (128, vec![true; 3]),
        (640, vec![true, false, true]),
        (710, vec![false, true]),
        (711, vec![true, true]),
    ] {
        put(&mut d, at, &word);
    }
    put(&mut d, 359, &[true, true, false]);
    put(&mut d, 659, &[true]);
    run(&p, &mut d, 6_000_000);
    let rows = read_matrix(&take(&d, 668));
    assert_eq!(
        rows.iter()
            .map(|r| r.iter().map(|x| value(x)).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        vec![vec![13, 9], vec![14, 7]]
    );
    assert_eq!(
        take(&d, 669),
        input,
        "shift preserves raw matrix until caller clears it"
    );
    assert_eq!(take(&d, 141), little(11));
    for (at, word) in [
        (128, vec![true; 3]),
        (640, vec![true, false, true]),
        (710, vec![false, true]),
        (711, vec![true, true]),
    ] {
        assert_eq!(take(&d, at), word);
    }
    for at in 340..357 {
        assert!(take(&d, at).is_empty(), "uncleared stage port {at}");
    }
    assert!(take(&d, 659).is_empty());
}
#[test]
fn signature_shift_clear_consumes_raw_matrix_only_after_readout() {
    let p = signature_shift_and_clear_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 141, &little(8));
    put(&mut d, 669, &matrix(&[vec![(little(5), little(3))]]));
    run(&p, &mut d, 5_000_000);
    assert!(take(&d, 669).is_empty());
    assert_eq!(value(&read_matrix(&take(&d, 668))[0][0]), 10);
}
#[test]
fn machine_resources_refuse_before_reporting_false_halt() {
    let p = signature_shift_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 141, &little(15));
    put(&mut d, 669, &matrix(&[vec![(little(4), little(2))]]));
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 40,
                max_stack_bits: 1_000,
            },
        )
        .unwrap_err();
    assert!(err.to_string().contains("capacity refusal"));
}
