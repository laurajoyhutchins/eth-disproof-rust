use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_flatten::{
    final_flatten_command, flat_program, flat_row_command, h_flat_program, integer_cache_program,
    normalize_component_program, normalize_program, padding_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(s: &mut Config<R, S>, p: usize, bits: &[bool]) {
    s.stacks[p] = VecDeque::from(bits.to_vec());
}
fn get<const R: usize, const S: usize>(s: &Config<R, S>, p: usize) -> Vec<bool> {
    s.stacks[p].iter().copied().collect()
}
fn word(n: u64) -> Vec<bool> {
    if n == 0 {
        return vec![];
    }
    (0..64 - n.leading_zeros())
        .map(|i| ((n >> i) & 1) != 0)
        .collect()
}
fn val(bits: &[bool]) -> u64 {
    bits.iter()
        .enumerate()
        .map(|(i, b)| if *b { 1u64 << i } else { 0 })
        .sum()
}
fn frame_rev(bits: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for &b in bits.iter().rev() {
        out.extend([true, b]);
    }
    out.push(false);
    out
}
fn encode(pairs: &[(Vec<bool>, Vec<bool>)]) -> Vec<bool> {
    let mut out = Vec::new();
    for (positive, negative) in pairs {
        out.push(true);
        out.extend(frame_rev(positive));
        out.extend(frame_rev(negative));
    }
    out.push(false);
    out
}
fn rows(xs: &[u64]) -> Vec<(Vec<bool>, Vec<bool>)> {
    xs.iter().map(|&n| (word(n), vec![])).collect()
}
fn run<const R: usize, const S: usize>(
    p: &lean_eth_reference::bit_program::Program<R, S>,
    cfg: &mut Config<R, S>,
) -> u64 {
    p.run(
        cfg,
        RunLimits {
            max_steps: 12_000_000,
            max_stack_bits: 1_000_000,
        },
    )
    .unwrap()
    .instructions
}
fn expected(a: usize, r: usize) -> Vec<u64> {
    let mut xs = vec![1u64; r];
    for _ in 0..a {
        let mut prev = 0;
        for x in &mut xs {
            prev = prev * 2 + *x;
            *x = prev;
        }
    }
    xs
}
fn flatten(xs: &[Vec<bool>], width: usize) -> Vec<bool> {
    xs.iter()
        .flat_map(|w| {
            w.iter()
                .take(width)
                .copied()
                .chain(std::iter::repeat(false))
                .take(width)
                .collect::<Vec<_>>()
        })
        .collect()
}

#[test]
fn padding_is_exact_five_label_lean_program() {
    let p = padding_program().unwrap();
    assert_eq!(p.code().len(), 5);
    assert_eq!(p.entry(), 0);
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 2);
}
#[test]
fn normalization_is_exact_twelve_label_link_with_real_prefix_clear_and_reverse() {
    let p = normalize_program().unwrap();
    assert_eq!(p.code().len(), 12);
    for width in 0usize..=7 {
        for n in 0usize..=11 {
            let input = (0..n).map(|i| i % 3 == 1).collect::<Vec<_>>();
            let mut d = p.initial(vec![true; width]);
            put(&mut d, 0, &input);
            put(&mut d, 5, &[true, false, true]);
            let steps = run(&p, &mut d);
            assert_eq!(steps, (9 + 7 * width + 2 * n.saturating_sub(width)) as u64);
            assert_eq!(get(&d, 0), flatten(&[input], width));
            assert!(get(&d, 2).is_empty() && get(&d, 7).is_empty());
            assert_eq!(get(&d, 5), vec![true, false, true]);
        }
    }
}
#[test]
fn normalize_component_preserves_width_and_reverses_into_existing_buffer() {
    let p = normalize_component_program().unwrap();
    for width in 0..=6 {
        for n in 0..=9 {
            let input = (0..n).map(|i| i % 2 == 0).collect::<Vec<_>>();
            let buffer = vec![true, false, true, true];
            let mut d = p.initial(input.clone());
            put(&mut d, 1, &vec![false; width]);
            put(&mut d, 2, &buffer);
            run(&p, &mut d);
            let mut expect = flatten(&[input], width);
            expect.reverse();
            expect.extend(buffer);
            assert!(get(&d, 0).is_empty());
            assert_eq!(get(&d, 1).len(), width);
            assert_eq!(get(&d, 2), expect);
            for i in 3..9 {
                assert!(get(&d, i).is_empty(), "scratch {i}");
            }
        }
    }
}
#[test]
fn flatten_real_encoded_rows_with_both_signed_components() {
    let p = flat_program().unwrap();
    for width in 0usize..=7 {
        for n in 0..=5 {
            let pairs = (0..n)
                .map(|i| (word((i * i * 7 + 3) as u64), word((i * 5 + 1) as u64)))
                .collect::<Vec<_>>();
            let mut d = p.initial(encode(&pairs));
            put(&mut d, 18, &vec![true; width]);
            put(&mut d, 12, &[false, true, true]);
            run(&p, &mut d);
            let positives = pairs.iter().map(|x| x.0.clone()).collect::<Vec<_>>();
            let negatives = pairs.iter().map(|x| x.1.clone()).collect::<Vec<_>>();
            assert_eq!(get(&d, 0), flatten(&positives, width), "w={width},n={n}");
            assert_eq!(get(&d, 1), flatten(&negatives, width), "w={width},n={n}");
            assert!(get(&d, 15).is_empty() && get(&d, 16).is_empty() && get(&d, 17).is_empty());
            assert_eq!(get(&d, 18), vec![true; width]);
            assert_eq!(get(&d, 12), vec![false, true, true]);
        }
    }
}
#[test]
fn flatten_output_is_in_ascending_row_order_not_reversed() {
    let p = flat_program().unwrap();
    let row = rows(&[1, 2, 7, 19]);
    let mut d = p.initial(encode(&row));
    put(&mut d, 18, &[true, true, true, true, true, true]);
    run(&p, &mut d);
    for (index, &val_expected) in [1u64, 2, 7, 19].iter().enumerate() {
        assert_eq!(val(&get(&d, 0)[index * 6..(index + 1) * 6]), val_expected);
    }
}
#[test]
fn h_flat_program_runs_full_composed_builder_and_parser() {
    let p = h_flat_program().unwrap();
    for a in 0..=4 {
        for r in 0..=5 {
            let width = 1 + 2 * a * r;
            let mut d = p.initial(vec![true; a]);
            put(&mut d, 18, &vec![false; r]);
            put(&mut d, 19, &vec![true; width]);
            put(&mut d, 12, &[true, true, false]);
            run(&p, &mut d);
            let got = get(&d, 0);
            assert_eq!(got.len(), r * width);
            assert_eq!(get(&d, 1), vec![false; r * width]);
            for (i, &x) in expected(a, r).iter().enumerate() {
                assert_eq!(
                    val(&got[i * width..(i + 1) * width]),
                    x,
                    "a={a},r={r},i={i}"
                );
            }
            for i in [15, 16, 17, 18] {
                assert!(get(&d, i).is_empty(), "a={a} r={r} scratch={i}");
            }
            assert_eq!(get(&d, 19), vec![true; width]);
            assert_eq!(get(&d, 12), vec![true, true, false]);
        }
    }
}
#[test]
fn integer_cache_produces_actual_coefficients_denominator_and_retained_width() {
    let p = integer_cache_program().unwrap();
    for a in 0..=3 {
        for r in 0..=5 {
            let width = 1 + 2 * a * r;
            let a_bits = vec![false; a];
            let r_bits = vec![true; r];
            let w_bits = vec![false; width];
            let mut d = p.initial(vec![]);
            put(&mut d, 20, &a_bits);
            put(&mut d, 21, &r_bits);
            put(&mut d, 22, &w_bits);
            put(&mut d, 11, &[true, false, true, true]);
            run(&p, &mut d);
            let got = get(&d, 0);
            assert_eq!(got.len(), r * width);
            assert_eq!(get(&d, 1), vec![false; r * width]);
            for (i, x) in expected(a, r).iter().enumerate() {
                assert_eq!(
                    val(&got[i * width..(i + 1) * width]),
                    *x,
                    "a={a},r={r},i={i}"
                );
            }
            assert_eq!(
                get(&d, 2),
                [vec![false; r.saturating_sub(1)], vec![true]].concat()
            );
            assert_eq!(get(&d, 19), w_bits);
            assert_eq!(get(&d, 20), a_bits);
            assert_eq!(get(&d, 21), r_bits);
            assert_eq!(get(&d, 22), w_bits);
            assert_eq!(get(&d, 11), vec![true, false, true, true]);
            for i in [3, 15, 16, 17, 18, 23] {
                assert!(get(&d, i).is_empty(), "stack {i}:a={a},r={r}");
            }
        }
    }
}
#[test]
fn control_sizes_are_independent_of_width_and_count() {
    let p = integer_cache_program().unwrap();
    let q = h_flat_program().unwrap();
    assert!(p.code().len() > q.code().len());
    assert_eq!(
        final_flatten_command().unwrap().size().unwrap() + 1,
        final_flatten_command()
            .unwrap()
            .compiled(15, 0)
            .unwrap()
            .code()
            .len()
    );
    assert_eq!(
        flat_row_command().unwrap().size().unwrap() + 1,
        flat_row_command()
            .unwrap()
            .compiled(15, 16)
            .unwrap()
            .code()
            .len()
    );
}
#[test]
fn insufficient_machine_budget_fails_closed() {
    let p = integer_cache_program().unwrap();
    let mut d = p.initial(vec![]);
    put(&mut d, 20, &[true; 6]);
    put(&mut d, 21, &[true; 7]);
    put(&mut d, 22, &[true; 100]);
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 1_000_000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, lean_eth_reference::Error::Capacity(_)));
}
