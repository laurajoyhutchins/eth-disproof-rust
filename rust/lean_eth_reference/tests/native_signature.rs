//! Exact source-key semantics, instruction counts, and composed signed-matrix
//! -> unsigned shifted coefficients -> assignment signature regression.
//! Mathematical expectations are independent host-language oracles in tests.
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_matrix_preprocess::pre_matrix_program;
use lean_eth_reference::native_signature::{
    canonical_row_program, choice_add_program, dot_step_command, normalize_program,
    prepare_log_program, row_program, signature_program, signed_matrix_signature_program,
};
use std::collections::VecDeque;

fn set<const R: usize, const S: usize>(d: &mut Config<R, S>, p: usize, b: &[bool]) {
    d.stacks[p] = VecDeque::from(b.to_vec());
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, p: usize) -> Vec<bool> {
    d.stacks[p].iter().copied().collect()
}
fn execute<const R: usize, const S: usize>(program: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    program
        .run(
            d,
            RunLimits {
                max_steps: 5_000_000,
                max_stack_bits: 300_000,
            },
        )
        .unwrap()
        .instructions
}
fn bits(mut n: usize) -> Vec<bool> {
    let mut x = vec![];
    while n > 0 {
        x.push(n & 1 == 1);
        n >>= 1;
    }
    x
}
fn bitvalue(x: &[bool]) -> usize {
    x.iter()
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
fn frame(bits: &[bool]) -> Vec<bool> {
    let mut w = vec![];
    for b in bits {
        w.extend([true, *b]);
    }
    w.push(false);
    w
}
fn words(records: &[Vec<bool>]) -> Vec<bool> {
    records.iter().flat_map(|r| frame(r)).collect()
}
fn signed(row: &[(usize, usize)]) -> Vec<bool> {
    row.iter()
        .flat_map(|(p, n)| [frame(&bits(*p)), frame(&bits(*n))].concat())
        .collect()
}
fn encode_signed_matrix(matrix: &[Vec<(usize, usize)>]) -> Vec<bool> {
    words(&matrix.iter().map(|r| signed(r)).collect::<Vec<_>>())
}
fn read_frame(stream: &mut &[bool]) -> Vec<bool> {
    let mut w = vec![];
    loop {
        let Some((a, tail)) = stream.split_first() else {
            panic!("missing frame terminator")
        };
        *stream = tail;
        if !*a {
            return w;
        }
        let Some((b, tail)) = stream.split_first() else {
            panic!("bad escaping")
        };
        w.push(*b);
        *stream = tail;
    }
}
fn decode_words(mut w: &[bool]) -> Vec<Vec<bool>> {
    let mut ws = vec![];
    while !w.is_empty() {
        ws.push(read_frame(&mut w));
    }
    ws
}
fn decode_matrix(w: &[bool]) -> Vec<Vec<Vec<bool>>> {
    decode_words(w).iter().map(|r| decode_words(r)).collect()
}

#[test]
fn ten_label_log_preparation_is_literal_and_consumes_most_significant_prefix() {
    let p = prepare_log_program().unwrap();
    assert_eq!(p.code().len(), 10);
    for n in 0..=127 {
        for padding in 0..=5 {
            let input = [bits(n), vec![false; padding]].concat();
            let mut c = p.initial(input);
            execute(&p, &mut c);
            assert!(get(&c, 0).is_empty());
            let high_word = get(&c, 1);
            let want = if n == 0 {
                vec![]
            } else {
                bits(n).into_iter().rev().skip(1).collect()
            };
            assert_eq!(high_word, want, "n={n} padding={padding}");
        }
    }
}
#[test]
fn canonicalizer_preserves_numeric_value_and_is_width_minimal() {
    let p = normalize_program().unwrap();
    for n in 1..=180 {
        for padding in 0..=7 {
            let input = [bits(n), vec![false; padding]].concat();
            let mut c = p.initial(input.clone());
            c.regs = [true; 3];
            let ticks = execute(&p, &mut c);
            assert!(ticks >= 20);
            assert_eq!(get(&c, 0), bits(n), "n={n} padding={padding}");
            assert_eq!(c.regs, [false; 3]);
            for s in [1, 2] {
                assert!(get(&c, s).is_empty());
            }
        }
    }
}
#[test]
fn conditional_bit_stack_adder_switches_between_constant_and_coefficient() {
    let p = choice_add_program().unwrap();
    for w in [0, 1, 4, 8, 17] {
        for coeff in [0, 2, 5, 18, 31] {
            for accumulator in [0, 1, 8, 27] {
                for selector in [false, true] {
                    let mut c = p.initial([]);
                    set(&mut c, 0, &bits(w));
                    set(&mut c, 1, &bits(coeff));
                    set(&mut c, 2, &bits(accumulator));
                    c.regs[0] = selector;
                    execute(&p, &mut c);
                    assert_eq!(
                        bitvalue(&get(&c, 3)),
                        accumulator + if selector { coeff } else { w }
                    );
                    assert_eq!(get(&c, 0), bits(w));
                    assert_eq!(get(&c, 1), bits(coeff));
                    assert_eq!(get(&c, 2), bits(accumulator));
                    for s in 4..=8 {
                        assert!(get(&c, s).is_empty());
                    }
                }
            }
        }
    }
}
#[test]
fn one_dot_step_consumes_framed_word_and_bit_and_preserves_constant() {
    let p = dot_step_command().unwrap().compiled(9, 2).unwrap();
    for w in [0, 3, 8] {
        for coeff in [0, 1, 7] {
            for acc in [0, 4, 9] {
                for selector in [false, true] {
                    let mut c = p.initial([]);
                    set(&mut c, 0, &bits(w));
                    set(&mut c, 9, &words(&[bits(coeff), bits(123)]));
                    set(&mut c, 10, &[selector, false]);
                    set(&mut c, 2, &bits(acc));
                    execute(&p, &mut c);
                    assert_eq!(
                        bitvalue(&get(&c, 2)),
                        acc + if selector { coeff } else { w }
                    );
                    assert_eq!(get(&c, 9), words(&[bits(123)]));
                    assert_eq!(get(&c, 10), vec![false]);
                    for s in 1..=8 {
                        if s != 2 {
                            assert!(get(&c, s).is_empty(), "dirty {s}");
                        }
                    }
                    assert!(get(&c, 11).is_empty());
                }
            }
        }
    }
}
#[test]
fn source_row_scanner_has_correct_conditional_baseline_and_cleans_buffers() {
    let p = row_program().unwrap();
    for w in [0, 1, 5, 17] {
        for coeffs in [vec![], vec![0], vec![2, 8], vec![0, 3, 9]] {
            let n = coeffs.len();
            for mask in 0..(1 << n) {
                let assignment = (0..n).map(|i| mask & (1 << i) != 0).collect::<Vec<_>>();
                let acc = 4usize;
                let mut c = p.initial([]);
                set(&mut c, 0, &bits(w));
                set(
                    &mut c,
                    9,
                    &words(&coeffs.iter().copied().map(bits).collect::<Vec<_>>()),
                );
                set(&mut c, 10, &assignment);
                set(&mut c, 2, &bits(acc));
                execute(&p, &mut c);
                let want = acc
                    + coeffs
                        .iter()
                        .enumerate()
                        .map(|(i, v)| if assignment[i] { *v } else { w })
                        .sum::<usize>();
                assert_eq!(
                    bitvalue(&get(&c, 2)),
                    want,
                    "w={w} coeffs={coeffs:?} mask={mask}"
                );
                for q in [1, 3, 4, 5, 6, 7, 8, 9, 10, 11] {
                    assert!(get(&c, q).is_empty(), "dirty {q}");
                }
            }
        }
    }
}
#[test]
fn canonical_row_adds_a_positive_seed_even_for_empty_rows() {
    let p = canonical_row_program().unwrap();
    for w in [0, 1, 9] {
        for coeffs in [vec![], vec![0], vec![1, 5, 0], vec![2, 8]] {
            for mask in 0..(1 << coeffs.len()) {
                let assignment = (0..coeffs.len())
                    .map(|i| mask & (1 << i) != 0)
                    .collect::<Vec<_>>();
                let mut c = p.initial([]);
                set(&mut c, 0, &bits(w));
                set(
                    &mut c,
                    9,
                    &words(&coeffs.iter().copied().map(bits).collect::<Vec<_>>()),
                );
                set(&mut c, 10, &assignment);
                set(&mut c, 2, &[true]);
                execute(&p, &mut c);
                let want = 1 + coeffs
                    .iter()
                    .enumerate()
                    .map(|(i, v)| if assignment[i] { *v } else { w })
                    .sum::<usize>();
                assert_eq!(
                    get(&c, 2),
                    bits(want),
                    "w={w} coeffs={coeffs:?} mask={mask}"
                );
            }
        }
    }
}
#[test]
fn complete_signature_scanner_keys_all_rows_in_reverse_framed_order() {
    let p = signature_program().unwrap();
    let matrices = [
        vec![],
        vec![vec![]],
        vec![vec![0, 3], vec![1, 2]],
        vec![vec![4, 0, 9], vec![1, 1, 1], vec![8, 2, 5]],
    ];
    for rows in matrices {
        for w in [0, 1, 3, 9] {
            let n = rows.first().map_or(0, Vec::len);
            for assignment in 0..(1 << n) {
                let bits_mask = (0..n)
                    .map(|i| assignment & (1 << i) != 0)
                    .collect::<Vec<_>>();
                let row_bytes = words(
                    &rows
                        .iter()
                        .map(|r| words(&r.iter().copied().map(bits).collect::<Vec<_>>()))
                        .collect::<Vec<_>>(),
                );
                let mut c = p.initial(row_bytes.clone());
                set(&mut c, 0, &bits(w));
                set(&mut c, 12, &bits_mask);
                set(&mut c, 13, &row_bytes);
                execute(&p, &mut c);
                let got = decode_words(&get(&c, 14));
                let expected = rows
                    .iter()
                    .map(|r| {
                        bits(
                            1 + r
                                .iter()
                                .enumerate()
                                .map(|(i, v)| if bits_mask[i] { *v } else { w })
                                .sum::<usize>(),
                        )
                    })
                    .rev()
                    .collect::<Vec<_>>();
                assert_eq!(got, expected, "W={w} rows={rows:?} bits={bits_mask:?}");
                assert_eq!(get(&c, 0), bits(w));
                assert_eq!(get(&c, 12), bits_mask);
                assert!(get(&c, 13).is_empty());
                for k in 1..12 {
                    assert!(get(&c, k).is_empty(), "dirty {k}");
                }
            }
        }
    }
}
#[test]
fn signed_matrix_preprocessing_and_signature_composition_agree_with_integer_oracle() {
    let preprocess = pre_matrix_program().unwrap();
    let signature = signature_program().unwrap();
    for matrix in [
        vec![],
        vec![vec![]],
        vec![vec![(1, 0)]],
        vec![vec![(1, 2), (7, 3)], vec![(0, 1), (3, 2)]],
        vec![vec![(12, 3), (0, 9), (2, 1)], vec![(5, 5), (8, 0), (0, 0)]],
    ] {
        let n = matrix.first().map_or(0, Vec::len);
        for w in [9usize, 16, 32] {
            for mask in 0..(1 << n) {
                let assignment = (0..n).map(|i| mask & (1 << i) != 0).collect::<Vec<_>>();
                let mut p = preprocess.initial([]);
                set(&mut p, 0, &bits(w));
                set(&mut p, 14, &encode_signed_matrix(&matrix));
                execute(&preprocess, &mut p);
                let shifted = decode_matrix(&get(&p, 15));
                for (i, row) in matrix.iter().enumerate() {
                    for (j, (plus, minus)) in row.iter().enumerate() {
                        assert_eq!(bitvalue(&shifted[i][j]), w.saturating_sub(*minus) + *plus);
                    }
                }
                let mut s = signature.initial([]);
                set(&mut s, 0, &bits(w));
                set(&mut s, 12, &assignment);
                set(&mut s, 13, &get(&p, 15));
                execute(&signature, &mut s);
                let keys = decode_words(&get(&s, 14));
                let expected = matrix
                    .iter()
                    .map(|row| {
                        let sum = row
                            .iter()
                            .enumerate()
                            .map(|(i, (plus, minus))| {
                                if assignment[i] {
                                    w.saturating_sub(*minus) + *plus
                                } else {
                                    w
                                }
                            })
                            .sum::<usize>();
                        bits(sum + 1)
                    })
                    .rev()
                    .collect::<Vec<_>>();
                assert_eq!(
                    keys, expected,
                    "w={w} matrix={matrix:?} mask={assignment:?}"
                );
            }
        }
    }
}
#[test]
fn finite_machine_rejects_exhausted_step_and_stack_limits() {
    let p = signature_program().unwrap();
    let mut s = p.initial(words(&[words(&[bits(2), bits(4)])]));
    set(&mut s, 0, &bits(7));
    set(&mut s, 12, &[true, false]);
    assert!(
        p.run(
            &mut s,
            RunLimits {
                max_steps: 30,
                max_stack_bits: 100_000
            }
        )
        .is_err()
    );
    let mut s = p.initial(words(&[words(&[bits(2), bits(4)])]));
    set(&mut s, 0, &bits(7));
    set(&mut s, 12, &[true, false]);
    assert!(
        p.run(
            &mut s,
            RunLimits {
                max_steps: 200_000,
                max_stack_bits: 7
            }
        )
        .is_err()
    );
}

#[test]
fn single_machine_composed_signed_matrix_signature_matches_direct_integer_arithmetic() {
    let program = signed_matrix_signature_program().unwrap();
    let matrices = [
        vec![],
        vec![vec![]],
        vec![vec![(7, 3)]],
        vec![vec![(2, 3), (0, 4)], vec![(12, 1), (15, 0)]],
        vec![
            vec![(0, 0), (9, 7), (2, 1)],
            vec![(1, 1), (8, 0), (0, 5)],
            vec![(3, 0), (2, 2), (4, 3)],
        ],
    ];
    for matrix in matrices {
        let columns = matrix.first().map_or(0, Vec::len);
        for w in [8usize, 17] {
            for mask in 0..(1 << columns) {
                let selected = (0..columns)
                    .map(|j| mask & (1 << j) != 0)
                    .collect::<Vec<_>>();
                let raw = encode_signed_matrix(&matrix);
                let mut cfg = program.initial(raw.clone());
                set(&mut cfg, 0, &bits(w));
                set(&mut cfg, 17, &selected);
                execute(&program, &mut cfg);
                let expect = matrix
                    .iter()
                    .map(|row| {
                        let n = 1 + row
                            .iter()
                            .enumerate()
                            .map(|(j, (p, m))| {
                                if selected[j] {
                                    w.saturating_sub(*m) + *p
                                } else {
                                    w
                                }
                            })
                            .sum::<usize>();
                        bits(n)
                    })
                    .rev()
                    .collect::<Vec<_>>();
                assert_eq!(decode_words(&get(&cfg, 18)), expect);
                assert_eq!(get(&cfg, 0), bits(w));
                assert_eq!(get(&cfg, 17), selected);
                assert!(get(&cfg, 14).is_empty());
                let shifted = decode_matrix(&get(&cfg, 15));
                for (i, row) in matrix.iter().enumerate() {
                    for (j, (p, m)) in row.iter().enumerate() {
                        assert_eq!(bitvalue(&shifted[i][j]), w.saturating_sub(*m) + *p);
                    }
                }
                for scratch in 1..=13 {
                    assert!(get(&cfg, scratch).is_empty(), "dirty {scratch}");
                }
                assert!(get(&cfg, 16).is_empty());
            }
        }
    }
}

/// The source's crucial signed-signature relation: on the admissible domain
/// N <= W, two complete machine-produced keys collide iff every row's
/// original signed linear form collides. All 2^h head assignments are tested,
/// with the actual Boolean-stack machine executed for every one of them.
#[test]
fn physical_signature_collision_iff_integer_linear_forms_agree() {
    let program = signed_matrix_signature_program().unwrap();
    let w = 23usize;
    let rows: Vec<Vec<(usize, usize)>> = vec![
        vec![(1, 0), (0, 2), (2, 4), (2, 0), (0, 0), (3, 1)],
        vec![(1, 1), (0, 0), (2, 1), (2, 0), (1, 3), (1, 0)],
        vec![(0, 1), (1, 0), (0, 2), (0, 0), (2, 0), (1, 1)],
        vec![(3, 0), (1, 1), (1, 1), (2, 2), (0, 0), (0, 1)],
    ];
    let signed = encode_signed_matrix(&rows);
    let mut keys = Vec::new();
    let mut linear = Vec::new();
    let mut worst_steps = 0u64;
    let mut worst_peak = 0usize;
    for mask in 0..(1usize << 6) {
        let assignment = (0..6).map(|i| mask & (1 << i) != 0).collect::<Vec<_>>();
        let mut cfg = program.initial(signed.clone());
        set(&mut cfg, 0, &bits(w));
        set(&mut cfg, 17, &assignment);
        let stats = program
            .run(
                &mut cfg,
                RunLimits {
                    max_steps: 6_000_000,
                    max_stack_bits: 400_000,
                },
            )
            .unwrap();
        worst_steps = worst_steps.max(stats.instructions);
        worst_peak = worst_peak.max(stats.peak_stack_bits);
        keys.push(get(&cfg, 18));
        linear.push(
            rows.iter()
                .map(|row| {
                    row.iter()
                        .enumerate()
                        .map(|(i, (p, n))| {
                            if assignment[i] {
                                *p as i64 - *n as i64
                            } else {
                                0
                            }
                        })
                        .sum::<i64>()
                })
                .collect::<Vec<_>>(),
        );
    }
    for x in 0..keys.len() {
        for y in 0..keys.len() {
            assert_eq!(
                keys[x] == keys[y],
                linear[x] == linear[y],
                "assignments {x} and {y}"
            );
        }
    }
    eprintln!(
        "signed signature 4x6: max executed instructions={worst_steps}, peak stack bits={worst_peak}, programs=64"
    );
}
