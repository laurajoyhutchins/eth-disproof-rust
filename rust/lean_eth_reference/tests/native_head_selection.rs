//! Source-defined TDD for indexed head selection from actual bit-stack machines.
//! `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_head_selection::{
    color_prefix_program, color_program, head_full_program, head_test_program, heads_program,
    heads_support_program, read_program, type_bit_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, bits: &[bool]) {
    d.stacks[i] = VecDeque::from(bits.to_vec());
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: 5_000_000,
            max_stack_bits: 100_000,
        },
    )
    .expect("source machine should halt")
    .instructions
}
fn bits(seed: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| seed & (1 << (i % 10)) != 0).collect()
}
fn one_hot(width: usize, g: usize) -> Vec<bool> {
    (0..width).map(|i| i == g).collect()
}
fn indices(js: &[usize]) -> Vec<bool> {
    let mut result = Vec::new();
    for &j in js {
        result.push(true);
        result.extend(vec![true; 2 * j]);
        result.push(false);
    }
    result.push(false);
    result
}

#[test]
fn indexed_read_has_exact_38_labels_and_source_steps() {
    let p = read_program::<5>(0, 1).unwrap();
    assert_eq!(p.code().len(), 38);
    let mut cases = 0;
    for width in 0..=5usize {
        for count in 1..=5usize {
            for j in 0..count {
                for seed in 0..8usize {
                    let source = bits(seed * 29 + j * 7 + count, width * count);
                    let mut d = p.initial(source.clone());
                    put(&mut d, 1, &[true, false]);
                    put(&mut d, 2, &vec![true; j]);
                    put(&mut d, 3, &vec![true; width]);
                    d.regs[3] = true;
                    let t = run(&p, &mut d);
                    assert_eq!(get(&d, 0), source);
                    assert_eq!(
                        get(&d, 1),
                        [
                            source[j * width..(j + 1) * width].to_vec(),
                            vec![true, false]
                        ]
                        .concat()
                    );
                    for i in [2, 4, 5, 6, 7] {
                        assert!(get(&d, i).is_empty(), "work {i}");
                    }
                    assert_eq!(t, (j * (14 * width + 10) + 15 * width + 16) as u64);
                    assert!(d.regs[3]);
                    cases += 1;
                }
            }
        }
    }
    assert!(cases > 500);
}

#[test]
fn five_label_color_prefix_stops_at_first_true_and_retains_suffix() {
    let p = color_prefix_program().unwrap();
    assert_eq!(p.code().len(), 5);
    for g in 0..=12usize {
        let mut d = p.initial([vec![false; g], vec![true, false, true, true]].concat());
        put(&mut d, 1, &[false]);
        let t = run(&p, &mut d);
        assert_eq!(t, (4 * g + 3) as u64);
        assert_eq!(get(&d, 0), vec![false, true, true]);
        assert_eq!(get(&d, 1), [vec![true; g], vec![false]].concat());
    }
}

#[test]
fn complete_color_decoder_counts_actual_one_hot_word_and_charges_steps() {
    let p = color_program().unwrap();
    let labels = p.code().len();
    for width in 1..=7usize {
        for count in 1..=4usize {
            for j in 0..count {
                for g in 0..width {
                    let rows: Vec<Vec<bool>> = (0..count)
                        .map(|i| one_hot(width, (i + g) % width))
                        .collect();
                    let source: Vec<bool> = rows.iter().flatten().copied().collect();
                    let mut d = p.initial(source.clone());
                    put(&mut d, 1, &vec![true; j]);
                    put(&mut d, 2, &vec![true; width]);
                    let t = run(&p, &mut d);
                    let expected_g = (j + g) % width;
                    assert_eq!(get(&d, 3), vec![true; expected_g]);
                    assert_eq!(get(&d, 0), source);
                    assert_eq!(get(&d, 1), vec![true; j]);
                    assert_eq!(get(&d, 2), vec![true; width]);
                    for i in 4..=9 {
                        assert!(get(&d, i).is_empty(), "uncleared port {i}");
                    }
                    assert_eq!(
                        t,
                        (j * (14 * width + 17)
                            + 15 * width
                            + 21
                            + 4 * expected_g
                            + 3
                            + 2 * (width - expected_g - 1)
                            + 3
                            + 1) as u64
                    );
                    assert_eq!(p.code().len(), labels);
                }
            }
        }
    }
}

#[test]
fn seven_label_indexed_bit_reader_handles_out_of_range() {
    let p = type_bit_program().unwrap();
    assert_eq!(p.code().len(), 7);
    for len in 0..=9usize {
        for index in 0..=11usize {
            for seed in 0..12 {
                let bits = bits(seed * 19 + len, len);
                let mut d = p.initial(Vec::<bool>::new());
                put(&mut d, 0, &vec![true; index]);
                put(&mut d, 1, &bits);
                d.regs[2] = true;
                run(&p, &mut d);
                assert_eq!(
                    d.regs,
                    [false, false, bits.get(index).copied().unwrap_or(false)],
                    "len={len} index={index} seed={seed} bits={bits:?}"
                );
                assert!(get(&d, 0).is_empty() && get(&d, 1).is_empty());
            }
        }
    }
}

#[test]
fn actual_head_test_reads_low_and_head_flag_without_touching_persistent_masters() {
    let p = head_test_program().unwrap();
    for width in 1..=5usize {
        for count in 1..=4usize {
            for j in 0..count {
                for z in 0..=width {
                    let rows: Vec<Vec<bool>> =
                        (0..count).map(|i| bits(i * 3 + width + 2, width)).collect();
                    let flat: Vec<bool> = rows.iter().flatten().copied().collect();
                    let low = bits(23 + z, count);
                    let mut d = p.initial(Vec::<bool>::new());
                    put(&mut d, 31, &low);
                    put(&mut d, 32, &vec![true; z]);
                    put(&mut d, 33, &flat);
                    put(&mut d, 38, &vec![true; width]);
                    put(&mut d, 39, &vec![true; j]);
                    put(&mut d, 45, &[true, false]);
                    let t = run(&p, &mut d);
                    assert!(t > 0);
                    assert_eq!(d.regs[6], low[j]);
                    assert_eq!(d.regs[4], rows[j].get(z).copied().unwrap_or(false));
                    assert_eq!(get(&d, 31), low);
                    assert_eq!(get(&d, 33), flat);
                    assert_eq!(get(&d, 45), vec![true, false]);
                    for i in [12, 13, 16, 17, 18, 19, 20, 21, 34, 36, 42] {
                        assert!(get(&d, i).is_empty(), "uncleared {i}");
                    }
                }
            }
        }
    }
}

#[test]
fn full_head_selector_emits_increasing_original_ids_and_preserves_tail_rows() {
    let p = head_full_program().unwrap();
    let labels = p.code().len();
    for width in 1..=5usize {
        for count in 0..=6usize {
            for seed in 0..18usize {
                let rows: Vec<Vec<bool>> = (0..count + 2)
                    .map(|i| bits(13 * seed + i * 7 + width, width))
                    .collect();
                let flat: Vec<bool> = rows.iter().flatten().copied().collect();
                let low = bits(seed * 7 + 11, count + 2);
                let z = seed % (width + 2);
                let chosen: Vec<usize> = (0..count)
                    .filter(|&i| low[i] && rows[i].get(z).copied().unwrap_or(false))
                    .collect();
                let mut d = p.initial(Vec::<bool>::new());
                put(&mut d, 30, &vec![true; count]);
                put(&mut d, 31, &low);
                put(&mut d, 32, &vec![true; z]);
                put(&mut d, 33, &flat);
                put(&mut d, 38, &vec![true; width]);
                d.regs[8] = true;
                run(&p, &mut d);
                assert_eq!(
                    get(&d, 0),
                    indices(&chosen),
                    "width={width} n={count} seed={seed}"
                );
                assert_eq!(get(&d, 1), vec![false; chosen.len()]);
                assert_eq!(get(&d, 33), flat);
                assert_eq!(get(&d, 31), low);
                assert_eq!(d.regs, [false; 16]);
                for i in [12, 13, 16, 17, 18, 19, 20, 21, 34, 36, 39, 42] {
                    assert!(get(&d, i).is_empty(), "uncleared work port {i}");
                }
                assert_eq!(p.code().len(), labels);
            }
        }
    }
}

#[test]
fn paid_head_selection_and_support_connect_in_original_16x768_work_bank() {
    let head = heads_program().unwrap();
    let combined = heads_support_program().unwrap();
    assert!(head.code().len() < combined.code().len());
    for n in 0..=7usize {
        for width in 1..=4usize {
            let rows: Vec<Vec<bool>> = (0..n + 1).map(|i| bits(i * 7 + n * 3, width)).collect();
            let flat: Vec<bool> = rows.iter().flatten().copied().collect();
            let low = bits(211 + n * 17, n + 1);
            let z = (n + width) % width;
            let chosen: Vec<usize> = (0..n).filter(|&i| low[i] && rows[i][z]).collect();
            let mut d = combined.initial(Vec::<bool>::new());
            put(&mut d, 128, &vec![true; n]);
            put(&mut d, 134, &low);
            put(&mut d, 649, &vec![true; z]);
            put(&mut d, 133, &flat);
            put(&mut d, 132, &vec![true; width]);
            put(&mut d, 670, &[true, false, true]);
            put(&mut d, 650, &[true, false]);
            put(&mut d, 651, &[true, true]);
            put(&mut d, 659, &[false, true]);
            put(&mut d, 342, &[true, false, true]);
            put(&mut d, 98, &[false, true, false]);
            run(&combined, &mut d);
            let mut expected = vec![false; n];
            for &j in &chosen {
                expected[j] = true;
            }
            assert_eq!(get(&d, 650), indices(&chosen));
            assert_eq!(get(&d, 651), vec![false; chosen.len()]);
            assert_eq!(get(&d, 652), vec![true; chosen.len()]);
            assert_eq!(get(&d, 670), expected);
            assert_eq!(get(&d, 133), flat);
            assert_eq!(get(&d, 134), low);
            assert_eq!(get(&d, 98), vec![false, true, false]);
            assert!(get(&d, 659).is_empty());
            for i in 340..=403 {
                assert!(get(&d, i).is_empty(), "dirty work stack {i}");
            }
            assert_eq!(d.pc, None);
        }
    }
}

#[test]
fn bounded_head_selector_refuses_incomplete_execution() {
    let p = heads_support_program().unwrap();
    let mut d = p.initial(Vec::<bool>::new());
    put(&mut d, 128, &[true; 3]);
    put(&mut d, 134, &[true; 3]);
    put(&mut d, 133, &[true; 12]);
    put(&mut d, 132, &[true; 4]);
    assert!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: 20,
                max_stack_bits: 10000
            }
        )
        .is_err()
    );
}
