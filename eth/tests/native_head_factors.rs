//! Source-derived finite machine tests for factor-relative ID selection and
//! the complete staged `LeafHeadSetupProgram.prepareHead` composition.
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_head_factors::{
    factor_emit_command, factor_full_program, factor_test_program, factors_program,
    prepare_head_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, at: usize, bits: &[bool]) {
    c.stacks[at] = VecDeque::from(bits.to_vec());
}
fn get<const R: usize, const S: usize>(c: &Config<R, S>, at: usize) -> Vec<bool> {
    c.stacks[at].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, c: &mut Config<R, S>) -> u64 {
    p.run(
        c,
        RunLimits {
            max_steps: 8_000_000,
            max_stack_bits: 200_000,
        },
    )
    .expect("source-defined program should halt")
    .instructions
}
fn bits(seed: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (seed >> (i % 12)) & 1 != 0).collect()
}
fn encode_nat(n: usize) -> Vec<bool> {
    [vec![true; n], vec![false]].concat()
}
fn frame(bits: &[bool]) -> Vec<bool> {
    let mut r = Vec::new();
    for &bit in bits {
        r.extend([true, bit]);
    }
    r.push(false);
    r
}
fn factor_indices(ids: &[usize]) -> Vec<bool> {
    let mut result = Vec::new();
    for &id in ids {
        result.push(true);
        result.extend(frame(&encode_nat(id)));
    }
    result.push(false);
    result
}
fn head_indices(ids: &[usize]) -> Vec<bool> {
    let mut result = Vec::new();
    for &id in ids {
        result.push(true);
        result.extend(vec![true; 2 * id]);
        result.push(false);
    }
    result.push(false);
    result
}
fn type_bit_cost(index: usize, bits_len: usize) -> usize {
    if index == 0 {
        2 * bits_len.saturating_sub(1) + 6
    } else {
        3 + type_bit_cost(index - 1, bits_len.saturating_sub(1))
    }
}

#[test]
fn factor_test_uses_paid_offset_and_reads_only_factor_bit() {
    let p = factor_test_program().unwrap();
    for width in 0..=5usize {
        for a in 0..=3usize {
            for j in 0..=3usize {
                for z in 0..=width + 1 {
                    let rows: Vec<_> = (0..a + j + 2)
                        .map(|i| bits(i * 13 + width * 17 + z, width))
                        .collect();
                    let flat: Vec<_> = rows.iter().flatten().copied().collect();
                    let mut c = p.initial(Vec::<bool>::new());
                    put(&mut c, 31, &vec![true; a]);
                    put(&mut c, 32, &vec![true; z]);
                    put(&mut c, 33, &flat);
                    put(&mut c, 38, &vec![true; width]);
                    put(&mut c, 39, &vec![true; j]);
                    put(&mut c, 45, &[true, false, false]);
                    c.regs[8] = true;
                    let steps = run(&p, &mut c);
                    let look = (a + j) * (14 * width + 17) + 15 * width + 22;
                    let cost = look + 9 * (a + j) + 7 * z + 18 + type_bit_cost(z, width) + 1;
                    assert_eq!(steps, cost as u64, "A={a} j={j} z={z} width={width}");
                    assert_eq!(c.regs[4], rows[a + j].get(z).copied().unwrap_or(false));
                    assert!(c.regs[8]);
                    assert_eq!(get(&c, 31), vec![true; a]);
                    assert_eq!(get(&c, 33), flat);
                    assert_eq!(get(&c, 45), vec![true, false, false]);
                    for i in [12, 16, 17, 18, 19, 20, 21, 34, 36, 40, 42] {
                        assert!(get(&c, i).is_empty(), "uncleared work {i}");
                    }
                }
            }
        }
    }
}

#[test]
fn factor_emit_is_precisely_nat_framed_and_uses_source_cost() {
    let p = factor_emit_command().unwrap().compiled(39, 0).unwrap();
    for j in 0..=18 {
        let mut c = p.initial(vec![true; j]);
        put(&mut c, 0, &[false, true]);
        put(&mut c, 1, &[true, false]);
        let steps = run(&p, &mut c);
        assert_eq!(
            get(&c, 0),
            [
                factor_indices(&[j])[..factor_indices(&[j]).len() - 1].to_vec(),
                vec![false, true]
            ]
            .concat()
        );
        assert_eq!(get(&c, 1), vec![false, true, false]);
        assert_eq!(steps, (12 * j + 22) as u64);
        assert!(get(&c, 34).is_empty());
        assert!(get(&c, 42).is_empty());
    }
}

#[test]
fn full_factor_scan_uses_relative_ids_not_absolute_offset() {
    let p = factor_full_program().unwrap();
    assert_eq!(p.code().len(), factor_full_program().unwrap().code().len());
    for width in 1..=5usize {
        for a in 0..=4usize {
            for n in 0..=5usize {
                for seed in 0..10usize {
                    let rows: Vec<Vec<bool>> = (0..a + n + 2)
                        .map(|i| bits(i * 7 + seed * 23 + width, width))
                        .collect();
                    let flat: Vec<_> = rows.iter().flatten().copied().collect();
                    let z = seed % (width + 2);
                    let ids: Vec<_> = (0..n)
                        .filter(|&j| rows[a + j].get(z).copied().unwrap_or(false))
                        .collect();
                    let mut c = p.initial(Vec::<bool>::new());
                    put(&mut c, 30, &vec![true; n]);
                    put(&mut c, 31, &vec![true; a]);
                    put(&mut c, 32, &vec![true; z]);
                    put(&mut c, 33, &flat);
                    put(&mut c, 38, &vec![true; width]);
                    c.regs[7] = true;
                    run(&p, &mut c);
                    assert_eq!(
                        get(&c, 0),
                        factor_indices(&ids),
                        "A={a} n={n} z={z} width={width} seed={seed}"
                    );
                    assert_eq!(get(&c, 1), vec![false; ids.len()]);
                    assert_eq!(get(&c, 31), vec![true; a]);
                    assert_eq!(get(&c, 33), flat);
                    assert_eq!(c.regs, [false; 16]);
                    for i in [12, 16, 17, 18, 19, 20, 21, 34, 36, 39, 40, 42] {
                        assert!(get(&c, i).is_empty(), "work {i}");
                    }
                }
            }
        }
    }
}

#[test]
fn isolated_factor_stage_preserves_head_outputs_and_cleans_dirty_bank() {
    let p = factors_program().unwrap();
    for a in 0..=4usize {
        for n in 0..=4usize {
            let width = 3usize;
            let z = 1usize;
            let rows: Vec<Vec<bool>> = (0..a + n + 1).map(|i| bits(i * 5 + 7, width)).collect();
            let ids: Vec<_> = (0..n).filter(|&j| rows[a + j][z]).collect();
            let mut c = p.initial(Vec::<bool>::new());
            put(&mut c, 128, &vec![true; a]);
            put(&mut c, 129, &vec![true; n]);
            put(&mut c, 132, &vec![true; width]);
            put(
                &mut c,
                133,
                &rows.iter().flatten().copied().collect::<Vec<_>>(),
            );
            put(&mut c, 649, &vec![true; z]);
            put(&mut c, 650, &[true, false, true]);
            put(&mut c, 670, &[false, true, false]);
            put(&mut c, 671, &[false, false, false]);
            put(&mut c, 659, &[true, false]);
            put(&mut c, 342, &[true, false, true]);
            put(&mut c, 92, &[true, false]);
            run(&p, &mut c);
            assert_eq!(get(&c, 671), factor_indices(&ids));
            assert_eq!(get(&c, 650), vec![true, false, true]);
            assert_eq!(get(&c, 670), vec![false, true, false]);
            assert_eq!(get(&c, 92), vec![true, false]);
            assert!(get(&c, 659).is_empty());
            for i in 340..404 {
                assert!(get(&c, i).is_empty(), "dirty stage stack {i}");
            }
        }
    }
}

#[test]
fn complete_prepare_head_produces_all_four_source_descriptors() {
    let p = prepare_head_program().unwrap();
    for a in 0..=4usize {
        for n in 0..=4usize {
            for width in 1..=4usize {
                let z = width - 1;
                let rows: Vec<Vec<bool>> = (0..a + n + 1)
                    .map(|i| bits(17 * i + 5 * a + 7 * n + width, width))
                    .collect();
                let low = bits(17 * a + 29 * n + width, a + n + 1);
                let head_ids: Vec<_> = (0..a).filter(|&j| low[j] && rows[j][z]).collect();
                let factor_ids: Vec<_> = (0..n).filter(|&j| rows[a + j][z]).collect();
                let mut c = p.initial(Vec::<bool>::new());
                put(&mut c, 128, &vec![true; a]);
                put(&mut c, 129, &vec![true; n]);
                put(&mut c, 132, &vec![true; width]);
                put(
                    &mut c,
                    133,
                    &rows.iter().flatten().copied().collect::<Vec<_>>(),
                );
                put(&mut c, 134, &low);
                put(&mut c, 649, &vec![true; z]);
                put(&mut c, 659, &[false, true]);
                put(&mut c, 340, &[true, false]);
                put(&mut c, 71, &[false, true]);
                run(&p, &mut c);
                let mut mask = vec![false; a];
                for &j in &head_ids {
                    mask[j] = true;
                }
                assert_eq!(get(&c, 650), head_indices(&head_ids));
                assert_eq!(get(&c, 651), vec![false; head_ids.len()]);
                assert_eq!(get(&c, 652), vec![true; head_ids.len()]);
                assert_eq!(get(&c, 670), mask);
                assert_eq!(get(&c, 671), factor_indices(&factor_ids));
                assert_eq!(get(&c, 71), vec![false, true]);
                assert_eq!(get(&c, 134), low);
                assert!(get(&c, 659).is_empty());
                for i in 340..404 {
                    assert!(get(&c, i).is_empty(), "dirty final work {i}");
                }
            }
        }
    }
}

#[test]
fn incomplete_factor_execution_is_refused_not_accepted() {
    let p = prepare_head_program().unwrap();
    let mut c = p.initial(Vec::<bool>::new());
    put(&mut c, 128, &[true; 4]);
    put(&mut c, 129, &[true; 3]);
    put(&mut c, 132, &[true; 2]);
    put(&mut c, 133, &[true; 14]);
    put(&mut c, 134, &[true; 4]);
    assert!(
        p.run(
            &mut c,
            RunLimits {
                max_steps: 12,
                max_stack_bits: 200_000
            }
        )
        .is_err()
    );
}
