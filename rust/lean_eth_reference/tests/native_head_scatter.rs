use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_head_scatter::{
    counted_skip_program, counted_transfer_program, replace_command, replace_program,
    scatter_step_command, scatter_step_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, word: &[bool]) {
    d.stacks[i] = VecDeque::from(word.to_vec());
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: 200_000,
            max_stack_bits: 3000,
        },
    )
    .expect("source command must halt")
    .instructions
}
fn bits(mask: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| mask & (1 << i) != 0).collect()
}
fn unary_frame(n: usize) -> Vec<bool> {
    let mut out = vec![true];
    for _ in 0..n {
        out.extend([true, true]);
    }
    out.push(false);
    out.push(false); // terminator of the record list
    out
}

#[test]
fn source_tables_and_aliases() {
    assert_eq!(
        counted_transfer_program::<8, 8>(4, 0, 7, 0, 1)
            .unwrap()
            .code()
            .len(),
        5
    );
    assert_eq!(
        counted_skip_program::<8, 8>(4, 0, 6, 0, 1)
            .unwrap()
            .code()
            .len(),
        7
    );
    let p = replace_program::<8>(0, 1).unwrap();
    assert_eq!(p.code().len(), 44);
    assert_eq!(replace_command::<8>(0, 1).unwrap().size().unwrap() + 1, 44);
    let sp = scatter_step_program().unwrap();
    assert_eq!(
        sp.code().len(),
        scatter_step_command().unwrap().size().unwrap() + 1
    );
    for (counter, src, dst) in [(0, 0, 7), (7, 0, 7), (4, 0, 0)] {
        assert!(counted_transfer_program::<8, 8>(counter, src, dst, 0, 1).is_err());
    }
    assert!(counted_skip_program::<8, 8>(4, 0, 4, 0, 1).is_err());
    assert!(matches!(replace_program::<8>(0, 0), Err(Error::Invalid(_))));
    assert!(matches!(replace_program::<8>(8, 1), Err(Error::Invalid(_))));
}

#[test]
fn replaces_one_flat_word_at_the_given_unary_index_and_charges_exact_steps() {
    let p = replace_program::<8>(0, 1).unwrap();
    let mut cases = 0;
    for width in 0..=5usize {
        for count in 1..=4usize {
            for index in 0..count {
                let total = width * count;
                for seed in 0..20usize {
                    let array = bits(seed.wrapping_mul(17).wrapping_add(5), total);
                    let replacement = bits(seed.wrapping_mul(13).wrapping_add(9), width);
                    let mut d = p.initial(array.clone());
                    put(&mut d, 1, &replacement);
                    put(&mut d, 2, &vec![true; index]);
                    put(&mut d, 3, &vec![false; width]);
                    d.regs[2] = true;
                    d.regs[6] = true;
                    let saved_regs = d.regs;
                    let instructions = run(&p, &mut d);
                    let expected = [
                        array[..index * width].to_vec(),
                        replacement.clone(),
                        array[(index + 1) * width..].to_vec(),
                    ]
                    .concat();
                    assert_eq!(
                        get(&d, 0),
                        expected,
                        "width={width} count={count} index={index}"
                    );
                    assert_eq!(get(&d, 1), replacement);
                    assert_eq!(get(&d, 3), vec![false; width]);
                    for i in [2, 4, 5, 6, 7] {
                        assert!(get(&d, i).is_empty(), "work port {i} not cleared");
                    }
                    for (i, &before) in saved_regs.iter().enumerate().skip(2) {
                        assert_eq!(d.regs[i], before);
                    }
                    assert!(!d.regs[0] && !d.regs[1]);
                    assert_eq!(d.pc, None);
                    let cost = index * (14 * width + 10) + 20 * width + 21;
                    assert_eq!(instructions, cost as u64, "width={width} index={index}");
                    cases += 1;
                }
            }
        }
    }
    assert!(cases >= 1000);
}

#[test]
fn preserves_an_ambient_array_tail_and_opaque_registers() {
    let p = replace_program::<8>(0, 1).unwrap();
    let mut d = p.initial([true, false, false, true, true, true]);
    put(&mut d, 1, &[false, false]);
    put(&mut d, 2, &[true]);
    put(&mut d, 3, &[false, true]);
    d.regs[4] = true;
    d.regs[7] = true;
    run(&p, &mut d);
    assert_eq!(get(&d, 0), vec![true, false, false, false, true, true]);
    assert!(d.regs[4] && d.regs[7]);
}

#[test]
fn head_scatter_step_overwrites_only_the_selected_ambient_bit() {
    let p = scatter_step_program().unwrap();
    for n in 1..=10usize {
        for index in 0..n {
            for bit in [false, true] {
                for seed in 0..12 {
                    let mask = bits(seed * 23 + 17, n);
                    let mut d = p.initial(unary_frame(index));
                    put(&mut d, 0, &mask);
                    put(&mut d, 1, &[bit, true, false]);
                    put(&mut d, 5, &[true]);
                    put(&mut d, 10, &[true, false, true]);
                    put(&mut d, 11, &[false, true]);
                    put(&mut d, 12, &[false]);
                    d.regs[3] = true;
                    d.regs[6] = true;
                    let saved = d.regs;
                    let instructions = run(&p, &mut d);
                    let mut expected = mask;
                    expected[index] = bit;
                    assert_eq!(get(&d, 0), expected, "n={n} j={index}");
                    assert_eq!(get(&d, 1), vec![true, false]);
                    assert_eq!(get(&d, 2), vec![false]);
                    assert_eq!(get(&d, 5), vec![true]);
                    for i in [3, 4, 6, 7, 8, 9] {
                        assert!(get(&d, i).is_empty());
                    }
                    assert_eq!(get(&d, 10), vec![true, false, true]);
                    assert_eq!(get(&d, 11), vec![false, true]);
                    assert_eq!(get(&d, 12), vec![false]);
                    assert_eq!(d.regs[3], saved[3]);
                    assert_eq!(d.regs[6], saved[6]);
                    assert_eq!(d.pc, None);
                    assert_eq!(instructions, (30 * index + 54) as u64);
                }
            }
        }
    }
}

#[test]
fn physical_index_sequence_processes_several_selected_heads() {
    let p = scatter_step_program().unwrap();
    let positions = [3usize, 0, 5, 2];
    let values = [true, false, true, true];
    let mut mask = vec![false; 7];
    let mut queue = Vec::new();
    for &j in &positions {
        queue.push(true);
        for _ in 0..j {
            queue.extend([true, true]);
        }
        queue.push(false);
    }
    queue.push(false);
    for (&j, &value) in positions.iter().zip(values.iter()) {
        let mut d = p.initial(queue);
        put(&mut d, 0, &mask);
        put(&mut d, 1, &[value]);
        put(&mut d, 5, &[true]);
        run(&p, &mut d);
        mask[j] = value;
        assert_eq!(get(&d, 0), mask);
        queue = get(&d, 2);
    }
    assert_eq!(queue, vec![false]);
    assert_eq!(mask, vec![false, false, true, true, false, true, false]);
}

#[test]
fn resource_limits_fail_closed_not_returning_an_incomplete_mask() {
    let p = scatter_step_program().unwrap();
    let mut d = p.initial(unary_frame(12));
    put(&mut d, 0, &[false; 13]);
    put(&mut d, 1, &[true]);
    put(&mut d, 5, &[true]);
    let e = p.run(
        &mut d,
        RunLimits {
            max_steps: 8,
            max_stack_bits: 999,
        },
    );
    assert!(matches!(e, Err(Error::Capacity(_))));
    assert!(
        d.pc.is_some(),
        "a capacity refusal must not be mistaken for halt"
    );
}

fn indices(js: &[usize]) -> Vec<bool> {
    let mut out = Vec::new();
    for &j in js {
        out.push(true);
        out.extend(std::iter::repeat_n(true, j * 2));
        out.push(false);
    }
    out.push(false);
    out
}

#[test]
fn whole_head_scatter_builds_zero_mask_and_restores_inputs() {
    use lean_eth_reference::native_head_scatter::{head_scatter_command, head_scatter_program};
    let p = head_scatter_program().unwrap();
    assert_eq!(
        p.code().len(),
        head_scatter_command().unwrap().size().unwrap() + 1
    );
    assert_eq!(p.code().len(), 98);
    for n in 0..=9usize {
        for seed in 0..70usize {
            let count = if n == 0 { 0 } else { seed % 6 };
            let js: Vec<usize> = (0..count).map(|i| (seed * 3 + 2 * i) % n).collect();
            let bs = bits(seed * 7 + 13, count);
            let ids = indices(&js);
            let mut d = p.initial(ids.clone());
            put(&mut d, 11, &bs);
            put(&mut d, 12, &vec![true; n]);
            d.regs[3] = true;
            d.regs[7] = true;
            let regs = d.regs;
            let cost = run(&p, &mut d);
            let mut expected = vec![false; n];
            for (&j, &bit) in js.iter().zip(&bs) {
                expected[j] = bit;
            }
            assert_eq!(get(&d, 0), expected, "n={n} js={js:?}");
            for i in 1..=9 {
                assert!(d.stacks[i].is_empty(), "port {i} not empty");
            }
            assert_eq!(get(&d, 10), ids);
            assert_eq!(get(&d, 11), bs);
            assert_eq!(get(&d, 12), vec![true; n]);
            assert_eq!(d.regs[3], regs[3]);
            assert_eq!(d.regs[7], regs[7]);
            let init_cost = 7 * ids.len() + 7 * count + 11 * n + 20;
            let scan_cost = 1 + js.iter().map(|j| 30 * j + 55).sum::<usize>();
            assert_eq!(cost, (init_cost + scan_cost + 12) as u64);
        }
    }
}

#[test]
fn whole_scatter_input_encoding_and_halt_are_independent_of_runtime_lengths() {
    use lean_eth_reference::native_head_scatter::head_scatter_program;
    let p = head_scatter_program().unwrap();
    let labels = p.code().len();
    let mut d = p.initial([false]);
    put(&mut d, 12, &[true; 30]);
    let cost = run(&p, &mut d);
    assert_eq!(p.code().len(), labels);
    assert_eq!(get(&d, 0), vec![false; 30]);
    assert_eq!(cost, (7 + 11 * 30 + 20 + 1 + 12) as u64);
    assert_eq!(d.pc, None);
}
