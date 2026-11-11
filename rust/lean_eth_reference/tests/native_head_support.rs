//! Independent source-derived acceptance of `LeafHeadSetupProgram.support`.
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_head_support::{
    scatter_support_standalone_program, support_command, support_program, true_count_program,
    true_count_standalone_program,
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
            max_steps: 2_000_000,
            max_stack_bits: 20_000,
        },
    )
    .expect("source-defined finite machine must halt")
    .instructions
}
fn encoding(js: &[usize]) -> Vec<bool> {
    let mut data = Vec::new();
    for &j in js {
        data.push(true);
        data.extend(std::iter::repeat_n(true, 2 * j));
        data.push(false);
    }
    data.push(false);
    data
}
fn prepare<const R: usize>(
    p: &Program<R, 768>,
    js: &[usize],
    n: usize,
    seed: usize,
) -> Config<R, 768> {
    let mut d = p.initial(Vec::<bool>::new());
    put(&mut d, 650, &encoding(js));
    put(
        &mut d,
        651,
        &(0..js.len())
            .map(|i| ((seed + i) & 1) == 0)
            .collect::<Vec<_>>(),
    );
    put(&mut d, 128, &vec![true; n]);
    d
}

#[test]
fn literal_true_count_is_six_labels_independent_of_runtime_length_or_bit_values() {
    let p = true_count_program().unwrap();
    assert_eq!(p.code().len(), 6);
    for len in 0..=15usize {
        for seed in 0..32usize {
            let source: Vec<bool> = (0..len).map(|i| seed & (1 << (i % 5)) != 0).collect();
            let mut d = p.initial(source.clone());
            d.regs = [true, true, true];
            put(&mut d, 1, &[false, true]);
            let instructions = run(&p, &mut d);
            assert_eq!(instructions, (4 * len + 4) as u64);
            assert_eq!(get(&d, 0), Vec::<bool>::new());
            assert_eq!(get(&d, 1), [vec![true; len], vec![false, true]].concat());
            assert_eq!(d.regs, [false; 3]);
        }
    }
}

#[test]
fn true_count_is_staged_in_the_source_banks_and_clears_dirty_destinations() {
    let p = true_count_standalone_program().unwrap();
    let labels = p.code().len();
    for len in 0..=14usize {
        let mut d = p.initial(Vec::<bool>::new());
        let source = (0..len).map(|i| i % 3 == 0).collect::<Vec<_>>();
        put(&mut d, 651, &source);
        put(&mut d, 652, &[true, false, false]);
        put(&mut d, 120, &[false, true, true]);
        put(&mut d, 659, &[false; 2]);
        put(&mut d, 340, &[true, true, true, false]);
        put(&mut d, 341, &[false, false, true, true, true]);
        let t = run(&p, &mut d);
        assert_eq!(get(&d, 652), vec![true; len]);
        assert_eq!(get(&d, 651), source);
        assert_eq!(get(&d, 120), vec![false, true, true]);
        assert!(get(&d, 659).is_empty());
        assert!(get(&d, 340).is_empty() && get(&d, 341).is_empty());
        // 20 L+51 includes the compiled halt, plus 2 per stale source bit
        // in temporary/work banks and 2 per preexisting output bit.
        assert_eq!(t, (20 * len + 51 + 2 * (2 + 4 + 5 + 3)) as u64);
        assert_eq!(p.code().len(), labels);
    }
}

#[test]
fn full_support_stages_true_count_then_scatter_with_exact_source_step_formula() {
    let p = support_program().unwrap();
    assert_eq!(
        p.code().len(),
        support_command().unwrap().size().unwrap() + 1
    );
    let labels = p.code().len();
    let mut cases = 0;
    for n in 0..=8usize {
        for seed in 0..=32usize {
            let count = if n == 0 { 0 } else { seed % 5 };
            let js = (0..count).map(|i| (seed + 2 * i) % n).collect::<Vec<_>>();
            let mut d = prepare(&p, &js, n, seed);
            let head_ids = get(&d, 650);
            let source_bits = get(&d, 651);
            let mut expected = vec![false; n];
            for &j in &js {
                expected[j] = true;
            }
            let instructions = run(&p, &mut d);
            assert_eq!(get(&d, 670), expected, "n={n} seed={seed}");
            assert_eq!(get(&d, 652), vec![true; count]);
            assert_eq!(get(&d, 128), vec![true; n]);
            assert_eq!(get(&d, 650), head_ids);
            assert_eq!(get(&d, 651), source_bits);
            for j in 340..=352 {
                assert!(get(&d, j).is_empty(), "uncleared support work port {j}");
            }
            assert!(get(&d, 659).is_empty());
            assert_eq!(d.pc, None);
            let i = head_ids.len();
            let sum = js.iter().map(|j| 30 * j + 55).sum::<usize>();
            // Count: 20*k+50; scatter: 16*i+16*k+29*n+sum+155;
            // plus one final compiled halt.
            assert_eq!(
                instructions,
                (36 * count + 16 * i + 29 * n + sum + 206) as u64,
                "wrong physical instruction count for n={n} seed={seed}"
            );
            assert_eq!(
                p.code().len(),
                labels,
                "runtime data changed static program size"
            );
            cases += 1;
        }
    }
    assert!(cases > 250);
}

#[test]
fn full_support_overwrites_stale_mask_and_count_but_preserves_protected_masters() {
    let p = support_program().unwrap();
    let js = [2, 0, 4];
    let mut d = prepare(&p, &js, 6, 1);
    put(&mut d, 652, &[true, true, true, true]);
    put(&mut d, 670, &[false, true, false]);
    put(&mut d, 659, &[false, true]);
    put(&mut d, 342, &[true, true, false]);
    put(&mut d, 141, &[true, false, false, true]);
    put(&mut d, 307, &[true, true, false]);
    d.regs[12] = true;
    let original_141 = get(&d, 141);
    let original_307 = get(&d, 307);
    let original_651 = get(&d, 651);
    let instructions = run(&p, &mut d);
    assert_eq!(get(&d, 670), vec![true, false, true, false, true, false]);
    assert_eq!(get(&d, 652), vec![true; 3]);
    assert_eq!(get(&d, 141), original_141);
    assert_eq!(get(&d, 307), original_307);
    assert_eq!(get(&d, 651), original_651);
    for j in 340..=352 {
        assert!(get(&d, j).is_empty());
    }
    assert!(get(&d, 659).is_empty());
    let i = encoding(&js).len();
    let sum = js.iter().map(|j| 30 * j + 55).sum::<usize>();
    let clean = 36 * js.len() + 16 * i + 29 * 6 + sum + 206;
    assert_eq!(instructions, (clean + 2 * (4 + 3 + 2 + 3)) as u64);
}

#[test]
fn staging_resource_refusal_does_not_masquerade_as_a_completed_mask() {
    let p = support_program().unwrap();
    let mut d = prepare(&p, &[0, 4, 1], 6, 0);
    let e = p.run(
        &mut d,
        RunLimits {
            max_steps: 18,
            max_stack_bits: 5000,
        },
    );
    assert!(matches!(e, Err(Error::Capacity(_))));
    assert!(d.pc.is_some());
}

#[test]
fn scatter_support_stage_uses_exact_callee_register_and_stack_maps() {
    let p = scatter_support_standalone_program().unwrap();
    let js = [2, 5, 1];
    let mut d = prepare(&p, &js, 7, 0);
    put(&mut d, 652, &[true, true, true]);
    let before = get(&d, 650);
    let t = run(&p, &mut d);
    let i = before.len();
    let sum = js.iter().map(|j| 30 * j + 55).sum::<usize>();
    assert_eq!(t, (16 * i + 16 * js.len() + 29 * 7 + sum + 156) as u64);
    assert_eq!(
        get(&d, 670),
        vec![false, true, true, false, false, true, false]
    );
    assert_eq!(get(&d, 650), before);
}

#[test]
fn high_registers_are_preserved_by_source_cast_add_embeddings() {
    let p = support_program().unwrap();
    let mut d = prepare(&p, &[0, 2], 4, 0);
    d.regs[9..16].fill(true);
    let protected = d.regs[9..16].to_vec();
    run(&p, &mut d);
    assert_eq!(&d.regs[9..16], protected.as_slice());
    assert_eq!(get(&d, 670), vec![true, false, true, false]);
}
