//! Independent physical-state and step-count checks for the pinned Lean
//! `NativeLayoutLoad.command`. Does not invoke the unported head evaluator.

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_layout::{self, HIGH_START, LOW_START, MASTER_COUNT};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, data: &[bool]) {
    d.stacks[port] = VecDeque::from(data.to_vec());
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn bits(n: usize, salt: usize) -> Vec<bool> {
    (0..n).map(|j| ((j * 17 + salt * 11) % 5) <= 1).collect()
}

#[test]
fn actual_source_table_has_fixed_size_and_exact_lifted_call_boundaries() {
    let c = native_layout::command().unwrap();
    let p = native_layout::program().unwrap();
    assert_eq!(c.size().unwrap(), 52 + 114);
    assert_eq!(p.code().len(), 167);
    assert_eq!(p.input_stack(), HIGH_START);
    assert_eq!(p.output_stack(), LOW_START);
    assert_eq!(native_layout::clear_ports().len(), 17);
    assert_eq!(
        native_layout::load_local_command()
            .unwrap()
            .compiled(730, 128)
            .unwrap()
            .code()
            .len(),
        113
    );
    assert_eq!(
        native_layout::load_low_command()
            .unwrap()
            .compiled(730, 128)
            .unwrap()
            .code()
            .len(),
        114
    );
}

#[test]
fn clears_dirty_destinations_then_copies_every_parked_word_without_reindexing() {
    let p = native_layout::program().unwrap();
    let clears = native_layout::clear_ports();
    for seed in 0..40usize {
        let mut d = p.initial(Vec::<bool>::new());
        let mut source = Vec::new();
        for i in 0..MASTER_COUNT {
            let v = bits((i + seed * 3) % 9, i + seed);
            put(&mut d, HIGH_START + i, &v);
            source.push(v);
        }
        for (j, port) in clears.iter().copied().enumerate() {
            put(&mut d, port, &bits((j + seed) % 6 + 1, seed + j));
        }
        put(&mut d, 789, &[true, false, true, true]);
        put(&mut d, 307, &[true, true]);
        put(&mut d, 40, &[false, true, false]);
        for r in 0..40 {
            d.regs[r] = (seed + r) % 2 == 0;
        }
        let before = d.clone();
        let exact = native_layout::expected_steps(&d.stacks).unwrap();
        let b = before.stacks.iter().map(VecDeque::len).max().unwrap();
        let outcome = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(outcome.instructions, exact, "seed {seed}");
        assert!(outcome.instructions <= 132 * b as u64 + 125);
        assert!(outcome.peak_stack_bits <= 1028 * b + 125);
        assert_eq!(d.pc, None);
        for (i, expected) in source.iter().enumerate() {
            assert_eq!(get(&d, LOW_START + i), *expected, "low master {i}");
            assert_eq!(get(&d, HIGH_START + i), *expected, "parked source {i}");
        }
        for port in [684, 660, 665] {
            assert!(d.stacks[port].is_empty(), "scratch port {port}");
        }
        for (i, (after, prev)) in d.stacks.iter().zip(&before.stacks).enumerate() {
            if (LOW_START..LOW_START + MASTER_COUNT).contains(&i) || [684, 660, 665].contains(&i) {
                continue;
            }
            assert_eq!(after, prev, "unexpected write on stack {i}");
        }
        for i in 16..40 {
            assert_eq!(d.regs[i], before.regs[i], "unexpected register write {i}");
        }
    }
}

#[test]
fn zero_length_masters_and_all_dirty_ports_obey_source_step_formula() {
    let p = native_layout::program().unwrap();
    for dirty in 0..=7 {
        let mut d = p.initial(Vec::<bool>::new());
        for stack in native_layout::clear_ports() {
            put(&mut d, stack, &bits(dirty, stack));
        }
        let expected = native_layout::expected_steps(&d.stacks).unwrap();
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, expected);
        for port in native_layout::clear_ports() {
            assert!(d.stacks[port].is_empty());
        }
        for i in 0..MASTER_COUNT {
            assert!(d.stacks[LOW_START + i].is_empty());
        }
    }
}

#[test]
fn a_real_step_budget_refuses_before_the_next_source_instruction() {
    let p = native_layout::program().unwrap();
    let mut d = p.initial([true, false, true]);
    let expected = native_layout::expected_steps(&d.stacks).unwrap();
    assert!(
        p.run(
            &mut d,
            RunLimits {
                max_steps: expected - 1,
                max_stack_bits: 100
            }
        )
        .is_err()
    );
    assert!(d.pc.is_some());
    let mut d = p.initial([true, false, true]);
    let stats = p
        .run(
            &mut d,
            RunLimits {
                max_steps: expected,
                max_stack_bits: 100,
            },
        )
        .unwrap();
    assert_eq!(stats.instructions, expected);
}

#[test]
fn first_actual_query_node_prefix_decodes_high_input_and_loads_parked_masters() {
    use lean_eth_reference::native_tuple::encode_words;
    let program = native_layout::first_node_layout_prefix_command()
        .unwrap()
        .compiled(330, 128)
        .unwrap();
    for has_node in [false, true] {
        for high_mask in [vec![], vec![false, true, true], vec![true, false]] {
            let h = high_mask.iter().filter(|&&x| x).count();
            let high_bits = (0..h).map(|j| j % 2 == 0).collect::<Vec<_>>();
            let assignment = high_bits
                .iter()
                .copied()
                .map(|v| vec![v])
                .collect::<Vec<_>>();
            let mut d = program.initial(encode_words(&assignment).unwrap());
            put(&mut d, 338, &high_mask);
            let node_bits = vec![false, true, true, false];
            let nodes = if has_node {
                vec![node_bits.clone()]
            } else {
                vec![]
            };
            put(&mut d, 300, &encode_words(&nodes).unwrap());
            for i in 0..MASTER_COUNT {
                put(&mut d, HIGH_START + i, &bits((i % 4) + 1, i));
                put(&mut d, LOW_START + i, &[true, true]);
            }
            let before = d.clone();
            let stats = program.run(&mut d, RunLimits::default()).unwrap();
            assert!(stats.instructions > 0);
            assert_eq!(get(&d, 300), get(&before, 300));
            assert_eq!(get(&d, 338), high_mask);
            assert_eq!(get(&d, 703), {
                let mut merged = Vec::with_capacity(high_mask.len());
                let mut j = 0;
                for selected in &high_mask {
                    merged.push(if *selected {
                        let x = high_bits[j];
                        j += 1;
                        x
                    } else {
                        false
                    });
                }
                merged.into_iter().rev().collect::<Vec<_>>()
            });
            if has_node {
                assert_eq!(get(&d, 78), node_bits);
                assert_eq!(get(&d, 301), encode_words(&[]).unwrap());
                for i in 0..MASTER_COUNT {
                    assert_eq!(get(&d, LOW_START + i), get(&before, HIGH_START + i));
                    assert_eq!(get(&d, HIGH_START + i), get(&before, HIGH_START + i));
                }
                for i in [660, 665, 684] {
                    assert!(d.stacks[i].is_empty());
                }
                assert!(!d.regs[37]); // the source reader consumes the tag and rewrites this register
            } else {
                assert_eq!(get(&d, 301), encode_words(&[]).unwrap());
                assert!(d.stacks[78].is_empty());
                for i in 0..MASTER_COUNT {
                    assert_eq!(get(&d, LOW_START + i), get(&before, LOW_START + i));
                }
                assert!(!d.regs[37]);
            }
        }
    }
}
