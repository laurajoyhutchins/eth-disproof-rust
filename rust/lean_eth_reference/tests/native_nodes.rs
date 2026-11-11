//! Test the physical node cursor and framed node reader with independent
//! expected words and exact source-step formulas from the pinned Lean files.

use lean_eth_reference::bit_program::{Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_nodes::{
    begin_node_command, begin_node_program, finish_node_control_command, guard_cursor_command,
    initialize_nodes_command, initialize_nodes_program, nodes_entry_command,
    query_nodes_entry_command, read_node_low_command,
};
use lean_eth_reference::native_tuple::encode_words;
use std::collections::VecDeque;

fn word<const R: usize, const S: usize>(d: &Config<R, S>, i: usize) -> Vec<bool> {
    d.stacks[i].iter().copied().collect()
}
fn set<const R: usize, const S: usize>(d: &mut Config<R, S>, i: usize, value: Vec<bool>) {
    d.stacks[i] = VecDeque::from(value);
}
fn patterns(n: usize) -> impl Iterator<Item = Vec<bool>> {
    (0..1usize << n).map(move |rank| (0..n).map(|i| (rank >> i) & 1 != 0).collect())
}
fn records_fixture(n: usize, rank: usize) -> Vec<Vec<bool>> {
    (0..n)
        .map(|i| (0..(i % 4)).map(|j| ((rank + i + j) % 3) == 1).collect())
        .collect()
}

#[test]
fn cursor_initializer_copies_actual_table_and_clears_only_named_ports() {
    let program = initialize_nodes_program().unwrap();
    for n in 0..=5 {
        for rank in 0..8 {
            let records = records_fixture(n, rank);
            let encoded = encode_words(&records).unwrap();
            let mut d = program.initial(Vec::new());
            set(&mut d, 300, encoded.clone());
            let dirty = [301, 302, 305, 307, 78, 850, 851, 863];
            let old_sizes: usize = dirty
                .iter()
                .map(|&port| {
                    set(&mut d, port, vec![true, false, rank % 2 != 0]);
                    3
                })
                .sum();
            set(&mut d, 789, vec![true, false, true]);
            set(&mut d, 703, vec![false, true]);
            d.regs[21] = true;
            let stats = program.run(&mut d, RunLimits::default()).unwrap();
            let expected = 2 * old_sizes + 7 * encoded.len() + 20 + 1 + 9 + 1;
            assert_eq!(stats.instructions, expected as u64);
            assert_eq!(word(&d, 300), encoded);
            assert_eq!(word(&d, 301), encoded);
            for port in [302, 305, 307, 78, 850, 851, 863] {
                assert!(d.stacks[port].is_empty(), "port {port}");
            }
            assert_eq!(word(&d, 789), vec![true, false, true]);
            assert_eq!(word(&d, 703), vec![false, true]);
            assert!(d.regs[21]);
        }
    }
}

#[test]
fn raw_node_reader_preserves_unused_suffix_and_returns_exact_steps() {
    let read = read_node_low_command().unwrap().compiled(301, 78).unwrap();
    for n in 0..=6 {
        for bits in patterns(n) {
            let tail = vec![vec![false, true], vec![], vec![true]];
            let mut list = vec![bits.clone()];
            list.extend(tail.clone());
            let mut d = read.initial(Vec::new());
            set(&mut d, 301, encode_words(&list).unwrap());
            d.regs[39] = true;
            let stats = read.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, (9 * n + 9) as u64);
            assert_eq!(word(&d, 301), encode_words(&tail).unwrap());
            assert_eq!(word(&d, 78), bits);
            assert!(d.stacks[302].is_empty());
            assert!(d.regs[39]);
        }
    }
}

#[test]
fn begin_node_clears_stale_work_banks_then_reads_one_framed_record() {
    let program = begin_node_program().unwrap();
    let changed = [78, 302, 660, 665, 710, 711, 712, 850, 851];
    for n in 0..=5 {
        for bits in patterns(n) {
            let tail = vec![vec![false, true], vec![true]];
            let mut records = vec![bits.clone()];
            records.extend(tail.clone());
            let mut d = program.initial(encode_words(&records).unwrap());
            let mut prior = 0usize;
            for port in changed {
                set(&mut d, port, vec![true, false, true]);
                prior += 3;
            }
            set(&mut d, 799, vec![false, false, true]);
            set(&mut d, 789, vec![true, true]);
            d.regs[21] = true;
            d.regs[39] = true;
            let stats = program.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(
                stats.instructions,
                (2 * prior + 3 * 9 + 9 * n + 9 + 1) as u64
            );
            assert_eq!(word(&d, 301), encode_words(&tail).unwrap());
            assert_eq!(word(&d, 78), bits);
            for port in [302, 660, 665, 710, 711, 712, 850, 851] {
                assert!(d.stacks[port].is_empty());
            }
            assert_eq!(word(&d, 799), vec![false, false, true]);
            assert_eq!(word(&d, 789), vec![true, true]);
            assert!(d.regs[21]);
            assert!(d.regs[39]);
        }
    }
}

#[test]
fn node_guard_is_a_non_consuming_peek_with_a_real_empty_tag() {
    let guard = guard_cursor_command().compiled(301, 78).unwrap();
    for records in [vec![], vec![vec![]], vec![vec![true], vec![]]] {
        let encoded = encode_words(&records).unwrap();
        let mut d = guard.initial(encoded.clone());
        let stats = guard.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, 2);
        assert_eq!(word(&d, 301), encoded);
        assert_eq!(d.regs[37], !records.is_empty());
        assert!(d.regs[38]);
    }
}

#[test]
fn diagnostic_node_iteration_checks_canonical_source_port_lifecycle() {
    // This loop uses the real source reader and finish-node *control* suffix,
    // but omits the node arithmetic / pair evaluator and node-result append.
    // It must NOT be described as the complete QueryStreamProgram.nodeLoop.
    let loop_command = Cmd::seq(
        initialize_nodes_command().unwrap(),
        Cmd::seq(
            guard_cursor_command(),
            Cmd::while_(
                37,
                Cmd::seq(
                    begin_node_command().unwrap(),
                    finish_node_control_command().unwrap(),
                ),
            ),
        ),
    );
    let program: Program<40, 896> = loop_command.compiled(300, 307).unwrap();
    for n in 0..=4 {
        for rank in 0..8 {
            let records = records_fixture(n, rank);
            let encoded = encode_words(&records).unwrap();
            let mut d = program.initial(encoded.clone());
            set(&mut d, 851, vec![true, true]);
            set(&mut d, 79, vec![false, true]);
            let stats = program.run(&mut d, RunLimits::default()).unwrap();
            assert!(stats.instructions > 0);
            assert_eq!(word(&d, 300), encoded);
            assert_eq!(word(&d, 301), vec![false]);
            assert_eq!(word(&d, 307), vec![true; n]);
            assert!(d.stacks[78].is_empty());
            assert!(d.stacks[850].is_empty());
            assert!(d.stacks[851].is_empty());
            assert_eq!(word(&d, 79), vec![false, true]);
            assert!(!d.regs[37]);
            assert!(d.regs[38]);
        }
    }
}

#[test]
fn complete_query_nodes_entry_preserves_both_high_assignment_and_node_tables() {
    let program = query_nodes_entry_command()
        .unwrap()
        .compiled(330, 863)
        .unwrap();
    let nodes_only = nodes_entry_command().unwrap().compiled(300, 863).unwrap();
    assert!(!nodes_only.code().is_empty());
    for width in 0..=4 {
        for mask in patterns(width) {
            let high = mask.iter().filter(|&&x| x).count();
            for assignment in patterns(high) {
                let counter =
                    encode_words(&assignment.iter().map(|&x| vec![x]).collect::<Vec<_>>()).unwrap();
                let nodes = vec![vec![true, false], vec![], vec![false]];
                let encoded_nodes = encode_words(&nodes).unwrap();
                let mut d = program.initial(counter.clone());
                set(&mut d, 338, mask.clone());
                set(&mut d, 300, encoded_nodes.clone());
                d.regs[21] = true;
                let stats = program.run(&mut d, RunLimits::default()).unwrap();
                assert!(stats.instructions > 0);
                assert_eq!(word(&d, 330), counter);
                assert_eq!(word(&d, 300), encoded_nodes);
                assert_eq!(word(&d, 301), encoded_nodes);
                let mut expected = Vec::new();
                let mut high_iter = assignment.iter();
                for selected in &mask {
                    expected.push(if *selected {
                        *high_iter.next().unwrap()
                    } else {
                        false
                    });
                }
                assert_eq!(
                    word(&d, 703),
                    expected.iter().rev().copied().collect::<Vec<_>>()
                );
                assert_eq!(
                    word(&d, 702),
                    mask.iter().rev().copied().collect::<Vec<_>>()
                );
                assert!(d.regs[37]);
                assert!(d.regs[38]);
                assert!(d.regs[21]);
            }
        }
    }
}
