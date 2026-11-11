use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_bootstrap::{
    address_local_command, address_local_program, bootstrap_prefix_node_command,
    bootstrap_prefix_program, count_rows_command, initialize_address_command,
    record_counter_program, retain_cache_program, row_count_local_command, row_count_local_program,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, bits: &[bool]) {
    d.stacks[port] = VecDeque::from(bits.to_vec());
}
fn read<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn framed(words: &[Vec<bool>]) -> Vec<bool> {
    let mut result = Vec::new();
    for word in words {
        result.push(true);
        for &bit in word {
            result.extend([true, bit]);
        }
        result.push(false);
    }
    result.push(false);
    result
}

#[test]
fn address_is_a_real_unary_multiply_on_fixed_stacks() {
    let p = address_local_program().unwrap();
    assert_eq!(p.input_stack(), 2);
    assert_eq!(p.output_stack(), 4);
    for r in 0..=7 {
        for node in 0..=7 {
            let mut d = p.initial([]);
            put(&mut d, 0, &vec![true; r]);
            put(&mut d, 2, &vec![true; node]);
            d.regs = [true, false, true];
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(
                stats.instructions,
                (7 * r * node + 14 * node + 7 * r + 13) as u64
            );
            assert_eq!(read(&d, 0), vec![true; r]);
            assert_eq!(read(&d, 2), vec![true; node]);
            assert_eq!(read(&d, 3), vec![true; r]);
            assert_eq!(read(&d, 4), vec![true; r * node]);
            assert!(d.stacks[5].is_empty() && d.stacks[6].is_empty());
        }
    }
    assert_eq!(
        p.code().len(),
        address_local_command().unwrap().size().unwrap() + 1
    );
}

#[test]
fn thirteen_label_record_counter_consumes_frames_not_payload_lengths() {
    let p = record_counter_program().unwrap();
    assert_eq!(p.code().len(), 13);
    assert_eq!(p.entry(), 2);
    let examples: Vec<Vec<Vec<bool>>> = vec![
        vec![],
        vec![vec![]],
        vec![vec![false]],
        vec![vec![true, false], vec![], vec![false, false, true]],
        vec![vec![true; 5], vec![false, false], vec![], vec![true]],
    ];
    for words in examples {
        let encoded = framed(&words);
        let mut d = p.initial(encoded);
        let prior = vec![false, true];
        put(&mut d, 1, &prior);
        let n = words.len();
        let payload: usize = words.iter().map(Vec::len).sum();
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, (4 * payload + 6 * n + 5) as u64);
        assert!(d.stacks[0].is_empty());
        assert_eq!(read(&d, 1), [vec![true; n], prior].concat());
        assert_eq!(d.regs, [false, false]);
    }
}

#[test]
fn local_row_count_copies_preserved_source_then_physically_parses() {
    let p = row_count_local_program().unwrap();
    assert_eq!(
        p.code().len(),
        row_count_local_command().unwrap().size().unwrap() + 1
    );
    for n in 0..=5 {
        let words: Vec<Vec<bool>> = (0..n)
            .map(|j| (0..j + 1).map(|b| (b + j) % 2 == 0).collect())
            .collect();
        let encoded = framed(&words);
        let mut d = p.initial([]);
        put(&mut d, 1, &encoded);
        d.regs[6] = true;
        d.regs[7] = true;
        let payload: usize = words.iter().map(Vec::len).sum();
        let expected = 7 * encoded.len() + 5 + 4 * payload + 6 * n + 5 + 1;
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, expected as u64);
        assert_eq!(read(&d, 1), encoded);
        assert_eq!(read(&d, 2), vec![true; n]);
        assert!(
            d.regs[6] && d.regs[7],
            "Fin.castAdd must preserve register indices"
        );
        assert!(d.stacks[14].is_empty());
    }
}

#[test]
fn staged_boot_prefix_preserves_caller_and_scrubs_visited_work_bank() {
    let pa = initialize_address_command()
        .unwrap()
        .compiled(307, 649)
        .unwrap();
    let pc = count_rows_command().unwrap().compiled(136, 647).unwrap();
    assert!(!pa.code().is_empty() && !pc.code().is_empty());
    let p = bootstrap_prefix_program().unwrap();
    for r in 0..=4 {
        for node in 0..=4 {
            let words = vec![vec![false, true], vec![], vec![true, false, false]];
            let raw = framed(&words);
            let mut d = p.initial([]);
            put(&mut d, 130, &vec![true; r]);
            put(&mut d, 307, &vec![true; node]);
            put(&mut d, 136, &raw);
            for port in 340..=354 {
                put(&mut d, port, &[true, false, true]);
            }
            put(&mut d, 355, &[true, true]); // outside both staged workspaces
            put(&mut d, 627, &[false, true]); // high end of the reserved bank
            put(&mut d, 659, &[false, true]);
            put(&mut d, 660, &[true, false]);
            put(&mut d, 665, &[false, false, true]);
            put(&mut d, 710, &[true, false]);
            d.regs[7] = true;
            let before = d.clone();
            p.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(read(&d, 648), vec![true; r]);
            assert_eq!(read(&d, 649), vec![true; r * node]);
            assert_eq!(read(&d, 647), vec![true; words.len()]);
            assert_eq!(read(&d, 130), vec![true; r]);
            assert_eq!(read(&d, 307), vec![true; node]);
            assert_eq!(read(&d, 136), raw);
            for port in 340..=354 {
                assert!(d.stacks[port].is_empty(), "dirty workspace at {port}");
            }
            assert!(d.stacks[659].is_empty());
            assert_eq!(read(&d, 660), read(&before, 660));
            assert_eq!(read(&d, 665), read(&before, 665));
            assert_eq!(read(&d, 710), read(&before, 710));
            assert!(d.regs[..7].iter().all(|&v| !v));
            assert!(!d.regs[7]); // resetWork owns registers 0..8
            for port in 0..768 {
                if (340..=354).contains(&port) || [647, 648, 649, 659].contains(&port) {
                    continue;
                }
                assert_eq!(d.stacks[port], before.stacks[port], "frame port {port}");
            }
        }
    }
}

#[test]
fn retention_uses_actual_preserving_copies_and_does_not_reconstruct_cache() {
    let p = retain_cache_program().unwrap();
    for n in 0..=5 {
        let mut d = p.initial([]);
        put(&mut d, 659, &[true, false, false]);
        let mut expected = 2 * 3 + 3 + 1;
        for (offset, (src, dst)) in [(640, 710), (641, 711), (642, 712)].iter().enumerate() {
            let bits: Vec<bool> = (0..n + offset).map(|i| i % 2 == 0).collect();
            put(&mut d, *src, &bits);
            put(&mut d, *dst, &[false, true]);
            expected += 7 * bits.len() + 5;
        }
        let before = d.clone();
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, expected as u64);
        assert!(d.stacks[659].is_empty());
        for (src, dst) in [(640, 710), (641, 711), (642, 712)] {
            assert_eq!(read(&d, src), read(&before, src));
            assert_eq!(
                read(&d, dst),
                [read(&before, src), read(&before, dst)].concat()
            );
        }
    }
}

#[test]
fn node_abi_widens_indices_without_shifting_them() {
    let p = bootstrap_prefix_node_command()
        .unwrap()
        .compiled(307, 647)
        .unwrap();
    let mut d = p.initial([]);
    put(&mut d, 130, &[true, true]);
    put(&mut d, 307, &[true, true, true]);
    put(&mut d, 136, &framed(&[vec![true], vec![]]));
    put(&mut d, 800, &[false, true]); // beyond the lifted 768-stack submachine
    d.regs[19] = true; // beyond the lifted 16-register submachine
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(read(&d, 648), vec![true, true]);
    assert_eq!(read(&d, 649), vec![true; 6]);
    assert_eq!(read(&d, 647), vec![true, true]);
    assert_eq!(read(&d, 800), vec![false, true]);
    assert!(d.regs[19]);
}
