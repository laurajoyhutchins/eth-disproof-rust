//! Pinned physical pair setup, with independent direct count/word oracles.
//! Not a test of the as-yet-unported signed pair computations.

use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_pair_setup::{
    count_command, count_false_command, count_false_program, setup_caller_command,
    setup_caller_program, setup_command,
};
use std::collections::VecDeque;

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, value: &[bool]) {
    d.stacks[port] = VecDeque::from(value.to_vec());
}
fn read<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn mask(width: usize, rank: usize) -> Vec<bool> {
    (0..width).map(|i| rank & (1 << i) != 0).collect()
}

#[test]
fn physical_false_counter_matches_every_mask_up_to_eight_bits() {
    let p = count_false_program().unwrap();
    assert_eq!(count_false_command().size().unwrap(), 6);
    assert_eq!(p.code().len(), 7);
    for width in 0..=8 {
        for rank in 0..(1 << width) {
            let bits = mask(width, rank);
            let false_count = bits.iter().filter(|&&b| !b).count();
            let mut d = p.initial(bits);
            put(&mut d, 1, &[false, true]);
            d.regs = [true, true, false];
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, (3 * width + false_count + 4) as u64);
            assert!(d.stacks[0].is_empty());
            assert_eq!(
                read(&d, 1),
                [vec![true; false_count], vec![false, true]].concat()
            );
            assert_eq!(d.regs, [false, false, true]);
        }
    }
}

#[test]
fn isolated_pair_count_charges_both_sides_of_its_runtime_cleanup() {
    let code = count_command().unwrap();
    let p = code.compiled(338, 832).unwrap();
    assert_eq!(code.size().unwrap(), 77);
    for width in 0..=7 {
        for rank in 0..(1 << width) {
            let bits = mask(width, rank);
            let false_count = bits.iter().filter(|&&b| !b).count();
            let mut d = p.initial(Vec::<bool>::new());
            put(&mut d, 338, &bits);
            let dirty = [325, 326, 327, 328, 329];
            let mut scratch_size = 0;
            for (index, stack) in dirty.iter().copied().enumerate() {
                let v = mask(index % 4 + 1, rank + index);
                scratch_size += v.len();
                put(&mut d, stack, &v);
            }
            let old_destination = vec![false, true, true];
            put(&mut d, 832, &old_destination);
            put(&mut d, 243, &[true, false, true, false]);
            d.regs[12] = true;
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            // Local `isolated` overhead includes two passes of bank cleanup,
            // +9-bit work-register reset on each side, and the actual count.
            let count_steps =
                2 * scratch_size + 10 * width + 10 * false_count + 2 * old_destination.len() + 68;
            assert_eq!(stats.instructions, (count_steps + 1) as u64);
            assert_eq!(read(&d, 338), bits);
            assert_eq!(read(&d, 832), vec![true; false_count]);
            assert_eq!(read(&d, 243), vec![true, false, true, false]);
            assert!(d.regs[12]);
            for port in dirty {
                assert!(d.stacks[port].is_empty(), "port {port}");
            }
            for r in 0..9 {
                assert!(!d.regs[r], "work register {r}");
            }
            let b = width.max(4).max(old_destination.len());
            assert!(stats.instructions - 1 <= 100 * (b + 1) as u64);
        }
    }
}

#[test]
fn full_pair_setup_caller_stages_free_count_and_native_metadata() {
    let c = setup_command().unwrap();
    let p = setup_caller_program().unwrap();
    assert_eq!(c.size().unwrap(), 94);
    assert_eq!(p.code().len(), 96);
    assert_eq!(setup_caller_command().unwrap().size().unwrap(), 95);
    for width in 0..=7 {
        for rank in 0..(1 << width) {
            let bits = mask(width, rank);
            let free = bits.iter().filter(|&&b| !b).count();
            let mut d = p.initial(Vec::<bool>::new());
            put(&mut d, 338, &bits);
            let meta = vec![true, false, rank % 2 == 0, true, true];
            put(&mut d, 243, &meta);
            for i in 325..=329 {
                put(&mut d, i, &[true, false]);
            }
            for (i, port) in [833, 834, 835].into_iter().enumerate() {
                put(&mut d, port, &mask(i + 1, rank));
            }
            put(&mut d, 832, &[true, false, true]);
            put(&mut d, 789, &[true, false, true, true]);
            put(&mut d, 738, &[false, true]);
            for i in 0..40 {
                d.regs[i] = (i + rank) % 3 == 0;
            }
            let prior = d.clone();
            let stats = p.run(&mut d, RunLimits::default()).unwrap();
            let old_scratch = 5 * 2;
            let old_other = 1 + 2 + 3;
            let expected = 2 * old_scratch
                + 10 * width
                + 10 * free
                + 2 * 3
                + 2 * old_other
                + 7 * meta.len()
                + 84;
            assert_eq!(
                stats.instructions, expected as u64,
                "width {width}, rank {rank}"
            );
            assert_eq!(read(&d, 832), vec![true; free]);
            assert_eq!(read(&d, 833), meta);
            assert_eq!(read(&d, 338), bits);
            assert_eq!(read(&d, 789), read(&prior, 789));
            assert_eq!(read(&d, 738), read(&prior, 738));
            for stack in [325, 326, 327, 328, 329, 834, 835] {
                assert!(d.stacks[stack].is_empty(), "scratch {stack}");
            }
            for i in 0..9 {
                assert!(!d.regs[i]);
            }
            for i in 9..40 {
                assert_eq!(d.regs[i], prior.regs[i]);
            }
            for i in 0..896 {
                if [325, 326, 327, 328, 329, 832, 833, 834, 835].contains(&i) {
                    continue;
                }
                assert_eq!(d.stacks[i], prior.stacks[i], "unexpected stack write {i}");
            }
        }
    }
}

#[test]
fn empty_pair_mask_gives_one_valid_zero_free_coordinate_count() {
    let p = setup_caller_program().unwrap();
    let mut d = p.initial(Vec::<bool>::new());
    put(&mut d, 243, &[false]);
    let stats = p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 7 + 84);
    assert!(d.stacks[832].is_empty());
    assert_eq!(read(&d, 833), vec![false]);
}
