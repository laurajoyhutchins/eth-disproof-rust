//! Source-pinned execution tests for `PairNativeSetup.expandCaller`.
//! The independent specifications here calculate only expected *end states*;
//! execution runs through compiled finite tables and physically paid copies.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_pair_setup::{
    expand_caller_command, expand_caller_program, expand_command, expand_program, fill_command,
    restriction_command, restriction_program, setup_caller_program,
};

fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, bits: &[bool]) {
    d.stacks[port] = bits.iter().copied().collect();
}
fn get<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    p.run(
        d,
        RunLimits {
            max_steps: 2_000_000,
            max_stack_bits: 30_000,
        },
    )
    .unwrap()
    .instructions
}
fn mask(n: usize, seed: usize) -> Vec<bool> {
    // Top-first original descending index: n-1,n-2,...,0.
    (0..n).rev().map(|i| (seed >> i) & 1 != 0).collect()
}
fn free_bits(n: usize, seed: usize) -> Vec<bool> {
    (0..n).map(|i| ((seed >> i) & 1) != 0).collect()
}
fn expected(mask_desc: &[bool], free_ascending: &[bool]) -> Vec<bool> {
    assert_eq!(
        mask_desc.iter().filter(|&&fixed| !fixed).count(),
        free_ascending.len()
    );
    let mut unread = free_ascending.iter().rev();
    let mut output: Vec<_> = mask_desc
        .iter()
        .map(|&fixed| {
            if fixed {
                false
            } else {
                *unread.next().unwrap()
            }
        })
        .collect();
    output.reverse();
    output
}

#[test]
fn local_restriction_is_the_source_fixed_program_and_preserves_output_suffix() {
    let cmd = restriction_command();
    let p = restriction_program().unwrap();
    assert_eq!(cmd.size().unwrap(), 7);
    assert_eq!(p.code().len(), 8);
    assert_eq!(p.input_stack(), 0);
    assert_eq!(p.output_stack(), 3);
    for n in 0..=9 {
        for seed in 0..(1usize << n) {
            let mask_desc = mask(n, seed);
            let source_desc = (0..n)
                .rev()
                .map(|i| (i + seed) % 3 == 0)
                .collect::<Vec<_>>();
            let high = mask_desc
                .iter()
                .zip(&source_desc)
                .filter_map(|(&h, &bit)| h.then_some(bit))
                .collect::<Vec<_>>();
            let low = mask_desc
                .iter()
                .zip(&source_desc)
                .filter_map(|(&h, &bit)| (!h).then_some(bit))
                .collect::<Vec<_>>();
            let mut d = p.initial(mask_desc);
            put(&mut d, 1, &high);
            put(&mut d, 2, &low);
            put(&mut d, 3, &[true, false, true]);
            d.regs = [true, true, true, true];
            assert_eq!(run(&p, &mut d), (5 * n + 3) as u64);
            for i in 0..3 {
                assert!(d.stacks[i].is_empty(), "port {i}, n={n}, seed={seed}");
            }
            let mut want = source_desc.into_iter().rev().collect::<Vec<_>>();
            want.extend([true, false, true]);
            assert_eq!(get(&d, 3), want, "n={n}, seed={seed}");
            assert!(!d.regs[1]);
        }
    }
}

#[test]
fn fill_copies_physical_inputs_and_overwrites_only_its_selected_output() {
    for is_e in [true, false] {
        let p = fill_command(is_e)
            .unwrap()
            .compiled(338, if is_e { 858 } else { 857 })
            .unwrap();
        for n in 0..=16 {
            for seed in [0, 1, 3, 0x2aa, 0x5555, 0xffff] {
                let m = mask(n, seed);
                let free = m.iter().filter(|&&x| !x).count();
                let bits = free_bits(free, seed ^ (n * 0x35));
                let input_port = if is_e { 834 } else { 835 };
                let output_port = if is_e { 858 } else { 857 };
                let mut d = p.initial([]);
                put(&mut d, 338, &m);
                put(
                    &mut d,
                    input_port,
                    &bits.iter().rev().copied().collect::<Vec<_>>(),
                );
                put(&mut d, output_port, &[true, true, false]);
                for j in 325..=329 {
                    put(&mut d, j, &[true, j % 2 == 0]);
                }
                for (j, v) in [
                    (243, vec![false]),
                    (832, vec![true, true]),
                    (833, vec![false, true]),
                    (851, vec![true]),
                    (895, vec![false, true]),
                ] {
                    put(&mut d, j, &v);
                }
                d.regs[12] = true;
                let before = d.clone();
                let steps = run(&p, &mut d);
                assert_eq!(get(&d, output_port), expected(&m, &bits));
                for j in 325..=329 {
                    assert!(d.stacks[j].is_empty());
                }
                assert!(d.regs[..9].iter().all(|&x| !x));
                assert!(d.regs[12]);
                for j in 0..896 {
                    if j == output_port || (325..=329).contains(&j) {
                        continue;
                    }
                    assert_eq!(d.stacks[j], before.stacks[j], "stage {is_e}, port {j}");
                }
                let dirty = 5 * 2;
                let old_output = 3;
                // prepare+local restriction+finish, plus compiled halt.
                let expected_steps = 2 * dirty + 21 * n + 7 * free + 2 * old_output + 73;
                assert_eq!(steps, expected_steps as u64, "stage {is_e}, n={n}");
            }
        }
    }
}

#[test]
fn expand_caller_populates_both_ambient_masks_and_preserves_protected_ports() {
    let p = expand_caller_program().unwrap();
    let cmd = expand_caller_command().unwrap();
    assert_eq!(p.code().len(), cmd.size().unwrap() + 1);
    for n in 0..=16 {
        for seed in [0, 1, 3, 0x2aa, 0x5555, 0xffff] {
            let m = mask(n, seed);
            let free = m.iter().filter(|&&x| !x).count();
            let e = free_bits(free, seed ^ 0xa5a5);
            let u = free_bits(free, (seed ^ 0x5aaa).wrapping_mul(3));
            let mut d = p.initial([]);
            put(&mut d, 338, &m);
            put(&mut d, 834, &e.iter().rev().copied().collect::<Vec<_>>());
            put(&mut d, 835, &u.iter().rev().copied().collect::<Vec<_>>());
            put(&mut d, 857, &[true, false]);
            put(&mut d, 858, &[false, true, true]);
            for j in 325..=329 {
                put(&mut d, j, &[true, false, true]);
            }
            for (j, bits) in [
                (243, vec![false, true, true]),
                (832, vec![true]),
                (833, vec![true, false]),
                (320, vec![true]),
                (322, vec![false]),
                (895, vec![true, true]),
            ] {
                put(&mut d, j, &bits);
            }
            for i in 0..40 {
                d.regs[i] = (i + n + seed) % 4 == 0;
            }
            let before = d.clone();
            let steps = run(&p, &mut d);
            assert!(steps > 0);
            assert_eq!(get(&d, 858), expected(&m, &e), "E: n={n}, seed={seed}");
            assert_eq!(get(&d, 857), expected(&m, &u), "U: n={n}, seed={seed}");
            for j in 325..=329 {
                assert!(d.stacks[j].is_empty());
            }
            assert!(d.regs[..9].iter().all(|&x| !x));
            assert_eq!(d.regs[9..], before.regs[9..]);
            for j in 0..896 {
                if [857, 858].contains(&j) || (325..=329).contains(&j) {
                    continue;
                }
                assert_eq!(
                    d.stacks[j], before.stacks[j],
                    "port {j}, n={n}, seed={seed}"
                );
            }
        }
    }
}

#[test]
fn expansion_is_identical_to_two_standalone_physical_fill_calls() {
    let combined = expand_program().unwrap();
    let one = fill_command(true).unwrap().compiled(338, 858).unwrap();
    let two = fill_command(false).unwrap().compiled(338, 857).unwrap();
    for n in [0, 1, 2, 5, 9, 17] {
        let m = mask(n, 0x15377);
        let free = m.iter().filter(|&&x| !x).count();
        let e = free_bits(free, 0xa4b2);
        let u = free_bits(free, 0x35ad);
        let mut both = combined.initial([]);
        put(&mut both, 338, &m);
        put(&mut both, 834, &e.iter().rev().copied().collect::<Vec<_>>());
        put(&mut both, 835, &u.iter().rev().copied().collect::<Vec<_>>());
        for j in 325..=329 {
            put(&mut both, j, &[true, false]);
        }
        let mut serial = both.clone();
        run(&combined, &mut both);
        serial.pc = Some(one.entry());
        run(&one, &mut serial);
        serial.pc = Some(two.entry());
        run(&two, &mut serial);
        assert_eq!(both, serial, "n={n}");
    }
    assert_eq!(
        expand_command().unwrap().size().unwrap(),
        fill_command(true).unwrap().size().unwrap() + fill_command(false).unwrap().size().unwrap()
    );
}

#[test]
fn setup_then_install_residuals_then_expand_preserves_shared_controllers() {
    let setup = setup_caller_program().unwrap();
    let expand = expand_caller_program().unwrap();
    for n in [0, 1, 4, 8, 15] {
        let m = mask(n, 0x6495);
        let free = m.iter().filter(|&&x| !x).count();
        let e = free_bits(free, 0xac7);
        let u = free_bits(free, 0x17ba);
        let mut d = setup.initial([]);
        put(&mut d, 338, &m);
        put(&mut d, 243, &[true, true, false]);
        run(&setup, &mut d);
        assert_eq!(get(&d, 832), vec![true; free]);
        assert_eq!(get(&d, 833), vec![true, true, false]);
        put(&mut d, 834, &e.iter().rev().copied().collect::<Vec<_>>());
        put(&mut d, 835, &u.iter().rev().copied().collect::<Vec<_>>());
        d.pc = Some(expand.entry());
        run(&expand, &mut d);
        assert_eq!(get(&d, 857), expected(&m, &u));
        assert_eq!(get(&d, 858), expected(&m, &e));
        assert_eq!(get(&d, 832), vec![true; free]);
        assert_eq!(get(&d, 833), vec![true, true, false]);
    }
}

#[test]
fn capacity_failure_cannot_be_mistaken_for_a_completed_expansion() {
    let p = expand_caller_program().unwrap();
    let mut d = p.initial([]);
    put(&mut d, 338, &[false, true, false, true]);
    put(&mut d, 834, &[true, false]);
    put(&mut d, 835, &[false, true]);
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 100_000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(d.pc.is_some());
}
