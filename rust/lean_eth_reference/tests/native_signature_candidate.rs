//! Differential acceptance for the literal predecessor-rescan program.
//! Independent Rust arithmetic here is only an oracle for the *finite machine*;
//! production invokes no Rust-side scalar signatures or predecessor loops.

use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_signature_candidate::{
    candidate_program, countdown_advance, countdown_test, predecessor_increment, probe_program,
    ripple_program, tuple_candidate_machine, zero_program,
};

fn bits(value: u64, n: usize) -> Vec<bool> {
    (0..n).map(|i| value & (1 << i) != 0).collect()
}
fn value(word: &[bool]) -> u64 {
    word.iter()
        .enumerate()
        .fold(0, |acc, (i, b)| acc | ((*b as u64) << i))
}
fn frame(word: &[bool]) -> Vec<bool> {
    word.iter()
        .flat_map(|b| [true, *b])
        .chain([false])
        .collect()
}
fn words(items: &[Vec<bool>]) -> Vec<bool> {
    items.iter().flat_map(|x| frame(x)).collect()
}
fn serialized_matrix(rows: &[Vec<Vec<bool>>]) -> Vec<bool> {
    words(&rows.iter().map(|row| words(row)).collect::<Vec<_>>())
}
fn key(w: u64, rows: &[Vec<Vec<bool>>], bits: &[bool]) -> Vec<bool> {
    let mut k = Vec::new();
    for row in rows {
        assert_eq!(row.len(), bits.len());
        let n: u64 = 1 + row
            .iter()
            .zip(bits)
            .map(|(c, b)| if *b { value(c) } else { w })
            .sum::<u64>();
        let canonical = bits_of_positive(n);
        let mut part = frame(&canonical);
        part.extend(k);
        k = part;
    }
    k
}
fn bits_of_positive(value: u64) -> Vec<bool> {
    assert!(value > 0);
    bits(value, (64 - value.leading_zeros()) as usize)
}
fn put<const R: usize, const S: usize>(c: &mut Config<R, S>, i: usize, word: &[bool]) {
    c.stacks[i] = word.iter().copied().collect();
}
fn get<const R: usize, const S: usize>(c: &Config<R, S>, i: usize) -> Vec<bool> {
    c.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, c: &mut Config<R, S>) -> u64 {
    c.pc = Some(p.entry());
    let stats = p
        .run(
            c,
            RunLimits {
                max_steps: 6_000_000,
                max_stack_bits: 200_000,
            },
        )
        .unwrap();
    assert_eq!(c.pc, None);
    stats.instructions
}
fn run_candidate<const R: usize, const S: usize>(
    p: &Program<R, S>,
    ports: [usize; 24],
    regs: [usize; 16],
    offset: (u64, usize),
    rows: &[Vec<Vec<bool>>],
    assignment_info: (usize, u64),
) -> (Config<R, S>, u64) {
    let (w, w_width) = offset;
    let (h, candidate) = assignment_info;
    let assignment = bits(candidate, h);
    let mut s = p.initial([]);
    put(&mut s, ports[0], &bits(w, w_width));
    put(&mut s, ports[15], &serialized_matrix(rows));
    put(&mut s, ports[16], &assignment);
    put(&mut s, ports[18], &vec![false; h]);
    put(&mut s, ports[22], &[false]); // poison prior freshness
    s.regs[regs[4]] = true; // poison prior key match
    s.regs[regs[15]] = true; // poison countdown guard
    let original_w = get(&s, ports[0]);
    let original_rows = get(&s, ports[15]);
    let steps = run(p, &mut s);
    assert_eq!(get(&s, ports[0]), original_w);
    assert_eq!(get(&s, ports[15]), original_rows);
    assert_eq!(get(&s, ports[16]), assignment);
    assert_eq!(get(&s, ports[17]), key(w, rows, &assignment));
    let expected_fresh =
        (0..candidate).all(|i| key(w, rows, &bits(i, h)) != key(w, rows, &assignment));
    assert_eq!(
        get(&s, ports[22]),
        [expected_fresh],
        "h={h}, candidate={candidate}"
    );
    assert_eq!(get(&s, ports[18]), vec![false; h]);
    for i in [1usize, 3, 4, 5, 12, 13, 14, 19, 20, 21, 23] {
        assert!(
            get(&s, ports[i]).is_empty(),
            "local scratch {i} not released"
        );
    }
    assert!(steps > 10, "full predicate must execute fixed-control code");
    (s, steps)
}

#[test]
fn literal_ripple_and_zero_programs_are_exact_fixed_tables() {
    let z = zero_program().unwrap();
    assert_eq!(z.code().len(), 10);
    for carry in [false, true] {
        let p = ripple_program(carry).unwrap();
        assert_eq!(p.code().len(), 11);
        for h in 0..=5 {
            for n in 0..1u64 << h {
                let mut s = p.initial(bits(n, h));
                s.regs[2] = true; // independent from flag
                run(&p, &mut s);
                let expected = if carry {
                    (n + 1) % (1u64 << h).max(1)
                } else {
                    n.wrapping_sub(1) % (1u64 << h).max(1)
                };
                if carry && n == (1u64 << h).saturating_sub(1) {
                    continue;
                }
                if !carry && n == 0 {
                    continue;
                }
                assert_eq!(value(&get(&s, 0)), expected, "h={h}, n={n}, carry={carry}");
                assert!(get(&s, 1).is_empty());
            }
        }
    }
    for h in 0..=5 {
        for n in 0..1u64 << h {
            let mut s = z.initial(bits(n, h));
            let original = get(&s, 0);
            run(&z, &mut s);
            assert_eq!(s.regs[2], n == 0);
            assert_eq!(get(&s, 0), original);
            assert!(get(&s, 1).is_empty());
        }
    }
}

#[test]
fn counter_operations_preserve_word_width_and_inject_same_ports() {
    let increment = predecessor_increment().unwrap().compiled(18, 18).unwrap();
    let test = countdown_test().unwrap().compiled(19, 19).unwrap();
    let advance = countdown_advance().unwrap().compiled(19, 19).unwrap();
    for h in 1..=5 {
        for n in 1..1u64 << h {
            let mut s = advance.initial([]);
            put(&mut s, 19, &bits(n, h));
            run(&advance, &mut s);
            assert_eq!(get(&s, 19), bits(n - 1, h));
            assert_eq!(s.regs[15], n > 1);
            assert!(get(&s, 20).is_empty());
        }
    }
    let mut z = test.initial([]);
    put(&mut z, 19, &[false, false, false]);
    run(&test, &mut z);
    assert!(!z.regs[15]);
    assert_eq!(get(&z, 19), [false, false, false]);
    let mut s = increment.initial([]);
    put(&mut s, 18, &[true, false, true]);
    run(&increment, &mut s);
    assert_eq!(get(&s, 18), [false, true, true]);
}

#[test]
fn complete_candidate_rescan_matches_independent_arithmetic_and_duplicate_oracle() {
    let p = candidate_program().unwrap();
    let ports = std::array::from_fn(|i| i);
    let regs = std::array::from_fn(|i| i);
    let empty_rows: Vec<Vec<Vec<bool>>> = vec![];
    run_candidate(&p, ports, regs, (0, 1), &empty_rows, (0, 0));
    for candidate in 0..4 {
        run_candidate(&p, ports, regs, (0, 1), &empty_rows, (2, candidate));
    }
    let equal = vec![vec![bits(1, 2), bits(1, 2)]];
    for candidate in 0..4 {
        run_candidate(&p, ports, regs, (0, 1), &equal, (2, candidate));
    }
    let injective = vec![vec![bits(1, 2), bits(2, 2)]];
    for candidate in 0..4 {
        run_candidate(&p, ports, regs, (0, 1), &injective, (2, candidate));
    }
    let two_rows = vec![vec![bits(2, 3), bits(1, 3)], vec![bits(1, 2), bits(3, 2)]];
    for candidate in 0..4 {
        run_candidate(&p, ports, regs, (1, 2), &two_rows, (2, candidate));
    }
    let three = vec![vec![bits(0, 2), bits(1, 2), bits(2, 2)]];
    for candidate in 0..8 {
        run_candidate(&p, ports, regs, (0, 1), &three, (3, candidate));
    }
}

#[test]
fn full_candidate_does_not_depend_on_old_regs_and_leaves_root_frame_untouched() {
    let p = candidate_program().unwrap();
    let mut s = p.initial([]);
    for i in 0..16 {
        s.regs[i] = i % 2 == 0;
    }
    put(&mut s, 0, &[true]);
    put(&mut s, 15, &serialized_matrix(&[vec![bits(3, 2)]]));
    put(&mut s, 16, &[true]);
    put(&mut s, 18, &[false]);
    put(&mut s, 22, &[false]);
    run(&p, &mut s);
    assert_eq!(get(&s, 22), [true]);
    assert_eq!(get(&s, 16), [true]);
    assert_eq!(get(&s, 18), [false]);
    assert!(get(&s, 20).is_empty());
    assert!(get(&s, 21).is_empty());
}

#[test]
fn physical_40x896_candidate_lift_preserves_unmapped_caller_stacks() {
    let p = tuple_candidate_machine().unwrap();
    let ports = lean_eth_reference::native_signature_rescan::RESCAN_STACKS;
    let regs = std::array::from_fn(|i| i);
    let rows = vec![vec![bits(1, 2), bits(1, 2)]];
    let (out, _) = run_candidate(&p, ports, regs, (0, 1), &rows, (2, 2));
    assert!(get(&out, 895).is_empty()); // this fixture starts with no sentinel
    for v in 0..3 {
        let mut physical = p.initial([]);
        put(&mut physical, 141, &[true]);
        put(&mut physical, 847, &serialized_matrix(&rows));
        put(&mut physical, 838, &bits(v, 2));
        put(&mut physical, 844, &[false, false]);
        put(&mut physical, 362, &[true]);
        put(&mut physical, 895, &[true, false, true]);
        physical.regs[33] = true;
        run(&p, &mut physical);
        assert_eq!(get(&physical, 895), [true, false, true]);
        assert!(physical.regs[33]);
        assert_eq!(get(&physical, 838), bits(v, 2));
    }
}

#[test]
fn physical_probe_uses_complete_remaining_word_and_real_predecessor_signature() {
    let p = probe_program().unwrap();
    let rows = vec![vec![bits(1, 2), bits(1, 2)]];
    for (candidate, available, fresh) in [
        (0u64, true, true),
        (1, true, true),
        (2, true, false),
        (3, true, true),
        (2, false, false),
    ] {
        let mut s = p.initial([]);
        put(&mut s, 141, &[false]);
        put(&mut s, 847, &serialized_matrix(&rows));
        put(&mut s, 838, &bits(candidate, 2));
        put(&mut s, 844, &[false, false]);
        put(
            &mut s,
            843,
            &if available {
                vec![false, true, false]
            } else {
                vec![false, false, false]
            },
        );
        put(&mut s, 362, &[!fresh]);
        s.regs[39] = false;
        s.regs[38] = !available;
        put(&mut s, 895, &[true, true, false]);
        run(&p, &mut s);
        assert_eq!(s.regs[38], available);
        assert_eq!(
            get(&s, 843),
            if available {
                vec![false, true, false]
            } else {
                vec![false, false, false]
            }
        );
        assert_eq!(get(&s, 895), [true, true, false]);
        if available {
            assert_eq!(s.regs[39], fresh);
            assert_eq!(get(&s, 362), [fresh]);
        } else {
            assert!(!s.regs[39]);
            assert_eq!(get(&s, 362), [!fresh]);
            assert!(get(&s, 839).is_empty());
        }
    }
}

#[test]
fn physical_probe_preserves_registers_and_rejects_large_budget() {
    let p = probe_program().unwrap();
    let mut s = p.initial([]);
    put(&mut s, 843, &[false, false, false, true]);
    put(&mut s, 838, &[true, true, true]);
    put(&mut s, 844, &[false, false, false]);
    put(&mut s, 362, &[false]);
    s.regs[37] = true;
    s.regs[34] = true;
    let e = p
        .run(
            &mut s,
            RunLimits {
                max_steps: 75,
                max_stack_bits: 10000,
            },
        )
        .unwrap_err();
    assert!(matches!(e, lean_eth_reference::Error::Capacity(_)));
    assert!(s.pc.is_some());
    assert!(s.regs[37]);
    assert!(s.regs[34]);
}

#[test]
fn budget_refusal_is_reported_instead_of_partial_truth() {
    let p = candidate_program().unwrap();
    let mut s = p.initial([]);
    put(&mut s, 0, &[false]);
    put(&mut s, 16, &[true, true, true]);
    put(&mut s, 18, &[false, false, false]);
    put(&mut s, 22, &[true]);
    let err = p
        .run(
            &mut s,
            RunLimits {
                max_steps: 10,
                max_stack_bits: 50_000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, lean_eth_reference::Error::Capacity(_)));
    assert!(s.pc.is_some());
}
