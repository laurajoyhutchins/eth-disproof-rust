//! Independent numeric oracles validate the pinned finite bit-machine
//! tables; no host arithmetic is used inside the production programs.
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_signature_arithmetic::{
    attained_key_program, canonical_row_program, choice_add_program, dot_step_program, row_program,
};
use lean_eth_reference::native_signature_key::rescan_key_call;

fn set<const R: usize, const S: usize>(s: &mut Config<R, S>, at: usize, data: &[bool]) {
    s.stacks[at] = data.iter().copied().collect();
}
fn get<const R: usize, const S: usize>(s: &Config<R, S>, at: usize) -> Vec<bool> {
    s.stacks[at].iter().copied().collect()
}
fn bits(n: u64, width: usize) -> Vec<bool> {
    (0..width).map(|bit| (n >> bit) & 1 != 0).collect()
}
fn value(bits: &[bool]) -> u128 {
    bits.iter().enumerate().fold(
        0u128,
        |acc, (i, b)| {
            if *b { acc + (1u128 << i) } else { acc }
        },
    )
}
fn canon(n: u64) -> Vec<bool> {
    assert!(n > 0);
    bits(n, (64 - n.leading_zeros()) as usize)
}
fn frame(payload: &[bool]) -> Vec<bool> {
    payload
        .iter()
        .flat_map(|&b| [true, b])
        .chain([false])
        .collect()
}
fn words(records: &[Vec<bool>]) -> Vec<bool> {
    records.iter().flat_map(|record| frame(record)).collect()
}
fn matrix(rows: &[Vec<Vec<bool>>]) -> Vec<bool> {
    words(&rows.iter().map(|row| words(row)).collect::<Vec<_>>())
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, s: &mut Config<R, S>) -> u64 {
    s.pc = Some(p.entry());
    let t = p
        .run(
            s,
            RunLimits {
                max_steps: 4_000_000,
                max_stack_bits: 200_000,
            },
        )
        .unwrap();
    assert!(s.pc.is_none());
    t.instructions
}

#[test]
fn choice_add_exhaustive_small_operands_and_both_bit_branches() {
    let p = choice_add_program().unwrap();
    for left in 0..16u64 {
        for right in 0..16u64 {
            for w in 0..2 {
                for widths in [(4, 4, 4), (6, 3, 5), (2, 6, 8)] {
                    let mut s = p.initial([]);
                    let x = bits(left, widths.2);
                    let z = bits(right, widths.1);
                    let offset = bits(9, widths.0);
                    set(&mut s, 0, &offset);
                    set(&mut s, 1, &z);
                    set(&mut s, 2, &x);
                    s.regs[0] = w == 1;
                    run(&p, &mut s);
                    assert_eq!(
                        value(&get(&s, 3)),
                        value(&x) + if w == 1 { value(&z) } else { value(&offset) },
                        "left={left} right={right} bit={w}"
                    );
                    assert_eq!(get(&s, 0), offset);
                    assert_eq!(get(&s, 1), z);
                    assert_eq!(get(&s, 2), x);
                    for i in 4..=8 {
                        assert!(get(&s, i).is_empty(), "nonempty scratch stack {i}");
                    }
                }
            }
        }
    }
}

#[test]
fn choice_add_uses_real_adder_instead_of_a_host_integer_operation() {
    let p = choice_add_program().unwrap();
    assert_eq!(
        p.code().len(),
        70,
        "source finite size: two 34-label addAt branches, branch and halt"
    );
    assert!(
        p.code()
            .iter()
            .any(|i| matches!(i, lean_eth_reference::bit_program::Instr::Xor { .. }))
    );
    assert!(
        p.code()
            .iter()
            .any(|i| matches!(i, lean_eth_reference::bit_program::Instr::And { .. }))
    );
}

#[test]
fn dot_step_consumes_one_framed_coefficient_and_assignment_bit() {
    let p = dot_step_program().unwrap();
    for bit in [false, true] {
        let mut s = p.initial([]);
        set(&mut s, 0, &bits(3, 3));
        set(
            &mut s,
            9,
            &[frame(&bits(12, 4)), frame(&bits(7, 3))].concat(),
        );
        set(&mut s, 10, &[bit, true]);
        set(&mut s, 2, &bits(5, 3));
        run(&p, &mut s);
        assert_eq!(value(&get(&s, 2)), 5 + if bit { 12 } else { 3 });
        assert_eq!(get(&s, 9), frame(&bits(7, 3)));
        assert_eq!(get(&s, 10), [true]);
        assert_eq!(get(&s, 0), bits(3, 3));
        for i in 1..=8 {
            if i != 2 {
                assert!(get(&s, i).is_empty(), "scratch {i}");
            }
        }
        assert!(get(&s, 11).is_empty());
    }
}

#[test]
fn canonical_row_handles_empty_row_and_zero_offset() {
    let p = canonical_row_program().unwrap();
    for offset in [0u64, 1, 6] {
        let mut s = p.initial([]);
        set(&mut s, 0, &bits(offset, 4));
        set(&mut s, 2, &[true]); // source canonicalRow initializer, value 1
        run(&p, &mut s);
        assert_eq!(get(&s, 2), [true]);
        assert_eq!(get(&s, 0), bits(offset, 4));
        for k in 1..12 {
            if k != 2 {
                assert!(get(&s, k).is_empty(), "scratch {k}");
            }
        }
    }
}

#[test]
fn canonical_row_matches_independent_sum_over_assignment_bits() {
    let p = canonical_row_program().unwrap();
    for width in 1..=4usize {
        for mask in 0..(1u64 << width) {
            for w in [0u64, 2, 7] {
                let coeffs: Vec<_> = (0..width).map(|i| (3 * i as u64 + mask + 2) % 13).collect();
                let row: Vec<Vec<bool>> = coeffs.iter().map(|&c| bits(c, 5)).collect();
                let mut s = p.initial([]);
                set(&mut s, 0, &bits(w, 4));
                set(&mut s, 9, &words(&row));
                set(&mut s, 10, &bits(mask, width));
                set(&mut s, 2, &[true]);
                run(&p, &mut s);
                let expected = 1
                    + (0..width)
                        .map(|i| if (mask >> i) & 1 == 1 { coeffs[i] } else { w })
                        .sum::<u64>();
                assert_eq!(
                    get(&s, 2),
                    canon(expected),
                    "width={width} mask={mask} W={w}"
                );
                assert_eq!(get(&s, 0), bits(w, 4));
                for k in 1..12 {
                    if k != 2 {
                        assert!(get(&s, k).is_empty(), "scratch={k}");
                    }
                }
            }
        }
    }
}

#[test]
fn raw_row_program_preserves_untrimmed_arithmetic_and_consumes_assignment() {
    let p = row_program().unwrap();
    let mut s = p.initial([]);
    set(&mut s, 0, &bits(4, 5));
    set(&mut s, 9, &words(&[bits(6, 4), bits(9, 5)]));
    set(&mut s, 10, &[true, false]);
    set(&mut s, 2, &[true]);
    run(&p, &mut s);
    assert_eq!(value(&get(&s, 2)), 1 + 6 + 4);
    assert!(get(&s, 9).is_empty());
    assert!(get(&s, 10).is_empty());
}

#[test]
fn full_attained_signature_key_matches_reverse_row_record_order() {
    let p = attained_key_program().unwrap();
    let rows = vec![
        vec![bits(8, 5), bits(2, 5)],
        vec![bits(3, 5), bits(9, 5)],
        vec![bits(7, 5), bits(4, 5)],
    ];
    let assignment = [true, false];
    let offset = 6;
    let mut s = p.initial([]);
    set(&mut s, 0, &bits(offset, 5));
    set(&mut s, 12, &assignment);
    set(&mut s, 15, &matrix(&rows));
    run(&p, &mut s);
    let values = rows
        .iter()
        .map(|r| 1 + value(&r[0]) as u64 + offset)
        .collect::<Vec<_>>();
    let expected = words(&values.iter().rev().map(|&v| canon(v)).collect::<Vec<_>>());
    assert_eq!(get(&s, 14), expected);
    assert_eq!(get(&s, 15), matrix(&rows));
    assert_eq!(get(&s, 12), assignment);
    assert!(get(&s, 13).is_empty());
}

#[test]
fn actual_rescan_key_call_produces_source_signature_in_local_bank() {
    let row = canonical_row_program().unwrap();
    let p = rescan_key_call(&row).unwrap().compiled(12, 14).unwrap();
    let rows = vec![vec![bits(1, 3), bits(5, 3)], vec![bits(3, 3), bits(7, 3)]];
    let mut s = p.initial([]);
    set(&mut s, 0, &bits(2, 2));
    set(&mut s, 12, &[false, true]);
    set(&mut s, 15, &matrix(&rows));
    set(&mut s, 16, &[false, true]);
    set(&mut s, 17, &[true, false, true]);
    run(&p, &mut s);
    let expected = words(&[canon(1 + 2 + 7), canon(1 + 2 + 5)]);
    assert_eq!(get(&s, 14), expected);
    assert_eq!(get(&s, 16), [false, true]);
    assert_eq!(get(&s, 17), [true, false, true]);
    assert_eq!(get(&s, 15), matrix(&rows));
}

#[test]
fn insufficient_budget_is_explicit_not_a_fake_halt() {
    let p = attained_key_program().unwrap();
    let mut s = p.initial([]);
    set(&mut s, 0, &bits(2, 2));
    set(&mut s, 12, &[true]);
    set(&mut s, 15, &matrix(&[vec![bits(3, 2)]]));
    let error = p
        .run(
            &mut s,
            RunLimits {
                max_steps: 7,
                max_stack_bits: 99999,
            },
        )
        .unwrap_err();
    assert!(matches!(error, lean_eth_reference::Error::Capacity(_)));
    assert!(s.pc.is_some());
}

#[test]
fn very_long_carry_is_propagated_by_the_real_finite_adder() {
    let p = choice_add_program().unwrap();
    let mut s = p.initial([]);
    set(&mut s, 0, &[false]);
    set(&mut s, 1, &[true]);
    set(&mut s, 2, &[true; 96]);
    s.regs = [true; 8];
    run(&p, &mut s);
    let want: Vec<bool> = std::iter::repeat_n(false, 96).chain([true]).collect();
    assert_eq!(get(&s, 3), want);
    for i in 4..=8 {
        assert!(get(&s, i).is_empty());
    }
}

#[test]
fn arbitrary_non_selector_registers_do_not_affect_choice_add_output() {
    let p = choice_add_program().unwrap();
    for mask in 0..256u16 {
        let mut s = p.initial([]);
        s.regs = std::array::from_fn(|i| (mask >> i) & 1 == 1);
        set(&mut s, 0, &bits(13, 6));
        set(&mut s, 1, &bits(25, 6));
        set(&mut s, 2, &bits(7, 5));
        let expected = 7 + if s.regs[0] { 25 } else { 13 };
        run(&p, &mut s);
        assert_eq!(value(&get(&s, 3)), expected);
    }
}
