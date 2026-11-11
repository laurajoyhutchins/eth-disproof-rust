//! These are original OpenAI source instructions, not synthetic fixtures.
//! Source blob identities are verified by tools/extract_original_lean_tables.py.
//! The generated functions execute the original finite machine steps directly.
use lean_eth_reference::bit_program::{Config, RunLimits};
use std::array;
use std::collections::VecDeque;

mod add {
    include!(concat!(env!("OUT_DIR"), "/original_binary-add.rs"));
}
mod parity {
    include!(concat!(env!("OUT_DIR"), "/original_query-parity.rs"));
}
mod type_bit {
    include!(concat!(env!("OUT_DIR"), "/original_type-bit.rs"));
}

fn config<const R: usize, const S: usize>(entry: usize) -> Config<R, S> {
    Config {
        pc: Some(entry),
        regs: [false; R],
        stacks: array::from_fn(|_| VecDeque::new()),
    }
}

fn little_endian(mut n: usize) -> Vec<bool> {
    let mut out = Vec::new();
    while n != 0 {
        out.push(n & 1 != 0);
        n >>= 1;
    }
    out
}

#[test]
fn original_binary_adder_compiles_to_executable_rust() {
    assert_eq!(
        (add::LABELS, add::INPUT_STACK, add::OUTPUT_STACK),
        (13, 0, 2)
    );
    for x in 0..128 {
        for y in 0..128 {
            let mut c = config::<8, 3>(add::ENTRY);
            c.stacks[0].extend(little_endian(x));
            c.stacks[1].extend(little_endian(y));
            let stats = add::run(&mut c, RunLimits::default()).unwrap();
            let observed = c.stacks[2]
                .iter()
                .rev()
                .enumerate()
                .fold(0usize, |acc, (i, bit)| acc | (usize::from(*bit) << i));
            assert_eq!(observed, x + y, "original add {x} + {y}");
            assert!(c.pc.is_none());
            assert!(c.stacks[0].is_empty() && c.stacks[1].is_empty());
            assert!(stats.instructions > 0);
        }
    }
}

#[test]
fn original_query_parity_matches_all_short_bit_words() {
    assert_eq!(
        (parity::LABELS, parity::INPUT_STACK, parity::OUTPUT_STACK),
        (4, 0, 0)
    );
    for n in 0..9 {
        for mask in 0..(1usize << n) {
            for initial in [false, true] {
                let bits: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 != 0).collect();
                let mut c = config::<3, 1>(parity::ENTRY);
                c.regs[2] = initial;
                c.stacks[0].extend(bits.iter().copied());
                let stats = parity::run(&mut c, RunLimits::default()).unwrap();
                assert_eq!(c.regs[2], bits.iter().fold(initial, |b, bit| b ^ bit));
                assert!(c.stacks[0].is_empty() && c.pc.is_none());
                assert_eq!(stats.instructions, (3 * n + 3) as u64);
            }
        }
    }
}

#[test]
fn original_type_bit_routine_reads_by_index_and_cleans_stacks() {
    assert_eq!(
        (
            type_bit::LABELS,
            type_bit::INPUT_STACK,
            type_bit::OUTPUT_STACK
        ),
        (7, 1, 1)
    );
    for n in 0..7 {
        for mask in 0..(1usize << n) {
            let bits: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 != 0).collect();
            for index in 0..(n + 3) {
                let mut c = config::<3, 2>(type_bit::ENTRY);
                c.stacks[0].extend(std::iter::repeat_n(false, index));
                c.stacks[1].extend(bits.iter().copied());
                type_bit::run(&mut c, RunLimits::default()).unwrap();
                assert_eq!(c.regs[2], bits.get(index).copied().unwrap_or(false));
                assert!(!c.regs[0]);
                assert!(!c.regs[1]);
                assert!(c.stacks.iter().all(VecDeque::is_empty));
                assert!(c.pc.is_none());
            }
        }
    }
}

#[test]
fn original_binary_add_refuses_before_excess_stack_push() {
    let mut c = config::<8, 3>(add::ENTRY);
    c.stacks[0].extend([true, true]);
    c.stacks[1].extend([true, false]);
    let initial = c.clone();
    assert!(
        add::run(
            &mut c,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 4
            }
        )
        .is_err()
    );
    assert_eq!(c.pc, Some(1));
    assert_ne!(c, initial);
}
