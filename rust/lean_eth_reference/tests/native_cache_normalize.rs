//! Independent finite input/width oracle for the source's 12-label pad/clear/transfer.
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::native_cache_normalize::{
    COMPONENT_PORTS, expected_compiled_steps, flat_program, normalize_component_program,
    normalize_program,
};
use std::collections::VecDeque;

fn bits(n: usize, len: usize) -> Vec<bool> {
    (0..len).map(|i| n & (1 << i) != 0).collect()
}
fn read<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn put<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, word: &[bool]) {
    d.stacks[port] = VecDeque::from(word.to_vec());
}
fn padded(width: usize, word: &[bool]) -> Vec<bool> {
    (0..width)
        .map(|i| word.get(i).copied().unwrap_or(false))
        .collect()
}

#[test]
fn exact_source_table_and_port_lifting() {
    let code = normalize_program().unwrap();
    assert_eq!(code.code().len(), 12);
    assert_eq!(code.entry(), 0);
    assert_eq!(COMPONENT_PORTS, [0, 4, 5, 6, 7, 2, 8, 3]);
    assert_eq!(
        code.code()[4],
        lean_eth_reference::bit_program::Instr::Goto { next: 5 }
    );
    assert_eq!(
        code.code()[7],
        lean_eth_reference::bit_program::Instr::Goto { next: 8 }
    );
    assert!(matches!(
        code.code()[11],
        lean_eth_reference::bit_program::Instr::Halt
    ));
}

#[test]
fn full_component_exhaustive_width_and_input_values_with_dirty_output() {
    let program = normalize_component_program().unwrap();
    for width in 0..=8 {
        for length in 0..=8 {
            for value in 0..(1usize << length) {
                let word = bits(value, length);
                let mut d = program.initial(Vec::<bool>::new());
                let prior = vec![true, false, true];
                put(&mut d, 0, &word);
                put(&mut d, 1, &vec![true; width]);
                put(&mut d, 2, &prior);
                d.regs[6] = true;
                d.regs[7] = true;
                let steps = program
                    .run(&mut d, RunLimits::default())
                    .unwrap()
                    .instructions;
                assert_eq!(
                    steps,
                    expected_compiled_steps(width, length).unwrap(),
                    "width={width}, length={length}, value={value}"
                );
                assert_eq!(read(&d, 0), Vec::<bool>::new());
                assert_eq!(read(&d, 1), vec![true; width]);
                let mut expected = padded(width, &word);
                expected.reverse();
                expected.extend(prior);
                assert_eq!(
                    read(&d, 2),
                    expected,
                    "width={width}, length={length}, value={value}"
                );
                for port in 3..9 {
                    assert!(d.stacks[port].is_empty(), "work port {port}");
                }
                assert!(d.regs[6] && d.regs[7]);
            }
        }
    }
}

#[test]
fn normalizer_preserves_opaque_modulus_and_refuses_insufficient_budget() {
    let program = normalize_program().unwrap();
    let mut d = program.initial([true, false, true, false, true]);
    put(&mut d, 7, &[true, false]);
    put(&mut d, 5, &[true, true, false]);
    let initial = d.clone();
    let result = program.run(
        &mut d,
        RunLimits {
            max_steps: 1,
            ..RunLimits::default()
        },
    );
    assert!(result.is_err());
    assert_ne!(d.pc, None);
    let mut d = initial;
    let stats = program.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 7 * 2 + 2 * 3 + 9);
    assert_eq!(read(&d, 0), vec![true, false]);
    assert_eq!(read(&d, 5), vec![true, true, false]);
    assert!(d.stacks[7].is_empty());
}

fn frame(bits: &[bool]) -> Vec<bool> {
    let mut result = Vec::new();
    for &bit in bits {
        result.extend([true, bit]);
    }
    result.push(false);
    result
}
fn pair_encoding(words: &[Vec<bool>]) -> Vec<bool> {
    let mut out = Vec::new();
    for word in words {
        out.push(true);
        let mut reversed = word.clone();
        reversed.reverse();
        out.extend(frame(&reversed));
        out.extend(frame(&[]));
    }
    out.push(false);
    out
}
#[test]
fn complete_flat_program_parses_and_normalizes_real_framed_rows() {
    let program = flat_program().unwrap();
    for width in 0..=6 {
        for count in 0..=4 {
            for seed in 0usize..16 {
                let words: Vec<_> = (0..count)
                    .map(|i| {
                        let len = (seed + i) % 5;
                        bits((seed * 7 + i * 5) & ((1 << len) - 1), len)
                    })
                    .collect();
                let input = pair_encoding(&words);
                let mut d = program.initial(input);
                put(&mut d, 18, &vec![true; width]);
                d.regs[5] = true;
                let stats = program.run(&mut d, RunLimits::default()).unwrap();
                assert!(stats.instructions > 0);
                assert!(d.pc.is_none());
                assert!(d.regs[5]);
                let expected: Vec<_> = words.iter().flat_map(|w| padded(width, w)).collect();
                assert_eq!(
                    read(&d, 0),
                    expected,
                    "width={width} count={count} seed={seed}"
                );
                assert_eq!(read(&d, 1), vec![false; width * count]);
                assert_eq!(read(&d, 18), vec![true; width]);
                assert_eq!(read(&d, 15), Vec::<bool>::new());
                for i in 2..18 {
                    assert!(d.stacks[i].is_empty(), "stale work {i}");
                }
            }
        }
    }
}
