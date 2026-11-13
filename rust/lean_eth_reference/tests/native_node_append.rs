//! Behavior tests for the literal NodeAppendSpace source-defined subcommands.
//! This suite does not substitute for NodeReadoutSpace or native query output.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Program, RunLimits};
use lean_eth_reference::native_node_append::{append_command, handoff_command, prepare_command};

fn put(s: &mut Config<40, 896>, port: usize, word: &[bool]) {
    s.stacks[port] = word.iter().copied().collect();
}

fn get(s: &Config<40, 896>, port: usize) -> Vec<bool> {
    s.stacks[port].iter().copied().collect()
}

fn run(p: &Program<40, 896>, s: &mut Config<40, 896>) -> u64 {
    let stats = p
        .run(
            s,
            RunLimits {
                max_steps: 200_000,
                max_stack_bits: 20_000,
            },
        )
        .unwrap();
    assert_eq!(s.pc, None);
    stats.instructions
}

fn bits(mask: usize, len: usize) -> Vec<bool> {
    (0..len).map(|i| ((mask >> i) & 1) != 0).collect()
}

#[test]
fn prepare_clears_dirty_destinations_and_preserves_source_words() {
    let p = prepare_command().unwrap().compiled(194, 39).unwrap();
    for (a, b, c) in [
        (vec![], vec![], vec![]),
        (vec![true, false, true], vec![false], vec![true, true]),
        (vec![false, false], vec![true, false], vec![]),
    ] {
        let mut s = p.initial([]);
        for port in [5, 12, 39, 89] {
            put(&mut s, port, &[false, true, false]);
        }
        put(&mut s, 194, &a);
        put(&mut s, 202, &b);
        put(&mut s, 204, &c);
        put(&mut s, 895, &[true, false, true]);
        s.regs[36] = true;
        run(&p, &mut s);
        for (port, want) in [(5, &a), (12, &b), (39, &c), (194, &a), (202, &b), (204, &c)] {
            assert_eq!(&get(&s, port), want, "stack {port}");
        }
        assert!(get(&s, 89).is_empty());
        assert_eq!(get(&s, 895), [true, false, true]);
        assert!(s.regs[36]);
    }
}

#[test]
fn append_matches_independent_concatenation_for_all_short_words() {
    let p = append_command().unwrap().compiled(862, 863).unwrap();
    for n in 0..=4 {
        for m in 0..=4 {
            for x in 0..(1usize << n) {
                for y in 0..(1usize << m) {
                    let first = bits(x, n);
                    let second = bits(y, m);
                    let mut s = p.initial([]);
                    put(&mut s, 863, &first);
                    put(&mut s, 862, &second);
                    put(&mut s, 895, &[false, true]);
                    s.regs[35] = true;
                    let executed = run(&p, &mut s);
                    let expected: Vec<bool> = first.iter().chain(second.iter()).copied().collect();
                    assert_eq!(get(&s, 863), expected, "a={first:?}, b={second:?}");
                    assert!(get(&s, 862).is_empty());
                    assert!(get(&s, 89).is_empty());
                    assert_eq!(get(&s, 895), [false, true]);
                    assert!(s.regs[35]);
                    assert_eq!(
                        executed,
                        (6 * (n + m) + 9 + 1) as u64,
                        "Lean appendCost plus compiled halt"
                    );
                }
            }
        }
    }
}

#[test]
fn handoff_replaces_dirty_destination_and_consumes_stream() {
    let p = handoff_command().unwrap().compiled(863, 265).unwrap();
    for n in 0..=6 {
        for x in 0..(1usize << n) {
            let source = bits(x, n);
            let mut s = p.initial([]);
            put(&mut s, 863, &source);
            put(&mut s, 265, &[true, false, true]);
            put(&mut s, 850, &[false, true]);
            s.regs[36] = true;
            let executed = run(&p, &mut s);
            assert_eq!(get(&s, 265), source);
            assert!(get(&s, 863).is_empty());
            assert!(get(&s, 89).is_empty());
            assert_eq!(get(&s, 850), [false, true]);
            assert!(s.regs[36]);
            assert_eq!(
                executed,
                (2 * 3 + 6 * n + 9 + 1) as u64,
                "Lean handoffCost plus compiled halt"
            );
        }
    }
}

#[test]
fn combined_prepare_append_handoff_preserves_source_order_and_protected_frame() {
    let command = lean_eth_reference::bit_program::Cmd::seq(
        prepare_command().unwrap(),
        lean_eth_reference::bit_program::Cmd::seq(
            append_command().unwrap(),
            handoff_command().unwrap(),
        ),
    );
    let p = command.compiled(194, 265).unwrap();
    let mut s = p.initial([]);
    put(&mut s, 194, &[false, true]);
    put(&mut s, 202, &[true, true, false]);
    put(&mut s, 204, &[false]);
    put(&mut s, 863, &[true, false]);
    put(&mut s, 862, &[false, true, true]);
    put(&mut s, 89, &[true, true, true]);
    put(&mut s, 265, &[true, true]);
    put(&mut s, 895, &[false, true]);
    s.regs[36] = true;
    run(&p, &mut s);
    assert_eq!(get(&s, 265), [true, false, false, true, true]);
    for port in [863, 862, 89] {
        assert!(get(&s, port).is_empty());
    }
    assert_eq!(get(&s, 5), [false, true]);
    assert_eq!(get(&s, 12), [true, true, false]);
    assert_eq!(get(&s, 39), [false]);
    assert_eq!(get(&s, 895), [false, true]);
    assert!(s.regs[36]);
}

#[test]
fn instruction_capacity_refuses_instead_of_reporting_success() {
    let p = append_command().unwrap().compiled(862, 863).unwrap();
    let mut s = p.initial([]);
    put(&mut s, 862, &[true, false]);
    put(&mut s, 863, &[false, true]);
    let error = p
        .run(
            &mut s,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 100,
            },
        )
        .unwrap_err();
    assert!(matches!(error, Error::Capacity(_)));
    assert!(s.pc.is_some(), "refusal is not a successful halt");
}
