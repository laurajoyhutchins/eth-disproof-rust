//! Machine-trace tests for the physical source tuple increment and loop.
//! The expected assignments use an independent integer-to-tuple model, not
//! the Rust implementation of `bump_words` under test.

use std::collections::VecDeque;

use lean_eth_reference::bit_program::{Atom, Cmd, Config, RunLimits};
use lean_eth_reference::native_tuple::{
    CounterPorts, HIGH_QUERY_PORTS, bump_word, bump_words, encode_words, enumerate_command,
    high_loop_command, increment_command, odometer_program,
};

fn bits<const R: usize, const S: usize>(state: &Config<R, S>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}

fn shape_word(lengths: &[usize], mut rank: usize) -> Vec<Vec<bool>> {
    lengths
        .iter()
        .map(|&length| {
            (0..length)
                .map(|_| {
                    let bit = rank & 1 == 1;
                    rank >>= 1;
                    bit
                })
                .collect()
        })
        .collect()
}

#[test]
fn physical_odometer_agrees_with_independent_tuple_arithmetic() {
    let machine = odometer_program().unwrap();
    assert_eq!(machine.code().len(), 18);
    for shape in [
        vec![],
        vec![0],
        vec![1],
        vec![2],
        vec![1, 1],
        vec![0, 2],
        vec![2, 0],
        vec![1, 2],
        vec![2, 1],
        vec![1, 0, 2],
    ] {
        let total: usize = shape.iter().sum();
        for rank in 0..(1 << total) {
            let words = shape_word(&shape, rank);
            let input = encode_words(&words).unwrap();
            let mut state = machine.initial(input);
            state.regs = [true, true, false];
            let report = machine.run(&mut state, RunLimits::default()).unwrap();
            assert!(report.instructions > 0);
            assert_eq!(
                bits(&state, 0),
                encode_words(&shape_word(&shape, (rank + 1) % (1 << total))).unwrap()
            );
            assert!(state.stacks[1].is_empty());
            assert_eq!(state.regs, [false, false, rank + 1 == 1 << total]);
            assert!(state.pc.is_none());
            let (carry, bumped) = bump_words(&words);
            assert_eq!(carry, rank + 1 == 1 << total);
            assert_eq!(bumped, shape_word(&shape, (rank + 1) % (1 << total)));
        }
    }
}

#[test]
fn fixed_width_word_carry_and_zero_width_cases() {
    for width in 0..=7 {
        for rank in 0..(1 << width) {
            let bits = shape_word(&[width], rank).remove(0);
            let (carry, next) = bump_word(&bits);
            assert_eq!(carry, rank + 1 == 1 << width);
            assert_eq!(
                next,
                shape_word(&[width], (rank + 1) % (1 << width)).remove(0)
            );
        }
    }
    assert_eq!(encode_words(&[]).unwrap(), [false]);
    assert_eq!(encode_words(&[vec![]]).unwrap(), [true, false, false]);
}

#[test]
fn actual_enumerator_visits_every_assignment_and_pays_overflow() {
    const PORTS: CounterPorts = CounterPorts {
        registers: [0, 1, 2],
        counter: 0,
        scratch: 1,
    };
    // A real compiled callback, observing each visit by appending one bit
    // to an unrelated stack. This is not a SAT residual-query replacement.
    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 3,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 2, src: 3 }),
    );
    let program = enumerate_command::<4, 3>(PORTS, callback.clone())
        .unwrap()
        .compiled(0, 0)
        .unwrap();
    assert_eq!(program.code().len(), callback.size().unwrap() + 22);
    for shape in [
        vec![],
        vec![0],
        vec![1],
        vec![2],
        vec![1, 1],
        vec![0, 2],
        vec![2, 0],
        vec![1, 2],
        vec![2, 1],
        vec![1, 0, 2],
    ] {
        let width: usize = shape.iter().sum();
        let expected_visits = 1 << width;
        let initial = encode_words(
            &shape
                .iter()
                .map(|&size| vec![false; size])
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let mut state = program.initial(initial.clone());
        let mut observations = Vec::new();
        let mut steps = 0;
        while state.pc.is_some() {
            assert!(steps < 10_000, "unexpected loop");
            if state.pc == Some(2) {
                // callback's first concrete site
                observations.push(bits(&state, 0));
                assert!(state.stacks[1].is_empty());
                assert!(state.regs[2]);
            }
            program.step(&mut state).unwrap();
            steps += 1;
        }
        assert_eq!(observations.len(), expected_visits, "shape={shape:?}");
        for (index, observed) in observations.iter().enumerate() {
            assert_eq!(observed, &encode_words(&shape_word(&shape, index)).unwrap());
        }
        assert_eq!(bits(&state, 0), initial, "final overflow wraps to zero");
        assert!(state.stacks[1].is_empty());
        assert_eq!(bits(&state, 2).len(), expected_visits);
        assert!(bits(&state, 2).iter().all(|bit| *bit));
        assert!(!state.regs[2]);
        assert_eq!(
            steps,
            program
                .run(&mut program.initial(initial), RunLimits::default())
                .unwrap()
                .instructions as usize
        );
    }
}

#[test]
fn high_query_physical_port_mapping_and_unrelated_state_are_preserved() {
    let body = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 22,
            value: true,
        }),
        Cmd::Atom(Atom::Push {
            stack: 600,
            src: 22,
        }),
    );
    let program = high_loop_command(body).unwrap().compiled(789, 789).unwrap();
    let mut state = program.initial(encode_words(&[vec![false], vec![false]]).unwrap());
    state.stacks[338] = VecDeque::from([true, false, true]);
    state.stacks[791] = VecDeque::from([false, true]);
    state.regs[37] = true;
    let stats = program.run(&mut state, RunLimits::default()).unwrap();
    assert!(stats.peak_stack_bits >= 2);
    assert_eq!(bits(&state, 600), [true; 4]);
    assert_eq!(
        bits(&state, 789),
        encode_words(&[vec![false], vec![false]]).unwrap()
    );
    assert!(state.stacks[790].is_empty());
    assert_eq!(bits(&state, 338), [true, false, true]);
    assert_eq!(bits(&state, 791), [false, true]);
    assert!(state.regs[37]);
    assert_eq!(HIGH_QUERY_PORTS.registers, [19, 20, 21]);
}

#[test]
fn bad_ports_and_exhausted_resources_fail_closed() {
    assert!(
        increment_command::<3, 2>(CounterPorts {
            registers: [0, 0, 2],
            counter: 0,
            scratch: 1,
        })
        .is_err()
    );
    assert!(
        increment_command::<3, 2>(CounterPorts {
            registers: [0, 1, 2],
            counter: 0,
            scratch: 0,
        })
        .is_err()
    );
    assert!(
        increment_command::<3, 2>(CounterPorts {
            registers: [0, 1, 3],
            counter: 0,
            scratch: 1,
        })
        .is_err()
    );
    let program = high_loop_command(Cmd::Skip)
        .unwrap()
        .compiled(789, 789)
        .unwrap();
    let mut state = program.initial(encode_words(&[vec![false; 5]]).unwrap());
    let failure = program
        .run(
            &mut state,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 10_000,
            },
        )
        .unwrap_err();
    assert!(failure.to_string().contains("capacity refusal"));
    assert!(state.pc.is_some());
}
