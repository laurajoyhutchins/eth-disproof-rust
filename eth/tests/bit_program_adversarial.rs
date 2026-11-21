//! Deterministic property tests of the physical source machine. No external
//! proptest dependency or exponential SAT oracle is involved.
use lean_eth_reference::bit_program::{Config, Instr, Program, RunLimits, run_with_instruction_at};
use lean_eth_reference::{Cnf, Error, Literal};
use std::collections::VecDeque;

fn random(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

/// Independent Lean-style state: the stack top is index zero of a Vec.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ListConfig {
    pc: Option<usize>,
    regs: [bool; 3],
    stacks: [Vec<bool>; 2],
}

impl ListConfig {
    fn from_native(native: &Config<3, 2>) -> Self {
        Self {
            pc: native.pc,
            regs: native.regs,
            stacks: std::array::from_fn(|s| native.stacks[s].iter().copied().collect()),
        }
    }
}

fn assert_native_represents_list(native: &Config<3, 2>, expected: &ListConfig, context: &str) {
    assert_eq!(native.pc, expected.pc, "{context}: program counter");
    assert_eq!(native.regs, expected.regs, "{context}: registers");
    for s in 0..2 {
        let observed: Vec<_> = native.stacks[s].iter().copied().collect();
        assert_eq!(
            observed, expected.stacks[s],
            "{context}: logical stack {s} (head at index zero)"
        );
        // Check the actual host primitive independently of deque iteration:
        // Peek/Pop depend on front(), while the oracle uses Vec::first().
        assert_eq!(
            native.stacks[s].front().copied(),
            expected.stacks[s].first().copied(),
            "{context}: physical top of stack {s}"
        );
    }
}

fn model(op: &Instr, before: &ListConfig) -> ListConfig {
    let mut after = before.clone();
    let next = match *op {
        Instr::Halt => None,
        Instr::Goto { next } => Some(next),
        Instr::Set { dst, value, next } => {
            after.regs[dst] = value;
            Some(next)
        }
        Instr::Copy { dst, src, next } => {
            after.regs[dst] = before.regs[src];
            Some(next)
        }
        Instr::Not { dst, src, next } => {
            after.regs[dst] = !before.regs[src];
            Some(next)
        }
        Instr::And {
            dst,
            left,
            right,
            next,
        } => {
            after.regs[dst] = before.regs[left] && before.regs[right];
            Some(next)
        }
        Instr::Or {
            dst,
            left,
            right,
            next,
        } => {
            after.regs[dst] = before.regs[left] || before.regs[right];
            Some(next)
        }
        Instr::Xor {
            dst,
            left,
            right,
            next,
        } => {
            after.regs[dst] = before.regs[left] ^ before.regs[right];
            Some(next)
        }
        Instr::Branch { test, yes, no } => Some(if before.regs[test] { yes } else { no }),
        Instr::Push { stack, src, next } => {
            // This model uses Vec list semantics, not the production
            // VecDeque::push_front. Lean's stack head is index zero.
            after.stacks[stack].insert(0, before.regs[src]);
            Some(next)
        }
        Instr::Peek {
            stack,
            value,
            present,
            next,
        } => {
            let top = before.stacks[stack].first().copied();
            // A shared value/present register means the LAST write wins.
            after.regs[value] = top.unwrap_or(false);
            after.regs[present] = top.is_some();
            Some(next)
        }
        Instr::Pop {
            stack,
            value,
            present,
            next,
        } => {
            let top = if after.stacks[stack].is_empty() {
                None
            } else {
                Some(after.stacks[stack].remove(0))
            };
            after.regs[value] = top.unwrap_or(false);
            after.regs[present] = top.is_some();
            Some(next)
        }
    };
    after.pc = next;
    after
}

#[test]
fn all_twelve_opcodes_preserve_physical_state_invariants_under_seeded_adversarial_states() {
    let mut seed = 0x4f63_dcb1_2259_aa35_u64;
    for opcode in 0..12 {
        for trial in 0..96 {
            let rand_reg = (random(&mut seed) % 3) as usize;
            let source = (random(&mut seed) % 3) as usize;
            let stack = (random(&mut seed) % 2) as usize;
            let other = (random(&mut seed) % 3) as usize;
            let instr = match opcode {
                0 => Instr::Halt,
                1 => Instr::Goto { next: 1 },
                2 => Instr::Set {
                    dst: rand_reg,
                    value: random(&mut seed) & 1 != 0,
                    next: 1,
                },
                3 => Instr::Copy {
                    dst: rand_reg,
                    src: source,
                    next: 1,
                },
                4 => Instr::Not {
                    dst: rand_reg,
                    src: source,
                    next: 1,
                },
                5 => Instr::And {
                    dst: rand_reg,
                    left: source,
                    right: other,
                    next: 1,
                },
                6 => Instr::Or {
                    dst: rand_reg,
                    left: source,
                    right: other,
                    next: 1,
                },
                7 => Instr::Xor {
                    dst: rand_reg,
                    left: source,
                    right: other,
                    next: 1,
                },
                8 => Instr::Branch {
                    test: rand_reg,
                    yes: 1,
                    no: 2,
                },
                9 => Instr::Push {
                    stack,
                    src: source,
                    next: 1,
                },
                10 => Instr::Peek {
                    stack,
                    value: rand_reg,
                    present: source,
                    next: 1,
                },
                _ => Instr::Pop {
                    stack,
                    value: rand_reg,
                    present: source,
                    next: 1,
                },
            };
            let program =
                Program::<3, 2>::new(0, 1, 0, vec![instr.clone(), Instr::Halt, Instr::Halt])
                    .unwrap();
            let mut actual = program.initial(std::iter::empty());
            actual.regs = [
                random(&mut seed) & 1 != 0,
                random(&mut seed) & 1 != 0,
                random(&mut seed) & 1 != 0,
            ];
            for s in 0..2 {
                let n = match (trial + s) % 4 {
                    0 => 0,
                    1 => 1,
                    2 => 2,
                    _ => 9,
                };
                actual.stacks[s] = (0..n)
                    .map(|_| random(&mut seed) & 1 != 0)
                    .collect::<VecDeque<_>>();
            }
            let before = ListConfig::from_native(&actual);
            let expected = model(&instr, &before);
            assert!(program.step(&mut actual).unwrap());
            assert_native_represents_list(
                &actual,
                &expected,
                &format!("opcode={opcode}, trial={trial}, instruction={instr:?}"),
            );
            let mutated_stacks: Vec<_> = (0..2)
                .filter(|&s| before.stacks[s] != expected.stacks[s])
                .collect();
            assert!(mutated_stacks.len() <= 1);
            for s in mutated_stacks {
                let prev = &before.stacks[s];
                let now = &expected.stacks[s];
                assert!(now.iter().skip(1).eq(prev.iter()) || prev.iter().skip(1).eq(now.iter()));
            }
            if actual.pc.is_none() {
                assert!(!program.step(&mut actual).unwrap());
                assert_native_represents_list(
                    &actual,
                    &expected,
                    "halted machine must be idempotent",
                );
            }
        }
    }
}

/// Force a non-contiguous backing ring before executing actual production
/// instructions. Ordinary short stack tests often exercise only contiguous
/// VecDeque storage and can miss an incorrect head/front interpretation.
fn physically_wrapped_word(epoch: usize) -> (VecDeque<bool>, Vec<bool>) {
    let mut word = VecDeque::with_capacity(8);
    // Build the expected list independently, even during fixture setup.
    let mut list = Vec::new();
    let capacity = word.capacity();
    for i in 0..capacity {
        let bit = (i + epoch).is_multiple_of(3);
        word.push_back(bit);
        list.push(bit);
    }
    for _ in 0..capacity - 2 {
        assert_eq!(word.pop_front(), Some(list.remove(0)));
    }
    for i in 0..capacity - 2 {
        let bit = (i + epoch).is_multiple_of(2);
        word.push_back(bit);
        list.push(bit);
    }
    assert!(
        !word.as_slices().1.is_empty(),
        "the wraparound fixture must really have two physical slices"
    );
    assert_eq!(word.iter().copied().collect::<Vec<_>>(), list);
    (word, list)
}

/// Exhaustively check the four primitive operations (push false/true,
/// peek, pop) for all six-operation traces against a carried list-state
/// oracle. This checks the exact host assumptions of DequeContract in Lean;
/// it does not assert their universal validity for all native allocations.
#[test]
fn native_deque_contract_covers_all_short_action_traces() {
    const ALPHABET: usize = 4;
    const STEPS: usize = 6;
    let mut split_samples = 0usize;
    let mut capacity_growth = 0usize;
    let mut empty_removals = 0usize;
    for layout in 0..3 {
        for trace in 0..ALPHABET.pow(STEPS as u32) {
            let (mut actual, mut expected) = match layout {
                0 => (VecDeque::new(), Vec::new()),
                1 => (VecDeque::from([true, false]), vec![true, false]),
                _ => physically_wrapped_word(7),
            };
            let mut code = trace;
            for step in 0..STEPS {
                let action = code % ALPHABET;
                code /= ALPHABET;
                let old_capacity = actual.capacity();
                match action {
                    0 | 1 => {
                        let bit = action == 1;
                        actual.push_front(bit);
                        expected.insert(0, bit);
                    }
                    2 => assert_eq!(
                        actual.front().copied(),
                        expected.first().copied(),
                        "layout={layout} trace={trace} step={step} peek"
                    ),
                    _ => {
                        let wanted = if expected.is_empty() {
                            empty_removals += 1;
                            None
                        } else {
                            Some(expected.remove(0))
                        };
                        assert_eq!(
                            actual.pop_front(),
                            wanted,
                            "layout={layout} trace={trace} step={step} pop"
                        );
                    }
                }
                split_samples += usize::from(!actual.as_slices().1.is_empty());
                capacity_growth += usize::from(actual.capacity() > old_capacity);
                assert_eq!(actual.len(), expected.len());
                assert_eq!(
                    actual.front().copied(),
                    expected.first().copied(),
                    "layout={layout} trace={trace} step={step} head"
                );
                assert_eq!(
                    actual.iter().copied().collect::<Vec<_>>(),
                    expected,
                    "layout={layout} trace={trace} step={step} full list"
                );
            }
        }
    }
    assert!(split_samples > 0, "wrapped ring states must be exercised");
    assert!(capacity_growth > 0, "heap growth must be exercised");
    assert!(empty_removals > 0, "empty pop must be exercised");
}

#[test]
fn native_deque_front_push_pop_match_independent_lists_even_when_wrapped() {
    let mut seed = 0x8c71_ef92_4bad_0315_u64;
    let mut wrapped = 0usize;
    let mut empty_reads = 0usize;
    let mut present_reads = 0usize;
    let mut aliased_reads = 0usize;

    for epoch in 0..12 {
        let (wrapped_word, wrapped_list) = physically_wrapped_word(epoch);
        let registers = [epoch & 1 != 0, epoch & 2 != 0, epoch & 4 != 0];
        let second_list = vec![epoch & 1 == 0, true, false];
        let mut actual = Config::<3, 2> {
            pc: Some(0),
            regs: registers,
            stacks: [wrapped_word, second_list.iter().copied().collect()],
        };
        let mut expected = ListConfig {
            pc: Some(0),
            regs: registers,
            stacks: [wrapped_list, second_list],
        };
        assert_native_represents_list(&actual, &expected, "initial wrapped state");
        // Drain the wrapped word past empty, then refill before mixing
        // arbitrary operations. This forces empty/singleton/deep states.
        let phase = expected.stacks[0].len() + 3;
        for step in 0..2 * phase + 400 {
            let sample = random(&mut seed);
            let stack = if step < 2 * phase {
                0
            } else {
                (sample as usize >> 5) % 2
            };
            let src = ((sample >> 13) % 3) as usize;
            let value = ((sample >> 21) % 3) as usize;
            let present = if (step + epoch) & 1 == 0 {
                value
            } else {
                (value + 1) % 3
            };
            let opcode = if step < phase {
                2 // Pop until the original deque is empty, then pop empty.
            } else if step < 2 * phase {
                0 // Push values back into the same deque.
            } else {
                (sample % 3) as usize
            };
            let instruction = match opcode {
                0 => Instr::Push {
                    stack,
                    src,
                    next: 0,
                },
                1 => Instr::Peek {
                    stack,
                    value,
                    present,
                    next: 0,
                },
                _ => Instr::Pop {
                    stack,
                    value,
                    present,
                    next: 0,
                },
            };
            let program = Program::<3, 2>::new(0, 1, 0, vec![instruction.clone()])
                .expect("valid one-instruction program");

            if !actual.stacks[stack].as_slices().1.is_empty() {
                wrapped += 1;
            }
            if opcode != 0 {
                if expected.stacks[stack].is_empty() {
                    empty_reads += 1;
                } else {
                    present_reads += 1;
                }
                if value == present {
                    aliased_reads += 1;
                }
            }
            // Carry the independent list-state oracle across the entire
            // trace. Never reconstruct it from the native deque after a step:
            // that could hide a common head/iteration indexing error.
            expected = model(&instruction, &expected);
            assert!(program.step(&mut actual).unwrap());
            assert_native_represents_list(
                &actual,
                &expected,
                &format!("epoch={epoch} step={step} stack={stack} instruction={instruction:?}"),
            );
            if step + 1 == phase {
                assert!(expected.stacks[0].is_empty());
                assert!(actual.stacks[0].is_empty());
            }
        }
    }
    assert!(wrapped > 0, "must exercise physically split ring storage");
    assert!(
        empty_reads > 0 && present_reads > 0,
        "must observe both read states"
    );
    assert!(aliased_reads > 0, "must exercise ordered alias writes");
}

#[test]
fn capacity_refusal_does_not_claim_halting_or_break_stack_cap() {
    let program = Program::<1, 1>::new(
        0,
        0,
        0,
        vec![Instr::Push {
            stack: 0,
            src: 0,
            next: 0,
        }],
    )
    .unwrap();
    let mut state = program.initial(std::iter::empty());
    let original = state.clone();
    assert!(matches!(
        program.run(
            &mut state,
            RunLimits {
                max_steps: 0,
                max_stack_bits: 8
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert_eq!(state, original);
    assert!(matches!(
        program.run(
            &mut state,
            RunLimits {
                max_steps: 100,
                max_stack_bits: 4
            }
        ),
        Err(Error::Capacity(_))
    ));
    assert_eq!(state.pc, Some(0));
    assert_eq!(state.stacks[0].len(), 4);
}

#[test]
fn exact_source_instruction_accounting_includes_halt_and_peak() {
    let p = Program::<2, 1>::new(
        0,
        0,
        0,
        vec![
            Instr::Push {
                stack: 0,
                src: 0,
                next: 1,
            },
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 2,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    let mut c = p.initial(std::iter::empty());
    let stats = p.run(&mut c, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 3);
    assert_eq!(stats.peak_stack_bits, 1);
    assert_eq!(c.pc, None);
    assert!(c.stacks[0].is_empty());
    assert!(c.regs[1]);
}

#[test]
fn integer_mask_boundaries_never_silently_truncate() {
    let full = Cnf::from_signed(128, &[&[128]]).unwrap();
    assert!(full.eval_mask_checked(1_u128 << 127).unwrap());
    assert!(!full.eval_mask_checked(0).unwrap());
    let too_wide = Cnf::from_signed(129, &[]).unwrap();
    assert!(matches!(
        too_wide.eval_mask_checked(0),
        Err(Error::Capacity(_))
    ));
    assert!(matches!(
        Literal::from_dimacs(i64::MIN, 128),
        Err(Error::Invalid(_))
    ));
}

#[test]
fn malformed_program_addresses_are_rejected_before_execution() {
    assert!(matches!(
        Program::<1, 1>::new(0, 0, 0, vec![Instr::Goto { next: 1 }]),
        Err(Error::Invalid(_)),
    ));
    assert!(matches!(
        Program::<1, 1>::new(
            0,
            0,
            0,
            vec![Instr::Push {
                stack: 1,
                src: 0,
                next: 0
            }]
        ),
        Err(Error::Invalid(_)),
    ));
    assert!(matches!(
        Program::<1, 1>::new(
            0,
            0,
            0,
            vec![Instr::Set {
                dst: 1,
                value: true,
                next: 0
            }]
        ),
        Err(Error::Invalid(_)),
    ));
}

/*
 * Capacity oracle for the *actual* Rust bounded runner.
 *
 * The oracle intentionally pays for a full state copy and exact rescan after
 * every unbounded Program::step. Unlike the production cached counter, it
 * calculates admission from the candidate post-state, so it detects missed
 * increments/decrements and verifies that rejected operations leave the
 * complete configuration unchanged. This is adversarial testing, not a
 * Rust-to-Lean proof or an allocation bound.
 */
fn reference_bounded_run<const R: usize, const S: usize>(
    program: &Program<R, S>,
    state: &mut Config<R, S>,
    limits: RunLimits,
) -> Result<(u64, usize), Error> {
    let mut peak = state.stack_bits()?;
    if peak > limits.max_stack_bits {
        return Err(Error::Capacity("oracle initial stack-bit limit".into()));
    }
    let mut steps = 0_u64;
    while state.pc.is_some() {
        if steps >= limits.max_steps {
            return Err(Error::Capacity("oracle instruction limit".into()));
        }
        let mut candidate = state.clone();
        program.step(&mut candidate)?;
        let live = candidate.stack_bits()?;
        if live > limits.max_stack_bits {
            return Err(Error::Capacity("oracle candidate stack-bit limit".into()));
        }
        *state = candidate;
        peak = peak.max(live);
        steps += 1;
    }
    Ok((steps, peak))
}

#[test]
fn bounded_run_matches_independent_poststate_oracle_at_every_small_capacity() {
    // All 12 instruction constructors, including aliased read registers,
    // empty/nonempty Pops, both branch outcomes, and multiple live stacks.
    let instructions = [
        Instr::Halt,
        Instr::Goto { next: 1 },
        Instr::Set {
            dst: 0,
            value: true,
            next: 1,
        },
        Instr::Copy {
            dst: 0,
            src: 0,
            next: 1,
        },
        Instr::Not {
            dst: 0,
            src: 0,
            next: 1,
        },
        Instr::And {
            dst: 0,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Or {
            dst: 0,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Xor {
            dst: 0,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Branch {
            test: 0,
            yes: 1,
            no: 1,
        },
        Instr::Push {
            stack: 1,
            src: 0,
            next: 1,
        },
        Instr::Peek {
            stack: 1,
            value: 0,
            present: 0,
            next: 1,
        },
        Instr::Pop {
            stack: 1,
            value: 0,
            present: 0,
            next: 1,
        },
    ];
    let mut accepted = 0;
    let mut refused = 0;
    for instruction in instructions {
        let program =
            Program::<2, 2>::new(0, 1, 0, vec![instruction.clone(), Instr::Halt]).unwrap();
        for first_len in 0..=2 {
            for second_len in 0..=2 {
                for first_reg in [false, true] {
                    for capacity in 0..=5 {
                        for step_limit in [0, 1, 2] {
                            let mut state = program.initial([]);
                            state.regs = [first_reg, !first_reg];
                            state.stacks[0].extend((0..first_len).map(|i| i % 2 == 0));
                            state.stacks[1].extend((0..second_len).map(|i| i % 2 != 0));
                            let limits = RunLimits {
                                max_steps: step_limit,
                                max_stack_bits: capacity,
                            };
                            let mut actual = state.clone();
                            let mut reference = state;
                            let result = program.run(&mut actual, limits);
                            let expected = reference_bounded_run(&program, &mut reference, limits);
                            assert_eq!(
                                actual, reference,
                                "state mismatch for {instruction:?}, {limits:?}"
                            );
                            match (result, expected) {
                                (Ok(stats), Ok((steps, peak))) => {
                                    assert_eq!(stats.instructions, steps);
                                    assert_eq!(stats.peak_stack_bits, peak);
                                    assert!(actual.stack_bits().unwrap() <= capacity);
                                    accepted += 1;
                                }
                                (Err(Error::Capacity(_)), Err(Error::Capacity(_))) => {
                                    // Both machines refuse before committing the failing step.
                                    refused += 1;
                                }
                                (actual_result, oracle_result) => {
                                    panic!(
                                        "bounded runner diverged for {instruction:?}, {limits:?}: \
                                         {actual_result:?} vs {oracle_result:?}"
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(accepted > 0 && refused > 0);
}

#[test]
fn arbitrary_callback_refuses_bad_operands_without_mutating_any_state() {
    // Program::new already rejects these. The public generic callback has
    // no such construction-time guarantee and must reject before indexing.
    let malformed = [
        Instr::Push {
            stack: 2,
            src: 0,
            next: 0,
        },
        Instr::Push {
            stack: 0,
            src: 2,
            next: 0,
        },
        Instr::Pop {
            stack: 2,
            value: 0,
            present: 0,
            next: 0,
        },
        Instr::Peek {
            stack: 0,
            value: 2,
            present: 0,
            next: 0,
        },
        Instr::Branch {
            test: 2,
            yes: 0,
            no: 0,
        },
        Instr::Goto { next: usize::MAX },
    ];
    for instruction in malformed {
        for cap in [0, 1, 2] {
            let initial = Config::<2, 2> {
                pc: Some(0),
                regs: [true, false],
                stacks: std::array::from_fn(|_| VecDeque::new()),
            };
            let mut actual = initial.clone();
            let result = run_with_instruction_at(
                &mut actual,
                RunLimits {
                    max_steps: 1,
                    max_stack_bits: cap,
                },
                2,
                |_| Ok(instruction.clone()),
            );
            assert!(
                matches!(result, Err(Error::Invalid(_))),
                "invalid callback opcode {instruction:?} was not rejected: {result:?}"
            );
            assert_eq!(
                actual, initial,
                "invalid callback opcode mutated state before refusal"
            );
        }
    }
}

#[test]
fn callback_runner_rejects_nonfinite_successors_before_any_mutation() {
    // All these instructions have valid register and stack operands. Their
    // successor addresses, however, do not belong to the two-label machine.
    // A branch must validate BOTH successors, not only the taken one.
    let bad_instructions = [
        Instr::Goto { next: 2 },
        Instr::Set {
            dst: 0,
            value: false,
            next: 2,
        },
        Instr::Branch {
            test: 0,
            yes: 1,
            no: 2,
        },
        Instr::Push {
            stack: 0,
            src: 0,
            next: 2,
        },
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 1,
            next: 2,
        },
    ];
    for instruction in bad_instructions {
        let mut state = Config::<2, 2> {
            pc: Some(0),
            regs: [true, false],
            stacks: std::array::from_fn(|i| {
                if i == 0 {
                    VecDeque::from([true])
                } else {
                    VecDeque::new()
                }
            }),
        };
        let before = state.clone();
        let mut called = 0;
        let result = run_with_instruction_at(
            &mut state,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 3,
            },
            2,
            |pc| {
                called += 1;
                assert_eq!(pc, 0);
                Ok(instruction.clone())
            },
        );
        assert!(
            matches!(result, Err(Error::Invalid(_))),
            "accepted out-of-range successor in {instruction:?}: {result:?}"
        );
        assert_eq!(called, 1);
        assert_eq!(state, before, "invalid instruction mutated configuration");
    }
}

#[test]
fn callback_runner_refuses_invalid_active_pc_without_fetching() {
    for active in [2, usize::MAX] {
        let mut state = Config::<1, 1> {
            pc: Some(active),
            regs: [true],
            stacks: [VecDeque::from([false])],
        };
        let before = state.clone();
        let result = run_with_instruction_at(
            &mut state,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 1,
            },
            2,
            |_| panic!("invalid active program counter reached the callback"),
        );
        assert!(matches!(result, Err(Error::Invalid(_))));
        assert_eq!(state, before);
    }

    // An already halted source machine must not fetch or manufacture a
    // successor, even if the supplied label count is zero.
    let mut halted = Config::<1, 1> {
        pc: None,
        regs: [false],
        stacks: [VecDeque::new()],
    };
    let result = run_with_instruction_at(
        &mut halted,
        RunLimits {
            max_steps: 0,
            max_stack_bits: 0,
        },
        0,
        |_| panic!("halted configuration reached callback"),
    )
    .expect("valid halted configuration was refused");
    assert_eq!(result.instructions, 0);
    assert_eq!(result.peak_stack_bits, 0);
    assert_eq!(halted.pc, None);
}

/*
 * A genuinely independent finite-trace oracle for the *whole* bounded runner.
 * Unlike reference_bounded_run, this does not call production Program::step:
 * each candidate state is calculated through the ListConfig/Vec model above.
 *
 * The list model shares the literal opcode inputs with production (it is not
 * a proof of source-table identity), but it neither uses VecDeque nor the
 * production cached bit counter. Its refusals leave all previous committed
 * steps intact and its success preserves complete source-shaped state.
 */
fn independently_model_bounded_run(
    code: &[Instr],
    state: &mut ListConfig,
    limits: RunLimits,
) -> Result<(u64, usize), Error> {
    let live_bits = |cfg: &ListConfig| -> usize { cfg.stacks.iter().map(Vec::len).sum() };
    let mut peak = live_bits(state);
    if peak > limits.max_stack_bits {
        return Err(Error::Capacity("model initial stack capacity".into()));
    }
    let mut executed = 0_u64;
    while let Some(pc) = state.pc {
        if executed >= limits.max_steps {
            return Err(Error::Capacity("model instruction limit".into()));
        }
        let instr = code
            .get(pc)
            .ok_or_else(|| Error::Invalid("model nonfinite program counter".into()))?;
        let next = model(instr, state);
        let next_live = live_bits(&next);
        if next_live > limits.max_stack_bits {
            return Err(Error::Capacity("model push exceeds stack capacity".into()));
        }
        *state = next;
        peak = peak.max(next_live);
        executed += 1;
    }
    Ok((executed, peak))
}

#[test]
fn real_bounded_runner_matches_independent_list_semantics_over_finite_traces() {
    let instructions = [
        Instr::Halt,
        Instr::Goto { next: 1 },
        Instr::Set {
            dst: 0,
            value: true,
            next: 1,
        },
        Instr::Copy {
            dst: 0,
            src: 0,
            next: 1,
        },
        Instr::Not {
            dst: 0,
            src: 0,
            next: 1,
        },
        Instr::And {
            dst: 2,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Or {
            dst: 2,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Xor {
            dst: 2,
            left: 0,
            right: 1,
            next: 1,
        },
        Instr::Branch {
            test: 0,
            yes: 1,
            no: 1,
        },
        Instr::Push {
            stack: 1,
            src: 0,
            next: 1,
        },
        Instr::Peek {
            stack: 1,
            value: 0,
            present: 0,
            next: 1,
        },
        Instr::Pop {
            stack: 1,
            value: 0,
            present: 0,
            next: 1,
        },
    ];
    let multi_step = vec![
        Instr::Push {
            stack: 0,
            src: 0,
            next: 1,
        },
        Instr::Push {
            stack: 1,
            src: 1,
            next: 2,
        },
        Instr::Pop {
            stack: 0,
            value: 0,
            present: 0,
            next: 3,
        },
        Instr::Pop {
            stack: 1,
            value: 1,
            present: 1,
            next: 4,
        },
        Instr::Halt,
    ];
    let mut tested = 0_u64;
    let mut refusals = 0_u64;
    for code in instructions
        .into_iter()
        .map(|instr| vec![instr, Instr::Halt])
        .chain(std::iter::once(multi_step))
    {
        let program = Program::<3, 2>::new(0, 1, 0, code.clone()).unwrap();
        for len0 in 0..=2 {
            for len1 in 0..=2 {
                for reg0 in [false, true] {
                    for reg1 in [false, true] {
                        for max_bits in 0..=6 {
                            for max_steps in 0..=5 {
                                let mut actual = program.initial([]);
                                actual.regs = [reg0, reg1, !reg0];
                                actual.stacks[0].extend((0..len0).map(|i| i % 2 == 0));
                                actual.stacks[1].extend((0..len1).map(|i| i % 2 != 0));
                                let mut logical = ListConfig::from_native(&actual);
                                let limits = RunLimits {
                                    max_steps,
                                    max_stack_bits: max_bits,
                                };
                                let result = program.run(&mut actual, limits);
                                let reference =
                                    independently_model_bounded_run(&code, &mut logical, limits);
                                assert_native_represents_list(
                                    &actual,
                                    &logical,
                                    &format!("{code:?} {limits:?} {len0}/{len1}"),
                                );
                                match (result, reference) {
                                    (Ok(stats), Ok((steps, peak))) => {
                                        assert_eq!(stats.instructions, steps);
                                        assert_eq!(stats.peak_stack_bits, peak);
                                    }
                                    (Err(Error::Capacity(_)), Err(Error::Capacity(_))) => {
                                        refusals += 1;
                                    }
                                    (actual_result, logical_result) => panic!(
                                        "native/list bounded outcomes differ: \
                                         code={code:?}, limits={limits:?}, \
                                         actual={actual_result:?}, logical={logical_result:?}"
                                    ),
                                }
                                tested += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(tested > 1000);
    assert!(refusals > 0);
}
