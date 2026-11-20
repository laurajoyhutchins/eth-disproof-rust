//! Deterministic property tests of the physical source machine. No external
//! proptest dependency or exponential SAT oracle is involved.
use lean_eth_reference::bit_program::{Config, Instr, Program, RunLimits};
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
                assert_native_represents_list(&actual, &expected, "halted machine must be idempotent");
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
        let bit = (i + epoch) % 3 == 0;
        word.push_back(bit);
        list.push(bit);
    }
    for _ in 0..capacity - 2 {
        assert_eq!(word.pop_front(), Some(list.remove(0)));
    }
    for i in 0..capacity - 2 {
        let bit = (i + epoch) % 2 == 0;
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
