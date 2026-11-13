use lean_eth_reference::bit_program::{Atom, Cmd, Config, Instr, Program, RunLimits};
use std::array;
use std::collections::VecDeque;

fn one(instruction: Instr, regs: [bool; 3], stacks: [Vec<bool>; 2]) -> Config<3, 2> {
    let program = Program::<3, 2>::new(0, 1, 0, vec![instruction, Instr::Halt]).unwrap();
    let mut state = program.initial([]);
    state.regs = regs;
    state.stacks = stacks.map(VecDeque::from);
    assert!(program.step(&mut state).unwrap());
    assert_eq!(state.pc, Some(1));
    state
}

#[test]
fn primitive_boolean_arithmetic_exhaustively_matches_truth_tables() {
    for a in [false, true] {
        for b in [false, true] {
            for c in [false, true] {
                let regs = [a, b, c];
                let zero = array::from_fn(|_| Vec::new());
                let instructions = [
                    (
                        Instr::Set {
                            dst: 0,
                            value: false,
                            next: 1,
                        },
                        false,
                    ),
                    (
                        Instr::Set {
                            dst: 0,
                            value: true,
                            next: 1,
                        },
                        true,
                    ),
                    (
                        Instr::Copy {
                            dst: 0,
                            src: 1,
                            next: 1,
                        },
                        b,
                    ),
                    (
                        Instr::Not {
                            dst: 0,
                            src: 1,
                            next: 1,
                        },
                        !b,
                    ),
                    (
                        Instr::And {
                            dst: 0,
                            left: 1,
                            right: 2,
                            next: 1,
                        },
                        b && c,
                    ),
                    (
                        Instr::Or {
                            dst: 0,
                            left: 1,
                            right: 2,
                            next: 1,
                        },
                        b || c,
                    ),
                    (
                        Instr::Xor {
                            dst: 0,
                            left: 1,
                            right: 2,
                            next: 1,
                        },
                        b ^ c,
                    ),
                    (
                        Instr::Not {
                            dst: 0,
                            src: 0,
                            next: 1,
                        },
                        !a,
                    ),
                    (
                        Instr::And {
                            dst: 0,
                            left: 0,
                            right: 2,
                            next: 1,
                        },
                        a && c,
                    ),
                    (
                        Instr::Xor {
                            dst: 0,
                            left: 0,
                            right: 0,
                            next: 1,
                        },
                        false,
                    ),
                ];
                for (instr, wanted) in instructions {
                    let state = one(instr, regs, zero.clone());
                    assert_eq!(state.regs, [wanted, b, c]);
                }
            }
        }
    }
}

#[test]
fn peek_and_pop_follow_lean_readregs_even_when_registers_alias() {
    for top in [None, Some(false), Some(true)] {
        for alias in [false, true] {
            for pop in [false, true] {
                let stack: Vec<bool> = top.into_iter().collect();
                let inst = match (pop, alias) {
                    (true, true) => Instr::Pop {
                        stack: 0,
                        value: 1,
                        present: 1,
                        next: 1,
                    },
                    (true, false) => Instr::Pop {
                        stack: 0,
                        value: 0,
                        present: 1,
                        next: 1,
                    },
                    (false, true) => Instr::Peek {
                        stack: 0,
                        value: 1,
                        present: 1,
                        next: 1,
                    },
                    (false, false) => Instr::Peek {
                        stack: 0,
                        value: 0,
                        present: 1,
                        next: 1,
                    },
                };
                let state = one(inst, [true, true, false], [stack.clone(), vec![true]]);
                assert_eq!(state.regs[1], top.is_some());
                if !alias {
                    assert_eq!(state.regs[0], top.unwrap_or(false));
                } else {
                    assert!(state.regs[0]);
                }
                assert_eq!(
                    state.stacks[0].iter().copied().collect::<Vec<_>>(),
                    if pop { vec![] } else { stack }
                );
                assert_eq!(
                    state.stacks[1].iter().copied().collect::<Vec<_>>(),
                    vec![true]
                );
            }
        }
    }
}

#[test]
fn branch_push_goto_and_halt_have_exact_source_step_count() {
    let code = vec![
        Instr::Branch {
            test: 0,
            yes: 1,
            no: 2,
        },
        Instr::Push {
            stack: 1,
            src: 0,
            next: 3,
        },
        Instr::Goto { next: 3 },
        Instr::Halt,
    ];
    let program = Program::<1, 2>::new(0, 1, 0, code).unwrap();
    for initial in [false, true] {
        let mut state = program.initial([true, false]);
        state.regs[0] = initial;
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, 3);
        assert_eq!(stats.peak_stack_bits, if initial { 3 } else { 2 });
        assert_eq!(state.pc, None);
        assert_eq!(
            state.stacks[0].iter().copied().collect::<Vec<_>>(),
            vec![true, false]
        );
        assert_eq!(
            state.stacks[1].iter().copied().collect::<Vec<_>>(),
            if initial { vec![true] } else { vec![] }
        );
        assert!(!program.step(&mut state).unwrap());
    }
}

#[test]
fn structured_compiler_generates_exact_finite_tables() {
    let command = Cmd::<2, 2>::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::ite(0, Cmd::Atom(Atom::Push { stack: 1, src: 0 }), Cmd::Skip),
    );
    let program = command.compiled(0, 1).unwrap();
    assert_eq!(command.size().unwrap(), 3);
    assert_eq!(program.entry(), 1);
    assert_eq!(
        program.code(),
        &[
            Instr::Halt,
            Instr::Set {
                dst: 0,
                value: true,
                next: 2
            },
            Instr::Branch {
                test: 0,
                yes: 3,
                no: 0
            },
            Instr::Push {
                stack: 1,
                src: 0,
                next: 0
            },
        ]
    );
    let mut state = program.initial([]);
    let stats = program.run(&mut state, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 4);
    assert_eq!(
        state.stacks[1].iter().copied().collect::<Vec<_>>(),
        vec![true]
    );
}

#[test]
fn structured_while_loops_recheck_guard_and_keep_list_order() {
    // The actual pre-loop peek is required: `while` tests a Boolean register,
    // and neither `while` nor `pop` implicitly checks the stack's top.
    let program = Cmd::<2, 1>::seq(
        Cmd::Atom(Atom::Peek {
            stack: 0,
            value: 0,
            present: 1,
        }),
        Cmd::while_(
            1,
            Cmd::seq(
                Cmd::Atom(Atom::Pop {
                    stack: 0,
                    value: 0,
                    present: 1,
                }),
                Cmd::Atom(Atom::Peek {
                    stack: 0,
                    value: 0,
                    present: 1,
                }),
            ),
        ),
    )
    .compiled(0, 0)
    .unwrap();
    for n in 0..=5 {
        let mut state = program.initial((0..n).map(|i| i % 2 == 0));
        let stats = program.run(&mut state, RunLimits::default()).unwrap();
        assert_eq!(stats.instructions, 1 + 3 * n as u64 + 2);
        assert!(state.stacks[0].is_empty());
        assert_eq!(state.regs, [false, false]);
        assert_eq!(state.pc, None);
    }
}

#[test]
fn call_relocates_all_jumps_and_replaces_each_halt_with_return() {
    let subroutine = Program::<2, 1>::new(
        0,
        0,
        0,
        vec![
            Instr::Set {
                dst: 0,
                value: true,
                next: 1,
            },
            Instr::Branch {
                test: 0,
                yes: 2,
                no: 3,
            },
            Instr::Halt,
            Instr::Halt,
        ],
    )
    .unwrap();
    let command = Cmd::<2, 1>::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: false,
        }),
        Cmd::seq(
            Cmd::Call(subroutine),
            Cmd::Atom(Atom::Push { stack: 0, src: 0 }),
        ),
    );
    let program = command.compiled(0, 0).unwrap();
    assert_eq!(
        program.code(),
        &[
            Instr::Halt,
            Instr::Set {
                dst: 0,
                value: false,
                next: 2
            },
            Instr::Set {
                dst: 0,
                value: true,
                next: 3
            },
            Instr::Branch {
                test: 0,
                yes: 4,
                no: 5
            },
            Instr::Goto { next: 6 },
            Instr::Goto { next: 6 },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 0
            },
        ]
    );
    let mut config = program.initial([]);
    let stats = program.run(&mut config, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 6);
    assert_eq!(
        config.stacks[0].iter().copied().collect::<Vec<_>>(),
        vec![true]
    );
}

#[test]
fn source_program_rejects_unreachable_invalid_fin_indices() {
    assert!(
        Program::<1, 1>::new(
            0,
            0,
            0,
            vec![
                Instr::Halt,
                Instr::Set {
                    dst: 1,
                    value: false,
                    next: 0
                },
            ]
        )
        .is_err()
    );
    assert!(Program::<1, 1>::new(0, 0, 0, vec![Instr::Goto { next: 1 }]).is_err());
    assert!(
        Program::<1, 1>::new(
            0,
            0,
            0,
            vec![Instr::Push {
                stack: 1,
                src: 0,
                next: 0
            }]
        )
        .is_err()
    );
    assert!(Cmd::<1, 1>::while_(1, Cmd::Skip).compiled(0, 0).is_err());
    assert!(Program::<1, 0>::new(0, 0, 0, vec![Instr::Halt]).is_err());
}

#[test]
fn budget_refusal_is_before_the_failing_instruction() {
    let program = Cmd::<1, 1>::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 0, src: 0 }),
    )
    .compiled(0, 0)
    .unwrap();
    let mut config = program.initial([false, true]);
    assert!(
        program
            .run(
                &mut config,
                RunLimits {
                    max_steps: 10,
                    max_stack_bits: 2
                }
            )
            .is_err()
    );
    assert_eq!(config.pc, Some(2));
    assert_eq!(config.regs, [true]);
    assert_eq!(
        config.stacks[0].iter().copied().collect::<Vec<_>>(),
        vec![false, true]
    );
    let mut config = program.initial([]);
    assert!(
        program
            .run(
                &mut config,
                RunLimits {
                    max_steps: 1,
                    max_stack_bits: 10
                }
            )
            .is_err()
    );
    assert_eq!(config.pc, Some(2));
}

#[test]
fn canonical_terminal_is_stricter_than_merely_halted() {
    let program = Program::<2, 2>::new(0, 1, 0, vec![Instr::Halt]).unwrap();
    let mut config = program.initial([]);
    program.run(&mut config, RunLimits::default()).unwrap();
    assert!(program.is_canonical_terminal(&config, &[]));
    config.regs[0] = true;
    assert!(!program.is_canonical_terminal(&config, &[]));
    config.regs[0] = false;
    config.stacks[0].push_back(true);
    assert!(!program.is_canonical_terminal(&config, &[]));
}

#[test]
fn arbitrary_corrupted_program_counter_is_rejected_not_indexed() {
    let program = Program::<1, 1>::new(0, 0, 0, vec![Instr::Halt]).unwrap();
    let mut config = program.initial([]);
    config.pc = Some(7);
    assert!(program.step(&mut config).is_err());
    assert_eq!(config.pc, Some(7));
    assert!(program.run(&mut config, RunLimits::default()).is_err());
    assert_eq!(config.pc, Some(7));
}

#[test]
fn compiled_empty_command_uses_the_exact_source_exit_label() {
    let p = Cmd::<1, 1>::Skip.compiled(0, 0).unwrap();
    assert_eq!(p.entry(), 0);
    assert_eq!(p.code(), &[Instr::Halt]);
    let mut c = p.initial([]);
    let stats = p.run(&mut c, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 1);
    assert_eq!(c.pc, None);
}
