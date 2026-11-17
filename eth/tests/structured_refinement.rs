//! Independent big-step command interpreter used as a test oracle for the
//! finite-table compiler. Mirrors the *declarative* StructuredProgram.Eval
//! cases, not the compiled BitProgram site-dispatch implementation.

use lean_eth_reference::bit_program::{Atom, Cmd, Config, RunLimits};

fn atom<const R: usize, const S: usize>(op: &Atom, cfg: &mut Config<R, S>) {
    match *op {
        Atom::Set { dst, value } => cfg.regs[dst] = value,
        Atom::Copy { dst, src } => cfg.regs[dst] = cfg.regs[src],
        Atom::Not { dst, src } => cfg.regs[dst] = !cfg.regs[src],
        Atom::And { dst, left, right } => cfg.regs[dst] = cfg.regs[left] && cfg.regs[right],
        Atom::Or { dst, left, right } => cfg.regs[dst] = cfg.regs[left] || cfg.regs[right],
        Atom::Xor { dst, left, right } => cfg.regs[dst] = cfg.regs[left] ^ cfg.regs[right],
        Atom::Push { stack, src } => cfg.stacks[stack].push_front(cfg.regs[src]),
        Atom::Peek {
            stack,
            value,
            present,
        } => {
            let top = cfg.stacks[stack].front().copied();
            cfg.regs[value] = top.unwrap_or(false);
            cfg.regs[present] = top.is_some();
        }
        Atom::Pop {
            stack,
            value,
            present,
        } => {
            let top = cfg.stacks[stack].pop_front();
            cfg.regs[value] = top.unwrap_or(false);
            cfg.regs[present] = top.is_some();
        }
    }
}

fn eval<const R: usize, const S: usize>(cmd: &Cmd<R, S>, cfg: &mut Config<R, S>) -> u64 {
    match cmd {
        Cmd::Skip => 0,
        Cmd::Atom(op) => {
            atom(op, cfg);
            1
        }
        Cmd::Call(program) => {
            let mut state = cfg.clone();
            state.pc = Some(program.entry());
            let steps = program
                .run(&mut state, RunLimits::default())
                .unwrap()
                .instructions;
            cfg.regs = state.regs;
            cfg.stacks = state.stacks;
            steps
        }
        Cmd::Seq(a, b) => eval(a, cfg) + eval(b, cfg),
        Cmd::If { test, yes, no } => {
            1 + if cfg.regs[*test] {
                eval(yes, cfg)
            } else {
                eval(no, cfg)
            }
        }
        Cmd::While { test, body } => {
            let mut steps = 1;
            while cfg.regs[*test] {
                steps += eval(body, cfg) + 1;
                assert!(steps < 100_000, "a test loop must make progress");
            }
            steps
        }
    }
}

fn atom_for(index: usize) -> Atom {
    match index % 12 {
        0 => Atom::Set {
            dst: 0,
            value: true,
        },
        1 => Atom::Set {
            dst: 1,
            value: false,
        },
        2 => Atom::Copy { dst: 0, src: 1 },
        3 => Atom::Not { dst: 1, src: 0 },
        4 => Atom::And {
            dst: 1,
            left: 0,
            right: 1,
        },
        5 => Atom::Or {
            dst: 0,
            left: 0,
            right: 1,
        },
        6 => Atom::Xor {
            dst: 1,
            left: 0,
            right: 1,
        },
        7 => Atom::Push { stack: 0, src: 0 },
        8 => Atom::Push { stack: 1, src: 1 },
        9 => Atom::Peek {
            stack: 0,
            value: 0,
            present: 1,
        },
        10 => Atom::Pop {
            stack: 1,
            value: 1,
            present: 0,
        },
        _ => Atom::Pop {
            stack: 0,
            value: 0,
            present: 0,
        },
    }
}

fn deterministic_program(seed: usize, depth: usize) -> Cmd<2, 2> {
    if depth == 0 {
        return Cmd::Atom(atom_for(seed));
    }
    match seed % 4 {
        0 => Cmd::seq(
            deterministic_program(seed / 2 + 1, depth - 1),
            deterministic_program(seed + 7, depth - 1),
        ),
        1 => Cmd::ite(
            seed / 5 % 2,
            deterministic_program(seed + 3, depth - 1),
            deterministic_program(seed + 5, depth - 1),
        ),
        2 => Cmd::seq(Cmd::Skip, deterministic_program(seed + 1, depth - 1)),
        _ => Cmd::seq(deterministic_program(seed + 2, depth - 1), Cmd::Skip),
    }
}

#[test]
fn compiled_tables_refine_structured_big_step_semantics() {
    for seed in 0..120 {
        let command = deterministic_program(seed, 4);
        let machine = command.compiled(0, 1).unwrap();
        assert_eq!(machine.code().len(), command.size().unwrap() + 1);
        for mask in 0..8u8 {
            let input = [mask & 4 != 0, mask & 2 != 0, mask & 1 != 0];
            let mut actual = machine.initial(input);
            let mut expected = actual.clone();
            actual.regs = [mask & 1 != 0, mask & 2 != 0];
            expected.regs = actual.regs;
            let semantic_steps = eval(&command, &mut expected);
            let stats = machine.run(&mut actual, RunLimits::default()).unwrap();
            assert_eq!(
                stats.instructions,
                semantic_steps + 1,
                "seed={seed} mask={mask}"
            );
            assert_eq!(actual.regs, expected.regs, "seed={seed} mask={mask}");
            assert_eq!(actual.stacks, expected.stacks, "seed={seed} mask={mask}");
            assert_eq!(actual.pc, None);
        }
    }
}

#[test]
fn compiled_while_matches_big_step_for_every_short_input() {
    // Read a stack until empty, accumulate whether any bit was set in r2.
    let command = Cmd::<3, 1>::seq(
        Cmd::Atom(Atom::Peek {
            stack: 0,
            value: 0,
            present: 1,
        }),
        Cmd::while_(
            1,
            Cmd::seq(
                Cmd::Atom(Atom::Or {
                    dst: 2,
                    left: 0,
                    right: 2,
                }),
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
        ),
    );
    let machine = command.compiled(0, 0).unwrap();
    for n in 0..=7u8 {
        for mask in 0..(1u8 << n) {
            let input = (0..n).map(|i| (mask >> i) & 1 != 0).collect::<Vec<_>>();
            let mut expected = machine.initial(input.clone());
            let mut actual = expected.clone();
            let semantic_steps = eval(&command, &mut expected);
            let stats = machine.run(&mut actual, RunLimits::default()).unwrap();
            assert_eq!(stats.instructions, semantic_steps + 1);
            assert_eq!(actual.regs, expected.regs);
            assert_eq!(actual.stacks, expected.stacks);
            assert_eq!(actual.regs[2], input.contains(&true));
        }
    }
}
