//! Table-driven independent oracle for the pinned StackCompiler.controller.
//!
//! This test implements the source's ready -> reader -> action -> ready
//! transition table, not the production simulator's lowered Micro list.
//! It checks every emitted action, head coordinate, and blank/nonblank value.
//! This is independent Rust evidence, *not* imported Lean differential proof.
use std::collections::{BTreeMap, BTreeSet};

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, Program};
use lean_eth_reference::native_high::branch_program;
use lean_eth_reference::tm2_resources::{
    PrimitiveAction as Act, PrimitiveEvent, PrimitiveLimits, run_primitive_traced,
};

#[derive(Clone, Default)]
struct ModelTape {
    head: i64,
    cells: BTreeMap<i64, bool>,
}

impl ModelTape {
    fn new(bits: &[bool]) -> Self {
        let cells = bits
            .iter()
            .enumerate()
            .map(|(i, &bit)| (i as i64, bit))
            .collect();
        Self { head: 0, cells }
    }

    fn top(&self) -> Option<bool> {
        self.cells.get(&self.head).copied()
    }

    fn emit(
        &mut self,
        source_index: u64,
        micro_index: u64,
        port: usize,
        action: Act,
    ) -> PrimitiveEvent {
        let before = self.top();
        let head_before = self.head;
        match action {
            Act::Write(Some(bit)) => {
                self.cells.insert(self.head, bit);
            }
            Act::Write(None) => {
                self.cells.remove(&self.head);
            }
            Act::Left => self.head -= 1,
            Act::Right => self.head += 1,
            Act::Halt => {}
        }
        PrimitiveEvent {
            source_index,
            micro_index,
            tape: port,
            action,
            head_before,
            head_after: self.head,
            cell_before: before,
            cell_after: self.top(),
        }
    }
}

#[derive(Clone, Copy)]
enum Work {
    Keep,
    Pop,
    Push(bool),
    Halt,
}

struct Model<const S: usize> {
    tapes: [ModelTape; S],
    steps: Vec<PrimitiveEvent>,
    micro_index: u64,
    source_index: u64,
    input_port: usize,
}

impl<const S: usize> Model<S> {
    fn from_config<const R: usize>(p: &Program<R, S>, c: &Config<R, S>) -> Self {
        let tapes = std::array::from_fn(|port| {
            let bits: Vec<bool> = c.stacks[port]
                .iter()
                .flat_map(|&bit| {
                    if port == p.input_stack() {
                        vec![bit]
                    } else {
                        vec![false, bit]
                    }
                })
                .collect();
            ModelTape::new(&bits)
        });
        Self {
            tapes,
            steps: Vec::new(),
            micro_index: 0,
            source_index: 0,
            input_port: p.input_stack(),
        }
    }

    fn action(&mut self, port: usize, action: Act) {
        let e = self.tapes[port].emit(self.source_index, self.micro_index, port, action);
        self.steps.push(e);
    }

    /// Direct transcription of StackCompiler.controller's *finite state
    /// machine*: one entry write; width right/left scans; decision write;
    /// zero or 2*width mutation actions; one return write. A halt decision
    /// has no action or return state.
    fn controller_step(&mut self, port: usize, work: Work) {
        let width = if port == self.input_port { 1 } else { 2 };
        let first = self.tapes[port].top();
        self.action(port, Act::Write(first));
        for _ in 0..width {
            self.action(port, Act::Right);
        }
        for _ in 0..width {
            self.action(port, Act::Left);
        }
        match work {
            Work::Halt => self.action(port, Act::Halt),
            other => {
                let current = self.tapes[port].top();
                self.action(port, Act::Write(current));
                match other {
                    Work::Keep => {}
                    Work::Pop => {
                        for _ in 0..width {
                            self.action(port, Act::Write(None));
                            self.action(port, Act::Right);
                        }
                    }
                    Work::Push(value) => {
                        // Source StackEncoding Bool code: raw width 1 on
                        // input; [false, value] width 2 on work stacks.
                        let bits = if width == 1 {
                            vec![value]
                        } else {
                            vec![false, value]
                        };
                        for bit in bits.into_iter().rev() {
                            self.action(port, Act::Left);
                            self.action(port, Act::Write(Some(bit)));
                        }
                    }
                    Work::Halt => unreachable!(),
                }
                let current = self.tapes[port].top();
                self.action(port, Act::Write(current));
            }
        }
        self.micro_index += 1;
    }

    fn source_step<const R: usize>(&mut self, p: &Program<R, S>, c: &mut Config<R, S>) {
        let instr = &p.code()[c.pc.unwrap()];
        // The TM2 statement constructor tree is direct from
        // BitProgramCompile.compileInstr. The simulator's Micro layout is
        // *not* consulted here.
        match instr {
            Instr::Halt => self.controller_step(p.output_stack(), Work::Halt),
            Instr::Goto { .. } => self.controller_step(self.input_port, Work::Keep),
            Instr::Branch { .. } => {
                self.controller_step(self.input_port, Work::Keep);
                self.controller_step(self.input_port, Work::Keep);
            }
            Instr::Push { stack, src, .. } => {
                self.controller_step(*stack, Work::Push(c.regs[*src]));
                self.controller_step(self.input_port, Work::Keep);
            }
            Instr::Pop { stack, .. } => {
                self.controller_step(*stack, Work::Pop);
                self.controller_step(self.input_port, Work::Keep);
            }
            Instr::Peek { stack, .. } => {
                self.controller_step(*stack, Work::Keep);
                self.controller_step(self.input_port, Work::Keep);
            }
            _ => {
                self.controller_step(self.input_port, Work::Keep);
                self.controller_step(self.input_port, Work::Keep);
            }
        }
        assert!(p.step(c).unwrap());
        self.source_index += 1;
    }
}

fn compare<const R: usize, const S: usize>(p: &Program<R, S>, start: Config<R, S>) {
    let mut model = Model::from_config(p, &start);
    let mut oracle_cfg = start.clone();
    let mut budget = 0;
    while oracle_cfg.pc.is_some() {
        model.source_step(p, &mut oracle_cfg);
        budget += 1;
        assert!(budget < 1500, "the test oracle must not loop without bound");
    }
    let mut actual_cfg = start;
    let (stats, trace) =
        run_primitive_traced(p, &mut actual_cfg, PrimitiveLimits::default(), 40_000).unwrap();
    assert_eq!(actual_cfg, oracle_cfg);
    assert_eq!(trace, model.steps, "primitive transition stream diverged");
    assert_eq!(stats.primitive_steps as usize, trace.len());
    assert_eq!(stats.tm2_microsteps, model.micro_index);
    let visited: BTreeSet<(usize, i64)> = trace
        .iter()
        .flat_map(|event| {
            [
                (event.tape, event.head_before),
                (event.tape, event.head_after),
            ]
        })
        .collect();
    assert_eq!(stats.visited_cells, visited.len());
    assert_eq!(
        stats.head_moves as usize,
        trace
            .iter()
            .filter(|e| matches!(e.action, Act::Left | Act::Right))
            .count()
    );
    assert_eq!(
        stats.writes as usize,
        trace
            .iter()
            .filter(|e| matches!(e.action, Act::Write(_)))
            .count()
    );
}

#[test]
fn controller_trace_matches_all_twelve_instruction_kinds() {
    let instructions = [
        Instr::Halt,
        Instr::Goto { next: 1 },
        Instr::Set {
            dst: 1,
            value: true,
            next: 1,
        },
        Instr::Copy {
            dst: 0,
            src: 1,
            next: 1,
        },
        Instr::Not {
            dst: 0,
            src: 1,
            next: 1,
        },
        Instr::And {
            dst: 0,
            left: 1,
            right: 2,
            next: 1,
        },
        Instr::Or {
            dst: 0,
            left: 1,
            right: 2,
            next: 1,
        },
        Instr::Xor {
            dst: 0,
            left: 1,
            right: 2,
            next: 1,
        },
        Instr::Branch {
            test: 0,
            yes: 1,
            no: 1,
        },
        Instr::Push {
            stack: 1,
            src: 2,
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
            present: 1,
            next: 1,
        },
    ];
    for instr in instructions {
        for input in [vec![], vec![false], vec![true, false]] {
            for scratch in [vec![], vec![false], vec![true, false]] {
                let p = Program::<3, 2>::new(0, 1, 0, vec![instr.clone(), Instr::Halt]).unwrap();
                let mut start = p.initial(input.clone());
                start.stacks[1].extend(scratch.clone());
                start.regs = [false, true, true];
                compare(&p, start);
            }
        }
    }
}

#[test]
fn controller_trace_matches_real_high_branch_for_varied_words() {
    let p = branch_program().unwrap();
    for input in [
        vec![],
        vec![false],
        vec![true],
        vec![true, false],
        vec![false, true, false],
        vec![true, false, true, false],
    ] {
        compare(&p, p.initial(input));
    }
}

#[test]
fn trace_budget_refusal_is_atomic() {
    let p = Program::<2, 2>::new(
        0,
        1,
        0,
        vec![
            Instr::Push {
                stack: 1,
                src: 0,
                next: 1,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    let original = p.initial([false]);
    let mut candidate = original.clone();
    assert!(matches!(
        run_primitive_traced(&p, &mut candidate, PrimitiveLimits::default(), 5),
        Err(Error::Capacity(_))
    ));
    assert_eq!(candidate, original);
    let (stats, records) =
        run_primitive_traced(&p, &mut candidate, PrimitiveLimits::default(), 100).unwrap();
    assert_eq!(records.len() as u64, stats.primitive_steps);
}

#[test]
fn controller_trace_matches_structured_loop_and_expanded_call() {
    use lean_eth_reference::bit_program::{Atom, Cmd};
    let sub = Program::<3, 2>::new(
        0,
        1,
        0,
        vec![
            Instr::Peek {
                stack: 1,
                value: 1,
                present: 2,
                next: 1,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    let program = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::seq(
            Cmd::while_(
                0,
                Cmd::seq(
                    Cmd::Atom(Atom::Push { stack: 1, src: 0 }),
                    Cmd::Atom(Atom::Set {
                        dst: 0,
                        value: false,
                    }),
                ),
            ),
            Cmd::Call(sub),
        ),
    )
    .compiled(0, 1)
    .unwrap();
    compare(&program, program.initial([true, false, true]));
}

#[test]
fn controller_trace_matches_raw_single_tape_encoding() {
    let program = Program::<2, 1>::new(
        0,
        0,
        0,
        vec![
            Instr::Pop {
                stack: 0,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Push {
                stack: 0,
                src: 0,
                next: 2,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    for input in [vec![], vec![false], vec![true, false]] {
        compare(&program, program.initial(input));
    }
}
