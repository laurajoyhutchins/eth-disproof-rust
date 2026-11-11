//! Independent finite-state controller oracle for the pinned Lean compiler.
//! This test implements ready/read/act/return without using production Micro.
//! It is finite Rust evidence, not an executed Lean proof.
use std::collections::{BTreeMap, BTreeSet};

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, Program};
use lean_eth_reference::native_high::branch_program;
use lean_eth_reference::tm2_resources::{
    PrimitiveAction as Act, PrimitiveEvent, PrimitiveLimits, run_primitive_traced,
};

#[derive(Clone, Default)]
struct Tape {
    head: i64,
    cells: BTreeMap<i64, bool>,
}

impl Tape {
    fn from_bits(bits: &[bool]) -> Self {
        let cells = bits.iter().enumerate().map(|(i, &b)| (i as i64, b)).collect();
        Self { head: 0, cells }
    }
    fn top(&self) -> Option<bool> {
        self.cells.get(&self.head).copied()
    }
    fn apply(&mut self, source: u64, micro: u64, port: usize, action: Act) -> PrimitiveEvent {
        let head_before = self.head;
        let cell_before = self.top();
        match action {
            Act::Write(Some(bit)) => { self.cells.insert(self.head, bit); }
            Act::Write(None) => { self.cells.remove(&self.head); }
            Act::Left => self.head -= 1,
            Act::Right => self.head += 1,
            Act::Halt => {}
        }
        PrimitiveEvent {
            source_index: source, micro_index: micro, tape: port,
            action, head_before, head_after: self.head,
            cell_before, cell_after: self.top(),
        }
    }
}

#[derive(Clone, Copy)]
enum Effect { Keep, Push(bool), Pop, Halt }

struct Oracle<const S: usize> {
    tapes: [Tape; S],
    events: Vec<PrimitiveEvent>,
    source: u64,
    micro: u64,
    input: usize,
}
impl<const S: usize> Oracle<S> {
    fn new<const R: usize>(p: &Program<R, S>, c: &Config<R, S>) -> Self {
        let tapes = std::array::from_fn(|port| {
            let bits: Vec<bool> = c.stacks[port].iter().flat_map(|&bit| {
                if port == p.input_stack() { vec![bit] } else { vec![false, bit] }
            }).collect();
            Tape::from_bits(&bits)
        });
        Self { tapes, events: Vec::new(), source: 0, micro: 0, input: p.input_stack() }
    }
    fn action(&mut self, port: usize, op: Act) {
        self.events.push(self.tapes[port].apply(self.source, self.micro, port, op));
    }
    // Direct finite-state StackCompiler.controller, rather than a flat cost
    // formula or production transition routine. Exactly one action per step.
    fn controller(&mut self, port: usize, effect: Effect) {
        let width = if port == self.input { 1 } else { 2 };
        self.action(port, Act::Write(self.tapes[port].top()));
        for _ in 0..width { self.action(port, Act::Right); }
        for _ in 0..width { self.action(port, Act::Left); }
        if let Effect::Halt = effect {
            self.action(port, Act::Halt);
        } else {
            self.action(port, Act::Write(self.tapes[port].top()));
            match effect {
                Effect::Keep => {}
                Effect::Pop => {
                    for _ in 0..width {
                        self.action(port, Act::Write(None));
                        self.action(port, Act::Right);
                    }
                }
                Effect::Push(bit) => {
                    let block = if width == 1 { vec![bit] } else { vec![false, bit] };
                    for value in block.into_iter().rev() {
                        self.action(port, Act::Left);
                        self.action(port, Act::Write(Some(value)));
                    }
                }
                Effect::Halt => unreachable!(),
            }
            self.action(port, Act::Write(self.tapes[port].top()));
        }
        self.micro += 1;
    }
    fn source_step<const R: usize>(&mut self, p: &Program<R, S>, c: &mut Config<R, S>) {
        let instr = &p.code()[c.pc.unwrap()];
        match instr {
            Instr::Halt => self.controller(p.output_stack(), Effect::Halt),
            Instr::Goto { .. } => self.controller(self.input, Effect::Keep),
            Instr::Branch { .. } => {
                self.controller(self.input, Effect::Keep);
                self.controller(self.input, Effect::Keep);
            }
            Instr::Push { stack, src, .. } => {
                self.controller(*stack, Effect::Push(c.regs[*src]));
                self.controller(self.input, Effect::Keep);
            }
            Instr::Pop { stack, .. } => {
                self.controller(*stack, Effect::Pop);
                self.controller(self.input, Effect::Keep);
            }
            Instr::Peek { stack, .. } => {
                self.controller(*stack, Effect::Keep);
                self.controller(self.input, Effect::Keep);
            }
            _ => {
                self.controller(self.input, Effect::Keep);
                self.controller(self.input, Effect::Keep);
            }
        }
        assert!(p.step(c).unwrap());
        self.source += 1;
    }
}
fn compare<const R: usize, const S: usize>(p: &Program<R, S>, input: Config<R, S>) {
    let mut oracle = Oracle::new(p, &input);
    let mut expected = input.clone();
    while expected.pc.is_some() {
        assert!(oracle.source < 1500, "test oracle must remain bounded");
        oracle.source_step(p, &mut expected);
    }
    let mut actual = input;
    let (stats, events) = run_primitive_traced(
        p, &mut actual, PrimitiveLimits::default(), 40_000
    ).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(events, oracle.events, "primitive action stream diverged");
    assert_eq!(stats.primitive_steps, events.len() as u64);
    assert_eq!(stats.tm2_microsteps, oracle.micro);
    let touched: BTreeSet<_> = events.iter().flat_map(|e| {
        [(e.tape, e.head_before), (e.tape, e.head_after)]
    }).collect();
    assert_eq!(stats.visited_cells, touched.len());
    assert_eq!(stats.head_moves as usize, events.iter().filter(|e| {
        matches!(e.action, Act::Left | Act::Right)
    }).count());
    assert_eq!(stats.writes as usize, events.iter().filter(|e| {
        matches!(e.action, Act::Write(_))
    }).count());
}

#[test]
fn all_twelve_lean_instruction_types_match_controller_transition_events() {
    let kinds = [
        Instr::Halt, Instr::Goto { next: 1 },
        Instr::Set { dst: 1, value: true, next: 1 },
        Instr::Copy { dst: 0, src: 1, next: 1 },
        Instr::Not { dst: 0, src: 1, next: 1 },
        Instr::And { dst: 0, left: 1, right: 2, next: 1 },
        Instr::Or { dst: 0, left: 1, right: 2, next: 1 },
        Instr::Xor { dst: 0, left: 1, right: 2, next: 1 },
        Instr::Branch { test: 0, yes: 1, no: 1 },
        Instr::Push { stack: 1, src: 2, next: 1 },
        Instr::Peek { stack: 1, value: 0, present: 0, next: 1 },
        Instr::Pop { stack: 1, value: 0, present: 1, next: 1 },
    ];
    for kind in kinds {
        for word in [vec![], vec![false], vec![true, false]] {
            for scratch in [vec![], vec![false], vec![true, false]] {
                let p = Program::<3, 2>::new(0, 1, 0, vec![kind.clone(), Instr::Halt]).unwrap();
                let mut initial = p.initial(word.clone());
                initial.stacks[1].extend(scratch.clone());
                initial.regs = [false, true, true];
                compare(&p, initial);
            }
        }
    }
}

#[test]
fn genuine_high_branch_program_has_same_primitive_transition_stream() {
    let p = branch_program().unwrap();
    for bits in [vec![], vec![false], vec![true], vec![true, false],
                 vec![false, true, false], vec![true, false, true, false]] {
        compare(&p, p.initial(bits));
    }
}

#[test]
fn trace_limit_refuses_atomically() {
    let p = Program::<2, 2>::new(
        0, 1, 0, vec![Instr::Push { stack: 1, src: 0, next: 1 }, Instr::Halt],
    ).unwrap();
    let original = p.initial([false]);
    let mut candidate = original.clone();
    assert!(matches!(
        run_primitive_traced(&p, &mut candidate, PrimitiveLimits::default(), 5),
        Err(Error::Capacity(_))
    ));
    assert_eq!(candidate, original);
    let (stats, events) = run_primitive_traced(
        &p, &mut candidate, PrimitiveLimits::default(), 100
    ).unwrap();
    assert_eq!(events.len() as u64, stats.primitive_steps);
}
