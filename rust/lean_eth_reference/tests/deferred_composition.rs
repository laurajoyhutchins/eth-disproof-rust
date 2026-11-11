//! Differential checks for source-physical on-demand graph execution.
use std::sync::Arc;

use lean_eth_reference::bit_program::{
    Atom, Block, Cmd, DeferredProgram, Instr, Program, RunLimits,
};

fn callee() -> Program<2, 2> {
    Program::new(
        0,
        1,
        2,
        vec![
            Instr::Halt,
            Instr::Goto { next: 0 },
            Instr::Set {
                dst: 0,
                value: true,
                next: 1,
            },
        ],
    )
    .unwrap()
}

#[test]
fn call_relocates_every_physical_label_including_halt_and_return() {
    let call = Block::call(DeferredProgram::table(callee()));
    let tail = Block::atom(Atom::Set {
        dst: 1,
        value: true,
    })
    .unwrap();
    let program = DeferredProgram::composed(0, 1, Block::seq(call, tail).unwrap()).unwrap();

    assert_eq!(program.labels(), 5);
    assert_eq!(program.entry(), 3);
    assert_eq!(program.instruction_at(0).unwrap(), Instr::Halt);
    assert_eq!(program.instruction_at(1).unwrap(), Instr::Goto { next: 4 });
    assert_eq!(program.instruction_at(2).unwrap(), Instr::Goto { next: 1 });
    assert_eq!(
        program.instruction_at(3).unwrap(),
        Instr::Set {
            dst: 0,
            value: true,
            next: 2
        }
    );
    assert_eq!(
        program.instruction_at(4).unwrap(),
        Instr::Set {
            dst: 1,
            value: true,
            next: 0
        }
    );
    assert!(program.instruction_at(5).is_err());

    let mut config = program.initial([]);
    let stats = program.run(&mut config, RunLimits::default()).unwrap();
    assert_eq!(stats.instructions, 5);
    assert_eq!(config.pc, None);
    assert_eq!(config.regs, [true, true]);
    assert_eq!(
        program.materialize(5).unwrap().code(),
        &(0..5)
            .map(|pc| program.instruction_at(pc).unwrap())
            .collect::<Vec<_>>()
    );
}

#[test]
fn nested_while_branch_and_call_match_existing_eager_compiler() {
    let command = Cmd::<2, 2>::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::seq(
            Cmd::while_(
                0,
                Cmd::Atom(Atom::Set {
                    dst: 0,
                    value: false,
                }),
            ),
            Cmd::Call(callee()),
        ),
    );
    let eager = command.compiled(0, 1).unwrap();

    let set_true = Block::atom(Atom::Set {
        dst: 0,
        value: true,
    })
    .unwrap();
    let set_false = Block::atom(Atom::Set {
        dst: 0,
        value: false,
    })
    .unwrap();
    let loop_ = Block::while_(0, set_false).unwrap();
    let call = Block::call(DeferredProgram::table(callee()));
    let graph = Block::seq(set_true, Block::seq(loop_, call).unwrap()).unwrap();
    let deferred = DeferredProgram::composed(0, 1, graph).unwrap();

    for input in [vec![], vec![true], vec![false, true]] {
        let mut expected = eager.initial(input.clone());
        let mut actual = deferred.initial(input);
        let expected_stats = eager.run(&mut expected, RunLimits::default()).unwrap();
        let actual_stats = deferred.run(&mut actual, RunLimits::default()).unwrap();
        assert_eq!(actual_stats, expected_stats);
        assert_eq!(actual.pc, expected.pc);
        assert_eq!(actual.regs, expected.regs);
        assert_eq!(actual.stacks, expected.stacks);
    }
}

#[test]
fn graph_sharing_avoids_materializing_hundreds_of_millions_of_labels() {
    let mut block = Block::<2, 2>::atom(Atom::Set {
        dst: 0,
        value: true,
    })
    .unwrap();
    for _ in 0..28 {
        block = Block::seq(Arc::clone(&block), block).unwrap();
    }
    let program = DeferredProgram::composed(0, 1, block).unwrap();
    assert_eq!(program.labels(), (1 << 28) + 1);
    assert_eq!(
        program.instruction_at(program.labels() - 1).unwrap(),
        Instr::Set {
            dst: 0,
            value: true,
            next: 0
        }
    );
    assert_eq!(program.instruction_at(0).unwrap(), Instr::Halt);
    assert!(program.materialize(1000).is_err());
    let mut cfg = program.initial([]);
    let result = program.run(
        &mut cfg,
        RunLimits {
            max_steps: 8,
            max_stack_bits: 1,
        },
    );
    assert!(result.is_err());
    assert!(cfg.pc.is_some()); // capacity refusal is not a successful halt
}

#[test]
fn malformed_source_addresses_and_budgets_refuse() {
    assert!(Block::<2, 2>::atom(Atom::Push { stack: 99, src: 0 }).is_err());
    assert!(Block::<2, 2>::ite(2, Block::skip(), Block::skip()).is_err());
    assert!(Block::<2, 2>::while_(2, Block::skip()).is_err());
    assert!(DeferredProgram::<2, 2>::composed(2, 0, Block::skip()).is_err());

    let push = Block::<2, 2>::atom(Atom::Push { stack: 0, src: 0 }).unwrap();
    let program = DeferredProgram::composed(0, 1, push).unwrap();
    let mut config = program.initial([false]);
    let result = program.run(
        &mut config,
        RunLimits {
            max_steps: 100,
            max_stack_bits: 1,
        },
    );
    assert!(result.is_err());
    assert_eq!(config.stacks[0].len(), 1); // refused before mutating
}

#[test]
fn empty_and_branching_blocks_match_original_layout() {
    let blank = DeferredProgram::<2, 2>::composed(0, 1, Block::skip()).unwrap();
    assert_eq!(blank.labels(), 1);
    assert_eq!(blank.entry(), 0);
    let mut halted = blank.initial([]);
    assert_eq!(
        blank
            .run(&mut halted, RunLimits::default())
            .unwrap()
            .instructions,
        1
    );

    let yes = Block::<2, 2>::atom(Atom::Set {
        dst: 1,
        value: true,
    })
    .unwrap();
    let no = Block::<2, 2>::atom(Atom::Set {
        dst: 1,
        value: false,
    })
    .unwrap();
    let branch = DeferredProgram::composed(0, 1, Block::ite(0, yes, no).unwrap()).unwrap();
    assert_eq!(branch.labels(), 4);
    assert_eq!(branch.entry(), 1);
    assert_eq!(
        branch.instruction_at(1).unwrap(),
        Instr::Branch {
            test: 0,
            yes: 2,
            no: 3
        }
    );
}

#[test]
fn repeat_matches_explicit_sequence_even_with_nonzero_callee_entry() {
    let leaf = Block::<2, 2>::atom(Atom::Copy { dst: 0, src: 1 }).unwrap();
    let call = Block::call(DeferredProgram::table(callee()));
    for part in [leaf, call] {
        for n in 0..8 {
            let repeated =
                DeferredProgram::composed(0, 1, Block::repeat(n, Arc::clone(&part)).unwrap())
                    .unwrap();
            let mut expanded = Block::<2, 2>::skip();
            for _ in 0..n {
                expanded = Block::seq(expanded, Arc::clone(&part)).unwrap();
            }
            let explicit = DeferredProgram::composed(0, 1, expanded).unwrap();
            assert_eq!(repeated.entry(), explicit.entry());
            assert_eq!(repeated.labels(), explicit.labels());
            for pc in 0..repeated.labels() {
                assert_eq!(
                    repeated.instruction_at(pc).unwrap(),
                    explicit.instruction_at(pc).unwrap(),
                    "n={n} pc={pc}"
                );
            }
        }
    }
}

#[test]
fn repeat_refuses_overflow_and_never_materializes_huge_control_space() {
    let atom = Block::<2, 2>::atom(Atom::Set {
        dst: 0,
        value: true,
    })
    .unwrap();
    let repeated = Block::repeat(1 << 30, Arc::clone(&atom)).unwrap();
    let source = DeferredProgram::composed(0, 1, repeated).unwrap();
    assert_eq!(source.labels(), (1 << 30) + 1);
    assert_eq!(source.entry(), 1);
    assert_eq!(
        source.instruction_at(source.labels() - 1).unwrap(),
        Instr::Set {
            dst: 0,
            value: true,
            next: 0
        }
    );
    assert!(source.materialize(1024).is_err());
    let two_sites = Block::<2, 2>::ite(
        0,
        Block::atom(Atom::Set { dst: 0, value: true }).unwrap(),
        Block::skip(),
    ).unwrap();
    assert!(Block::repeat(usize::MAX, two_sites).is_err());
}
