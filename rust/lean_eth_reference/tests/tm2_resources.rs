//! Independent finite fixtures for the pinned StackCompiler primitive action
//! counts and source-to-TM2 boundary agreement. No Lean parity claim here.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Config, Instr, Program, RunLimits};
use lean_eth_reference::tm2_resources::{PrimitiveLimits, run_primitive};

fn execute<const R: usize, const S: usize>(
    p: &Program<R, S>,
    mut source: Config<R, S>,
) -> (
    Config<R, S>,
    lean_eth_reference::tm2_resources::PrimitiveStats,
) {
    let mut physical = source.clone();
    let stats = run_primitive(p, &mut physical, PrimitiveLimits::default()).unwrap();
    let counts = p.run(&mut source, RunLimits::default()).unwrap();
    assert_eq!(counts.instructions, stats.source_steps);
    assert_eq!(physical, source, "TM2 and source final states diverge");
    assert!(stats.primitive_steps <= stats.source_steps * stats.source_step_overhead_bound);
    (physical, stats)
}

#[test]
fn explicit_push_and_halt_have_measured_tape_actions() {
    let p = Program::<3, 2>::new(
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
    let mut initial = p.initial([]);
    initial.regs[0] = true;
    let (final_state, cost) = execute(&p, initial);
    assert_eq!(
        final_state.stacks[1].iter().copied().collect::<Vec<_>>(),
        vec![true]
    );
    assert_eq!(cost.source_steps, 2);
    assert_eq!(cost.tm2_microsteps, 3); // push, goto, halt
    assert_eq!(cost.primitive_steps, 22); // width-2 push 11 + width-1 goto 5 + width-2 halt 6
    assert_eq!(cost.head_moves, 12); // scan/back plus two push moves
    assert_eq!(cost.visited_cells, 7); // five output positions and two input positions
    assert_eq!(cost.writes, 9); // push: 5, goto: 3, halt: 1
    assert_eq!(cost.peak_live_stack_bits, 1);
    assert_eq!(cost.peak_encoded_bits, 2);
    assert_eq!(cost.source_step_overhead_bound, 22);
}

#[test]
fn empty_stack_pop_still_pays_two_blank_moves_per_encoded_bit() {
    let p = Program::<3, 2>::new(
        0,
        1,
        0,
        vec![
            Instr::Pop {
                stack: 1,
                value: 0,
                present: 1,
                next: 1,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    let (final_state, cost) = execute(&p, p.initial([]));
    assert!(!final_state.regs[0]);
    assert!(!final_state.regs[1]);
    assert!(final_state.stacks[1].is_empty());
    assert_eq!(cost.primitive_steps, 22);
    assert_eq!(cost.head_moves, 12);
    assert_eq!(cost.peak_encoded_bits, 0);
}

#[test]
fn peek_alias_updates_present_last_even_if_read_value_is_false() {
    let p = Program::<3, 2>::new(
        0,
        1,
        0,
        vec![
            Instr::Peek {
                stack: 0,
                value: 1,
                present: 1,
                next: 1,
            },
            Instr::Halt,
        ],
    )
    .unwrap();
    let (final_state, cost) = execute(&p, p.initial([false]));
    assert!(final_state.regs[1]);
    assert_eq!(cost.source_steps, 2);
    assert_eq!(cost.tm2_microsteps, 3);
    assert_eq!(cost.primitive_steps, 16); // peek 5, goto 5, output halt 6
}

#[test]
fn branch_counts_executed_path_not_both_tree_arms() {
    for selected in [false, true] {
        let p = Program::<3, 2>::new(
            0,
            1,
            0,
            vec![
                Instr::Branch {
                    test: 0,
                    yes: 1,
                    no: 2,
                },
                Instr::Halt,
                Instr::Halt,
            ],
        )
        .unwrap();
        let mut initial = p.initial([]);
        initial.regs[0] = selected;
        let (_, cost) = execute(&p, initial);
        assert_eq!(cost.source_steps, 2);
        assert_eq!(cost.tm2_microsteps, 3);
        assert_eq!(cost.primitive_steps, 16);
        assert_eq!(cost.source_step_overhead_bound, 33); // statementSize branch = 3
    }
}

#[test]
fn all_twelve_lean_instruction_constructors_preserve_source_boundaries() {
    let operations = vec![
        Instr::Halt,
        Instr::Goto { next: 1 },
        Instr::Set {
            dst: 0,
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
