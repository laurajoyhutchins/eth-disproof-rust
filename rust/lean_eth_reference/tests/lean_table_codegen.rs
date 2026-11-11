//! Independently enumerate all fixture instructions and compare the compiled
//! Rust control flow with the existing source-faithful BitProgram interpreter.
//! This is NOT a comparison against a running original Lean/Mathlib build.

use lean_eth_reference::bit_program::{Instr, Program, RunLimits};

mod generated {
    include!(concat!(env!("OUT_DIR"), "/compiled_fixture.rs"));
}

fn reference() -> Program<4, 3> {
    use Instr::*;
    Program::new(
        0,
        2,
        0,
        vec![
            Branch { test: 3, yes: 1, no: 14 },
            Set { dst: 0, value: true, next: 2 },
            Push { stack: 0, src: 0, next: 3 },
            Peek { stack: 0, value: 1, present: 2, next: 4 },
            Branch { test: 2, yes: 5, no: 14 },
            Not { dst: 1, src: 1, next: 6 },
            Xor { dst: 3, left: 1, right: 0, next: 7 },
            And { dst: 2, left: 3, right: 0, next: 8 },
            Or { dst: 3, left: 2, right: 1, next: 9 },
            Copy { dst: 0, src: 3, next: 10 },
            Pop { stack: 0, value: 2, present: 1, next: 11 },
            Branch { test: 1, yes: 12, no: 14 },
            Goto { next: 13 },
            Halt,
            Peek { stack: 1, value: 2, present: 2, next: 15 },
            Halt,
        ],
    )
    .unwrap()
}

#[test]
fn codegen_preserves_full_machine_state_and_source_instruction_costs() {
    let source = reference();
    assert_eq!(
        (generated::ENTRY, generated::INPUT_STACK, generated::OUTPUT_STACK, generated::LABELS),
        (source.entry(), source.input_stack(), source.output_stack(), source.code().len()),
    );
    for input in [vec![], vec![false], vec![true, false, true]] {
        for start_branch in [false, true] {
            for optional_top in [None, Some(false), Some(true)] {
                let mut initial = source.initial(input.clone());
                initial.regs[3] = start_branch;
                if let Some(top) = optional_top {
                    initial.stacks[1].push_front(top);
                }
                for max_steps in 0..=20 {
                    for max_stack_bits in 0..=7 {
                        let limits = RunLimits { max_steps, max_stack_bits };
                        let mut interpreted = initial.clone();
                        let mut compiled = initial.clone();
                        let left = source.run(&mut interpreted, limits);
                        let right = generated::run(&mut compiled, limits);
                        assert_eq!(
                            left, right,
                            "run result: input={input:?} branch={start_branch} top={optional_top:?} limits={limits:?}"
                        );
                        assert_eq!(
                            interpreted, compiled,
                            "full frames: input={input:?} branch={start_branch} top={optional_top:?} limits={limits:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn invalid_program_counter_is_refused_identically() {
    let source = reference();
    let mut interpreted = source.initial([]);
    interpreted.pc = Some(99);
    let mut compiled = interpreted.clone();
    let limits = RunLimits::default();
    assert_eq!(source.run(&mut interpreted, limits), generated::run(&mut compiled, limits));
    assert_eq!(interpreted, compiled);
}
