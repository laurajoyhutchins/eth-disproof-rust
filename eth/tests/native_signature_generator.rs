//! Independent source-state oracle for the finite tuple generator initialization.
use lean_eth_reference::bit_program::{Atom, Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_signature_frames::{CONTROLLER_REGISTERS, TUPLE_STACKS};
use lean_eth_reference::native_signature_generator::{
    initial_fuel_command, power_two_program, reset_command, reset_generator_command, setup_with,
};

fn write<const R: usize, const S: usize>(s: &mut Config<R, S>, i: usize, word: &[bool]) {
    s.stacks[i] = word.iter().copied().collect();
}
fn read<const R: usize, const S: usize>(s: &Config<R, S>, i: usize) -> Vec<bool> {
    s.stacks[i].iter().copied().collect()
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, s: &mut Config<R, S>) -> u64 {
    s.pc = Some(p.entry());
    let r = p
        .run(
            s,
            RunLimits {
                max_steps: 5_000_000,
                max_stack_bits: 500_000,
            },
        )
        .unwrap();
    assert_eq!(s.pc, None);
    r.instructions
}
fn compiled(c: Cmd<40, 896>) -> Program<40, 896> {
    c.compiled(838, 843).unwrap()
}

#[test]
fn power_two_is_pinned_seven_label_machine_with_exact_cost_and_bits() {
    let p = power_two_program().unwrap();
    assert_eq!(p.code().len(), 7);
    assert_eq!((p.input_stack(), p.output_stack()), (0, 1));
    for h in 0..=60 {
        let source: Vec<bool> = (0..h).map(|i| i % 3 == 0).collect();
        let mut s = p.initial(source);
        s.regs[2] = true;
        assert_eq!(run(&p, &mut s), (4 * h + 5) as u64);
        assert!(read(&s, 0).is_empty());
        let mut expected = vec![false; h];
        expected.push(true);
        assert_eq!(read(&s, 1), expected);
        assert!(!s.regs[0] && !s.regs[1] && s.regs[2]);
    }
}

#[test]
fn reset_produces_binary_fuel_preserves_input_and_exact_step_cost() {
    let p = compiled(reset_command().unwrap());
    for h in 0..=32 {
        let mut s = p.initial(vec![]);
        write(&mut s, 651, &vec![false; h]);
        write(&mut s, 895, &[true, false, true]);
        s.regs[38] = false;
        s.regs[39] = true;
        assert_eq!(run(&p, &mut s), (18 * h + 18) as u64);
        assert_eq!(read(&s, 651), vec![false; h]);
        assert_eq!(read(&s, 838), vec![false; h]);
        let mut fuel = vec![false; h];
        fuel.push(true);
        assert_eq!(read(&s, 843), fuel);
        assert!(read(&s, 840).is_empty());
        assert!(read(&s, 841).is_empty());
        assert_eq!(read(&s, 895), [true, false, true]);
        assert!(s.regs[38]);
        assert!(!s.regs[39]);
    }
}

#[test]
fn complete_generator_reset_seeds_predecessor_without_mutating_other_tapes() {
    let p = compiled(reset_generator_command().unwrap());
    for h in [0, 1, 2, 3, 10, 40] {
        let mut s = p.initial(vec![]);
        write(&mut s, 651, &vec![false; h]);
        write(&mut s, 845, &[true, true, false]);
        write(&mut s, 710, &[false, true]);
        assert_eq!(run(&p, &mut s), (25 * h + 23) as u64);
        assert_eq!(read(&s, 838), vec![false; h]);
        assert_eq!(read(&s, 844), vec![false; h]);
        assert_eq!(read(&s, 843), [vec![false; h], vec![true]].concat());
        assert_eq!(read(&s, 845), [true, true, false]);
        assert_eq!(read(&s, 710), [false, true]);
        assert!(read(&s, 840).is_empty());
        assert!(read(&s, 841).is_empty());
    }
}

#[test]
fn setup_with_zero_heads_skips_loader_but_runs_one_empty_tuple_iteration() {
    let load = Cmd::Atom(Atom::Set {
        dst: 30,
        value: true,
    });
    let setup = setup_with(load).unwrap();
    let iteration = Cmd::seq(
        Cmd::Atom(Atom::Push {
            stack: 851,
            src: CONTROLLER_REGISTERS[0],
        }),
        Cmd::Atom(Atom::Set {
            dst: CONTROLLER_REGISTERS[0],
            value: false,
        }),
    );
    let p = compiled(Cmd::seq(setup, Cmd::while_(36, iteration)));
    let mut s = p.initial(vec![]);
    for &stack in &TUPLE_STACKS {
        write(&mut s, stack, &[true, false]);
    }
    write(&mut s, 130, &[]);
    write(&mut s, 649, &[]);
    write(&mut s, 851, &[]);
    run(&p, &mut s);
    assert!(!s.regs[30]); // loadHead is not reached for zero heads
    assert!(s.regs[37]); // zero levels means the sole empty tuple is a leaf
    assert_eq!(read(&s, 851), [true]); // once, never zero times
    for &stack in &TUPLE_STACKS {
        assert!(read(&s, stack).is_empty(), "uncleared tuple stack {stack}");
    }
    assert_eq!(read(&s, 130), Vec::<bool>::new());
}

#[test]
fn setup_with_nonempty_heads_uses_actual_generator_reset_after_loader() {
    let load = Cmd::Atom(Atom::Set {
        dst: 30,
        value: true,
    });
    let p = compiled(setup_with(load).unwrap());
    for heads in 1..=4 {
        for height in [0, 1, 2, 7] {
            let mut s = p.initial(vec![]);
            for &stack in &TUPLE_STACKS {
                write(&mut s, stack, &[true, false, true]);
            }
            write(&mut s, 130, &vec![true; heads]);
            write(&mut s, 649, &[true; 3]);
            write(&mut s, 651, &vec![false; height]);
            write(&mut s, 895, &[false, true, false]);
            run(&p, &mut s);
            assert!(s.regs[30]);
            assert!(s.regs[36]);
            assert!(!s.regs[37]);
            assert!(s.regs[38]);
            assert!(!s.regs[39]);
            assert_eq!(read(&s, 842), vec![true; heads]);
            assert_eq!(read(&s, 845), vec![true; 3]);
            assert_eq!(read(&s, 838), vec![false; height]);
            assert_eq!(read(&s, 844), vec![false; height]);
            assert_eq!(read(&s, 843), [vec![false; height], vec![true]].concat());
            for port in [836, 837, 839, 840, 841, 846, 847] {
                assert!(read(&s, port).is_empty(), "tuple tape {port} not clean");
            }
            assert_eq!(read(&s, 895), [false, true, false]);
        }
    }
}

#[test]
fn fuel_is_built_by_consuming_temporary_not_host_arithmetic() {
    let p = compiled(initial_fuel_command().unwrap());
    let mut s = p.initial(vec![]);
    write(&mut s, 840, &[false, true, false, true, false]);
    write(&mut s, 651, &[false; 5]);
    run(&p, &mut s);
    assert!(read(&s, 840).is_empty());
    assert_eq!(read(&s, 843), [false, false, false, false, false, true]);
    assert_eq!(read(&s, 651), [false; 5]);
}

#[test]
fn instruction_budget_refusal_is_explicit_not_a_partial_success() {
    let p = compiled(reset_command().unwrap());
    let mut s = p.initial(vec![]);
    write(&mut s, 651, &[false; 100]);
    s.pc = Some(p.entry());
    assert!(
        p.run(
            &mut s,
            RunLimits {
                max_steps: 25,
                max_stack_bits: 500_000
            }
        )
        .is_err()
    );
}
