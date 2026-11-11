//! Finite-table tests of the exact signature controller and level initializer.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, RunLimits};
use lean_eth_reference::native_signature_tuple::{
    TUPLE_STACKS, TuplePorts, TupleRoutines, initialize_levels_command, initialize_levels_program,
    query_ports,
};

fn run<const R: usize, const S: usize>(
    program: &lean_eth_reference::bit_program::Program<R, S>,
    config: &mut Config<R, S>,
) -> u64 {
    program
        .run(
            config,
            RunLimits {
                max_steps: 100_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap()
        .instructions
}

fn set(i: usize, val: bool) -> Cmd<40, 896> {
    Cmd::Atom(Atom::Set { dst: i, value: val })
}
fn mark(port: usize) -> Cmd<40, 896> {
    Cmd::seq(
        set(5, true),
        Cmd::Atom(Atom::Push {
            stack: port,
            src: 5,
        }),
    )
}

#[test]
fn initializer_matches_pinned_abi_for_zero_and_nonzero_heads() {
    let p = initialize_levels_program().unwrap();
    for n in 0..6 {
        for addr in 0..6 {
            let mut d = p.initial([]);
            d.stacks[130].extend(std::iter::repeat_n(true, n));
            d.stacks[649].extend(std::iter::repeat_n(true, addr));
            d.stacks[800].extend([false, true, true, false]);
            d.regs[20] = true;
            let prior = d.stacks[800].clone();
            let instructions = run(&p, &mut d);
            assert_eq!(
                instructions,
                (7 * (n + addr) + 14) as u64,
                "source compiled cost"
            );
            assert_eq!(d.stacks[130].len(), n);
            assert_eq!(d.stacks[649].len(), addr);
            assert_eq!(d.stacks[TUPLE_STACKS[6]].len(), n);
            assert_eq!(d.stacks[TUPLE_STACKS[9]].len(), addr);
            assert!(d.stacks[TUPLE_STACKS[5]].is_empty());
            assert_eq!(d.stacks[800], prior);
            assert!(d.regs[20]);
            assert!(d.regs[36]);
            assert_eq!(d.regs[37], n == 0);
            assert_eq!(d.regs[1], n != 0);
            assert!(d.pc.is_none());
        }
    }
}

fn machine(probe: Cmd<40, 896>, leaf: bool) -> TupleRoutines<40, 896> {
    TupleRoutines {
        setup: Cmd::seq(set(36, true), set(37, leaf)),
        probe,
        descend: Cmd::seq(mark(702), set(37, true)),
        advance: Cmd::seq(mark(703), set(37, true)),
        ascend: Cmd::seq(mark(704), set(36, false)),
        visit: mark(701),
    }
}

#[test]
fn controller_visits_one_leaf_and_ascends_once() {
    let q = machine(mark(705), true);
    let p = query_ports().program(&q, 837, 851).unwrap();
    let mut d = p.initial([]);
    run(&p, &mut d);
    assert_eq!(d.stacks[701].len(), 1);
    assert_eq!(d.stacks[704].len(), 1);
    assert!(d.stacks[705].is_empty());
    assert!(!d.regs[36]);
}

#[test]
fn controller_uses_fresh_duplicate_and_exhausted_branches() {
    for (available, fresh, expected) in [(true, true, 702), (true, false, 703), (false, false, 704)]
    {
        let probe = Cmd::seq(mark(705), Cmd::seq(set(38, available), set(39, fresh)));
        let q = machine(probe, false);
        let p = query_ports().program(&q, 837, 851).unwrap();
        let mut d = p.initial([]);
        run(&p, &mut d);
        assert_eq!(d.stacks[705].len(), 1);
        assert_eq!(d.stacks[expected].len(), 1);
        assert_eq!(d.stacks[701].len(), if expected == 704 { 0 } else { 1 });
        assert_eq!(d.stacks[702].len(), usize::from(expected == 702));
        assert_eq!(d.stacks[703].len(), usize::from(expected == 703));
        assert_eq!(d.stacks[704].len(), 1);
        assert!(!d.regs[36]);
    }
}

#[test]
fn empty_tuple_is_visited_once_after_physical_initializer() {
    let mut q = machine(Cmd::Skip, true);
    q.setup = initialize_levels_command().unwrap();
    let p = query_ports().program(&q, 837, 851).unwrap();
    let mut d = p.initial([]);
    d.stacks[649].extend([true, true]);
    run(&p, &mut d);
    assert_eq!(d.stacks[701].len(), 1);
    assert_eq!(d.stacks[704].len(), 1);
    assert_eq!(d.stacks[845].len(), 2);
    assert!(!d.regs[36]);
}

#[test]
fn invalid_port_and_finite_instruction_budget_fail_closed() {
    assert!(matches!(
        TuplePorts::<40>::new(40, 37, 38, 39),
        Err(Error::Invalid(_))
    ));
    let q = machine(Cmd::seq(set(38, true), set(39, true)), false);
    let p = query_ports().program(&q, 837, 851).unwrap();
    let mut d = p.initial([]);
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 3,
                max_stack_bits: 100,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(d.pc.is_some());
}
