//! Source-bound M1 `NodeReadoutSpace` ABI and real scratch prefix.
//! No fake numeric `MomentsReadoutProgram` is substituted for the missing port.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, RunLimits};
use lean_eth_reference::native_node_readout::{
    READOUT_REGISTERS, clear_ports, clear_prefix_command, lift_readout_program,
    node_append_readout_prefix, readout_stack_ports, scratch_ports,
};
use std::collections::HashSet;

fn put(d: &mut Config<40, 896>, p: usize, bits: &[bool]) {
    d.stacks[p] = bits.iter().copied().collect();
}
fn get(d: &Config<40, 896>, p: usize) -> Vec<bool> {
    d.stacks[p].iter().copied().collect()
}

const EXPECTED: [usize; 40] = [
    862, 89, 90, 91, 92, 5, 94, 95, 96, 97, 98, 99, 12, 101, 102, 850, 104, 105, 106, 107, 108,
    109, 110, 111, 39, 113, 114, 280, 212, 243, 118, 119, 120, 121, 122, 123, 128, 125, 126, 127,
];

#[test]
fn exact_source_port_map_is_injective_and_fin_cast_add_is_identity() {
    assert_eq!(READOUT_REGISTERS, [0, 1, 2, 3, 4, 5, 6, 7]);
    assert_eq!(readout_stack_ports(), EXPECTED);
    assert_eq!(EXPECTED.iter().copied().collect::<HashSet<_>>().len(), 40);
    assert!(EXPECTED.iter().all(|p| *p < 896));
}

#[test]
fn scratch_ports_are_exactly_the_source_ordered_nonmasters() {
    let masters: HashSet<_> = [862, 5, 12, 850, 39, 280, 212, 243, 128]
        .into_iter()
        .collect();
    let expected: Vec<_> = EXPECTED
        .into_iter()
        .filter(|p| !masters.contains(p))
        .collect();
    assert_eq!(scratch_ports(), expected);
    assert_eq!(scratch_ports().len(), 31);
    assert!(scratch_ports().iter().all(|p| (88..128).contains(p)));
    assert_eq!(clear_ports().first(), Some(&862));
    assert_eq!(&clear_ports()[1..], scratch_ports());
    assert_eq!(clear_ports().len(), 32);
}

#[test]
fn prefix_physically_clears_all_scratch_and_output_but_not_masters() {
    let p = clear_prefix_command().unwrap().compiled(850, 862).unwrap();
    for n in 0..=3 {
        let mut d = p.initial([]);
        let scratch = clear_ports();
        for &port in &scratch {
            put(&mut d, port, &vec![true; n]);
        }
        for (port, word) in [
            (5, vec![true, false]),
            (12, vec![false, true, true]),
            (39, vec![true]),
            (850, vec![false, true]),
            (280, vec![false]),
            (212, vec![true, true]),
            (243, vec![false]),
            (128, vec![true, false]),
        ] {
            put(&mut d, port, &word);
        }
        put(&mut d, 863, &[true, false, true]);
        put(&mut d, 895, &[false, true]);
        d.regs[37] = true;
        let stats = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(
            stats.instructions,
            (32 * (2 * n + 3) + 1) as u64,
            "source clearCost + compiled halt"
        );
        assert_eq!(d.pc, None);
        for port in scratch {
            assert!(get(&d, port).is_empty(), "scratch {port}");
        }
        for (port, word) in [
            (5, vec![true, false]),
            (12, vec![false, true, true]),
            (39, vec![true]),
            (850, vec![false, true]),
            (280, vec![false]),
            (212, vec![true, true]),
            (243, vec![false]),
            (128, vec![true, false]),
        ] {
            assert_eq!(get(&d, port), word, "master {port}");
        }
        assert_eq!(get(&d, 863), [true, false, true]);
        assert_eq!(get(&d, 895), [false, true]);
        assert!(d.regs[37]);
    }
}

#[test]
fn lifted_machine_uses_true_source_register_and_stack_maps() {
    // This small independent machine is an ABI probe, NOT a numerical readout.
    let local = Cmd::<8, 40>::seq(
        Cmd::Atom(Atom::Set {
            dst: 3,
            value: true,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Push { stack: 0, src: 3 }),
            Cmd::seq(
                Cmd::Atom(Atom::Push { stack: 15, src: 3 }),
                Cmd::Atom(Atom::Push { stack: 39, src: 3 }),
            ),
        ),
    )
    .compiled(0, 39)
    .unwrap();
    let p = lift_readout_program(local)
        .unwrap()
        .compiled(862, 127)
        .unwrap();
    let mut d = p.initial([]);
    d.regs[35] = true;
    put(&mut d, 862, &[false]);
    put(&mut d, 850, &[false]);
    put(&mut d, 127, &[false]);
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 862), [true, false]);
    assert_eq!(get(&d, 850), [true, false]);
    assert_eq!(get(&d, 127), [true, false]);
    assert!(d.regs[3]);
    assert!(d.regs[35]);
}

#[test]
fn node_append_prefix_really_prepares_masters_then_clears_readout_work() {
    let p = node_append_readout_prefix()
        .unwrap()
        .compiled(194, 862)
        .unwrap();
    let mut d = p.initial([]);
    for port in [5, 12, 39, 89, 862] {
        put(&mut d, port, &[true, false]);
    }
    for &port in &scratch_ports() {
        put(&mut d, port, &[false, true]);
    }
    put(&mut d, 194, &[true, false, true]);
    put(&mut d, 202, &[false, false]);
    put(&mut d, 204, &[true, true]);
    put(&mut d, 850, &[true, false]);
    put(&mut d, 863, &[false, true]);
    put(&mut d, 895, &[true]);
    d.regs[37] = true;
    p.run(&mut d, RunLimits::default()).unwrap();
    assert_eq!(get(&d, 5), [true, false, true]);
    assert_eq!(get(&d, 12), [false, false]);
    assert_eq!(get(&d, 39), [true, true]);
    for port in clear_ports() {
        assert!(get(&d, port).is_empty(), "port {port}");
    }
    assert_eq!(get(&d, 850), [true, false]);
    assert_eq!(get(&d, 863), [false, true]);
    assert_eq!(get(&d, 895), [true]);
    assert!(d.regs[37]);
}

#[test]
fn resource_limit_does_not_turn_incomplete_readout_into_a_halt() {
    let p = node_append_readout_prefix()
        .unwrap()
        .compiled(194, 862)
        .unwrap();
    let mut d = p.initial([]);
    put(&mut d, 194, &[true, false, true]);
    let error = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 100,
            },
        )
        .unwrap_err();
    assert!(matches!(error, Error::Capacity(_)));
    assert!(d.pc.is_some());
}
