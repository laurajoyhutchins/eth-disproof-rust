//! Source-order integration for the real NodeAppendSpace control structure.
//! The numerical moments program supplied here is a diagnostic fixture, not
//! the original source readout. This tests the composition seam, not SAT counts.

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_node_append;
use lean_eth_reference::native_node_readout::{
    clear_prefix_command, lift_readout_program, node_append_with_readout,
};
use std::collections::VecDeque;

fn readout_fixture() -> Program<8, 40> {
    // Reads a master staged by prepare (local stack 5), then writes one bit
    // into the readout output (local stack 0). No semantic count shortcut.
    Cmd::<8, 40>::seq(
        Cmd::Atom(Atom::Peek {
            stack: 5,
            value: 2,
            present: 3,
        }),
        Cmd::Atom(Atom::Push { stack: 0, src: 2 }),
    )
    .compiled(5, 0)
    .unwrap()
}

fn put(state: &mut Config<40, 896>, port: usize, bits: &[bool]) {
    state.stacks[port] = VecDeque::from(bits.to_vec());
}

fn word(state: &Config<40, 896>, port: usize) -> Vec<bool> {
    state.stacks[port].iter().copied().collect()
}

#[test]
fn physical_code_matches_the_original_nested_source_commands() {
    // QueryNodeFinish calls NodeAppendSpace.command, whose exact source tree
    // is seq prepare (seq (seq clearPrefix (call readout)) append).
    // Comparing *all* compiled instructions catches changes to source sites.
    let expected = Cmd::seq(
        native_node_append::prepare_command().unwrap(),
        Cmd::seq(
            Cmd::seq(
                clear_prefix_command().unwrap(),
                lift_readout_program(readout_fixture()).unwrap(),
            ),
            native_node_append::append_command().unwrap(),
        ),
    )
    .compiled(850, 863)
    .unwrap();
    let actual = node_append_with_readout(readout_fixture())
        .unwrap()
        .compiled(850, 863)
        .unwrap();
    assert_eq!(actual.code(), expected.code());
}

#[test]
fn physical_readout_uses_prepared_master_and_appends_in_source_order() {
    let program = node_append_with_readout(readout_fixture())
        .unwrap()
        .compiled(850, 863)
        .unwrap();
    let mut state = program.initial(Vec::<bool>::new());

    // Deliberately dirty source, destination, scratch and saved-stream banks.
    put(&mut state, 194, &[true, false]);
    put(&mut state, 202, &[false, true]);
    put(&mut state, 204, &[true, true, false]);
    put(&mut state, 5, &[false]);
    put(&mut state, 12, &[true]);
    put(&mut state, 39, &[false]);
    put(&mut state, 89, &[false, true]);
    put(&mut state, 862, &[false, false]);
    put(&mut state, 863, &[false, true]);
    put(&mut state, 850, &[true, false]);
    put(&mut state, 895, &[true, false, true]);
    state.regs[37] = true;

    program.run(&mut state, RunLimits::default()).unwrap();

    assert_eq!(state.pc, None);
    assert_eq!(word(&state, 5), vec![true, false]); // from 194, not stale 5
    assert_eq!(word(&state, 12), vec![false, true]); // from 202
    assert_eq!(word(&state, 39), vec![true, true, false]); // from 204
    assert_eq!(word(&state, 863), vec![false, true, true]); // old stream + readout
    assert!(word(&state, 862).is_empty());
    assert!(word(&state, 89).is_empty());
    assert_eq!(word(&state, 194), vec![true, false]);
    assert_eq!(word(&state, 202), vec![false, true]);
    assert_eq!(word(&state, 204), vec![true, true, false]);
    assert_eq!(word(&state, 850), vec![true, false]);
    assert_eq!(word(&state, 895), vec![true, false, true]);
    assert!(state.regs[3]); // source-provided readout observed a present bit
    assert!(state.regs[37]); // protected controller register
}

#[test]
fn resource_refusal_is_not_reported_as_a_completed_node() {
    let program = node_append_with_readout(readout_fixture())
        .unwrap()
        .compiled(850, 863)
        .unwrap();
    let mut state = program.initial(Vec::<bool>::new());
    put(&mut state, 194, &[true]);
    put(&mut state, 863, &[false, true]);

    let error = program
        .run(
            &mut state,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 200,
            },
        )
        .unwrap_err();
    assert!(matches!(error, Error::Capacity(_)));
    assert!(state.pc.is_some());
    assert_eq!(word(&state, 863), vec![false, true]);
}
