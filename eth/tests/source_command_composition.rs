//! Independent source-command-tree receipts for query and counting wrappers.
//! The baselines copy their former ordering instead of using the shared helper.

use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd};
use lean_eth_reference::native_high::{self, clear_program, copy_program};
use lean_eth_reference::native_nodes;

fn source_clear<const R: usize, const S: usize>(port: usize) -> Result<Cmd<R, S>, Error> {
    Ok(Cmd::Call(clear_program(port, 0, 1)?))
}

// The original right-associated form used by NodeReadoutSpace.clearMany.
fn previous_node_clear(ports: &[usize]) -> Result<Cmd<40, 896>, Error> {
    let mut command = Cmd::Skip;
    for &stack in ports.iter().rev() {
        command = Cmd::seq(source_clear(stack)?, command);
    }
    Ok(command)
}

// BankRoutines.clearCmd does NOT append Skip after the last temporary clear.
fn previous_bank_clear(tmp: usize, changed: &[usize]) -> Result<Cmd<40, 896>, Error> {
    let mut command = source_clear(tmp)?;
    for &port in changed.iter().rev() {
        command = Cmd::seq(source_clear(port)?, command);
    }
    Ok(command)
}

#[test]
fn node_clear_many_keeps_order_duplicate_clears_and_skip_leaf() {
    for ports in [vec![], vec![301], vec![301, 302, 301], vec![0, 895]] {
        let actual = native_nodes::clear_many(&ports).unwrap();
        let expected = previous_node_clear(&ports).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(
            actual.compiled(0, 0).unwrap(),
            expected.compiled(0, 0).unwrap()
        );
    }
}

#[test]
fn counting_seed_preserves_the_bank_clear_terminal_and_nested_calls() {
    let reset = Cmd::seq(
        source_clear::<40, 896>(791).unwrap(),
        previous_bank_clear(791, &[330, 791, 792]).unwrap(),
    );
    let copy = Cmd::Call(copy_program(338, 792, 791, 0, 1).unwrap());
    let branch = Cmd::Call(
        native_high::branch_program()
            .unwrap()
            .lift::<40, 896>([0, 1], [792, 330])
            .unwrap(),
    );
    let expected = Cmd::seq(reset, Cmd::seq(copy, branch));
    let actual = native_high::seed_command().unwrap();
    assert_eq!(actual, expected);
    assert_eq!(
        actual.compiled(338, 330).unwrap(),
        expected.compiled(338, 330).unwrap()
    );
}

#[test]
fn counting_initializer_preserves_repeated_port_clears_and_guard_set() {
    let reset = Cmd::seq(
        source_clear::<40, 896>(792).unwrap(),
        previous_bank_clear(792, &[788, 789, 790, 323, 791, 792]).unwrap(),
    );
    let copy = Cmd::Call(copy_program(330, 789, 792, 0, 1).unwrap());
    let expected = Cmd::seq(
        reset,
        Cmd::seq(
            copy,
            Cmd::Atom(Atom::Set {
                dst: 21,
                value: true,
            }),
        ),
    );
    let actual = native_high::high_count_init_command().unwrap();
    assert_eq!(actual, expected);
    assert_eq!(
        actual.compiled(330, 788).unwrap(),
        expected.compiled(330, 788).unwrap()
    );
}
