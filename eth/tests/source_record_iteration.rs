//! Independent reconstruction of the six pre-refactor record-iteration trees.
//! A command-tree identity check compares every nested finite instruction table.

use lean_eth_reference::bit_program::{Atom, Cmd};
use lean_eth_reference::native_clause_dedup;
use lean_eth_reference::native_clause_filter;
use lean_eth_reference::native_clause_relation_scan::{self, Mode};
use lean_eth_reference::native_membership;
use lean_eth_reference::native_normalization_primitives;
use lean_eth_reference::native_query_prefix;
use lean_eth_reference::native_record_membership;
use lean_eth_reference::native_tautology_filter;

/// Old source expression, deliberately not calling the production constructor.
fn previous<const R: usize, const S: usize>(
    tag: usize,
    present: usize,
    found: usize,
    source: usize,
    reader: Cmd<R, S>,
    callback: Cmd<R, S>,
) -> Cmd<R, S> {
    let advance = Cmd::ite(
        found,
        Cmd::Atom(Atom::Set {
            dst: tag,
            value: false,
        }),
        Cmd::Atom(Atom::Pop {
            stack: source,
            value: tag,
            present,
        }),
    );
    let body = Cmd::seq(reader, Cmd::seq(callback, advance));
    Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: found,
            value: false,
        }),
        Cmd::seq(
            Cmd::Atom(Atom::Pop {
                stack: source,
                value: tag,
                present,
            }),
            Cmd::while_(tag, body),
        ),
    )
}

fn assert_same<const R: usize, const S: usize>(
    new: Cmd<R, S>,
    old: Cmd<R, S>,
    input: usize,
    output: usize,
) {
    assert_eq!(new, old);
    assert_eq!(
        new.compiled(input, output).unwrap(),
        old.compiled(input, output).unwrap()
    );
}

#[test]
fn dedup_and_three_clause_filter_modes_match_the_previous_command_tree() {
    let reader = Cmd::Call(
        native_query_prefix::frame_program()
            .unwrap()
            .lift::<15, 16>([0, 1], [13, 15])
            .unwrap(),
    );
    assert_same(
        native_clause_dedup::scan_command().unwrap(),
        previous(
            0,
            1,
            14,
            13,
            reader.clone(),
            native_clause_dedup::dedup_callback().unwrap(),
        ),
        13,
        13,
    );
    for mode in [Mode::Equivalent, Mode::StrictSubset, Mode::MissingCore] {
        assert_same(
            native_clause_filter::filter_scan(mode).unwrap(),
            previous(
                0,
                1,
                14,
                13,
                reader.clone(),
                native_clause_dedup::filter_callback(mode).unwrap(),
            ),
            13,
            13,
        );
    }
}

#[test]
fn three_relation_modes_match_the_previous_command_tree() {
    let reader = Cmd::Call(
        native_query_prefix::frame_program()
            .unwrap()
            .lift::<15, 12>([12, 13], [10, 11])
            .unwrap(),
    );
    for mode in [Mode::Equivalent, Mode::StrictSubset, Mode::MissingCore] {
        assert_same(
            native_clause_relation_scan::scan_command(mode).unwrap(),
            previous(
                12,
                13,
                14,
                10,
                reader.clone(),
                native_clause_relation_scan::callback(mode).unwrap(),
            ),
            10,
            11,
        );
    }
}

#[test]
fn tautology_membership_and_reversal_keep_their_exact_source_syntax() {
    let frame = native_query_prefix::frame_program().unwrap();
    assert_same(
        native_tautology_filter::scan_command().unwrap(),
        previous(
            10,
            11,
            12,
            0,
            Cmd::Call(frame.lift::<13, 11>([10, 11], [0, 1]).unwrap()),
            native_tautology_filter::callback_command().unwrap(),
        ),
        0,
        0,
    );
    let membership_frame = native_record_membership::frame_program().unwrap();
    assert_same(
        native_record_membership::iterate_command().unwrap(),
        previous(
            5,
            6,
            4,
            0,
            Cmd::Call(membership_frame.lift::<7, 5>([5, 6], [0, 1]).unwrap()),
            native_membership::membership_callback_command().unwrap(),
        ),
        0,
        1,
    );
    let reader = Cmd::Call(
        native_record_membership::frame_program()
            .unwrap()
            .lift::<3, 4>([0, 1], [0, 3])
            .unwrap(),
    );
    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 2,
            value: true,
        }),
        native_normalization_primitives::emit_if_selected_command().unwrap(),
    );
    assert_same(
        native_normalization_primitives::reverse_records_command().unwrap(),
        previous(0, 1, 2, 0, reader, callback),
        0,
        2,
    );
}
