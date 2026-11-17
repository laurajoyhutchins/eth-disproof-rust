//! Compose the real first QueryStream node in source order and compare an
//! independently staged physical Rust replay. The next signed pair callback
//! is absent; no source-defined nonterminal count is produced.

use lean_eth_reference::bit_program::{Cmd, Config, RunLimits};
use lean_eth_reference::native_bootstrap;
use lean_eth_reference::native_layout;
use lean_eth_reference::native_nodes;
use lean_eth_reference::native_pair_setup;
use lean_eth_reference::native_query_first_node::{
    first_node_before_pairs_command, first_node_before_pairs_entry, first_node_before_pairs_program,
};
use lean_eth_reference::native_query_prefix;
use lean_eth_reference::native_tuple::encode_words;
use lean_eth_reference::remaining;
use std::collections::VecDeque;

fn put(d: &mut Config<40, 896>, port: usize, word: &[bool]) {
    d.stacks[port] = VecDeque::from(word.to_vec());
}

fn limits() -> RunLimits {
    RunLimits {
        max_steps: 30_000_000,
        max_stack_bits: 300_000,
    }
}

fn fixture(has_node: bool) -> Config<40, 896> {
    let p = first_node_before_pairs_program().unwrap();
    let mut state = p.initial(encode_words(&[vec![true]]).unwrap());
    put(&mut state, 338, &[false, true]);
    let nodes: Vec<Vec<bool>> = if has_node {
        vec![vec![true, false, true]]
    } else {
        vec![]
    };
    put(&mut state, 300, &encode_words(&nodes).unwrap());
    // Parking exactly the 14 source LayoutMasters words; the later loader
    // copies them to 128..141, never constructing numerical values in Rust.
    put(&mut state, 732, &[true, true, true]); // low 130: r
    put(
        &mut state,
        738,
        &[true, false, true, false, true, false, false],
    ); // low 136
    put(&mut state, 740, &[true, true, true]); // low 138
    put(&mut state, 741, &[true, true]); // low 139
    put(&mut state, 742, &[true; 13]); // low 140
    put(&mut state, 243, &[true, false, true]);
    put(&mut state, 323, &[]); // final QueryStream reconstruction is absent.
    state
}

fn replay(cmd: Cmd<40, 896>, state: &mut Config<40, 896>) -> u64 {
    let program = cmd.compiled(330, 832).unwrap();
    state.pc = Some(program.entry());
    let stats = program.run(state, limits()).unwrap();
    assert!(state.pc.is_none());
    stats.instructions
}

#[test]
fn one_node_composition_equals_independent_source_stage_replay() {
    for has_node in [false, true] {
        let whole = first_node_before_pairs_program().unwrap();
        let mut state = fixture(has_node);
        let mut other = state.clone();
        let stats = whole.run(&mut state, limits()).unwrap();
        assert!(state.pc.is_none());

        let mut stage_steps = 0;
        stage_steps += replay(
            native_query_prefix::prepare_high_command().unwrap(),
            &mut other,
        );
        stage_steps += replay(native_nodes::nodes_entry_command().unwrap(), &mut other);
        assert_eq!(other.regs[37], has_node, "node guard from physical source");

        if has_node {
            stage_steps += replay(native_nodes::begin_node_command().unwrap(), &mut other);
            stage_steps += replay(native_layout::command().unwrap(), &mut other);
            stage_steps += replay(
                native_bootstrap::bootstrap_node_command().unwrap(),
                &mut other,
            );
            stage_steps += replay(
                native_pair_setup::setup_caller_command().unwrap(),
                &mut other,
            );
            assert_eq!(
                other.stacks[832],
                VecDeque::from(vec![true]),
                "one false high coordinate is physically counted"
            );
            assert_eq!(
                other.stacks[833],
                VecDeque::from(vec![true, false, true]),
                "the original metadata word is retained"
            );
        }
        assert_eq!(state.regs, other.regs, "all registers agree");
        assert_eq!(state.stacks, other.stacks, "all 896 source stacks agree");
        assert!(state.stacks[323].is_empty(), "no fabricated query count");
        assert_eq!(state.stacks[300], fixture(has_node).stacks[300]);
        assert_eq!(state.stacks[338], fixture(has_node).stacks[338]);
        // Separate programs each execute their own terminal Halt.
        // The one composed source command has a single Halt and one
        // conditional branch, so the staged replay pays four additional
        // source instructions on the node-present path (none on no-node).
        let staged_halt_overhead = if has_node { 4 } else { 0 };
        assert_eq!(
            stats.instructions + staged_halt_overhead,
            stage_steps,
            "source instruction accounting must include the exact call boundary"
        );
        println!(
            "query_first_node has_node={has_node} source_instructions={} peak_live_stack_bits={} status=partial_before_signed_pairs count=NA",
            stats.instructions, stats.peak_stack_bits
        );
    }
}

#[test]
fn partial_command_is_the_original_source_order_not_a_counting_program() {
    let before_pair = first_node_before_pairs_command().unwrap();
    let manual = Cmd::seq(
        native_nodes::begin_node_command().unwrap(),
        Cmd::seq(
            native_layout::command().unwrap(),
            Cmd::seq(
                native_bootstrap::bootstrap_node_command().unwrap(),
                native_pair_setup::setup_caller_command().unwrap(),
            ),
        ),
    );
    assert_eq!(before_pair.size().unwrap(), manual.size().unwrap());
    assert_eq!(
        first_node_before_pairs_entry().unwrap().size().unwrap() + 1,
        first_node_before_pairs_program().unwrap().code().len()
    );
    assert!(matches!(
        remaining::query::command(),
        Err(lean_eth_reference::Error::NotImplemented(
            "QueryStreamProgram.command"
        ))
    ));
    assert!(matches!(
        remaining::query::pair_dfs(),
        Err(lean_eth_reference::Error::NotImplemented(
            "QueryStreamProgram.pairs"
        ))
    ));
}

#[test]
fn source_instruction_cap_refuses_composed_first_node() {
    let program = first_node_before_pairs_program().unwrap();
    let mut state = fixture(true);
    assert!(matches!(
        program.run(
            &mut state,
            RunLimits {
                max_steps: 1,
                max_stack_bits: 300_000
            }
        ),
        Err(lean_eth_reference::Error::Capacity(_))
    ));
    assert!(state.pc.is_some());
}
