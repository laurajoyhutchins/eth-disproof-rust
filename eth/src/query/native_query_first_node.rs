//! Source-ordered first-node QueryStream execution, ending BEFORE pair DFS.
//!
//! Matches QueryStreamProgram.command -> nodes -> nodeBody on the first
//! iteration in openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! This is not QueryStreamProgram.command or a nonterminal #SAT counter.
//! The signed pair iterator, node finish and reconstruction remain unavailable.

use crate::Error;
use crate::bit_program::{Cmd, Program};
use crate::{
    native_bootstrap, native_layout, native_nodes, native_pair_setup, native_query_prefix,
};

/// Exactly the first four source commands in QueryStreamProgram.nodeBody:
/// beginNode; NativeLayoutLoad.command; bootstrapNode; setupCaller.
/// QueryStreamProgram.pairs is the next command and MUST NOT be skipped
/// when constructing a full query counter.
pub fn first_node_before_pairs_command() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        native_nodes::begin_node_command()?,
        Cmd::seq(
            native_layout::command()?,
            Cmd::seq(
                native_bootstrap::bootstrap_node_command()?,
                native_pair_setup::setup_caller_command()?,
            ),
        ),
    ))
}

/// Source first-node entry. QueryStream's nodes iterates while register 37 is
/// true; here one physical guard executes only the FIRST body, and the return
/// port is intentionally not the final reconstructed query count.
///
/// A zero-node table correctly executes no body. A nonempty table stops at
/// the first signed pair enumeration boundary; it never claims a full query.
pub fn first_node_before_pairs_entry() -> Result<Cmd<40, 896>, Error> {
    Ok(Cmd::seq(
        native_query_prefix::prepare_high_command()?,
        Cmd::seq(
            native_nodes::nodes_entry_command()?,
            Cmd::ite(37, first_node_before_pairs_command()?, Cmd::Skip),
        ),
    ))
}

pub fn first_node_before_pairs_program() -> Result<Program<40, 896>, Error> {
    first_node_before_pairs_entry()?.compiled(330, 832)
}
