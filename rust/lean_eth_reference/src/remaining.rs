//! Unimplemented *source-defined* stages of the pinned OpenAI ETH executable path.
//! A stub is never a halt, a zero count, or a semantic SAT enumerator.
//! Lean: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Source paths below are relative to lean/OAI/Algorithms/SubexponentialSAT/.

use crate::Error;
use crate::bit_program::{Cmd, Program};

mod registry;
pub use registry::{Machine, Stage, Status, SOURCE_COMMIT, STAGES};

fn unavailable<T>(symbol: &'static str) -> Result<T, Error> {
    Err(Error::NotImplemented(symbol))
}

macro_rules! local_stub {
    ($name:ident, $symbol:literal) => {
        pub fn $name() -> Result<Cmd<40, 896>, Error> {
            unavailable($symbol)
        }
    };
}

/// The missing body of QueryStreamProgram.nodeLoop. Its first layout and
/// pair-setup components already execute elsewhere in this crate.
pub mod query {
    use super::*;
    /// The source-defined bootstrap compiles as a 16x768 local program.
    /// QueryStreamProgram.bootstrapNode lifts it to 40x896 separately.
    pub fn signature_bootstrap() -> Result<Program<16, 768>, Error> {
        crate::native_bootstrap::bootstrap_program()
    }
    /// Real lifted 16-register mask expansion, no diagnostic callback.
    /// Source PairNativeSetup.expandCaller; both inputs are preserved.
    pub fn pair_expand() -> Result<Cmd<40, 896>, Error> {
        crate::native_pair_setup::expand_caller_command()
    }
    local_stub!(signature_loader, "SignatureTupleLoader.loadHead");
    local_stub!(query_visitor, "QueryVisitorProgram.visitor");
    local_stub!(signature_tuple, "SignatureTupleComplete.command");
    /// Source QueryExecution.PairStart.command: reset dictionary then
    /// expand both masks physically through the finite BitProgram table.
    pub fn pair_start() -> Result<Cmd<40, 896>, Error> {
        crate::native_difference_pairs::pair_start_command()
    }

    /// Literal generic DifferencePairsProgram.command controller.
    /// Its argument is an already compiled physical command, not a host
    /// callback. It does NOT supply the unported signed tuple/commit body.
    pub fn pair_dfs_controller(callback: Cmd<40, 896>) -> Cmd<40, 896> {
        crate::native_difference_pairs::query_pairs_command(callback)
    }

    // QueryStreamProgram.pairs requires the signed pair callback from #103.
    // Its stub must not be mistaken for the independently executable controller.
    local_stub!(pair_dfs, "QueryStreamProgram.pairs");
    local_stub!(pair_commit, "QueryAssembler.commitPair");
    local_stub!(node_append, "NodeAppendSpace.command");
    local_stub!(node_finish, "QueryNodeFinish.command");
    local_stub!(node_loop, "QueryStreamProgram.nodeLoop");
    local_stub!(reconstruction, "QueryReconstruction.command");
    local_stub!(command, "QueryStreamProgram.command");
    pub fn program() -> Result<Program<40, 896>, Error> {
        unavailable("QueryStreamProgram.program")
    }
}

/// The actual marked and accepted query paths; neither is equivalent to the
/// existing diagnostic callback used by tuple enumeration tests.
pub mod high_query {
    use super::*;
    /// The source compiles a 40x768 low-bank command, then lifts it into the
    /// 40x896 marked-query address space.
    pub fn preparation_low() -> Result<Cmd<40, 768>, Error> {
        unavailable("NativeQueryPreparation.command")
    }
    local_stub!(preparation, "HighQueryProgram.prepare");
    pub fn marked(_k: usize) -> Result<Cmd<40, 896>, Error> {
        unavailable("HighQueryProgram.marked")
    }
    pub fn accepted(_k: usize) -> Result<Cmd<40, 896>, Error> {
        unavailable("HighQueryProgram.accepted")
    }
}

/// The fixed-width leaf, with its exact 40x896 -> 80x1220 boundary.
/// Do not call the exponential semantic LeafCounter in place of this port.
pub mod leaf {
    use super::*;
    local_stub!(preparation, "NativeLeafPreparation.command");
    pub fn rounds(_marked_query: Cmd<40, 896>) -> Result<Cmd<40, 896>, Error> {
        unavailable("NativeLeafRun.roundsCommand")
    }
    pub fn accepted_stage(_query: Cmd<40, 896>) -> Result<Cmd<40, 896>, Error> {
        unavailable("AcceptedQueryStage.command")
    }
    pub fn local_command(_k: usize) -> Result<Cmd<40, 896>, Error> {
        unavailable("NativeLeafProgram.localCommand")
    }
    pub fn local_program(_k: usize) -> Result<Program<40, 896>, Error> {
        unavailable("NativeLeafProgram.localProgram")
    }
    pub fn execution(_local_command: Cmd<40, 896>) -> Result<Cmd<80, 1220>, Error> {
        unavailable("NativeLeafExecution.command")
    }
    /// Source-defined seven-register, five-stack payload equality callback.
    /// This is NOT the full encoded-record membership search or terminal classifier.
    pub fn membership_callback() -> Result<Cmd<7, 5>, Error> {
        crate::native_membership::membership_callback_command()
    }
    /// Actual complete source encoded-list membership machine, not a SAT oracle.
    pub fn encoded_membership() -> Result<Program<7, 5>, Error> {
        crate::native_record_membership::raw_membership_program()
    }
    /// Actual lifted terminal classifier; only canonical encoded input is supported.
    pub fn terminal_classifier() -> Result<Cmd<80, 1220>, Error> {
        crate::native_terminal_classifier::terminal_classifier_command()
    }
    /// Actual source-ready terminal paths; the nonterminal leaf is still unsupported.
    pub fn terminal_ready() -> Result<Cmd<80, 1220>, Error> {
        crate::native_terminal_classifier::ready_command()
    }
    /// Actual source-native terminal power after the caller proves F is empty.
    pub fn terminal_power() -> Result<Cmd<80, 1220>, Error> {
        crate::native_terminal::terminal_power_command()
    }
    /// Actual source-native zero after the caller proves an empty clause.
    pub fn terminal_zero() -> Result<Cmd<80, 1220>, Error> {
        Ok(crate::native_terminal::terminal_zero_command())
    }
    /// Real source NativeLeafDispatch.command with a supplied physical leaf.
    /// This does not furnish the missing nonterminal NativeLeafProgram.
    pub fn terminal_dispatch(nonterminal: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
        crate::native_leaf_dispatch::command(nonterminal)
    }
    pub fn command(_k: usize) -> Result<Cmd<80, 1220>, Error> {
        unavailable("NativeLeafProgram.command")
    }
    pub fn program(_k: usize) -> Result<Program<80, 1220>, Error> {
        unavailable("NativeLeafProgram.program")
    }
}

/// Canonical frontend, bounded noncomputable fallback, DFS, and positivity.
/// FiniteFallback's source-chosen lookup table has no constructive Rust data.
pub mod outer {
    use super::*;
    /// Executable Lean FiniteFallback.cutoffCommand before dispatch.
    /// The bounded counting table and the outer entry remain unsupported.
    pub fn cutoff_scan(cutoff: usize) -> Result<Program<80, 1220>, Error> {
        crate::finite_fallback::cutoff_program(cutoff)
    }
    /// Source-defined physical header extraction only; not a complete frontend.
    pub fn ambient_header() -> Result<Cmd<80, 1220>, Error> {
        crate::native_ambient::ambient_command()
    }
    /// Actual source-linked 19-label unary parser and binary length stage.
    pub fn frontend_header() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend_header::header_command()
    }
    /// Source finite polarity-bit reversal for a single unary literal code.
    pub fn negate_literal() -> Result<Program<2, 2>, Error> {
        crate::native_normalization_primitives::negate_literal_program()
    }
    /// Source finite record-order reversal, before lifting to any bank.
    pub fn reverse_records() -> Result<Program<3, 4>, Error> {
        crate::native_normalization_primitives::reverse_records_program()
    }
    /// Full source finite literal deduplication within one framed clause.
    pub fn dedup_literals() -> Result<Program<10, 8>, Error> {
        crate::native_literal_dedup::dedup_program()
    }
    /// Source finite clause-wise literal cleanup on original 13x11 machine.
    /// This is not tautology removal, clause dedup or superset absorption.
    pub fn clean_literals() -> Result<Program<13, 11>, Error> {
        crate::native_literal_cleanup::clean_program()
    }
    /// Preserving reversed unary-polarity query with source 2x4 machine.
    pub fn negated_query() -> Result<Program<2, 4>, Error> {
        crate::native_negated_query::program()
    }
    /// Physical complementary-literal scanner on the original 10x8 bank.
    pub fn tautology_clause() -> Result<Program<10, 8>, Error> {
        crate::native_tautology_core::program()
    }
    /// Original formula-wide tautology filter on 13x11 source bank.
    /// Neither clause deduplication nor strict subset filtering is performed.
    pub fn tautology_filter() -> Result<Program<13, 11>, Error> {
        crate::native_tautology_filter::program()
    }
    /// Executable source prefix: literal cleanup then tautology filtering.
    /// Does not perform the later clause absorption or full frontend.
    pub fn normalization_prefix() -> Result<Program<13, 11>, Error> {
        crate::native_normalization_prefix::program()
    }
    /// Actual source finite clause subset machine on 10x8 bit ports.
    pub fn subset_clause() -> Result<Program<10, 8>, Error> {
        crate::native_clause_relations::subset_program()
    }
    /// Both directional physical subset checks, 12x10 machine.
    pub fn clause_relations() -> Result<Program<12, 10>, Error> {
        crate::native_clause_relations::relation_program()
    }
    /// Three-mode source record scan on encoded formula, 15x12.
    pub fn relation_scan(
        mode: crate::native_clause_relation_scan::Mode,
    ) -> Result<Program<15, 12>, Error> {
        crate::native_clause_relation_scan::program(mode)
    }
    /// Source physical preserving scanner on 15x13 work bank.
    pub fn preserving_relation_scan(
        mode: crate::native_clause_relation_scan::Mode,
    ) -> Result<Program<15, 13>, Error> {
        crate::native_clause_dedup::preserving_scan_program(mode)
    }
    /// Last-equivalent-clause selection with original source order.
    pub fn dedup_clauses() -> Result<Program<15, 16>, Error> {
        crate::native_clause_dedup::program()
    }
    /// Strict-subset physical self-filter, 15x16.
    pub fn filter_supersets() -> Result<Program<15, 16>, Error> {
        crate::native_clause_filter::self_filter_program(
            crate::native_clause_relation_scan::Mode::StrictSubset,
        )
    }
    /// Complete source normalization: literal cleanup, tautology filter,
    /// clause deduplication and strict-subset absorption. Not a SAT oracle.
    pub fn normalization_full() -> Result<Program<15, 16>, Error> {
        crate::native_normalization_full::program()
    }
    /// Physically execute full normalized-body transformation in Native's
    /// 80x1220 ABI, preserving original input stack 256 and binary header 267.
    pub fn frontend_normalization() -> Result<Cmd<80, 1220>, Error> {
        crate::native_outer_normalization::command()
    }
    /// Source-preserving body placement (1218 -> 265), not a CNF normalizer.
    pub fn place_body() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend_tail::place_body_command()
    }
    /// The two final source-native frontend operations. Header and
    /// normalization must have already executed on the real machine.
    pub fn frontend_tail() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend_tail::frontend_tail_command()
    }
    /// Full source-defined Native.frontendCommand. Input: canonical
    /// Encoding.encodeCNF on stack 256 with all work stacks initially empty.
    /// Output: normalized body 265, unary ambient 258, binary dimension 267,
    /// original encoded input preserved on 256. No #SAT count is produced.
    pub fn frontend() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend::command()
    }
    pub fn finite_fallback(_cutoff: usize, _large: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
        unavailable("FiniteFallback.dispatchCommand (noncomputable lookup)")
    }
    pub fn setup(_k: usize) -> Result<Cmd<80, 1220>, Error> {
        unavailable("Native.setupAfterFrontend")
    }
    pub fn dfs(_k: usize, _leaf: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
        unavailable("DFSCountProgram.command")
    }
    /// Complete source-defined physical full-word positivity suffix.
    /// This does not compute the count or make the outer DFS executable.
    pub fn answer_suffix() -> Result<Cmd<80, 1220>, Error> {
        crate::native_answer::answer_command()
    }
    pub fn outer_command(_k: usize, _leaf: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
        unavailable("Native.outerCommand")
    }
    pub fn entry(_cutoff: usize, _large: Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> {
        unavailable("Native.entryCommand")
    }
    pub fn counting_program(
        _cutoff: usize,
        _k: usize,
        _leaf: Cmd<80, 1220>,
    ) -> Result<Program<80, 1220>, Error> {
        unavailable("Native.countingProgram")
    }
}

/// A distinct TM2 primitive compiler is required to substantiate running time
/// and visited-space claims. Source BitProgram steps are not TM2 microsteps.
pub mod primitive {
    use super::*;
    #[derive(Debug)]
    pub struct Tm2Machine {
        _private: (),
    }
    pub fn compile<const R: usize, const S: usize>(
        _program: &Program<R, S>,
    ) -> Result<Tm2Machine, Error> {
        unavailable("BitProgram.tm / GuardedCompiler.primitive")
    }
}
