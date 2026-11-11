//! Unimplemented *source-defined* stages of the pinned OpenAI ETH executable path.
//! A stub is never a halt, a zero count, or a semantic SAT enumerator.
//! Lean: openai/math@4eaee87548250b2682affda7d05d947c05554bae.
//! Source paths below are relative to lean/OAI/Algorithms/SubexponentialSAT/.

use crate::Error;
use crate::bit_program::{Cmd, Program};

pub const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Executable,
    Partial,
    Stub,
    Noncomputable,
    ProofObligation,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Machine {
    Local,
    Outer,
    Tm2,
    Proof,
}
#[derive(Clone, Copy, Debug)]
pub struct Stage {
    pub id: &'static str,
    pub source_file: &'static str,
    pub lean_symbol: &'static str,
    pub status: Status,
    pub machine: Machine,
    pub requires: &'static [&'static str],
}

/// Execution/dependency spine, in prerequisite order. Executable means Rust
/// tests exist; imported-source Lean/Rust differential validation is pending.
/// Partial means only the identified control suffix/prefix is executable.
pub const STAGES: &[Stage] = &[
    Stage {
        id: "bit_machine",
        source_file: "BitProgram.lean",
        lean_symbol: "BitProgram.Instr",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &[],
    },
    Stage {
        id: "high_count_seed",
        source_file: "SqrtLogSpace/HighCountSeed.lean",
        lean_symbol: "HighCountSeed.initializeProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "high_tuple_loop",
        source_file: "ExecCNFTupleEnumeration.lean",
        lean_symbol: "ExecCNFTupleEnumeration.enumerate",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "prepare_high",
        source_file: "SqrtLogSpace/HighQueryAdapter.lean",
        lean_symbol: "HighQueryAdapter.prepareHigh",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "node_cursor",
        source_file: "SqrtLogSpace/QueryAssembler.lean",
        lean_symbol: "QueryAssembler.Nodes.beginNode",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "layout_load",
        source_file: "SqrtLogSpace/NativeLayoutLoad.lean",
        lean_symbol: "NativeLayoutLoad.command",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "pair_setup",
        source_file: "SqrtLogSpace/PairNativeSetup.lean",
        lean_symbol: "PairNativeSetup.setupCaller",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "node_finish_control",
        source_file: "SqrtLogSpace/QueryNodeFinish.lean",
        lean_symbol: "QueryNodeFinish.finishNode",
        status: Status::Partial,
        machine: Machine::Local,
        requires: &["node_cursor"],
    },
    Stage {
        id: "signature_bootstrap",
        source_file: "SqrtLogSpace/SignatureHeadLoader.lean",
        lean_symbol: "SignatureHeadLoader.bootstrapProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["layout_load"],
    },
    Stage {
        id: "pair_expand",
        source_file: "SqrtLogSpace/PairNativeSetup.lean",
        lean_symbol: "PairNativeSetup.expandCaller",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["pair_setup"],
    },
    Stage {
        id: "signature_loader",
        source_file: "SqrtLogSpace/SignatureTupleLoader.lean",
        lean_symbol: "SignatureTupleLoader.loadHead",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["signature_bootstrap"],
    },
    Stage {
        id: "query_visitor",
        source_file: "SqrtLogSpace/QueryVisitorProgram.lean",
        lean_symbol: "QueryVisitorProgram.visitor",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["signature_loader"],
    },
    Stage {
        id: "signature_tuple",
        source_file: "SqrtLogSpace/SignatureTupleCommand.lean",
        lean_symbol: "SignatureTupleComplete.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["signature_loader", "query_visitor"],
    },
    Stage {
        id: "pair_start",
        source_file: "SqrtLogSpace/QueryExecution.lean",
        lean_symbol: "QueryExecution.PairStart.command",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["pair_expand"],
    },
    Stage {
        id: "pair_dfs_controller",
        source_file: "SqrtLogSpace/DifferencePairsProgram.lean",
        lean_symbol: "DifferencePairsProgram.command",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "pair_dfs",
        source_file: "SqrtLogSpace/QueryStreamProgram.lean",
        lean_symbol: "QueryStreamProgram.pairs",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["pair_start", "pair_dfs_controller", "signature_tuple"],
    },
    Stage {
        id: "pair_commit",
        source_file: "SqrtLogSpace/QueryAssembler.lean",
        lean_symbol: "QueryAssembler.commitPair",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["pair_dfs"],
    },
    Stage {
        id: "node_append",
        source_file: "SqrtLogSpace/NodeAppendSpace.lean",
        lean_symbol: "NodeAppendSpace.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["pair_commit"],
    },
    Stage {
        id: "node_finish",
        source_file: "SqrtLogSpace/QueryNodeFinish.lean",
        lean_symbol: "QueryNodeFinish.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["node_append", "node_finish_control"],
    },
    Stage {
        id: "node_loop",
        source_file: "SqrtLogSpace/QueryStreamProgram.lean",
        lean_symbol: "QueryStreamProgram.nodeLoop",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &[
            "node_cursor",
            "layout_load",
            "signature_bootstrap",
            "pair_setup",
            "pair_dfs",
            "node_finish",
        ],
    },
    Stage {
        id: "reconstruction",
        source_file: "SqrtLogSpace/QueryReconstruction.lean",
        lean_symbol: "QueryReconstruction.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["node_loop"],
    },
    Stage {
        id: "query_stream",
        source_file: "SqrtLogSpace/QueryStreamProgram.lean",
        lean_symbol: "QueryStreamProgram.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["prepare_high", "node_loop", "reconstruction"],
    },
    Stage {
        id: "high_query_preparation_low",
        source_file: "SqrtLogSpace/NativeQueryPreparation.lean",
        lean_symbol: "NativeQueryPreparation.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "high_query_preparation",
        source_file: "SqrtLogSpace/HighQueryProgram.lean",
        lean_symbol: "HighQueryProgram.prepare",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["high_query_preparation_low"],
    },
    Stage {
        id: "high_query_marked",
        source_file: "SqrtLogSpace/HighQueryProgram.lean",
        lean_symbol: "HighQueryProgram.marked",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &[
            "high_count_seed",
            "high_query_preparation",
            "high_tuple_loop",
            "query_stream",
        ],
    },
    Stage {
        id: "high_query_accepted",
        source_file: "SqrtLogSpace/HighQueryProgram.lean",
        lean_symbol: "HighQueryProgram.accepted",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &[
            "high_count_seed",
            "high_query_preparation",
            "high_tuple_loop",
            "query_stream",
        ],
    },
    Stage {
        id: "leaf_preparation",
        source_file: "SqrtLogSpace/NativeLeafPreparation.lean",
        lean_symbol: "NativeLeafPreparation.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "greedy_rounds",
        source_file: "SqrtLogSpace/NativeLeafRun.lean",
        lean_symbol: "NativeLeafRun.roundsCommand",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["leaf_preparation", "high_query_marked"],
    },
    Stage {
        id: "accepted_stage",
        source_file: "SqrtLogSpace/AcceptedQueryStage.lean",
        lean_symbol: "AcceptedQueryStage.command",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["high_query_accepted"],
    },
    Stage {
        id: "leaf_local",
        source_file: "SqrtLogSpace/NativeLeafProgram.lean",
        lean_symbol: "NativeLeafProgram.localCommand",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["greedy_rounds", "accepted_stage"],
    },
    Stage {
        id: "leaf_execution",
        source_file: "SqrtLogSpace/NativeLeafExecution.lean",
        lean_symbol: "NativeLeafExecution.command",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["leaf_local"],
    },
    Stage {
        id: "encoded_membership_callback",
        source_file: "ExecCNFMembership.lean",
        lean_symbol: "ExecCNFMembership.callback",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "encoded_record_membership",
        source_file: "ExecCNFMembership.lean",
        lean_symbol: "ExecCNFMembership.rawMembershipProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["encoded_membership_callback"],
    },
    Stage {
        id: "terminal_power",
        source_file: "SqrtLogSpace/NativeTerminal.lean",
        lean_symbol: "NativeTerminal.power",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "terminal_zero",
        source_file: "SqrtLogSpace/NativeTerminal.lean",
        lean_symbol: "NativeTerminal.zero",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "terminal_classifier",
        source_file: "SqrtLogSpace/NativeTerminal.lean",
        lean_symbol: "NativeTerminal.classifier",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["encoded_record_membership"],
    },
    Stage {
        id: "terminal_ready",
        source_file: "SqrtLogSpace/NativeTerminal.lean",
        lean_symbol: "NativeTerminal.readyCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["terminal_classifier", "terminal_power", "terminal_zero"],
    },
    Stage {
        id: "terminal_dispatch",
        source_file: "SqrtLogSpace/NativeLeafDispatch.lean",
        lean_symbol: "NativeLeafDispatch.command",
        status: Status::Partial,
        machine: Machine::Outer,
        requires: &["terminal_ready", "leaf_execution"],
    },
    Stage {
        id: "leaf_command",
        source_file: "SqrtLogSpace/NativeLeafProgram.lean",
        lean_symbol: "NativeLeafProgram.command",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["terminal_dispatch"],
    },
    Stage {
        id: "ambient_header",
        source_file: "SqrtLogSpace/NativeFrontend.lean",
        lean_symbol: "Native.ambientCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "normalization_polarity",
        source_file: "SubexpNormalizeProgram.lean",
        lean_symbol: "SubexpNormalizeProgram.negateProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["bit_machine"],
    },
    Stage {
        id: "normalization_record_reverse",
        source_file: "SubexpNormalizeProgram.lean",
        lean_symbol: "SubexpNormalizeProgram.reverseRecordsProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["encoded_record_membership"],
    },
    Stage {
        id: "normalization_literal_dedup",
        source_file: "ExecLiteralDedupProgram.lean",
        lean_symbol: "ExecLiteralDedupProgram.dedupProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["normalization_record_reverse", "encoded_record_membership"],
    },
    Stage {
        id: "normalization_literal_cleanup",
        source_file: "ExecCleanLiteralsProgram.lean",
        lean_symbol: "ExecCleanLiteralsProgram.cleanProgram",
        status: Status::Executable,
        machine: Machine::Local,
        requires: &["normalization_literal_dedup"],
    },
    Stage {
        id: "normalization_full",
        source_file: "SubexpNormalizationProgram.lean",
        lean_symbol: "SubexpNormalizationProgram.program",
        status: Status::Stub,
        machine: Machine::Local,
        requires: &["normalization_literal_cleanup", "normalization_polarity"],
    },
    Stage {
        id: "frontend_header",
        source_file: "SqrtLogSpace/NativeProgram.lean",
        lean_symbol: "Native.headerCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "frontend_tail",
        source_file: "SqrtLogSpace/NativeFrontend.lean",
        lean_symbol: "Native.placeBodyCommand; Native.ambientCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["ambient_header"],
    },
    Stage {
        id: "frontend",
        source_file: "SqrtLogSpace/NativeFrontend.lean",
        lean_symbol: "Native.frontendCommand",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["frontend_header", "normalization_full", "frontend_tail"],
    },
    Stage {
        id: "cutoff_scan",
        source_file: "SqrtLogSpace/FiniteFallback.lean",
        lean_symbol: "FiniteFallback.cutoffCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "finite_fallback",
        source_file: "SqrtLogSpace/FiniteFallback.lean",
        lean_symbol: "FiniteFallback.dispatchCommand",
        status: Status::Noncomputable,
        machine: Machine::Outer,
        requires: &["frontend", "cutoff_scan"],
    },
    Stage {
        id: "outer_setup",
        source_file: "SqrtLogSpace/NativeSetupSpace.lean",
        lean_symbol: "Native.setupAfterFrontend",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["frontend"],
    },
    Stage {
        id: "outer_dfs",
        source_file: "SqrtLogSpace/DisjointReuse/DFSCountProgram.lean",
        lean_symbol: "DFSCountProgram.command",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["outer_setup", "leaf_command"],
    },
    Stage {
        id: "answer_suffix",
        source_file: "SqrtLogSpace/NativeProgram.lean",
        lean_symbol: "Native.answerCommand",
        status: Status::Executable,
        machine: Machine::Outer,
        requires: &["bit_machine"],
    },
    Stage {
        id: "outer_command",
        source_file: "SqrtLogSpace/NativeOuter.lean",
        lean_symbol: "Native.outerCommand",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["outer_setup", "outer_dfs", "answer_suffix"],
    },
    Stage {
        id: "entry",
        source_file: "SqrtLogSpace/NativeEntry.lean",
        lean_symbol: "Native.entryCommand",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["frontend", "finite_fallback", "outer_command"],
    },
    Stage {
        id: "counting_program",
        source_file: "SqrtLogSpace/NativeOuter.lean",
        lean_symbol: "Native.countingProgram",
        status: Status::Stub,
        machine: Machine::Outer,
        requires: &["entry"],
    },
    Stage {
        id: "primitive_tm2",
        source_file: "BitProgramCompile.lean",
        lean_symbol: "BitProgram.tm",
        status: Status::Stub,
        machine: Machine::Tm2,
        requires: &["counting_program"],
    },
    Stage {
        id: "final_theorem",
        source_file: "SqrtLogSpace/Final.lean",
        lean_symbol: "exact_count_and_sat",
        status: Status::ProofObligation,
        machine: Machine::Proof,
        requires: &["primitive_tm2"],
    },
];

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
macro_rules! outer_stub {
    ($name:ident, $symbol:literal) => {
        pub fn $name() -> Result<Cmd<80, 1220>, Error> {
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
    /// Source-preserving body placement (1218 -> 265), not a CNF normalizer.
    pub fn place_body() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend_tail::place_body_command()
    }
    /// The two final source-native frontend operations. Header and
    /// normalization must have already executed on the real machine.
    pub fn frontend_tail() -> Result<Cmd<80, 1220>, Error> {
        crate::native_frontend_tail::frontend_tail_command()
    }
    outer_stub!(frontend, "Native.frontendCommand");
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
