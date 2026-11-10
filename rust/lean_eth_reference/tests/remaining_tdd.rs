//! Source-pinned TDD acceptance gates for the unfinished OpenAI ETH Rust path.
//! Green tests protect the stub ABI and executable seams. Ignored tests are
//! deliberately RED until the corresponding native program is implemented.
//! Do not mark an incomplete count or a diagnostic callback as a success.

use lean_eth_reference::bit_program::{Atom, Cmd, Instr, Program, RunLimits};
use lean_eth_reference::remaining::{self, Machine, Stage, Status};
use lean_eth_reference::{Error, parse_dimacs};
use std::collections::{HashMap, HashSet};

const LEAN_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";

fn assert_refuses<T: std::fmt::Debug>(result: Result<T, Error>, symbol: &'static str) {
    match result {
        Err(Error::NotImplemented(actual)) => assert_eq!(actual, symbol),
        other => panic!("{symbol} did not fail closed: {other:?}"),
    }
}

fn graph() -> HashMap<&'static str, &'static Stage> {
    remaining::STAGES.iter().map(|s| (s.id, s)).collect()
}

#[test]
fn registry_is_source_pinned_unique_and_topologically_sorted() {
    assert_eq!(remaining::SOURCE_COMMIT, LEAN_COMMIT);
    assert_eq!(remaining::STAGES.len(), 42);
    let mut seen = HashSet::new();
    for stage in remaining::STAGES {
        assert!(seen.insert(stage.id), "duplicated stage {}", stage.id);
        assert!(stage.source_file.ends_with(".lean"));
        assert!(!stage.lean_symbol.is_empty());
        for prerequisite in stage.requires {
            assert!(
                seen.contains(prerequisite),
                "{} has absent or future prerequisite {prerequisite}",
                stage.id
            );
            assert_ne!(*prerequisite, stage.id);
        }
    }
    assert_eq!(remaining::STAGES.last().unwrap().id, "final_theorem");
}

#[test]
fn every_stage_contributes_to_final_theorem_without_orphaned_work() {
    let nodes = graph();
    let mut pending = vec!["final_theorem"];
    let mut ancestors = HashSet::new();
    while let Some(id) = pending.pop() {
        if ancestors.insert(id) {
            let stage = nodes.get(id).expect("dependency references missing stage");
            pending.extend_from_slice(stage.requires);
        }
    }
    for stage in remaining::STAGES {
        assert!(ancestors.contains(stage.id), "orphan stage: {}", stage.id);
    }
}

#[test]
fn machine_transitions_are_explicit_and_final_proof_is_not_executable() {
    let nodes = graph();
    for stage in remaining::STAGES {
        match stage.machine {
            Machine::Local => {
                for prerequisite in stage.requires {
                    assert_eq!(nodes[prerequisite].machine, Machine::Local);
                }
            }
            Machine::Outer => {
                for prerequisite in stage.requires {
                    assert!(matches!(
                        nodes[prerequisite].machine,
                        Machine::Local | Machine::Outer
                    ));
                }
            }
            Machine::Tm2 => {
                assert_eq!(stage.id, "primitive_tm2");
                assert_eq!(stage.status, Status::Stub);
                assert_eq!(stage.requires, &["counting_program"]);
            }
            Machine::Proof => {
                assert_eq!(stage.id, "final_theorem");
                assert_eq!(stage.status, Status::ProofObligation);
                assert_eq!(stage.requires, &["primitive_tm2"]);
            }
        }
        if stage.status == Status::Noncomputable {
            assert_eq!(stage.id, "finite_fallback");
        }
    }
    assert!(
        nodes["high_query_marked"]
            .requires
            .contains(&"high_count_seed")
    );
    assert!(
        nodes["high_query_accepted"]
            .requires
            .contains(&"high_count_seed")
    );
}

#[test]
fn every_executable_stage_is_in_the_pinned_source_manifest() {
    let manifest = include_str!("../reference/source-manifest.json");
    assert!(manifest.contains(LEAN_COMMIT));
    for stage in remaining::STAGES
        .iter()
        .filter(|s| s.status == Status::Executable)
    {
        assert!(
            manifest.contains(stage.source_file),
            "missing upstream blob pin for {}",
            stage.lean_symbol
        );
    }
}

#[test]
fn source_machine_dimensions_are_enforced_at_compile_time() {
    let _: fn() -> Result<Program<40, 768>, Error> = remaining::query::signature_bootstrap;
    let _: fn() -> Result<Cmd<40, 768>, Error> = remaining::high_query::preparation_low;
    let _: fn() -> Result<Cmd<40, 896>, Error> = remaining::high_query::preparation;
    let _: fn(usize) -> Result<Program<40, 896>, Error> = remaining::leaf::local_program;
    let _: fn(usize) -> Result<Program<80, 1220>, Error> = remaining::leaf::program;
    let _: fn(usize, usize, Cmd<80, 1220>) -> Result<Program<80, 1220>, Error> =
        remaining::outer::counting_program;
    let _: fn(Cmd<40, 896>) -> Result<Cmd<80, 1220>, Error> = remaining::leaf::execution;
    let _: fn(Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> = remaining::leaf::terminal_dispatch;
}

#[test]
fn unfinished_query_stages_return_the_exact_source_identity() {
    use remaining::query as q;
    assert_refuses(
        q::signature_bootstrap(),
        "SignatureHeadLoader.bootstrapProgram",
    );
    assert_refuses(q::pair_expand(), "PairNativeSetup.expandCaller");
    assert_refuses(q::signature_loader(), "SignatureTupleLoader.loadHead");
    assert_refuses(q::query_visitor(), "QueryVisitorProgram.visitor");
    assert_refuses(q::signature_tuple(), "SignatureTupleComplete.command");
    assert_refuses(q::pair_start(), "QueryExecution.PairStart.command");
    assert_refuses(q::pair_dfs(), "QueryStreamProgram.pairs");
    assert_refuses(q::pair_commit(), "QueryAssembler.commitPair");
    assert_refuses(q::node_append(), "NodeAppendSpace.command");
    assert_refuses(q::node_finish(), "QueryNodeFinish.command");
    assert_refuses(q::node_loop(), "QueryStreamProgram.nodeLoop");
    assert_refuses(q::reconstruction(), "QueryReconstruction.command");
    assert_refuses(q::command(), "QueryStreamProgram.command");
    assert_refuses(q::program(), "QueryStreamProgram.program");
}

#[test]
fn unfinished_high_queries_refuse_even_at_extreme_clause_widths() {
    use remaining::high_query as h;
    assert_refuses(h::preparation_low(), "NativeQueryPreparation.command");
    assert_refuses(h::preparation(), "HighQueryProgram.prepare");
    for k in [0, 1, 2, 3, 8, usize::MAX] {
        assert_refuses(h::marked(k), "HighQueryProgram.marked");
        assert_refuses(h::accepted(k), "HighQueryProgram.accepted");
    }
}

#[test]
fn leaf_callbacks_cannot_be_replaced_by_skip_or_diagnostic_programs() {
    use remaining::leaf as l;
    assert_refuses(l::preparation(), "NativeLeafPreparation.command");
    for query in [
        Cmd::<40, 896>::Skip,
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
    ] {
        assert_refuses(l::rounds(query.clone()), "NativeLeafRun.roundsCommand");
        assert_refuses(
            l::accepted_stage(query.clone()),
            "AcceptedQueryStage.command",
        );
        assert_refuses(l::execution(query), "NativeLeafExecution.command");
    }
    for k in [0, 2, 3, usize::MAX] {
        assert_refuses(l::local_command(k), "NativeLeafProgram.localCommand");
        assert_refuses(l::local_program(k), "NativeLeafProgram.localProgram");
        assert_refuses(l::command(k), "NativeLeafProgram.command");
        assert_refuses(l::program(k), "NativeLeafProgram.program");
    }
    assert_refuses(
        l::terminal_dispatch(Cmd::Skip),
        "NativeLeafDispatch.command",
    );
}

#[test]
fn outer_and_noncomputable_fallback_cannot_return_a_fake_answer() {
    use remaining::outer as o;
    assert_refuses(o::frontend(), "Native.frontendCommand");
    assert_refuses(o::answer_suffix(), "Native.answerCommand");
    for cutoff in [0, 1, 64, usize::MAX] {
        assert_refuses(
            o::finite_fallback(cutoff, Cmd::Skip),
            "FiniteFallback.dispatchCommand (noncomputable lookup)",
        );
        assert_refuses(o::entry(cutoff, Cmd::Skip), "Native.entryCommand");
        assert_refuses(
            o::counting_program(cutoff, 3, Cmd::Skip),
            "Native.countingProgram",
        );
    }
    for width in [0, 2, 3, usize::MAX] {
        assert_refuses(o::setup(width), "Native.setupAfterFrontend");
        assert_refuses(o::dfs(width, Cmd::Skip), "DFSCountProgram.command");
        assert_refuses(o::outer_command(width, Cmd::Skip), "Native.outerCommand");
    }
}

#[test]
fn primitive_refinement_refuses_on_a_valid_executable_program() {
    let p = Program::<2, 2>::new(0, 1, 0, vec![Instr::Halt]).unwrap();
    let original = p.clone();
    assert_refuses(
        remaining::primitive::compile(&p),
        "BitProgram.tm / GuardedCompiler.primitive",
    );
    assert_eq!(p, original);
}

// The tests below intentionally FAIL when explicitly enabled. They become
// normal tests only as each corresponding command is implemented and verified
// against the original imported-source Lean trace.

#[test]
#[ignore = "RED TDD: implement exact SignatureHeadLoader.bootstrapProgram"]
fn pending_signature_bootstrap_has_native_low_bank_abi() {
    let p = remaining::query::signature_bootstrap().expect("source bootstrap not implemented");
    assert_eq!((p.input_stack(), p.output_stack()), (307, 647));
    assert!(!p.code().is_empty());
}

#[test]
#[ignore = "RED TDD: implement QueryStreamProgram.program before enabling"]
fn pending_query_stream_has_native_callback_abi() {
    let p = remaining::query::program().expect("real source query stream not implemented");
    assert_eq!((p.input_stack(), p.output_stack()), (330, 323));
    assert!(!p.code().is_empty());
}

#[test]
#[ignore = "RED TDD: implement actual native leaf, not the exponential semantic leaf"]
fn pending_native_leaf_has_source_abi() {
    let local = remaining::leaf::local_program(3).expect("local native leaf not implemented");
    assert_eq!((local.input_stack(), local.output_stack()), (784, 788));
    let outer = remaining::leaf::program(3).expect("lifted native leaf not implemented");
    assert_eq!((outer.input_stack(), outer.output_stack()), (265, 263));
}

fn binary_count_word(n: usize) -> Vec<bool> {
    if n == 0 {
        return vec![false];
    }
    let mut x = n;
    let mut word = Vec::new();
    while x > 0 {
        word.push(x & 1 != 0);
        x >>= 1;
    }
    word
}

#[test]
#[ignore = "RED TDD: full canonical native program, imported-Lean oracle and bounded execution required"]
fn pending_native_end_to_end_counts_both_sat_and_unsat() {
    let cases = [
        ("p cnf 3 2\n1 2 0\n1 3 0\n", 5usize),
        ("p cnf 3 0\n", 8),
        ("p cnf 1 2\n1 0\n-1 0\n", 0),
    ];
    let leaf = remaining::leaf::command(3).expect("native leaf must be implemented first");
    let program = remaining::outer::counting_program(0, 3, leaf)
        .expect("native counting program not implemented");
    assert_eq!((program.input_stack(), program.output_stack()), (256, 1216));
    for (dimacs, expected) in cases {
        let f = parse_dimacs(dimacs).unwrap();
        let encoded = f.encode_lean();
        let word = encoded.bytes().map(|bit| bit == b'1');
        let mut config = program.initial(word);
        let stats = program
            .run(
                &mut config,
                RunLimits {
                    max_steps: 20_000_000,
                    max_stack_bits: 20_000_000,
                },
            )
            .unwrap();
        assert!(stats.instructions > 0);
        assert_eq!(config.pc, None);
        assert_eq!(
            config.stacks[256].iter().copied().collect::<Vec<_>>(),
            binary_count_word(expected)
        );
        assert_eq!(
            config.stacks[1216].iter().copied().collect::<Vec<_>>(),
            vec![expected > 0]
        );
    }
}
