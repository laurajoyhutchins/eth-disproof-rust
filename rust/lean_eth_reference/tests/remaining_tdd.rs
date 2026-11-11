//! Source-pinned scaffold contracts for the unfinished OpenAI ETH Rust path.
//! Active stub checks are TEMPORARY and must be retired as each stage is ported.
//! Ignored tests are ABI smoke gates, not source-refinement or correctness proof.
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
    // Milestone increments register new source stages. Enforce the exact
    // source nodes and graph invariants rather than a brittle stage count.
    for id in [
        "normalization_polarity",
        "normalization_record_reverse",
        "normalization_literal_dedup",
        "normalization_literal_cleanup",
        "normalization_full",
    ] {
        assert!(graph().contains_key(id), "missing stage: {id}");
    }
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

    let nodes = graph();
    for id in [
        "normalization_polarity",
        "normalization_record_reverse",
        "normalization_literal_dedup",
        "normalization_literal_cleanup",
        "normalization_negated_query",
        "normalization_tautology_core",
        "normalization_tautology_filter",
        "normalization_prefix",
    ] {
        assert_eq!(nodes[id].status, Status::Executable, "{id}");
        assert_eq!(nodes[id].machine, Machine::Local, "{id}");
    }
    assert_eq!(nodes["normalization_full"].status, Status::Stub);
    assert_eq!(nodes["frontend"].status, Status::Stub);
}

#[test]
fn registry_dependency_graph_has_no_orphaned_catalogue_entries() {
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

/// Check the *local manifest's shape*, not whether GitHub actually serves those
/// objects or that the Rust code refines the contents of a Lean source blob.
fn local_manifest_blob_sha<'a>(manifest: &'a str, path: &str) -> Option<&'a str> {
    let key = format!("\"lean/OAI/Algorithms/SubexponentialSAT/{path}\"");
    let mut matches = manifest.lines().filter_map(|line| {
        let tail = line.trim_start().strip_prefix(&key)?;
        let tail = tail.trim_start().strip_prefix(':')?.trim_start();
        let tail = tail.strip_prefix('"')?;
        let (sha, rest) = tail.split_once('"')?;
        (rest.trim().is_empty() || rest.trim() == ",").then_some(sha)
    });
    let sha = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    (sha.len() == 40
        && sha
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)))
    .then_some(sha)
}

#[test]
fn every_catalogued_source_has_an_exact_local_blob_pin() {
    let manifest = include_str!("../reference/source-manifest.json");
    assert!(manifest.contains(&format!("\"commit\": \"{LEAN_COMMIT}\"")));
    assert!(manifest.contains("\"repository\": \"openai/math\""));
    for stage in remaining::STAGES {
        assert!(
            local_manifest_blob_sha(manifest, stage.source_file).is_some(),
            "missing or malformed local upstream Git blob SHA for {}",
            stage.lean_symbol
        );
    }
}

#[test]
fn local_manifest_parser_rejects_wrong_names_duplicates_and_invalid_shas() {
    let path = "BitProgram.lean";
    let full = "lean/OAI/Algorithms/SubexponentialSAT/BitProgram.lean";
    let good = format!("  \"{full}\": \"{}\",", "a".repeat(40));
    assert_eq!(
        local_manifest_blob_sha(&good, path),
        Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
    );
    assert!(local_manifest_blob_sha(&good, "SubBitProgram.lean").is_none());
    assert!(local_manifest_blob_sha(&format!("{good}\n{good}"), path).is_none());
    assert!(local_manifest_blob_sha(&good.replace(&"a".repeat(40), "abc"), path).is_none());
    assert!(
        local_manifest_blob_sha(&good.replace(&"a".repeat(40), &"A".repeat(40)), path).is_none()
    );
}

#[test]
fn source_machine_dimensions_are_enforced_at_compile_time() {
    let _: fn() -> Result<Program<16, 768>, Error> = remaining::query::signature_bootstrap;
    let _: fn() -> Result<Cmd<40, 768>, Error> = remaining::high_query::preparation_low;
    let _: fn() -> Result<Cmd<40, 896>, Error> = remaining::high_query::preparation;
    let _: fn(usize) -> Result<Program<40, 896>, Error> = remaining::leaf::local_program;
    let _: fn(usize) -> Result<Program<80, 1220>, Error> = remaining::leaf::program;
    let _: fn(usize, usize, Cmd<80, 1220>) -> Result<Program<80, 1220>, Error> =
        remaining::outer::counting_program;
    let _: fn(Cmd<40, 896>) -> Result<Cmd<80, 1220>, Error> = remaining::leaf::execution;
    let _: fn(Cmd<80, 1220>) -> Result<Cmd<80, 1220>, Error> = remaining::leaf::terminal_dispatch;
    let _: fn() -> Result<Program<2, 2>, Error> = remaining::outer::negate_literal;
    let _: fn() -> Result<Program<3, 4>, Error> = remaining::outer::reverse_records;
    let _: fn() -> Result<Program<10, 8>, Error> = remaining::outer::dedup_literals;
    let _: fn() -> Result<Program<13, 11>, Error> = remaining::outer::clean_literals;
    let _: fn() -> Result<Program<2, 4>, Error> = remaining::outer::negated_query;
    let _: fn() -> Result<Program<10, 8>, Error> = remaining::outer::tautology_clause;
    let _: fn() -> Result<Program<13, 11>, Error> = remaining::outer::tautology_filter;
    let _: fn() -> Result<Program<13, 11>, Error> = remaining::outer::normalization_prefix;
}

#[test]
fn unfinished_query_stages_return_the_exact_source_identity() {
    use remaining::query as q;
    let bootstrap = q::signature_bootstrap().unwrap();
    assert_eq!(
        (bootstrap.input_stack(), bootstrap.output_stack()),
        (307, 647)
    );
    assert!(
        !q::pair_expand()
            .unwrap()
            .compiled(338, 857)
            .unwrap()
            .code()
            .is_empty()
    );
    assert_refuses(q::signature_loader(), "SignatureTupleLoader.loadHead");
    assert_refuses(q::query_visitor(), "QueryVisitorProgram.visitor");
    assert_refuses(q::signature_tuple(), "SignatureTupleComplete.command");
    assert!(
        !q::pair_start()
            .unwrap()
            .compiled(834, 857)
            .unwrap()
            .code()
            .is_empty()
    );
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
    // Generic source dispatch is an executable command factory. The real
    // nonterminal leaf remains unavailable and is still refused above.
    l::terminal_dispatch(Cmd::Skip).expect("source generic dispatch must compile");
}

#[test]
fn outer_and_noncomputable_fallback_cannot_return_a_fake_answer() {
    use remaining::outer as o;
    assert_refuses(o::frontend(), "Native.frontendCommand");
    // Physical positivity suffix is implemented, not a CNF counting oracle.
    o::answer_suffix().expect("source positivity suffix must compile");
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

// The following ignored tests currently fail because the stubs fail closed.
// Passing an ABI smoke test only demonstrates type/port compatibility. It does
// NOT establish source-table identity, Lean/Rust trace parity, exact arithmetic,
// end-to-end correctness or complexity. Behavioral oracles must be added before
// promoting any of them to a release acceptance gate.

#[test]
#[ignore = "RED TDD: implement exact SignatureHeadLoader.bootstrapProgram"]
fn pending_signature_bootstrap_abi_smoke_only() {
    let p = remaining::query::signature_bootstrap().expect("source bootstrap not implemented");
    assert_eq!((p.input_stack(), p.output_stack()), (307, 647));
    assert!(!p.code().is_empty());
}

#[test]
#[ignore = "RED TDD: implement QueryStreamProgram.program before enabling"]
fn pending_query_stream_abi_smoke_only() {
    let p = remaining::query::program().expect("real source query stream not implemented");
    assert_eq!((p.input_stack(), p.output_stack()), (330, 323));
    assert!(!p.code().is_empty());
}

#[test]
#[ignore = "RED TDD: implement actual native leaf, not the exponential semantic leaf"]
fn pending_native_leaf_abi_smoke_only() {
    let local = remaining::leaf::local_program(3).expect("local native leaf not implemented");
    assert_eq!((local.input_stack(), local.output_stack()), (784, 788));
    let outer = remaining::leaf::program(3).expect("lifted native leaf not implemented");
    assert_eq!((outer.input_stack(), outer.output_stack()), (265, 263));
}

/// Independent raw-literal truth-table oracle, deliberately not using Cnf::eval.
/// All fixtures have at most three variables and clauses of width at most three.
const COUNT_CASES: &[(usize, &[&[i32]], usize)] = &[
    (3, &[&[1, 2], &[1, 3]], 5),
    (3, &[], 8),
    (1, &[&[1], &[-1]], 0),
    (2, &[&[1, -1]], 4),
    (2, &[&[]], 0),
    (2, &[&[1, 2], &[-1, -2]], 2),
    (3, &[&[2]], 4),
    (3, &[&[1], &[2], &[3]], 1),
    (3, &[&[1, 2, 3]], 7),
];

fn brute_count_independent(variables: usize, clauses: &[&[i32]]) -> usize {
    assert!(variables < usize::BITS as usize);
    for clause in clauses {
        for &literal in *clause {
            assert!((1..=variables).contains(&(literal.unsigned_abs() as usize)));
        }
    }
    (0..(1usize << variables))
        .filter(|&assignment| {
            clauses.iter().all(|clause| {
                clause.iter().any(|&literal| {
                    let value = (assignment >> (literal.unsigned_abs() as usize - 1)) & 1 != 0;
                    value == (literal > 0)
                })
            })
        })
        .count()
}

fn make_dimacs(variables: usize, clauses: &[&[i32]]) -> String {
    let mut text = format!("p cnf {variables} {}\n", clauses.len());
    for clause in clauses {
        for literal in *clause {
            text.push_str(&format!("{literal} "));
        }
        text.push_str("0\n");
    }
    text
}

#[test]
fn goldens_cover_true_false_zero_empty_tautological_and_unused_variables() {
    for &(variables, clauses, expected) in COUNT_CASES {
        assert_eq!(brute_count_independent(variables, clauses), expected);
        let dimacs = make_dimacs(variables, clauses);
        let formula = parse_dimacs(&dimacs).unwrap();
        let mut semantic = 0;
        for mask in 0..(1u128 << variables) {
            if formula.eval(mask) {
                semantic += 1;
            }
        }
        assert_eq!(semantic, expected, "DIMACS semantics disagree: {dimacs}");
    }
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
    let leaf = remaining::leaf::command(3).expect("native leaf must be implemented first");
    let program = remaining::outer::counting_program(0, 3, leaf)
        .expect("native counting program not implemented");
    assert_eq!((program.input_stack(), program.output_stack()), (256, 1216));
    for &(variables, clauses, expected) in COUNT_CASES {
        let dimacs = make_dimacs(variables, clauses);
        let f = parse_dimacs(&dimacs).unwrap();
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
