//! Stubs describe unfinished work without fabricating success.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Cmd, Instr, Program};
use lean_eth_reference::remaining::{self, Machine, Status};

fn refused<T: std::fmt::Debug>(result: Result<T, Error>) {
    assert!(
        matches!(&result, Err(Error::NotImplemented(_))),
        "unexpected result: {result:?}"
    );
}

#[test]
fn dependency_spine_is_ordered_and_machine_bounds_are_declared() {
    let mut known = std::collections::HashSet::new();
    for stage in remaining::STAGES {
        assert!(known.insert(stage.id), "duplicate stage: {}", stage.id);
        assert!(!stage.source_file.is_empty());
        assert!(!stage.lean_symbol.is_empty());
        assert!(stage.source_file.ends_with(".lean"));
        for prerequisite in stage.requires {
            assert!(
                known.contains(prerequisite),
                "{} before {}",
                prerequisite,
                stage.id
            );
        }
        if matches!(stage.status, Status::ProofObligation) {
            assert_eq!(stage.machine, Machine::Proof);
        }
        if matches!(stage.status, Status::Noncomputable) {
            assert_eq!(stage.id, "finite_fallback");
        }
    }
    assert_eq!(
        remaining::SOURCE_COMMIT,
        "4eaee87548250b2682affda7d05d947c05554bae"
    );
    // Stage count is intentionally not fixed: the dependency graph checks
    // uniqueness, source identity, topological order and final proof boundary.
    for id in [
        "normalization_polarity",
        "normalization_record_reverse",
        "normalization_literal_dedup",
        "normalization_literal_cleanup",
        "normalization_full",
    ] {
        assert!(known.contains(id), "missing source stage: {id}");
    }
    assert_eq!(remaining::STAGES.last().unwrap().id, "final_theorem");
}

#[test]
fn unported_query_and_leaf_commands_refuse_all_parameters() {
    use remaining::{high_query, leaf, query};
    let bootstrap = query::signature_bootstrap().unwrap();
    assert_eq!((bootstrap.input_stack(), bootstrap.output_stack()), (307, 647));
    refused(query::pair_expand());
    refused(query::signature_loader());
    refused(query::query_visitor());
    refused(query::signature_tuple());
    refused(query::pair_start());
    refused(query::pair_dfs());
    refused(query::pair_commit());
    refused(query::node_append());
    refused(query::node_finish());
    refused(query::node_loop());
    refused(query::reconstruction());
    refused(query::command());
    refused(query::program());
    refused(high_query::preparation_low());
    refused(high_query::preparation());
    refused(high_query::marked(0));
    refused(high_query::accepted(usize::MAX));
    refused(leaf::preparation());
    refused(leaf::rounds(Cmd::Skip));
    refused(leaf::accepted_stage(Cmd::Skip));
    refused(leaf::local_command(0));
    refused(leaf::local_program(3));
    refused(leaf::execution(Cmd::Skip));
    // The source generic dispatcher is now executable, but the actual
    // nonterminal leaf remains explicitly unavailable.
    leaf::terminal_dispatch(Cmd::Skip).expect("source generic dispatch must compile");
    refused(leaf::command(3));
    refused(leaf::program(3));
}

#[test]
fn outer_count_and_primitive_do_not_fall_back_to_semantic_enumeration() {
    use remaining::{outer, primitive};
    refused(outer::frontend());
    refused(outer::finite_fallback(0, Cmd::Skip));
    refused(outer::finite_fallback(usize::MAX, Cmd::Skip));
    refused(outer::setup(2));
    refused(outer::dfs(2, Cmd::Skip));
    // The physical full-word positivity suffix is executable; it does not
    // compute a CNF count by itself.
    outer::answer_suffix().expect("source positivity suffix must compile");
    refused(outer::outer_command(2, Cmd::Skip));
    refused(outer::entry(0, Cmd::Skip));
    refused(outer::counting_program(100, 2, Cmd::Skip));
    let trivial = Program::<2, 2>::new(0, 1, 0, vec![Instr::Halt]).unwrap();
    refused(primitive::compile(&trivial));
}
