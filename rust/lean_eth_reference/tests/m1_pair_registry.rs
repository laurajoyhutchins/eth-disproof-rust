//! Milestone-one #102: distinguish executable pair boundaries from the
//! still-unimplemented production signed-pair callback.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_difference_pairs::{pair_start_command, query_pairs_command};
use lean_eth_reference::native_pair_setup::expand_caller_command;
use lean_eth_reference::remaining::{self, Status};

fn stack<const R: usize, const S: usize>(cfg: &Config<R, S>, port: usize) -> Vec<bool> {
    cfg.stacks[port].iter().copied().collect()
}
fn put<const R: usize, const S: usize>(cfg: &mut Config<R, S>, port: usize, bits: &[bool]) {
    cfg.stacks[port] = bits.iter().copied().collect();
}
fn run<const R: usize, const S: usize>(p: &Program<R, S>, cfg: &mut Config<R, S>) {
    let result = p
        .run(
            cfg,
            RunLimits {
                max_steps: 1_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
    assert!(result.instructions > 0);
    assert_eq!(cfg.pc, None);
}

#[test]
fn registry_distinguishes_the_executable_controller_from_the_signed_query() {
    let find = |id| remaining::STAGES.iter().find(|s| s.id == id).unwrap();
    for id in ["pair_expand", "pair_start", "pair_dfs_controller"] {
        assert_eq!(find(id).status, Status::Executable);
    }
    for id in ["signature_tuple", "pair_dfs", "pair_commit", "query_stream"] {
        assert_eq!(find(id).status, Status::Stub);
    }
    assert_eq!(
        find("pair_dfs_controller").lean_symbol,
        "DifferencePairsProgram.command"
    );
    assert_eq!(find("pair_dfs").lean_symbol, "QueryStreamProgram.pairs");
    assert!(find("pair_dfs").requires.contains(&"signature_tuple"));
    assert!(find("pair_dfs").requires.contains(&"pair_dfs_controller"));
    assert!(
        include_str!("../reference/source-manifest.json").contains(
            "\"lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsProgram.lean\": \"0ffbcd1bfd8ed16e12e017c892bd7d92b59689ce\""
        )
    );
}

#[test]
fn public_pair_boundaries_compile_to_the_same_finite_source_tables() {
    let expand = remaining::query::pair_expand()
        .unwrap()
        .compiled(338, 857)
        .unwrap();
    let native_expand = expand_caller_command().unwrap().compiled(338, 857).unwrap();
    assert_eq!(expand, native_expand);

    let start = remaining::query::pair_start()
        .unwrap()
        .compiled(834, 857)
        .unwrap();
    let native_start = pair_start_command().unwrap().compiled(834, 857).unwrap();
    assert_eq!(start, native_start);

    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 500, src: 0 }),
    );
    let actual = remaining::query::pair_dfs_controller(callback.clone())
        .compiled(832, 834)
        .unwrap();
    let native = query_pairs_command(callback).compiled(832, 834).unwrap();
    assert_eq!(actual, native);
}

#[test]
fn public_pair_start_really_expands_masks_and_clears_dictionary() {
    let p = remaining::query::pair_start()
        .unwrap()
        .compiled(338, 857)
        .unwrap();
    let mut cfg = p.initial([]);
    // Descending fixed mask: the middle position is fixed.
    put(&mut cfg, 338, &[false, true, false]);
    // Residual E/U masks are reversed before the expansion call.
    put(&mut cfg, 834, &[true, false]);
    put(&mut cfg, 835, &[false, true]);
    put(&mut cfg, 851, &[true, false, true]);
    put(&mut cfg, 243, &[false, true]);
    put(&mut cfg, 895, &[true, true]);
    for scratch in 325..=329 {
        put(&mut cfg, scratch, &[true, false]);
    }
    cfg.regs[22] = true;
    let source_e = stack(&cfg, 834);
    let source_u = stack(&cfg, 835);

    run(&p, &mut cfg);

    assert_eq!(stack(&cfg, 858), vec![false, false, true]);
    assert_eq!(stack(&cfg, 857), vec![true, false, false]);
    assert_eq!(stack(&cfg, 338), vec![false, true, false]);
    assert_eq!(stack(&cfg, 834), source_e);
    assert_eq!(stack(&cfg, 835), source_u);
    assert_eq!(stack(&cfg, 243), vec![false, true]);
    assert_eq!(stack(&cfg, 895), vec![true, true]);
    assert!(cfg.regs[22]);
    for scratch in [325, 326, 327, 328, 329, 851] {
        assert!(stack(&cfg, scratch).is_empty(), "scratch {scratch}");
    }
}

#[test]
fn public_pruned_controller_counts_strict_pairs_without_a_host_callback() {
    let callback = Cmd::seq(
        Cmd::Atom(Atom::Set {
            dst: 0,
            value: true,
        }),
        Cmd::Atom(Atom::Push { stack: 500, src: 0 }),
    );
    let p = remaining::query::pair_dfs_controller(callback)
        .compiled(832, 834)
        .unwrap();
    // Independent combinatorics: at J=1 only empty E; at J=2 choose
    // either empty E or one of n coordinates with two choices for U.
    for (n, j, visits) in [
        (0, 0, 0),
        (0, 1, 1),
        (2, 0, 0),
        (2, 1, 1),
        (2, 2, 5),
        (3, 2, 7),
    ] {
        let mut cfg = p.initial([]);
        put(&mut cfg, 832, &vec![true; n]);
        put(&mut cfg, 833, &vec![true; j]);
        put(&mut cfg, 895, &[false, true]);
        run(&p, &mut cfg);
        assert_eq!(stack(&cfg, 500), vec![true; visits], "n={n}, J={j}");
        assert_eq!(stack(&cfg, 832), vec![true; n]);
        assert_eq!(stack(&cfg, 833), vec![true; j]);
        assert_eq!(stack(&cfg, 895), vec![false, true]);
        assert!(stack(&cfg, 834).is_empty());
        assert!(stack(&cfg, 835).is_empty());
        assert!(!cfg.regs[36]);
    }
}

#[test]
fn signed_pair_callback_remains_unimplemented_and_budget_refuses() {
    match remaining::query::pair_dfs() {
        Err(Error::NotImplemented("QueryStreamProgram.pairs")) => {}
        other => panic!("signed pair callback must fail closed: {other:?}"),
    }
    let p = remaining::query::pair_dfs_controller(Cmd::Skip)
        .compiled(832, 834)
        .unwrap();
    let mut cfg = p.initial([]);
    put(&mut cfg, 832, &[true, true, true]);
    put(&mut cfg, 833, &[true, true]);
    let err = p
        .run(
            &mut cfg,
            RunLimits {
                max_steps: 2,
                max_stack_bits: 100,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(
        cfg.pc.is_some(),
        "budget exhaustion is not a completed computation"
    );
}
