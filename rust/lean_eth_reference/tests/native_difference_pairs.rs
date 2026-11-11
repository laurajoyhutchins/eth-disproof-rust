//! End-to-end source-machine tests for the pruned pair DFS.
//! The independent reference is `DifferencePairs.words`, not the ported
//! controller. Callback output is built by physical copy/push instructions.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::{Atom, Cmd, Config, Program, RunLimits};
use lean_eth_reference::native_difference_pairs::{
    PairPorts, pair_start_command, query_pair_ports, query_pairs_command, query_pairs_program,
    query_pairs_with_pair_start,
};
use lean_eth_reference::native_high::{clear_program, copy_program};
use lean_eth_reference::native_pair_setup::{expand_caller_command, setup_caller_command};

fn bits<const R: usize, const S: usize>(d: &Config<R, S>, port: usize) -> Vec<bool> {
    d.stacks[port].iter().copied().collect()
}
fn store<const R: usize, const S: usize>(d: &mut Config<R, S>, port: usize, word: &[bool]) {
    d.stacks[port] = word.iter().copied().collect();
}
fn run<const R: usize, const S: usize>(program: &Program<R, S>, d: &mut Config<R, S>) -> u64 {
    program
        .run(
            d,
            RunLimits {
                max_steps: 4_000_000,
                max_stack_bits: 500_000,
            },
        )
        .unwrap()
        .instructions
}

// None means coordinate not in E; Some(false) in E but not U;
// Some(true) in E and in U. An explicit independent recursive oracle.
fn words(n: usize, budget: usize) -> Vec<Vec<Option<bool>>> {
    if budget == 0 {
        return vec![];
    }
    if n == 0 {
        return vec![vec![]];
    }
    let mut output = Vec::new();
    for (prefix, remainder) in [
        (None, budget),
        (Some(false), budget - 1),
        (Some(true), budget - 1),
    ] {
        for tail in words(n - 1, remainder) {
            let mut w = vec![prefix];
            w.extend(tail);
            output.push(w);
        }
    }
    output
}
fn raw_words(w: &[Option<bool>]) -> (Vec<bool>, Vec<bool>) {
    (
        w.iter().map(Option::is_some).collect(),
        w.iter().map(|v| v.unwrap_or(false)).collect(),
    )
}

// Source `QueryStreamProgram.pairs` callback contract permits arbitrary
// scratch/reg writes except to the persistent controller ports. Every visit
// appends one fixed-width E and U word to the two physical log stacks.
fn log_masks(e: usize, u: usize, output_e: usize, output_u: usize) -> Cmd<40, 896> {
    Cmd::seq(
        Cmd::Call(copy_program(e, output_e, 509, 0, 1).unwrap()),
        Cmd::seq(
            Cmd::Call(copy_program(u, output_u, 509, 0, 1).unwrap()),
            Cmd::seq(
                Cmd::Atom(Atom::Set {
                    dst: 0,
                    value: true,
                }),
                Cmd::Atom(Atom::Push { stack: 502, src: 0 }),
            ),
        ),
    )
}
fn decode_visit_logs(
    d: &Config<40, 896>,
    n: usize,
    count: usize,
    e: usize,
    u: usize,
) -> Vec<(Vec<bool>, Vec<bool>)> {
    let a = bits(d, e);
    let b = bits(d, u);
    assert_eq!(a.len(), n * count);
    assert_eq!(b.len(), n * count);
    let mut seen: Vec<_> = a
        .chunks(n.max(1))
        .zip(b.chunks(n.max(1)))
        .map(|(x, y)| (x.to_vec(), y.to_vec()))
        .collect();
    if n == 0 {
        seen = vec![(vec![], vec![]); count];
    }
    seen.reverse();
    seen
}

#[test]
fn query_source_ports_and_injective_port_validation() {
    let p = query_pair_ports();
    assert_eq!(p.registers(), [0, 1, 2, 3, 4]);
    assert_eq!(p.stacks(), [832, 833, 834, 835]);
    assert!(matches!(
        PairPorts::<5, 4>::new([0, 1, 2, 3, 3], [0, 1, 2, 3]),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(
        PairPorts::<5, 4>::new([0, 1, 2, 3, 5], [0, 1, 2, 3]),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(
        PairPorts::<5, 4>::new([0, 1, 2, 3, 4], [0, 1, 2, 2]),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(
        PairPorts::<5, 4>::new([0, 1, 2, 3, 4], [0, 1, 2, 4]),
        Err(Error::Invalid(_))
    ));
}

#[test]
fn exact_full_visit_order_matches_independent_lean_words() {
    let p = query_pairs_program(log_masks(834, 835, 500, 501)).unwrap();
    assert_eq!(p.input_stack(), 832);
    assert_eq!(p.output_stack(), 834);
    for n in 0..=5 {
        for budget in 0..=n + 2 {
            let expected = words(n, budget);
            let mut d = p.initial([]);
            store(&mut d, 832, &vec![true; n]);
            store(&mut d, 833, &vec![true; budget]);
            d.regs[36] = true; // tuple controller register, not pair controller
            store(&mut d, 895, &[false, true, false]);
            let steps = run(&p, &mut d);
            assert!(steps > 0);
            assert_eq!(d.pc, None);
            assert_eq!(bits(&d, 502).len(), expected.len(), "n={n}, J={budget}");
            let visited = decode_visit_logs(&d, n, expected.len(), 500, 501);
            let wanted: Vec<_> = expected
                .iter()
                .map(|w| {
                    let (mut outer, mut inner) = raw_words(w);
                    outer.reverse();
                    inner.reverse();
                    (outer, inner)
                })
                .collect();
            assert_eq!(visited, wanted, "n={n}, J={budget}");
            assert_eq!(
                bits(&d, 832),
                vec![true; n],
                "restore depth n={n} J={budget}"
            );
            assert_eq!(
                bits(&d, 833),
                vec![true; budget],
                "restore budget n={n} J={budget}"
            );
            assert!(bits(&d, 834).is_empty());
            assert!(bits(&d, 835).is_empty());
            assert!(bits(&d, 509).is_empty());
            assert_eq!(bits(&d, 895), vec![false, true, false]);
            assert!(!d.regs[1]);
            assert!(d.regs[36], "tuple controller frame must remain untouched");
        }
    }
}

#[test]
fn signed_pair_pruning_respects_strict_budget() {
    for n in 0..=7 {
        for j in 0..=n + 2 {
            let oracle = words(n, j);
            let p = query_pairs_program(Cmd::Atom(Atom::Push { stack: 502, src: 0 })).unwrap();
            let mut d = p.initial([]);
            store(&mut d, 832, &vec![true; n]);
            store(&mut d, 833, &vec![true; j]);
            run(&p, &mut d);
            assert_eq!(bits(&d, 502).len(), oracle.len(), "n={n}, J={j}");
            // Each oracle word represents an E/U pair and U is a subset of E.
            assert!(
                oracle
                    .iter()
                    .all(|w| w.iter().filter(|o| o.is_some()).count() < j)
            );
        }
    }
}

#[test]
fn exhausted_budget_stops_without_callback_or_consuming_depth() {
    let p = query_pairs_program(Cmd::Atom(Atom::Set {
        dst: 10,
        value: true,
    }))
    .unwrap();
    let mut d = p.initial([]);
    store(&mut d, 832, &[true, true, true]);
    store(&mut d, 833, &[]);
    run(&p, &mut d);
    assert!(!d.regs[10]);
    assert_eq!(bits(&d, 832), vec![true, true, true]);
    assert!(bits(&d, 834).is_empty());
}

#[test]
fn a_real_pair_start_expands_each_leaf_and_preserves_controller_banks() {
    let whole = Cmd::seq(
        setup_caller_command().unwrap(),
        query_pairs_with_pair_start(log_masks(858, 857, 500, 501)).unwrap(),
    );
    let program = whole.compiled(338, 857).unwrap();
    for ambient in 0..=6usize {
        for fixed in 0..(1usize << ambient) {
            let high_desc: Vec<bool> = (0..ambient).rev().map(|i| fixed & (1 << i) != 0).collect();
            let free = high_desc.iter().filter(|&&b| !b).count();
            let j = (free + 1).min(3);
            let reference = words(free, j);
            let mut d = program.initial([]);
            store(&mut d, 338, &high_desc);
            store(&mut d, 243, &vec![true; j]);
            store(&mut d, 895, &[true, false, true]);
            store(&mut d, 851, &[true, true, true]);
            run(&program, &mut d);
            assert_eq!(bits(&d, 502).len(), reference.len());
            let visited = decode_visit_logs(&d, ambient, reference.len(), 500, 501);
            let mut expected: Vec<(Vec<bool>, Vec<bool>)> = Vec::new();
            for word in &reference {
                let (e, u) = raw_words(word);
                let mut e_iter = e.into_iter();
                let mut u_iter = u.into_iter();
                let (mut ambient_e, mut ambient_u) = (Vec::new(), Vec::new());
                for i in 0..ambient {
                    if fixed & (1 << i) != 0 {
                        ambient_e.push(false);
                        ambient_u.push(false);
                    } else {
                        ambient_e.push(e_iter.next().unwrap());
                        ambient_u.push(u_iter.next().unwrap());
                    }
                }
                expected.push((ambient_e, ambient_u));
            }
            assert_eq!(visited, expected, "ambient={ambient},fixed={fixed}");
            assert_eq!(bits(&d, 832), vec![true; free]);
            assert_eq!(bits(&d, 833), vec![true; j]);
            for s in [325, 326, 327, 328, 329, 834, 835, 509, 851] {
                assert!(bits(&d, s).is_empty(), "port {s}");
            }
            assert_eq!(bits(&d, 338), high_desc);
            assert_eq!(bits(&d, 243), vec![true; j]);
            assert_eq!(bits(&d, 895), vec![true, false, true]);
        }
    }
}

#[test]
fn finite_machine_rejects_a_too_small_instruction_budget() {
    let p = query_pairs_program(log_masks(834, 835, 500, 501)).unwrap();
    let mut d = p.initial([]);
    store(&mut d, 832, &[true, true, true, true]);
    store(&mut d, 833, &[true, true, true]);
    let err = p
        .run(
            &mut d,
            RunLimits {
                max_steps: 12,
                max_stack_bits: 10000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(d.pc.is_some());
}

#[test]
fn source_table_composes_as_command_without_extra_intermediate_halting() {
    let cb = Cmd::Atom(Atom::Set {
        dst: 0,
        value: true,
    });
    let p = query_pairs_program(cb.clone()).unwrap();
    let q = query_pairs_command(cb).compiled(832, 834).unwrap();
    assert_eq!(p.code(), q.code());
    assert_eq!(p.entry(), q.entry());
}

#[test]
fn pair_start_is_exact_source_composition() {
    let actual = pair_start_command().unwrap().compiled(834, 857).unwrap();
    let source = Cmd::seq(
        Cmd::Call(clear_program(851, 0, 1).unwrap()),
        expand_caller_command().unwrap(),
    )
    .compiled(834, 857)
    .unwrap();
    assert_eq!(actual.code(), source.code());
    assert_eq!(actual.entry(), source.entry());
}

#[test]
fn callback_may_overwrite_all_five_controller_registers() {
    let mut callback = log_masks(834, 835, 500, 501);
    for register in 0..5 {
        callback = Cmd::seq(
            callback,
            Cmd::Atom(Atom::Set {
                dst: register,
                value: register % 2 == 0,
            }),
        );
    }
    let p = query_pairs_program(callback).unwrap();
    for n in 0..=5 {
        for j in 0..=n + 1 {
            let mut d = p.initial([]);
            store(&mut d, 832, &vec![true; n]);
            store(&mut d, 833, &vec![true; j]);
            run(&p, &mut d);
            let oracle = words(n, j);
            assert_eq!(bits(&d, 502).len(), oracle.len());
            assert_eq!(bits(&d, 832), vec![true; n]);
            assert_eq!(bits(&d, 833), vec![true; j]);
            let want: Vec<_> = oracle
                .iter()
                .map(|w| {
                    let (mut e, mut u) = raw_words(w);
                    e.reverse();
                    u.reverse();
                    (e, u)
                })
                .collect();
            assert_eq!(decode_visit_logs(&d, n, oracle.len(), 500, 501), want);
        }
    }
}

#[test]
fn unary_budget_one_prunes_large_depth_without_exhaustive_visits() {
    let p = query_pairs_program(Cmd::Atom(Atom::Push { stack: 502, src: 0 })).unwrap();
    let mut d = p.initial([]);
    store(&mut d, 832, &vec![true; 512]);
    store(&mut d, 833, &[true]);
    let steps = run(&p, &mut d);
    assert_eq!(bits(&d, 502).len(), 1);
    assert_eq!(bits(&d, 832).len(), 512);
    assert_eq!(bits(&d, 833), vec![true]);
    assert!(steps < 15000, "paid instructions, not a mathematical bound");
}
