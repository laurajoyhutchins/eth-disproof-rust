//! End-to-end source-machine acceptance with independent oracles in tests only.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_clause_dedup;
use lean_eth_reference::native_clause_filter;
use lean_eth_reference::native_clause_relation_scan::Mode;
use lean_eth_reference::native_clause_relations;
use lean_eth_reference::native_normalization_full;
use std::collections::VecDeque;

fn frame(bits: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for b in bits {
        out.extend([true, *b]);
    }
    out.push(false);
    out
}
fn list<T>(xs: &[T], enc: impl Fn(&T) -> Vec<bool>) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.push(true);
        out.extend(frame(&enc(x)));
    }
    out.push(false);
    out
}
fn unary(v: usize) -> Vec<bool> {
    let mut w = vec![true; v];
    w.push(false);
    w
}
fn clause(xs: &[usize]) -> Vec<bool> {
    list(xs, |v| unary(*v))
}
fn formula(xs: &[Vec<usize>]) -> Vec<bool> {
    list(xs, |row| clause(row))
}
fn subset(a: &[usize], b: &[usize]) -> bool {
    a.iter().all(|x| b.contains(x))
}
fn equiv(a: &[usize], b: &[usize]) -> bool {
    subset(a, b) && subset(b, a)
}
fn strict(a: &[usize], b: &[usize]) -> bool {
    subset(a, b) && !subset(b, a)
}
fn last<T: Clone>(xs: &[T], eq: impl Fn(&T, &T) -> bool) -> Vec<T> {
    xs.iter()
        .enumerate()
        .filter(|(i, x)| !xs[i + 1..].iter().any(|y| eq(x, y)))
        .map(|(_, x)| x.clone())
        .collect()
}
fn expected(rows: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let clean = rows
        .iter()
        .map(|row| last(row, |a, b| a == b))
        .filter(|row| !row.iter().any(|v| row.contains(&(v ^ 1))))
        .collect::<Vec<_>>();
    let unique = last(&clean, |a, b| equiv(a, b));
    unique
        .iter()
        .filter(|candidate| !unique.iter().any(|other| strict(other, candidate)))
        .cloned()
        .collect()
}
fn output<const R: usize, const S: usize>(
    c: &lean_eth_reference::bit_program::Config<R, S>,
    s: usize,
) -> Vec<bool> {
    c.stacks[s].iter().copied().collect()
}

#[test]
fn actual_source_dual_relation_preserves_both_clause_words() {
    let p = native_clause_relations::relation_program().unwrap();
    for a in [vec![], vec![0], vec![0, 2], vec![0, 2, 2]] {
        for b in [vec![], vec![0], vec![2, 0], vec![1, 3]] {
            let mut c = p.initial(clause(&a));
            c.stacks[9] = VecDeque::from(clause(&b));
            p.run(&mut c, RunLimits::default()).unwrap();
            assert_eq!(
                (c.regs[10], c.regs[11], c.regs[9]),
                (equiv(&a, &b), strict(&a, &b), !subset(&b, &a))
            );
            assert_eq!(output(&c, 8), clause(&a));
            assert_eq!(output(&c, 9), clause(&b));
            for i in 0..8 {
                assert!(c.stacks[i].is_empty());
            }
        }
    }
}

#[test]
fn clause_dedup_and_strict_subset_removal_are_distinct_executable_passes() {
    let rows = vec![vec![0, 2], vec![2, 0], vec![0], vec![1, 3], vec![0, 2, 4]];
    let p = native_clause_dedup::program().unwrap();
    let mut d = p.initial(formula(&rows));
    p.run(&mut d, RunLimits::default()).unwrap();
    let dedup = last(&rows, |a, b| equiv(a, b));
    assert_eq!(output(&d, 13), formula(&dedup));
    let f = native_clause_filter::self_filter_program(Mode::StrictSubset).unwrap();
    let mut s = f.initial(formula(&dedup));
    f.run(&mut s, RunLimits::default()).unwrap();
    let retained = dedup
        .iter()
        .filter(|q| !dedup.iter().any(|c| strict(c, q)))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(output(&s, 13), formula(&retained));
    for i in 0..16 {
        if i != 13 {
            assert!(d.stacks[i].is_empty());
            assert!(s.stacks[i].is_empty());
        }
    }
}

#[test]
fn complete_source_normalizer_matches_oracle_across_randomized_formulas() {
    let p = native_normalization_full::program().unwrap();
    let mut seed = 0xcaa9aa097d371834_u64;
    let mut random = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    let mut fixtures = vec![
        vec![],
        vec![vec![]],
        vec![vec![0, 1]],
        vec![vec![0], vec![0, 2], vec![0, 2, 4]],
    ];
    for _ in 0..50 {
        let n = (random() % 7) as usize;
        fixtures.push(
            (0..n)
                .map(|_| {
                    let k = (random() % 7) as usize;
                    (0..k).map(|_| (random() % 10) as usize).collect()
                })
                .collect(),
        );
    }
    for rows in fixtures {
        let mut c = p.initial(formula(&rows));
        p.run(
            &mut c,
            RunLimits {
                max_steps: 15_000_000,
                max_stack_bits: 350_000,
            },
        )
        .unwrap();
        assert_eq!(output(&c, 13), formula(&expected(&rows)), "rows={rows:?}");
        for i in 0..16 {
            if i != 13 {
                assert!(c.stacks[i].is_empty(), "work {i}");
            }
        }
    }
}

#[test]
fn normalization_fails_closed_on_partial_budget() {
    let p = native_normalization_full::program().unwrap();
    let mut c = p.initial(formula(&[vec![0, 2, 4], vec![0, 2], vec![1, 3]]));
    let e = p
        .run(
            &mut c,
            RunLimits {
                max_steps: 4,
                max_stack_bits: 20_000,
            },
        )
        .unwrap_err();
    assert!(matches!(e, Error::Capacity(_)));
    assert!(c.pc.is_some());
}
