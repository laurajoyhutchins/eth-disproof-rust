//! Source-subprogram exercise with independent host oracles confined to tests.
use lean_eth_reference::bit_program::{Config, RunLimits};
use lean_eth_reference::{
    Error, native_negated_query, native_tautology_core, native_tautology_filter,
};
fn get<const R: usize, const S: usize>(c: &Config<R, S>, p: usize) -> Vec<bool> {
    c.stacks[p].iter().copied().collect()
}
fn unary(n: usize) -> Vec<bool> {
    let mut v = vec![true; n];
    v.push(false);
    v
}
fn frame(w: &[bool]) -> Vec<bool> {
    let mut r = Vec::new();
    for b in w {
        r.extend([true, *b])
    }
    r.push(false);
    r
}
fn list<T>(xs: &[T], to_bits: impl Fn(&T) -> Vec<bool>) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.push(true);
        out.extend(frame(&to_bits(x)))
    }
    out.push(false);
    out
}
fn clause(xs: &[usize]) -> Vec<bool> {
    list(xs, |n| unary(*n))
}
fn formula(xs: &[Vec<usize>]) -> Vec<bool> {
    list(xs, |row| clause(row))
}
fn is_tautology(c: &[usize]) -> bool {
    c.iter().any(|x| c.contains(&(x ^ 1)))
}
#[test]
fn unary_negated_query_preserves_source_and_scratch() {
    let p = native_negated_query::program().unwrap();
    for c in 0..=128 {
        let input = unary(c).into_iter().rev().collect::<Vec<_>>();
        let mut cfg = p.initial(input.clone());
        let stats = p.run(&mut cfg, RunLimits::default()).unwrap();
        assert_eq!(get(&cfg, 0), input, "c={c}");
        assert_eq!(
            get(&cfg, 1),
            unary(c ^ 1).into_iter().rev().collect::<Vec<_>>(),
            "c={c}"
        );
        assert!(cfg.stacks[2].is_empty() && cfg.stacks[3].is_empty());
        assert_eq!(cfg.regs, [false, false]);
        let expected = 16 * (c + 1) + 9 * ((c ^ 1) + 1) + (8 * (c / 2) + 10 + c % 2) + 20;
        assert_eq!(stats.instructions, expected as u64, "c={c}");
    }
}
#[test]
fn tautology_core_identifies_opposites_but_keeps_clause() {
    let p = native_tautology_core::program().unwrap();
    for rows in [
        vec![],
        vec![0],
        vec![0, 1],
        vec![1, 0],
        vec![0, 2],
        vec![2, 2],
        vec![2, 3],
        vec![0, 0, 0, 1],
        vec![4, 7, 2, 3],
        vec![10, 11, 10],
        vec![1, 3, 5],
        vec![2, 4, 6],
    ] {
        let source = clause(&rows);
        let mut cfg = p.initial(source.clone());
        let stats = p
            .run(
                &mut cfg,
                RunLimits {
                    max_steps: 500_000,
                    max_stack_bits: 15_000,
                },
            )
            .unwrap();
        assert_eq!(get(&cfg, 1), vec![is_tautology(&rows)], "{rows:?}");
        assert_eq!(get(&cfg, 2), source, "{rows:?}");
        assert!(cfg.stacks[0].is_empty());
        for i in 3..8 {
            assert!(cfg.stacks[i].is_empty(), "row={rows:?} scratch {i}")
        }
        assert!(stats.instructions > 0);
    }
}
#[test]
fn tautology_filter_retains_nontautologies_in_source_order() {
    let p = native_tautology_filter::program().unwrap();
    for rows in [
        vec![],
        vec![vec![]],
        vec![vec![0]],
        vec![vec![0, 1]],
        vec![vec![0, 1], vec![2]],
        vec![vec![1], vec![3, 2], vec![4, 5], vec![6]],
        vec![vec![0], vec![0], vec![2, 3], vec![0, 1, 2]],
    ] {
        let expected = rows
            .iter()
            .filter(|row| !is_tautology(row))
            .cloned()
            .collect::<Vec<_>>();
        let mut cfg = p.initial(formula(&rows));
        let stats = p
            .run(
                &mut cfg,
                RunLimits {
                    max_steps: 1_000_000,
                    max_stack_bits: 50_000,
                },
            )
            .unwrap();
        assert_eq!(get(&cfg, 0), formula(&expected), "rows={rows:?}");
        for i in 1..11 {
            assert!(cfg.stacks[i].is_empty(), "rows={rows:?} scratch {i}")
        }
        assert!(stats.instructions > 0);
    }
}
#[test]
fn tautology_filter_randomized_oracle_agrees() {
    let p = native_tautology_filter::program().unwrap();
    let mut seed: u64 = 0xa4527b1e39c0b411;
    for _ in 0..100 {
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed
        };
        let n = (next() % 7) as usize;
        let rows = (0..n)
            .map(|_| {
                let k = (next() % 6) as usize;
                (0..k).map(|_| (next() % 10) as usize).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let expected = rows
            .iter()
            .filter(|row| !is_tautology(row))
            .cloned()
            .collect::<Vec<_>>();
        let mut cfg = p.initial(formula(&rows));
        p.run(
            &mut cfg,
            RunLimits {
                max_steps: 1_000_000,
                max_stack_bits: 80_000,
            },
        )
        .unwrap();
        assert_eq!(get(&cfg, 0), formula(&expected), "rows={rows:?}");
        for i in 1..11 {
            assert!(cfg.stacks[i].is_empty(), "scratch {i}")
        }
    }
}
#[test]
fn tautology_capacity_refusal_is_not_classification() {
    let p = native_tautology_filter::program().unwrap();
    let mut cfg = p.initial(formula(&[vec![0, 1], vec![2]]));
    let err = p
        .run(
            &mut cfg,
            RunLimits {
                max_steps: 5,
                max_stack_bits: 2000,
            },
        )
        .unwrap_err();
    assert!(matches!(err, Error::Capacity(_)));
    assert!(cfg.pc.is_some());
}
