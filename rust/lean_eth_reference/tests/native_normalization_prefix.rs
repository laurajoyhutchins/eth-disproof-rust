//! Independent semantic checks confined to tests; execution uses source machine.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_normalization_prefix;
fn unary(n: usize) -> Vec<bool> {
    let mut a = vec![true; n];
    a.push(false);
    a
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.extend([true, *x])
    }
    out.push(false);
    out
}
fn encoded<T>(xs: &[T], f: impl Fn(&T) -> Vec<bool>) -> Vec<bool> {
    let mut out = Vec::new();
    for x in xs {
        out.push(true);
        out.extend(frame(&f(x)))
    }
    out.push(false);
    out
}
fn formula(rows: &[Vec<usize>]) -> Vec<bool> {
    encoded(rows, |r| encoded(r, |c| unary(*c)))
}
fn clean(rows: &[Vec<usize>]) -> Vec<Vec<usize>> {
    rows.iter()
        .map(|r| {
            r.iter()
                .enumerate()
                .filter(|(i, c)| !r[i + 1..].contains(c))
                .map(|(_, c)| *c)
                .collect::<Vec<_>>()
        })
        .filter(|r| !r.iter().any(|c| r.contains(&(c ^ 1))))
        .collect()
}
#[test]
fn prefix_matches_source_semantics_for_empty_and_duplicate_clauses() {
    let p = native_normalization_prefix::program().unwrap();
    for rows in [
        vec![],
        vec![vec![]],
        vec![vec![0, 0]],
        vec![vec![0, 1]],
        vec![vec![0, 0, 1, 2]],
        vec![vec![0], vec![0]],
        vec![vec![0, 0, 2, 2], vec![1, 1], vec![2, 3], vec![]],
        vec![vec![0, 2, 0], vec![4, 5, 4], vec![1, 1, 3, 3], vec![2, 2]],
    ] {
        let mut d = p.initial(formula(&rows));
        p.run(
            &mut d,
            RunLimits {
                max_steps: 2_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
        assert_eq!(
            d.stacks[0].iter().copied().collect::<Vec<_>>(),
            formula(&clean(&rows)),
            "rows={rows:?}"
        );
        for i in 1..11 {
            assert!(d.stacks[i].is_empty(), "dirty stack {i}")
        }
    }
}
#[test]
fn randomized_prefix_composes_literal_cleanup_and_tautology_removal() {
    let p = native_normalization_prefix::program().unwrap();
    let mut seed: u64 = 0x13123f78af1097c3;
    let mut rand = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        seed
    };
    for _ in 0..100 {
        let n = (rand() % 8) as usize;
        let rows = (0..n)
            .map(|_| {
                let k = (rand() % 7) as usize;
                (0..k).map(|_| (rand() % 12) as usize).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut d = p.initial(formula(&rows));
        p.run(
            &mut d,
            RunLimits {
                max_steps: 2_000_000,
                max_stack_bits: 100_000,
            },
        )
        .unwrap();
        assert_eq!(
            d.stacks[0].iter().copied().collect::<Vec<_>>(),
            formula(&clean(&rows)),
            "rows={rows:?}"
        );
        for i in 1..11 {
            assert!(d.stacks[i].is_empty());
        }
    }
}
