//! Independent test-only oracle for physical 13x11 clause-wise cleanup.
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_literal_cleanup::clean_program;

fn unary(n: usize) -> Vec<bool> {
    let mut a = vec![true; n];
    a.push(false);
    a
}
fn frame(xs: &[bool]) -> Vec<bool> {
    let mut a = vec![];
    for b in xs {
        a.extend([true, *b]);
    }
    a.push(false);
    a
}
fn encoded<T>(xs: &[T], f: impl Fn(&T) -> Vec<bool>) -> Vec<bool> {
    let mut a = vec![];
    for x in xs {
        a.push(true);
        a.extend(frame(&f(x)));
    }
    a.push(false);
    a
}
fn formula(rows: &[Vec<usize>]) -> Vec<bool> {
    encoded(rows, |r| encoded(r, |n| unary(*n)))
}
fn keep_last(rs: &[usize]) -> Vec<usize> {
    rs.iter()
        .enumerate()
        .filter(|(i, v)| !rs[i + 1..].contains(v))
        .map(|(_, v)| *v)
        .collect()
}

#[test]
fn actual_nested_cleaner_preserves_clause_order_and_removes_literal_duplicates() {
    let p = clean_program().unwrap();
    for rows in [
        vec![],
        vec![vec![]],
        vec![vec![0]],
        vec![vec![1, 1]],
        vec![vec![0, 1, 0]],
        vec![vec![], vec![1, 2, 1], vec![]],
        vec![vec![0, 1, 0, 2, 1], vec![4, 4], vec![3, 3, 0]],
        vec![vec![0, 1], vec![0, 1], vec![1, 0]],
    ] {
        let mut d = p.initial(formula(&rows));
        let steps = p
            .run(
                &mut d,
                RunLimits {
                    max_steps: 1_000_000,
                    max_stack_bits: 50_000,
                },
            )
            .unwrap();
        let cleaned = rows.iter().map(|r| keep_last(r)).collect::<Vec<_>>();
        assert_eq!(
            d.stacks[0].iter().copied().collect::<Vec<_>>(),
            formula(&cleaned),
            "formula={rows:?}"
        );
        for s in 1..11 {
            assert!(d.stacks[s].is_empty(), "dirty stack {s}");
        }
        assert!(steps.instructions > 0);
        assert_eq!(d.pc, None);
    }
}

#[test]
fn randomized_nested_cnfs_match_independent_literal_cleanup_oracle() {
    let p = clean_program().unwrap();
    let mut seed: u64 = 0x7add4317c90233e1;
    let mut rand = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed
    };
    for _ in 0..65 {
        let count = (rand() % 7) as usize;
        let rows = (0..count)
            .map(|_| {
                let len = (rand() % 7) as usize;
                (0..len).map(|_| (rand() % 9) as usize).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut d = p.initial(formula(&rows));
        let steps = p
            .run(
                &mut d,
                RunLimits {
                    max_steps: 1_000_000,
                    max_stack_bits: 50_000,
                },
            )
            .unwrap();
        let expected = rows.iter().map(|r| keep_last(r)).collect::<Vec<_>>();
        assert_eq!(
            d.stacks[0].iter().copied().collect::<Vec<_>>(),
            formula(&expected)
        );
        for s in 1..11 {
            assert!(d.stacks[s].is_empty());
        }
        assert!(steps.instructions > 0);
    }
}
