//! Host last-occurrence oracle appears only in tests; real source machine runs.
use lean_eth_reference::Error;
use lean_eth_reference::bit_program::RunLimits;
use lean_eth_reference::native_literal_dedup::dedup_program;

fn frame(w: &[bool]) -> Vec<bool> {
    let mut a = vec![];
    for b in w { a.extend([true, *b]); }
    a.push(false);
    a
}
fn encoded(rows: &[Vec<bool>]) -> Vec<bool> {
    let mut a = vec![];
    for r in rows { a.push(true); a.extend(frame(r)); }
    a.push(false);
    a
}
fn last(rows: &[Vec<bool>]) -> Vec<Vec<bool>> {
    rows.iter().enumerate().filter(|(i,r)| !rows[i+1..].contains(r)).map(|(_,r)| r.clone()).collect()
}

#[test]
fn literal_dedup_physically_keeps_last_record_in_original_order() {
    let p = dedup_program().unwrap();
    let cases = vec![
        vec![],
        vec![vec![]],
        vec![vec![true]],
        vec![vec![true], vec![true]],
        vec![vec![true], vec![false], vec![true]],
        vec![vec![true], vec![false], vec![true], vec![false]],
        vec![vec![true, false], vec![], vec![false, true], vec![], vec![true, false]],
        vec![vec![false; 21], vec![true; 13], vec![false; 21]],
    ];
    for rows in cases {
        let mut d = p.initial(encoded(&rows));
        let steps = p.run(&mut d, RunLimits::default()).unwrap();
        assert_eq!(d.stacks[0].iter().copied().collect::<Vec<_>>(), encoded(&last(&rows)), "rows={rows:?}");
        for s in 1..8 { assert!(d.stacks[s].is_empty(), "dirty stack {s}"); }
        assert!(steps.instructions > 0);
        assert_eq!(d.pc, None);
    }
}

#[test]
fn randomized_literal_dedup_matches_independent_test_oracle() {
    let p = dedup_program().unwrap();
    let mut seed: u64 = 0xe253a9a37d5a7493;
    let mut rand = || { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1); seed };
    for _ in 0..90 {
        let size = (rand()%11) as usize;
        let rows = (0..size).map(|_| {
            let len = (rand()%5) as usize;
            (0..len).map(|_| (rand()>>31)&1 != 0).collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        let mut d = p.initial(encoded(&rows));
        let n = encoded(&rows).len();
        let steps = p.run(&mut d, RunLimits { max_steps: 500_000, max_stack_bits: 10_000 }).unwrap();
        assert_eq!(d.stacks[0].iter().copied().collect::<Vec<_>>(), encoded(&last(&rows)));
        for s in 1..8 { assert!(d.stacks[s].is_empty()); }
        assert!(steps.instructions <= (100 * n.pow(2) + 10*n + 8) as u64);
    }
}

#[test]
fn budget_exhaustion_is_not_a_successful_dedup() {
    let p = dedup_program().unwrap();
    let mut d = p.initial(encoded(&[vec![true; 24], vec![true; 24]]));
    let e = p.run(&mut d, RunLimits { max_steps: 30, max_stack_bits: 10_000 }).unwrap_err();
    assert!(matches!(e, Error::Capacity(_)));
    assert!(d.pc.is_some());
}
