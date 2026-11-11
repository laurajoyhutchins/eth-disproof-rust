use lean_eth_reference::{
    Cnf, CountState, CountStats, EnumeratingLeaf, Limits, count_cnf, count_step, disjoint_children,
    parse_dimacs, priority_select,
};

fn shared() -> Cnf {
    Cnf::from_signed(3, &[&[1, 2], &[1, 3]]).unwrap()
}

#[test]
fn pinned_lean_encoding_vectors() {
    // Fixtures from nonexp-sudoku/tests/eth/test_lean_source_conformance.py.
    assert_eq!(Cnf::from_signed(0, &[]).unwrap().encode_lean(), "00");
    assert_eq!(Cnf::from_signed(1, &[]).unwrap().encode_lean(), "100");
    assert_eq!(
        Cnf::from_signed(1, &[&[]]).unwrap().encode_lean(),
        "1011000"
    );
    assert_eq!(
        Cnf::from_signed(1, &[&[1]]).unwrap().encode_lean(),
        "1011111111110101000"
    );
    assert_eq!(
        Cnf::from_signed(1, &[&[-1]]).unwrap().encode_lean(),
        "101111110101000"
    );
}

#[test]
fn finite_source_normalization_distinguishes_raw_and_normalized() {
    let source = Cnf::from_signed(3, &[&[1, -1], &[1, 2], &[1], &[1, 2]]).unwrap();
    assert_eq!(source.clauses().len(), 3);
    let normalized = source.normalize();
    assert_eq!(normalized, Cnf::from_signed(3, &[&[1]]).unwrap());
    // The Lean `Encoding.encodeCNF` serializes raw Finset syntax, not normalization.
    assert_ne!(source.encode_lean(), normalized.encode_lean());
}

#[test]
fn lean_priority_and_three_exact_dfs_transitions() {
    let f = shared();
    assert_eq!(
        priority_select(&f, 2, Limits::default()).unwrap(),
        Some((
            2,
            Cnf::from_signed(3, &[&[1]]).unwrap().clauses()[0].clone()
        ))
    );
    let mut s = CountState::initial(f);
    let mut oracle = EnumeratingLeaf { max_variables: 8 };
    let mut stats = CountStats::default();
    assert!(count_step(&mut s, 2, &mut oracle, Limits::default(), &mut stats).unwrap());
    assert_eq!(s.pending.len(), 2);
    assert_eq!(s.total, 0);
    assert!(count_step(&mut s, 2, &mut oracle, Limits::default(), &mut stats).unwrap());
    assert_eq!(s.total, 4);
    assert_eq!(s.pending.len(), 1);
    assert!(count_step(&mut s, 2, &mut oracle, Limits::default(), &mut stats).unwrap());
    assert_eq!(s.total, 5);
    assert!(s.pending.is_empty());
    assert!(!count_step(&mut s, 2, &mut oracle, Limits::default(), &mut stats).unwrap());
    assert_eq!((stats.nodes, stats.leaves, stats.peak_frontier), (3, 2, 2));
}

#[test]
fn shared_core_is_a_disjoint_partition() {
    let f = shared();
    let (_, core) = priority_select(&f, 2, Limits::default()).unwrap().unwrap();
    let (a, b) = disjoint_children(&f, 2, &core);
    for mask in 0..8u128 {
        assert_eq!(f.eval(mask), a.eval(mask) || b.eval(mask));
        assert!(!(a.eval(mask) && b.eval(mask)));
    }
    assert_eq!(a.variables(), 3);
    assert_eq!(b.variables(), 3);
}

#[test]
fn negative_core_and_overlap_are_disjoint() {
    let f = Cnf::from_signed(3, &[&[-1, 2], &[-1, 3], &[2, 3]]).unwrap();
    let core = Cnf::from_signed(3, &[&[-1]]).unwrap().clauses()[0].clone();
    let (a, b) = disjoint_children(&f, 2, &core);
    for mask in 0..8u128 {
        assert_eq!(f.eval(mask), a.eval(mask) || b.eval(mask));
        assert!(!(a.eval(mask) && b.eval(mask)));
    }
}

#[test]
fn declared_unused_variables_are_not_removed() {
    let f = Cnf::from_signed(6, &[&[1, 2], &[1, 3]]).unwrap();
    let (count, stats) = count_cnf(
        f,
        2,
        &mut EnumeratingLeaf { max_variables: 8 },
        Limits::default(),
    )
    .unwrap();
    assert_eq!(count, 5 * 8);
    assert_eq!(stats.nodes, 3);
}

#[test]
fn empty_cnf_and_empty_clause() {
    assert_eq!(
        count_cnf(
            Cnf::from_signed(3, &[]).unwrap(),
            2,
            &mut EnumeratingLeaf { max_variables: 8 },
            Limits::default()
        )
        .unwrap()
        .0,
        8
    );
    assert_eq!(
        count_cnf(
            Cnf::from_signed(3, &[&[]]).unwrap(),
            2,
            &mut EnumeratingLeaf { max_variables: 8 },
            Limits::default()
        )
        .unwrap()
        .0,
        0
    );
}

#[test]
fn property_every_small_formula_matches_independent_cube() {
    // All subsets of a six-clause library, with duplicates and raw tautologies.
    let clauses: &[&[i64]] = &[&[1, 2], &[1, 3], &[-1, 2], &[-2, 3], &[1, -1], &[]];
    for mask in 0..64 {
        let selected: Vec<&[i64]> = clauses
            .iter()
            .enumerate()
            .filter_map(|(i, c)| ((mask >> i) & 1 == 1).then_some(*c))
            .collect();
        let f = Cnf::from_signed(3, &selected).unwrap();
        let expected = (0..8u128).filter(|a| f.eval(*a)).count() as u128;
        let (actual, _) = count_cnf(
            f.normalize(),
            2,
            &mut EnumeratingLeaf { max_variables: 3 },
            Limits::default(),
        )
        .unwrap();
        assert_eq!(actual, expected, "family mask {mask}");
    }
}

#[test]
fn limits_refuse_instead_of_silent_partial_counts() {
    let limits = Limits {
        max_nodes: 1,
        ..Limits::default()
    };
    assert!(
        count_cnf(
            shared(),
            2,
            &mut EnumeratingLeaf { max_variables: 3 },
            limits
        )
        .is_err()
    );
    let f = Cnf::from_signed(21, &[&[1]]).unwrap();
    assert!(
        count_cnf(
            f,
            2,
            &mut EnumeratingLeaf { max_variables: 20 },
            Limits::default()
        )
        .is_err()
    );
}

#[test]
fn dimensional_input_validation() {
    assert!(parse_dimacs("p cnf 3 2\n1 2 0\n1 3 0\n").is_ok());
    for source in [
        "p cnf 3 2\n1 2 0",
        "p cnf 1 1\n2 0",
        "p cnf 1 1\n0 0",
        "p cnf 1 1\n1",
        "p cnf 2 -1\n",
        "p cnf 1 1\n1 0 9",
    ] {
        assert!(parse_dimacs(source).is_err(), "source {source:?}");
    }
}

#[test]
fn lean_bitstream_roundtrip_and_strict_decoder() {
    let source = Cnf::from_signed(4, &[&[-4, 2], &[1, -1], &[1, 2], &[]]).unwrap();
    let wire = source.encode_lean();
    assert_eq!(Cnf::decode_lean(&wire).unwrap(), source);
    // Syntax can preserve tautologies that normalized CNF representations remove.
    assert_ne!(source.encode_lean(), source.normalize().encode_lean());
    for bad in ["", "1", "01", "000", "x00", "10", "1001", "001", "101"] {
        assert!(Cnf::decode_lean(bad).is_err(), "malformed input {bad:?}");
    }
    // A duplicate clause remains invalid even if canonical set creation would deduplicate.
    let single = Cnf::from_signed(1, &[&[1]]).unwrap();
    let word = single.encode_lean();
    assert_eq!(Cnf::decode_lean(&word).unwrap().encode_lean(), word);
}

#[test]
fn big_threshold_comparisons_do_not_overflow() {
    let f = shared();
    let selection = priority_select(&f, usize::MAX, Limits::default()).unwrap();
    assert!(selection.is_none());
}

#[test]
fn literal_evaluation_is_bounded_for_large_declared_universe() {
    let f = Cnf::from_signed(129, &[&[129]]).unwrap();
    // No integer-shift panic or false success when asked to count >128-bit cube.
    assert!(
        count_cnf(
            f,
            2,
            &mut EnumeratingLeaf { max_variables: 129 },
            Limits {
                max_leaf_variables: 129,
                ..Limits::default()
            }
        )
        .is_err()
    );
}

#[test]
fn public_truth_evaluation_refuses_unrepresentable_assignment_masks() {
    let formula = Cnf::from_signed(129, &[&[129]]).unwrap();
    assert!(formula.eval_mask_checked(0).is_err());
    assert!(
        Cnf::from_signed(3, &[])
            .unwrap()
            .eval_mask_checked(8)
            .is_err()
    );
    assert!(
        Cnf::from_signed(3, &[])
            .unwrap()
            .eval_mask_checked(7)
            .unwrap()
    );
}
