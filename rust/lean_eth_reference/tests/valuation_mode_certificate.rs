use lean_eth_reference::Error;
use lean_eth_reference::valuation_mode_certificate::ModeRows;
use lean_eth_reference::valuation_modes::count_explicit_weights;
use lean_eth_reference::valuation_witness::{CrossingWitness, source_precision};

fn v2(n: i128) -> u32 {
    n.unsigned_abs().trailing_zeros()
}

#[test]
fn one_row_is_not_a_global_mode_certificate() {
    let single = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 3,
        target_rows: &[0],
    }
    .certify_assuming_complete_rows()
    .unwrap();
    let both = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 3,
        target_rows: &[0, 1],
    }
    .certify_assuming_complete_rows()
    .unwrap();
    assert_eq!(
        (
            single.source_weight,
            single.coarse_weight,
            single.prior_geometry_weight,
            single.whole_mode_weight
        ),
        (4, 6, 12, 14)
    );
    assert_eq!(
        (
            both.source_weight,
            both.coarse_weight,
            both.prior_geometry_weight,
            both.whole_mode_weight
        ),
        (4, 6, 6, 6)
    );
    assert_eq!(both.least_divisible_row, 1);
    assert_eq!(both.maximum_denominator_v2, 2);
    // Treating the high-valuation row as the whole mode would omit a
    // coefficient that is nonzero modulo 2^p for any p>6.
    assert!(single.whole_mode_weight > both.whole_mode_weight);
}

#[test]
fn source_derivative_grid_confirms_exact_linear_coefficient_valuation() {
    // Independent integer calculation: the rational coefficient of z in
    // C(t+alpha*z)/(C'(0)*(t+alpha*z-q)) * (2^(i+1)/(t+alpha*z-q))^b
    // equals alpha*C'(t)*2^((i+1)*b)/(C'(0)*(t-q)^(b+1)).
    // For small a, numerator and denominator fit in i128 exactly.
    for a in 2..=3u32 {
        let l = 1i128 << a;
        let alpha = 1i128 << (a + 1);
        let derivative = |t: i128| -> i128 { (-l..l).filter(|&q| q != t).map(|q| t - q).product() };
        let derivative0 = derivative(0);
        for t in -l..l {
            if t == 0 {
                continue;
            }
            let i = v2(t);
            if i >= a {
                continue;
            }
            assert_eq!(v2(derivative(t)), v2(derivative0));
            for x in 0..l {
                for y0 in 0..(1i128 << (i + 1)) {
                    let d = t - y0 + x;
                    if d == 0 || v2(d) > i {
                        continue;
                    }
                    if (x & (1 << i)) != (y0 & (1 << i)) {
                        continue;
                    }
                    for b in 0..=2u32 {
                        let cert = ModeRows {
                            a,
                            u: a,
                            t: t as i64,
                            y0: y0 as u64,
                            b,
                            target_rows: &[x as u64],
                        }
                        .certify_assuming_complete_rows()
                        .unwrap();
                        let numerator = alpha * derivative(t) * (1i128 << ((i + 1) * b));
                        let denominator = derivative0 * d.pow(b + 1);
                        assert_eq!(
                            v2(numerator) - v2(denominator),
                            cert.whole_mode_weight as u32,
                            "a={a},t={t},x={x},y0={y0},b={b}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn any_added_crossing_row_can_only_weaken_mode_pruning() {
    for a in 2..=4u32 {
        let l = 1u64 << a;
        for u in 1..=a {
            for t in -(l as i64)..l as i64 {
                if t == 0 || t.unsigned_abs().trailing_zeros() >= u {
                    continue;
                }
                let i = t.unsigned_abs().trailing_zeros();
                for y0 in 0..(1u64 << (i + 1)) {
                    let rows: Vec<u64> = (0..l)
                        .filter(|&x| {
                            if (x & (1 << i)) != (y0 & (1 << i)) {
                                return false;
                            }
                            CrossingWitness {
                                a,
                                u,
                                t,
                                x,
                                y0,
                                b: 2,
                            }
                            .certify()
                            .is_ok()
                        })
                        .collect();
                    if rows.len() < 2 {
                        continue;
                    }
                    let mut previous = u64::MAX;
                    for n in 1..=rows.len() {
                        let cert = ModeRows {
                            a,
                            u,
                            t,
                            y0,
                            b: 2,
                            target_rows: &rows[..n],
                        }
                        .certify_assuming_complete_rows()
                        .unwrap();
                        assert!(cert.whole_mode_weight <= previous);
                        assert!(cert.whole_mode_weight >= cert.prior_geometry_weight);
                        assert!(cert.prior_geometry_weight >= cert.coarse_weight);
                        previous = cert.whole_mode_weight;
                    }
                }
            }
        }
    }
}

#[test]
fn dense_packet_row_at_tile_residue_collapses_geometry_gain() {
    for a in 2..=6u32 {
        for u in 1..=a {
            let l = 1i64 << a;
            for t in -l..l {
                if t == 0 || t.unsigned_abs().trailing_zeros() >= u {
                    continue;
                }
                let i = t.unsigned_abs().trailing_zeros();
                for y0 in 0..(1u64 << (i + 1)) {
                    // In a dense packet the row slot x=y0 is present. Its
                    // denominator equals t, so v2(D)=i exactly.
                    let cert = ModeRows {
                        a,
                        u,
                        t,
                        y0,
                        b: 3,
                        target_rows: &[y0],
                    }
                    .certify_assuming_complete_rows()
                    .unwrap();
                    assert_eq!(cert.whole_mode_weight, cert.coarse_weight);
                    assert_eq!(cert.maximum_denominator_v2, i);
                }
            }
        }
    }
}

#[test]
fn source_precision_mode_budget_counts_are_checked_not_extrapolated() {
    let p = source_precision(4, 3, 2, 16, 32).unwrap() as usize;
    assert_eq!(p, 1184);
    let rows = [0, 1];
    let zero = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 0,
        target_rows: &rows,
    }
    .certify_assuming_complete_rows()
    .unwrap();
    let three = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 3,
        target_rows: &rows,
    }
    .certify_assuming_complete_rows()
    .unwrap();
    let original = count_explicit_weights(
        &[zero.source_weight as usize, three.source_weight as usize],
        p,
    )
    .unwrap();
    let coarse = count_explicit_weights(
        &[zero.coarse_weight as usize, three.coarse_weight as usize],
        p,
    )
    .unwrap();
    let sharp = count_explicit_weights(
        &[
            zero.whole_mode_weight as usize,
            three.whole_mode_weight as usize,
        ],
        p,
    )
    .unwrap();
    assert!(sharp <= coarse && coarse <= original);
    let naive_single = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 3,
        target_rows: &rows[..1],
    }
    .certify_assuming_complete_rows()
    .unwrap();
    assert!(naive_single.whole_mode_weight > three.whole_mode_weight);
    // Independent double loop, no generating-function recurrence involved.
    let count = |w0: usize, w1: usize| -> u128 {
        let mut n = 0;
        for x in 0..p / w0 + 1 {
            for y in 0..p / w1 + 1 {
                if x * w0 + y * w1 < p {
                    n += 1;
                }
            }
        }
        n
    };
    assert_eq!(original, count(1, 4));
    assert_eq!(
        sharp,
        count(
            zero.whole_mode_weight as usize,
            three.whole_mode_weight as usize
        )
    );
}

#[test]
fn incomplete_or_invalid_mode_evidence_refuses() {
    let empty = ModeRows {
        a: 4,
        u: 3,
        t: 4,
        y0: 1,
        b: 2,
        target_rows: &[],
    };
    assert!(matches!(
        empty.certify_assuming_complete_rows(),
        Err(Error::Invalid(_))
    ));
    let noncrossing = ModeRows {
        target_rows: &[4],
        ..empty
    };
    assert!(matches!(
        noncrossing.certify_assuming_complete_rows(),
        Err(Error::Invalid(_))
    ));
    assert!(matches!(
        count_explicit_weights(&[0], 10),
        Err(Error::Invalid(_))
    ));
    assert_eq!(count_explicit_weights(&[1, 4], 0).unwrap(), 0);
    assert!(matches!(
        count_explicit_weights(&[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 9999),
        Err(Error::Overflow)
    ));
}
