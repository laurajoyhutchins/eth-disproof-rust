use lean_eth_reference::Error;
use lean_eth_reference::valuation_witness::{CrossingWitness, source_precision};

#[test]
fn concrete_denominator_proves_more_than_the_paper_coarse_weight() {
    // t=4 has i=2; t-y0+x=3 has d=0, so each b factor gains
    // i+1-d=3 powers of two rather than only one.
    let w = CrossingWitness {
        a: 4,
        u: 3,
        t: 4,
        x: 0,
        y0: 1,
        b: 3,
    };
    let c = w.certify().unwrap();
    assert_eq!((c.i, c.denominator_v2), (2, 0));
    assert_eq!((c.original, c.paper_coarse, c.geometry_refined), (4, 6, 12));
    assert_eq!(
        w.source_coarse_mode().unwrap().stronger_weight().unwrap(),
        6
    );
}

#[test]
fn exhaustive_small_crossings_respect_both_monotone_bounds() {
    let mut strict = 0usize;
    for a in 2..=5u32 {
        let l = 1i64 << a;
        for u in 1..=a {
            for t in -l..l {
                if t == 0 {
                    continue;
                }
                let i = t.unsigned_abs().trailing_zeros();
                if i >= u {
                    continue;
                }
                for x in 0..l as u64 {
                    for y0 in 0..(1u64 << (i + 1)) {
                        let d = i128::from(t) - i128::from(y0) + i128::from(x);
                        if d == 0 || d.unsigned_abs().trailing_zeros() > i {
                            continue;
                        }
                        for b in 0..=3 {
                            let w = CrossingWitness { a, u, t, x, y0, b };
                            let c = w.certify().unwrap();
                            assert!(c.original <= c.paper_coarse);
                            assert!(c.paper_coarse <= c.geometry_refined);
                            assert_eq!(
                                c.geometry_refined - c.paper_coarse,
                                u64::from(b) * u64::from(i - c.denominator_v2)
                            );
                            strict += usize::from(c.paper_coarse < c.geometry_refined);
                        }
                    }
                }
            }
        }
    }
    assert!(strict > 0);
}

#[test]
fn source_precision_is_not_the_tiny_illustration_precision() {
    // Toy values of M,a,u: this is NOT asserted to satisfy active-call
    // packet-packing constraints from the asymptotic source proof.
    assert_eq!(source_precision(4, 3, 2, 16, 32).unwrap(), 1184);
    let c = CrossingWitness {
        a: 4,
        u: 3,
        t: 4,
        x: 0,
        y0: 1,
        b: 3,
    }
    .certify()
    .unwrap();
    assert!(u128::from(c.geometry_refined) < source_precision(4, 3, 2, 16, 32).unwrap());
}

#[test]
fn invalid_source_geometry_refuses_before_building_a_mode() {
    let valid = CrossingWitness {
        a: 4,
        u: 3,
        t: 4,
        x: 0,
        y0: 1,
        b: 2,
    };
    for invalid in [
        CrossingWitness { t: 0, ..valid },
        CrossingWitness { t: 16, ..valid },
        CrossingWitness { t: 8, ..valid },
        CrossingWitness { x: 16, ..valid },
        CrossingWitness { y0: 8, ..valid },
        CrossingWitness {
            x: 4,
            y0: 0,
            ..valid
        },
        CrossingWitness { u: 2, ..valid },
        CrossingWitness { a: 61, ..valid },
    ] {
        assert!(
            matches!(invalid.certify(), Err(Error::Invalid(_))),
            "{invalid:?}"
        );
    }
    assert!(matches!(
        source_precision(4, 0, 0, 16, 32),
        Err(Error::Invalid(_))
    ));
    assert_eq!(
        source_precision(60, 1, 0, u64::MAX, 0),
        Err(Error::Overflow)
    );
}
