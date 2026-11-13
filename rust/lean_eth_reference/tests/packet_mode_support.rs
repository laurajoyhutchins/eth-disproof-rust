use lean_eth_reference::Error;
use lean_eth_reference::packet_mode_support::{PacketSlots, TileMode};
use lean_eth_reference::valuation_modes::count_explicit_weights;
use lean_eth_reference::valuation_witness::source_precision;

#[test]
fn even_a_single_real_source_column_forces_the_coarse_mode_weight() {
    // The tile y0=1 includes column y=9. The paired row is x=9;
    // D=t-y0+x=12 has v2(D)=v2(t)=2, even with no row x=1.
    let packet = PacketSlots {
        a: 4,
        u: 3,
        t: 4,
        labels: (0, 1),
        real_slots: &[9],
    };
    let report = packet.certify_tile(1, 3).unwrap();
    match report {
        TileMode::Contributing {
            source_columns,
            target_rows,
            certificate,
        } => {
            assert_eq!(source_columns, vec![9]);
            assert_eq!(target_rows, vec![9]);
            assert_eq!(certificate.whole_mode_weight, 6);
            assert_eq!(certificate.coarse_weight, 6);
            assert_eq!(certificate.maximum_denominator_v2, 2);
        }
        other => panic!("unexpected tile report {other:?}"),
    }
}

#[test]
fn exhaustive_small_source_packet_occupancies_have_no_geometry_gain() {
    for a in 2..=3u32 {
        let l = 1u64 << a;
        for mask in 0..(1u64 << l) {
            let occupied: Vec<_> = (0..l).filter(|&x| mask & (1 << x) != 0).collect();
            for u in 1..=a {
                for t in -(l as i64)..l as i64 {
                    if t == 0 || t.unsigned_abs().trailing_zeros() >= u {
                        continue;
                    }
                    let i = t.unsigned_abs().trailing_zeros();
                    let packet = PacketSlots {
                        a,
                        u,
                        t,
                        labels: (4, 9),
                        real_slots: &occupied,
                    };
                    for y0 in 0..(1u64 << (i + 1)) {
                        let report = packet.certify_tile(y0, 2).unwrap();
                        if let TileMode::Contributing {
                            source_columns,
                            target_rows,
                            certificate,
                        } = report
                        {
                            assert_eq!(certificate.whole_mode_weight, certificate.coarse_weight);
                            assert!(!source_columns.is_empty());
                            assert!(source_columns.iter().all(|x| target_rows.contains(x)));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn sparse_dense_and_negative_point_packets_all_obey_paired_slot_theorem() {
    for a in 4..=5u32 {
        let l = 1u64 << a;
        let cases = [
            (0..l).collect::<Vec<_>>(),
            (0..l).step_by(2).collect(),
            (0..l).step_by(3).collect(),
            vec![0, 3, l / 2, l - 1],
        ];
        for occupied in cases {
            for u in 1..=a {
                for t in -(l as i64)..l as i64 {
                    if t == 0 || t.unsigned_abs().trailing_zeros() >= u {
                        continue;
                    }
                    let i = t.unsigned_abs().trailing_zeros();
                    let packet = PacketSlots {
                        a,
                        u,
                        t,
                        labels: (0, 63),
                        real_slots: &occupied,
                    };
                    for y0 in 0..(1u64 << (i + 1)) {
                        let report = packet.certify_tile(y0, 0).unwrap();
                        if let TileMode::Contributing { certificate, .. } = report {
                            assert_eq!(certificate.whole_mode_weight, certificate.coarse_weight);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn no_source_tile_or_equal_labels_produce_no_mode() {
    let packet = PacketSlots {
        a: 4,
        u: 3,
        t: 4,
        labels: (0, 1),
        real_slots: &[0, 2, 8],
    };
    assert_eq!(
        packet.certify_tile(1, 3).unwrap(),
        TileMode::EmptySourceTile
    );
    let local = PacketSlots {
        labels: (5, 5),
        ..packet
    };
    assert_eq!(local.certify_tile(0, 3).unwrap(), TileMode::LocalOnly);
}

#[test]
fn unverified_packet_shapes_refuse() {
    let good = PacketSlots {
        a: 4,
        u: 3,
        t: 4,
        labels: (0, 1),
        real_slots: &[1],
    };
    for bad in [
        PacketSlots {
            real_slots: &[1, 1],
            ..good
        },
        PacketSlots {
            real_slots: &[16],
            ..good
        },
        PacketSlots { t: 0, ..good },
        PacketSlots { t: 8, u: 3, ..good },
        PacketSlots {
            labels: (0, 64),
            ..good
        },
        PacketSlots { a: 61, ..good },
    ] {
        assert!(matches!(bad.certify_tile(1, 3), Err(Error::Invalid(_))));
    }
    assert!(matches!(good.certify_tile(8, 3), Err(Error::Capacity(_))));
}

#[test]
fn empty_source_tiles_can_be_deleted_from_mode_enumeration_exactly() {
    let packet = PacketSlots {
        a: 4,
        u: 3,
        t: 4,
        labels: (0, 1),
        real_slots: &[9],
    };
    let mut weights_original = Vec::new();
    let mut weights_live = Vec::new();
    let mut active_tiles = Vec::new();
    for y0 in 0..8 {
        weights_original.push(1usize); // source b=0 has weight b+1=1
        match packet.certify_tile(y0, 0).unwrap() {
            TileMode::Contributing { certificate, .. } => {
                active_tiles.push(y0);
                weights_live.push(certificate.source_weight as usize);
            }
            TileMode::EmptySourceTile => {}
            TileMode::LocalOnly => panic!("unequal packet must not be local"),
        }
    }
    assert_eq!(active_tiles, vec![1]);
    let precision = source_precision(4, 3, 2, 16, 32).unwrap() as usize;
    assert_eq!(precision, 1184);
    assert_eq!(
        count_explicit_weights(&weights_original, precision).unwrap(),
        98_071_305_243_152_509_620
    );
    assert_eq!(
        count_explicit_weights(&weights_live, precision).unwrap(),
        1184
    );

    // Direct small-precision algebraic check: the source mode form L_Z is
    // identically zero for every empty tile. A monomial with positive
    // exponent at such a tile vanishes; 0^0 is interpreted as 1.
    for p in 1..=8 {
        let mut source_sum = 0u64;
        let mut visited = 0u64;
        fn enumerate(
            j: usize,
            remaining: usize,
            seen_empty_positive: bool,
            p: u64,
            source_sum: &mut u64,
            visited: &mut u64,
        ) {
            if j == 8 {
                *visited += 1;
                if !seen_empty_positive {
                    *source_sum = (*source_sum + 1) % (1u64 << p);
                }
                return;
            }
            for exponent in 0..=remaining {
                enumerate(
                    j + 1,
                    remaining - exponent,
                    seen_empty_positive || (j != 1 && exponent != 0),
                    p,
                    source_sum,
                    visited,
                );
            }
        }
        enumerate(0, p - 1, false, p as u64, &mut source_sum, &mut visited);
        assert_eq!(visited as u128, count_explicit_weights(&[1; 8], p).unwrap());
        let pruned_sum = p as u64 % (1u64 << p);
        assert_eq!(source_sum, pruned_sum);
    }
}
