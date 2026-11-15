//! Exact independent finite checks for the two-bit SWAP expansion.
//!
//! Anthropic's ETH exposition describes SWAP = I - 2*singlet.
//! In the (00,01,10,11) basis, the integer singlet numerator is
//! v=(0,1,-1,0) and 2*singlet = vv^T.
//!
//! This is a local tensor identity, **not** a check of the original OpenAI
//! packet routing, the full Anthropic counting machine, or complexity.

fn singlet_numerator(index: usize) -> i128 {
    match index {
        0 | 3 => 0,
        1 => 1,
        2 => -1,
        _ => panic!("two-bit basis index outside 0..4"),
    }
}

fn swap_index(index: usize) -> usize {
    match index {
        1 => 2,
        2 => 1,
        0 | 3 => index,
        _ => panic!("two-bit basis index outside 0..4"),
    }
}

fn delta(i: usize, j: usize) -> i128 {
    i128::from(i == j)
}

fn direct_swap_entry(i: usize, j: usize) -> i128 {
    delta(swap_index(i), j)
}

fn swap_decomposition_entry(i: usize, j: usize) -> i128 {
    delta(i, j) - singlet_numerator(i) * singlet_numerator(j)
}

/// For λ independent crossings, one mode subset chooses the negative singlet
/// numerator in precisely those coordinates. Both arms use exact integers.
fn mode_entry(lambda: usize, row: usize, col: usize, selected: usize) -> i128 {
    (0..lambda)
        .map(|k| {
            let i = (row >> (2 * k)) & 3;
            let j = (col >> (2 * k)) & 3;
            if (selected >> k) & 1 == 1 {
                -singlet_numerator(i) * singlet_numerator(j)
            } else {
                delta(i, j)
            }
        })
        .product()
}

fn direct_tensor_entry(lambda: usize, row: usize, col: usize) -> i128 {
    (0..lambda)
        .map(|k| direct_swap_entry((row >> (2 * k)) & 3, (col >> (2 * k)) & 3))
        .product()
}

fn grouped_entry(lambda: usize, row: usize, col: usize, weight: usize) -> i128 {
    (0..(1 << lambda))
        .filter(|selected: &usize| selected.count_ones() as usize == weight)
        .map(|selected| mode_entry(lambda, row, col, selected))
        .sum()
}

#[test]
fn swap_equals_identity_minus_rank_one_singlet_numerator() {
    for i in 0..4 {
        for j in 0..4 {
            assert_eq!(
                direct_swap_entry(i, j),
                swap_decomposition_entry(i, j),
                "matrix entry ({i}, {j})"
            );
        }
    }
    // vv^T has one nonzero eigenvalue 2; its square is 2vv^T.
    for i in 0..4 {
        for j in 0..4 {
            let square: i128 = (0..4)
                .map(|k| {
                    singlet_numerator(i)
                        * singlet_numerator(k)
                        * singlet_numerator(k)
                        * singlet_numerator(j)
                })
                .sum();
            assert_eq!(square, 2 * singlet_numerator(i) * singlet_numerator(j));
        }
    }
}

#[test]
fn modes_grouped_by_weight_reconstruct_exact_crossing_tensors() {
    for lambda in 1..=3 {
        let dimension = 1 << (2 * lambda);
        for row in 0..dimension {
            for col in 0..dimension {
                let expected = direct_tensor_entry(lambda, row, col);
                let reconstructed: i128 = (0..=lambda)
                    .map(|weight| grouped_entry(lambda, row, col, weight))
                    .sum();
                assert_eq!(
                    reconstructed, expected,
                    "lambda={lambda}, row={row}, col={col}"
                );
            }
        }
    }
}

#[test]
fn finite_integer_contractions_agree_after_weight_grouping() {
    for lambda in 1..=3 {
        let dimension = 1 << (2 * lambda);
        let left = |i: usize| (i * 3 % 11) as i128 - 5;
        let right = |i: usize| (i * 7 % 13) as i128 - 6;
        let mut direct = 0_i128;
        let mut decomposed = 0_i128;
        for row in 0..dimension {
            for col in 0..dimension {
                direct += left(row) * direct_tensor_entry(lambda, row, col) * right(col);
                for weight in 0..=lambda {
                    decomposed += left(row) * grouped_entry(lambda, row, col, weight) * right(col);
                }
            }
        }
        assert_eq!(direct, decomposed, "lambda={lambda}");
    }
}

#[test]
fn signed_grouped_contraction_handles_shared_wires_and_zero_crossings() {
    // A single joint assignment chooses four bits a,b,c,d. Each swap crossing
    // reads overlapping adjacent bit pairs, so the crossings are NOT
    // independently summed. The external tensor weight can be negative.
    //
    // This is a finite regression for the universal Lean theorem, not a
    // substitute for its proof or a complexity bound.
    assert_eq!(-singlet_numerator(1) * singlet_numerator(1), -1);
    for crossing_count in 0..=4 {
        let mut direct = 0_i128;
        let mut grouped = 0_i128;
        for state in 0..16_usize {
            let wires = std::array::from_fn::<_, 4, _>(|k| (state >> k) & 1);
            let endpoints = std::array::from_fn::<_, 4, _>(|e| {
                let next = (e + 1) % 4;
                let after_next = (e + 2) % 4;
                (
                    (wires[e] << 1) | wires[next],
                    (wires[next] << 1) | wires[after_next],
                )
            });
            let external_weight = state as i128 % 7 - 3;
            let direct_entry: i128 = (0..crossing_count)
                .map(|e| direct_swap_entry(endpoints[e].0, endpoints[e].1))
                .product();
            direct += external_weight * direct_entry;

            let mut mode_sum = 0_i128;
            for weight in 0..=crossing_count {
                for selected in 0..(1_usize << crossing_count) {
                    if selected.count_ones() as usize != weight {
                        continue;
                    }
                    let entry: i128 = (0..crossing_count)
                        .map(|e| {
                            let (row, col) = endpoints[e];
                            if (selected >> e) & 1 == 1 {
                                -singlet_numerator(row) * singlet_numerator(col)
                            } else {
                                delta(row, col)
                            }
                        })
                        .product();
                    mode_sum += entry;
                }
            }
            assert_eq!(
                mode_sum, direct_entry,
                "shared-wire state={state}, crossings={crossing_count}"
            );
            grouped += external_weight * mode_sum;
        }
        assert_eq!(grouped, direct, "crossings={crossing_count}");
    }
}
