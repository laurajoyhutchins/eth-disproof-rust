//! Bounded, exact reference implementation of the matching-potential labeler.
//!
//! This implements the constructive argument in research/matching-potential-packing.md
//! for *small graphs*. Conditional expectations are represented by an exact
//! integer numerator with common denominator (D+1)^M, not floating point.
//! Checked u128 arithmetic intentionally refuses larger graphs. A future
//! unrestricted implementation must use existing arbitrary-precision crates.
//!
//! This is a packet *labeling* research reference, NOT a packet-contraction
//! engine, source-Lean differential, or a certificate for active recursion.

use crate::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BipartiteEdge {
    pub left: usize,
    pub right: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchingLabeling {
    pub alphabet: usize,
    pub left_labels: Vec<usize>,
    pub right_labels: Vec<usize>,
    pub edge_colors: Vec<usize>,
    pub matchings: usize,
    /// Ordered (left, right) pair classes, indexed left * alphabet + right.
    pub pair_loads: Vec<usize>,
    pub maximum_pair_load: usize,
    /// Exact common-denominator potential before/after conditional minimization.
    pub initial_potential_numerator: u128,
    pub final_potential_numerator: u128,
}

fn capacity() -> Error {
    Error::Capacity(
        "bounded matching-potential reference exceeded u128; arbitrary precision required".into(),
    )
}

fn potential_numerator(
    alphabet: usize,
    edges: &[BipartiteEdge],
    colors: &[usize],
    matchings: usize,
    left: &[Option<usize>],
    right: &[Option<usize>],
) -> Result<u128, Error> {
    let b = u128::try_from(alphabet).map_err(|_| capacity())?;
    let d = b.checked_mul(b).ok_or_else(capacity)?;
    let base = d.checked_add(1).ok_or_else(capacity)?;
    let mut total = 0u128;
    let m = u32::try_from(edges.len()).map_err(|_| capacity())?;
    for color in 0..matchings {
        let count = u32::try_from(colors.iter().filter(|&&c| c == color).count())
            .map_err(|_| capacity())?;
        let normalization = base.checked_pow(m - count).ok_or_else(capacity)?;
        for left_symbol in 0..alphabet {
            for right_symbol in 0..alphabet {
                let mut product = 1u128;
                for (&edge, &edge_color) in edges.iter().zip(colors) {
                    if edge_color != color {
                        continue;
                    }
                    // D times the conditional probability that this edge
                    // receives the ordered pair (left_symbol,right_symbol).
                    let numerator = match (left[edge.left], right[edge.right]) {
                        (Some(l), Some(r)) if l == left_symbol && r == right_symbol => d,
                        (Some(_), Some(_)) => 0,
                        (Some(l), None) if l == left_symbol => b,
                        (Some(_), None) => 0,
                        (None, Some(r)) if r == right_symbol => b,
                        (None, Some(_)) => 0,
                        (None, None) => 1,
                    };
                    let factor = d.checked_add(numerator).ok_or_else(capacity)?;
                    product = product.checked_mul(factor).ok_or_else(capacity)?;
                }
                let term = product.checked_mul(normalization).ok_or_else(capacity)?;
                total = total.checked_add(term).ok_or_else(capacity)?;
            }
        }
    }
    Ok(total)
}

/// Deterministically assign labels minimizing the exact conditional
/// expectation of a matching exponential potential.
///
/// Edge coloring is proper and greedy, using <=2*maximum_degree-1 colors.
/// The proof extends to arbitrary graphs with big integers, but this
/// independent executable reference is deliberately limited to 32 edges,
/// 32 vertices per side and alphabet <=8. Exceeding a bound refuses.
pub fn construct_bounded(
    left_vertices: usize,
    right_vertices: usize,
    edges: &[BipartiteEdge],
    alphabet: usize,
) -> Result<MatchingLabeling, Error> {
    if left_vertices == 0 || right_vertices == 0 || edges.is_empty() || alphabet < 2 {
        return Err(Error::Invalid(
            "nonempty bipartite graph and alphabet >=2 required".into(),
        ));
    }
    if left_vertices > 32 || right_vertices > 32 || edges.len() > 32 || alphabet > 8 {
        return Err(capacity());
    }
    let mut color_left: Vec<Vec<usize>> = vec![Vec::new(); left_vertices];
    let mut color_right: Vec<Vec<usize>> = vec![Vec::new(); right_vertices];
    let mut edge_colors = Vec::with_capacity(edges.len());
    for edge in edges {
        if edge.left >= left_vertices || edge.right >= right_vertices {
            return Err(Error::Invalid(
                "edge endpoint outside declared vertex part".into(),
            ));
        }
        let mut color = 0usize;
        while color_left[edge.left].contains(&color) || color_right[edge.right].contains(&color) {
            color = color.checked_add(1).ok_or_else(capacity)?;
        }
        color_left[edge.left].push(color);
        color_right[edge.right].push(color);
        edge_colors.push(color);
    }
    let matchings = 1 + edge_colors.iter().copied().max().unwrap_or(0);
    let max_degree = color_left
        .iter()
        .chain(&color_right)
        .map(Vec::len)
        .max()
        .unwrap_or(0);
    if matchings > max_degree.saturating_mul(2).saturating_sub(1) {
        return Err(Error::Invalid("edge coloring exceeded 2*Delta-1".into()));
    }

    let mut left = vec![None; left_vertices];
    let mut right = vec![None; right_vertices];
    let denominator = (u128::try_from(alphabet).map_err(|_| capacity())?)
        .checked_pow(2)
        .and_then(|d| d.checked_add(1))
        .and_then(|base| base.checked_pow(u32::try_from(edges.len()).ok()?))
        .ok_or_else(capacity)?;
    let d = alphabet.checked_mul(alphabet).ok_or_else(capacity)?;
    let initial = u128::try_from(d)
        .ok()
        .and_then(|d| d.checked_mul(u128::try_from(matchings).ok()?))
        .and_then(|dk| dk.checked_mul(denominator))
        .ok_or_else(capacity)?;
    let initial_evaluated =
        potential_numerator(alphabet, edges, &edge_colors, matchings, &left, &right)?;
    if initial != initial_evaluated {
        return Err(Error::Invalid(
            "conditional potential disagrees with matching independence".into(),
        ));
    }
    let mut last_potential = initial;
    // Fixed deterministic order, left vertices first, then right vertices.
    for vertex in 0..left_vertices + right_vertices {
        let mut best: Option<(usize, u128)> = None;
        for symbol in 0..alphabet {
            if vertex < left_vertices {
                left[vertex] = Some(symbol);
            } else {
                right[vertex - left_vertices] = Some(symbol);
            }
            let value =
                potential_numerator(alphabet, edges, &edge_colors, matchings, &left, &right)?;
            if best.is_none_or(|(_, current)| value < current) {
                best = Some((symbol, value));
            }
        }
        let (symbol, value) = best.ok_or_else(capacity)?;
        if value > last_potential {
            return Err(Error::Invalid(
                "conditional-expectation minimizer increased potential".into(),
            ));
        }
        if vertex < left_vertices {
            left[vertex] = Some(symbol);
        } else {
            right[vertex - left_vertices] = Some(symbol);
        }
        last_potential = value;
    }
    let left_labels = left.into_iter().map(|x| x.unwrap_or(0)).collect::<Vec<_>>();
    let right_labels = right
        .into_iter()
        .map(|x| x.unwrap_or(0))
        .collect::<Vec<_>>();
    let mut pair_loads = vec![0usize; d];
    for edge in edges {
        let index = left_labels[edge.left]
            .checked_mul(alphabet)
            .and_then(|i| i.checked_add(right_labels[edge.right]))
            .ok_or_else(capacity)?;
        pair_loads[index] += 1;
    }
    let maximum_pair_load = *pair_loads.iter().max().unwrap_or(&0);
    if pair_loads.iter().sum::<usize>() != edges.len() || last_potential > initial {
        return Err(Error::Invalid(
            "labeling certificate lost edges or increased potential".into(),
        ));
    }
    Ok(MatchingLabeling {
        alphabet,
        left_labels,
        right_labels,
        edge_colors,
        matchings,
        pair_loads,
        maximum_pair_load,
        initial_potential_numerator: initial,
        final_potential_numerator: last_potential,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disjoint_matching_has_exact_balanced_labeling() {
        let edges = (0..4)
            .map(|i| BipartiteEdge { left: i, right: i })
            .collect::<Vec<_>>();
        let result = construct_bounded(4, 4, &edges, 2).unwrap();
        assert_eq!(result.matchings, 1);
        assert_eq!(result.edge_colors, [0, 0, 0, 0]);
        assert_eq!(result.pair_loads.iter().sum::<usize>(), 4);
        assert!(result.maximum_pair_load <= 2);
        assert_eq!(result.initial_potential_numerator, 2500);
        assert!(result.final_potential_numerator <= 2500);
    }

    #[test]
    fn constructed_labels_satisfy_padded_class_bound_at_actual_color_threshold() {
        // Abstract packet-lemma parameters b=2, D=4, L=2, with k=1
        // matching. This is not the source's positive-u parameter schedule.
        // M=D*(k*ceil(log2 D)+L)=4*(2+2)=16 exactly.
        let edges = (0..16)
            .map(|i| BipartiteEdge { left: i, right: i })
            .collect::<Vec<_>>();
        let result = construct_bounded(16, 16, &edges, 2).unwrap();
        assert_eq!(result.matchings, 1);
        let m = edges.len();
        let d = result.pair_loads.len();
        let l = 2usize;
        assert_eq!(m, d * (result.matchings * 2 + l));
        let padded_load = result.maximum_pair_load.div_ceil(l) * l;
        assert!(padded_load * d <= 3 * m);
        assert!(padded_load * d / l <= 3 * m / l);
        for row_symbol in 0..2 {
            let row_ports = result.pair_loads[row_symbol * 2]
                + result.pair_loads[row_symbol * 2 + 1];
            assert!(row_ports <= 3 * m / 2);
        }
        for column_symbol in 0..2 {
            let column_ports = result.pair_loads[column_symbol]
                + result.pair_loads[2 + column_symbol];
            assert!(column_ports <= 3 * m / 2);
        }
        assert!(result.final_potential_numerator <= result.initial_potential_numerator);
    }

    #[test]
    fn shared_endpoints_and_parallel_edges_are_properly_colored() {
        let cases = vec![
            (2, 2, vec![(0, 0), (0, 1), (1, 0), (1, 1)]),
            (1, 1, vec![(0, 0), (0, 0)]),
            (1, 3, vec![(0, 0), (0, 1), (0, 2)]),
        ];
        for (rows, cols, edge_pairs) in cases {
            let edges = edge_pairs
                .into_iter()
                .map(|(left, right)| BipartiteEdge { left, right })
                .collect::<Vec<_>>();
            let result = construct_bounded(rows, cols, &edges, 2).unwrap();
            for (i, a) in edges.iter().enumerate() {
                for (j, b) in edges.iter().enumerate().skip(i + 1) {
                    if a.left == b.left || a.right == b.right {
                        assert_ne!(result.edge_colors[i], result.edge_colors[j]);
                    }
                }
            }
            assert!(result.final_potential_numerator <= result.initial_potential_numerator);
            assert_eq!(result.pair_loads.iter().sum::<usize>(), edges.len());
        }
    }

    #[test]
    fn bad_graphs_and_big_numerators_refuse() {
        assert!(construct_bounded(1, 1, &[], 2).is_err());
        assert!(construct_bounded(1, 1, &[BipartiteEdge { left: 1, right: 0 }], 2).is_err());
        assert!(construct_bounded(1, 1, &[BipartiteEdge { left: 0, right: 0 }], 1).is_err());
        let edges = (0..32)
            .map(|i| BipartiteEdge { left: i, right: i })
            .collect::<Vec<_>>();
        assert!(matches!(
            construct_bounded(32, 32, &edges, 8),
            Err(Error::Capacity(_))
        ));
        assert!(construct_bounded(33, 1, &[BipartiteEdge { left: 0, right: 0 }], 2).is_err());
    }
}
