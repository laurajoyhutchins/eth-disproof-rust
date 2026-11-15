//! Deterministic proper edge-coloring and exact conditional-expectation
//! vertex labeling for the appendix's *packing* subproblem.
//!
//! This is a finite graph operation, not an ETH counting implementation.
//! For a bipartite graph with M edges and maximum degree delta, greedy
//! edge coloring uses k <= 2*delta-1 matchings. For ordered vertex label
//! pairs D=q^2, the exact rational pessimistic estimator is
//!
//!   Phi = sum_{class gamma, matching j}
//!       E[2^(X_gamma,j) | partially chosen labels]
//!       / (1+1/D)^(m_j).
//!
//! Each matching contains disjoint edges, so the conditional expectations
//! factor even with some vertex labels already fixed. Phi initially equals
//! k*D. Choose the next vertex label minimizing Phi. Averaging over its
//! q possible labels recovers the previous Phi, so Phi cannot increase.
//! At completion, for each class gamma, AM-GM averages its k terms:
//!   (product_j A_gamma,j)^(1/k) <= (sum_j A_gamma,j)/k <= Phi/k <= D.
//! Consequently X_max <= (3/2) M/D + k*ceil(log2 D).
//! The normalization by k eliminates any extra log(k).
//!
//! The arithmetic evaluates Phi with a common integer denominator:
//! the class/matching term numerator is
//!   product_e (D + D*Pr[e has class gamma | partial labeling])
//!   * (D+1)^(max_j m_j - m_j).
//! No floating point, randomized success, or exponential SAT oracle.
//! Intermediate integer overflow and excessive work fail closed.
//!
//! The result proves an exact *finite packing labeling* for the provided
//! graph, not the paper's child-degree/precision/recursion invariants.

use crate::Error;

const MAX_ESTIMATED_EVALUATION_WORK: u128 = 20_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BipartiteGraph {
    pub left_vertices: usize,
    pub right_vertices: usize,
    /// Multiedges are permitted, but every endpoint must exist.
    pub edges: Vec<(usize, usize)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchingLabelCertificate {
    pub labels_per_side: u32,
    /// Each vertex is assigned one label in 0..q.
    pub left_labels: Vec<u32>,
    pub right_labels: Vec<u32>,
    /// Edge colors are proper: each color class is a matching.
    pub edge_colors: Vec<usize>,
    pub matching_count: usize,
    pub maximum_degree: usize,
    pub maximum_pair_class_load: usize,
    pub initial_potential: u128,
    pub final_potential: u128,
    pub exact_load_bound_numerator: u128,
    pub exact_load_bound_denominator: u128,
}

fn overflow() -> Error {
    Error::Capacity("exact matching-potential arithmetic exceeds u128".into())
}

fn checked_power(mut base: u128, mut exponent: usize) -> Result<u128, Error> {
    let mut result = 1u128;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result.checked_mul(base).ok_or_else(overflow)?;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = base.checked_mul(base).ok_or_else(overflow)?;
        }
    }
    Ok(result)
}

pub(crate) fn greedy_edge_colors(graph: &BipartiteGraph) -> Result<(Vec<usize>, usize, usize), Error> {
    let mut degree_left = vec![0usize; graph.left_vertices];
    let mut degree_right = vec![0usize; graph.right_vertices];
    let mut left_used = vec![Vec::<usize>::new(); graph.left_vertices];
    let mut right_used = vec![Vec::<usize>::new(); graph.right_vertices];
    let mut colors = Vec::with_capacity(graph.edges.len());
    let mut count = 0;
    for &(left, right) in &graph.edges {
        if left >= graph.left_vertices || right >= graph.right_vertices {
            return Err(Error::Invalid(
                "bipartite edge endpoint out of range".into(),
            ));
        }
        degree_left[left] = degree_left[left].checked_add(1).ok_or_else(overflow)?;
        degree_right[right] = degree_right[right].checked_add(1).ok_or_else(overflow)?;
        let mut color = 0usize;
        while left_used[left].contains(&color) || right_used[right].contains(&color) {
            color = color.checked_add(1).ok_or_else(overflow)?;
        }
        left_used[left].push(color);
        right_used[right].push(color);
        colors.push(color);
        count = count.max(color + 1);
    }
    let maximum_degree = degree_left
        .into_iter()
        .chain(degree_right)
        .max()
        .unwrap_or(0);
    if maximum_degree != 0 && count > maximum_degree.saturating_mul(2) - 1 {
        return Err(Error::Invalid(
            "proper greedy coloring exceeds 2 delta - 1".into(),
        ));
    }
    Ok((colors, count, maximum_degree))
}

struct Potential<'a> {
    graph: &'a BipartiteGraph,
    colors: &'a [usize],
    matching_edges: Vec<Vec<usize>>,
    q: u128,
    d: u128,
    max_m: usize,
    common_denominator: u128,
}

impl<'a> Potential<'a> {
    fn new(
        graph: &'a BipartiteGraph,
        colors: &'a [usize],
        count: usize,
        q: u32,
    ) -> Result<Self, Error> {
        let q = u128::from(q);
        let d = q.checked_mul(q).ok_or_else(overflow)?;
        let mut matching_edges = vec![Vec::new(); count];
        for (edge, &color) in colors.iter().enumerate() {
            matching_edges[color].push(edge);
        }
        let max_m = matching_edges.iter().map(Vec::len).max().unwrap_or(0);
        let common_denominator = checked_power(d.checked_add(1).ok_or_else(overflow)?, max_m)?;
        Ok(Self {
            graph,
            colors,
            matching_edges,
            q,
            d,
            max_m,
            common_denominator,
        })
    }

    /// Exact numerator for a common denominator (D+1)^max_matching_size.
    fn numerator(
        &self,
        left_labels: &[Option<u32>],
        right_labels: &[Option<u32>],
    ) -> Result<u128, Error> {
        let mut total = 0u128;
        let base = self.d.checked_add(1).ok_or_else(overflow)?;
        for (color, matching) in self.matching_edges.iter().enumerate() {
            debug_assert!(self.colors.iter().filter(|&&c| c == color).count() == matching.len());
            let scale = checked_power(base, self.max_m - matching.len())?;
            for row_class in 0..self.q {
                for col_class in 0..self.q {
                    let mut term = scale;
                    for &edge_index in matching {
                        let (row, col) = self.graph.edges[edge_index];
                        let row_match = left_labels[row].map(|l| u128::from(l) == row_class);
                        let col_match = right_labels[col].map(|l| u128::from(l) == col_class);
                        let hit_weight = match (row_match, col_match) {
                            (Some(true), Some(true)) => self.d,
                            (Some(false), _) | (_, Some(false)) => 0,
                            (None, None) => 1,
                            (Some(true), None) | (None, Some(true)) => self.q,
                        };
                        term = term
                            .checked_mul(self.d.checked_add(hit_weight).ok_or_else(overflow)?)
                            .ok_or_else(overflow)?;
                    }
                    total = total.checked_add(term).ok_or_else(overflow)?;
                }
            }
        }
        Ok(total)
    }
}

pub fn construct_matching_labels(
    graph: &BipartiteGraph,
    labels_per_side: u32,
) -> Result<MatchingLabelCertificate, Error> {
    if labels_per_side < 2 {
        return Err(Error::Invalid(
            "labels per vertex must be at least two".into(),
        ));
    }
    let (colors, k, maximum_degree) = greedy_edge_colors(graph)?;
    let q = u128::from(labels_per_side);
    let d = q.checked_mul(q).ok_or_else(overflow)?;
    let vertices = graph
        .left_vertices
        .checked_add(graph.right_vertices)
        .ok_or_else(overflow)?;
    let estimated_work = u128::try_from(vertices)
        .map_err(|_| overflow())?
        .checked_mul(q)
        .and_then(|v| v.checked_mul(d))
        .and_then(|v| v.checked_mul(u128::try_from(k.max(1)).ok()?))
        .and_then(|v| v.checked_mul(u128::try_from(graph.edges.len().max(1)).ok()?))
        .ok_or_else(overflow)?;
    if estimated_work > MAX_ESTIMATED_EVALUATION_WORK {
        return Err(Error::Capacity(
            "matching-potential reference exceeds work cap".into(),
        ));
    }
    let estimator = Potential::new(graph, &colors, k, labels_per_side)?;
    let mut left = vec![None; graph.left_vertices];
    let mut right = vec![None; graph.right_vertices];
    let initial = estimator.numerator(&left, &right)?;
    let allowed = u128::try_from(k)
        .map_err(|_| overflow())?
        .checked_mul(d)
        .and_then(|v| v.checked_mul(estimator.common_denominator))
        .ok_or_else(overflow)?;
    if initial != allowed {
        return Err(Error::Invalid(
            "initial rational potential was not kD".into(),
        ));
    }
    let mut current = initial;

    for vertex in 0..vertices {
        let mut chosen: Option<(u32, u128)> = None;
        for label in 0..labels_per_side {
            if vertex < graph.left_vertices {
                left[vertex] = Some(label);
            } else {
                right[vertex - graph.left_vertices] = Some(label);
            }
            let value = estimator.numerator(&left, &right)?;
            if chosen.is_none_or(|(_, best)| value < best) {
                chosen = Some((label, value));
            }
        }
        let (label, value) = chosen.expect("positive label count");
        if value > current {
            return Err(Error::Invalid("conditional potential increased".into()));
        }
        if vertex < graph.left_vertices {
            left[vertex] = Some(label);
        } else {
            right[vertex - graph.left_vertices] = Some(label);
        }
        current = value;
    }

    let left_labels: Vec<u32> = left.into_iter().map(|x| x.unwrap_or(0)).collect();
    let right_labels: Vec<u32> = right.into_iter().map(|x| x.unwrap_or(0)).collect();
    let d_usize = usize::try_from(d).map_err(|_| overflow())?;
    let mut loads = vec![0usize; d_usize];
    for &(u, v) in &graph.edges {
        let row = usize::try_from(left_labels[u]).map_err(|_| overflow())?;
        let col = usize::try_from(right_labels[v]).map_err(|_| overflow())?;
        let q_usize = usize::try_from(labels_per_side).map_err(|_| overflow())?;
        loads[row * q_usize + col] += 1;
    }
    let max_load = loads.into_iter().max().unwrap_or(0);
    let kd = u128::try_from(k)
        .map_err(|_| overflow())?
        .checked_mul(d)
        .ok_or_else(overflow)?;
    let log_d = u128::from(u128::BITS - (d - 1).leading_zeros());
    // Clear denominators in X <= 3M/(2D) + k*ceil(log2(D)).
    let denominator = d.checked_mul(2).ok_or_else(overflow)?;
    let rhs = u128::try_from(graph.edges.len())
        .map_err(|_| overflow())?
        .checked_mul(3)
        .and_then(|v| v.checked_add(kd.checked_mul(2)?.checked_mul(log_d)?))
        .ok_or_else(overflow)?;
    let lhs = u128::try_from(max_load)
        .map_err(|_| overflow())?
        .checked_mul(denominator)
        .ok_or_else(overflow)?;
    if lhs > rhs || current > initial {
        return Err(Error::Invalid(
            "matching load or potential certificate violated".into(),
        ));
    }

    Ok(MatchingLabelCertificate {
        labels_per_side,
        left_labels,
        right_labels,
        edge_colors: colors,
        matching_count: k,
        maximum_degree,
        maximum_pair_class_load: max_load,
        initial_potential: initial,
        final_potential: current,
        exact_load_bound_numerator: rhs,
        exact_load_bound_denominator: denominator,
    })
}
