//! Small exact-integer witness for the combined matching + symbol-port
//! conditional-expectation construction. No random sampling, floats,
//! SAT oracle, recursive tensor count or unproved source schedule.
//!
//! Normalized matching potential:
//! A_(gamma,j) = E[2^X_(gamma,j) | partial labels] / (1+1/D)^m_j.
//! Normalized real-port potential (z=(4delta+1)/(4delta)):
//! B_(shore,i,s) = E[z^C_(shore,i,s) | partial] / E[z^C_(shore,i,s)].
//!
//! Phi = (sum A)/(kD) + (sum B)/(2ar).
//! E Phi = 2 at the initially unassigned labels.  Exactly averaging
//! candidates for each vertex over b=r^a labels recovers the old
//! potential.  A deterministic minimum thus never increases Phi.
//! At completion, sum A<=2kD and every B<=4ar, implying the
//! bounds proved in two_adic_joint_potential.rs.
//!
//! This reference intentionally uses checked u128 arithmetic only,
//! and refuses when the exact common integer denominator overflows.
//! Input is limited to 5 edges, r<=3 and a<=2.  The general theorem
//! is a polynomial *mathematical construction*, not an assertion that
//! this tiny u128 prototype can execute its large-input hypotheses.

use crate::Error;
use crate::matching_packing::{BipartiteGraph, greedy_edge_colors};
use crate::two_adic_joint_potential::JointPotentialArithmetic;
use crate::two_adic_orbit_sparse::{
    OrbitSparsePacketLayout, construct_orbit_sparse_bounded,
};
use crate::two_adic_packet_layout::BipartiteEdge;

const MAX_EDGES: usize = 5;
const MAX_VERTICES: usize = 12;

fn overflow() -> Error {
    Error::Capacity("combined exact normalized potential exceeds u128".into())
}

fn invalid(message: &'static str) -> Error {
    Error::Invalid(message.into())
}

fn multiply(a: u128, b: u128) -> Result<u128, Error> {
    a.checked_mul(b).ok_or_else(overflow)
}

fn add(a: u128, b: u128) -> Result<u128, Error> {
    a.checked_add(b).ok_or_else(overflow)
}

fn pow(mut base: u128, mut exponent: usize) -> Result<u128, Error> {
    let mut product = 1u128;
    while exponent != 0 {
        if exponent & 1 != 0 {
            product = multiply(product, base)?;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = multiply(base, base)?;
        }
    }
    Ok(product)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JointPotentialCertificate {
    pub r: usize,
    pub a: u32,
    pub maximum_degree: usize,
    pub matching_count: usize,
    pub left_labels: Vec<usize>,
    pub right_labels: Vec<usize>,
    pub edge_colors: Vec<usize>,
    pub initial_potential_numerator: u128,
    pub final_potential_numerator: u128,
    pub common_positive_denominator: u128,
    pub choices_evaluated: usize,
    /// Each step's exact b-way averaging equality was checked.
    pub all_conditional_average_identities_verified: bool,
    /// Exact derived class-bound comparison: 2D X_max <=
    /// 3M + 2D*k*ceil(log2(2D)).
    pub pair_class_bound_verified: bool,
    pub maximum_pair_class_load: usize,
    pub maximum_row_symbol_load: usize,
    pub maximum_column_symbol_load: usize,
    pub threshold_audit: JointPotentialArithmetic,
    pub orbit_sparse_layout: OrbitSparsePacketLayout,
}

impl JointPotentialCertificate {
    pub fn structurally_admitted(&self) -> bool {
        self.orbit_sparse_layout.original_packet_bounds_hold()
    }

    /// Despite exact source-slot structure, this still does not
    /// constitute a source-defined deformation or counting run.
    pub fn source_recursion_admitted(&self) -> bool {
        false
    }
}

struct ExactPotential<'a> {
    graph: &'a BipartiteGraph,
    matchings: Vec<Vec<usize>>,
    d: u128,
    b: usize,
    r: usize,
    a: u32,
    k: usize,
    delta: usize,
    common_matching_denominator: u128,
    powers_num: Vec<u128>,
    powers_den: Vec<u128>,
    degrees_left: Vec<usize>,
    degrees_right: Vec<usize>,
    port_den_left: u128,
    port_den_right: u128,
    number_ports: u128,
    common_denominator: u128,
}

impl<'a> ExactPotential<'a> {
    fn prior_for_degree(&self, degree: usize) -> Result<u128, Error> {
        if degree == 0 {
            Ok(1)
        } else {
            add(
                multiply(u128::try_from(self.r - 1).map_err(|_| overflow())?, self.powers_den[degree])?,
                self.powers_num[degree],
            )
        }
    }

    fn new(
        graph: &'a BipartiteGraph,
        colors: &[usize],
        k: usize,
        delta: usize,
        r: usize,
        a: u32,
    ) -> Result<Self, Error> {
        let b = r.checked_pow(a).ok_or_else(overflow)?;
        let d = multiply(
            u128::try_from(b).map_err(|_| overflow())?,
            u128::try_from(b).map_err(|_| overflow())?,
        )?;
        let mut matchings = vec![Vec::new(); k];
        for (edge, &color) in colors.iter().enumerate() {
            matchings[color].push(edge);
        }
        let maximum_matching_size = matchings.iter().map(Vec::len).max().unwrap_or(0);
        let common_matching_denominator = pow(add(d, 1)?, maximum_matching_size)?;
        let v = multiply(4, u128::try_from(delta).map_err(|_| overflow())?)?;
        let u = add(v, 1)?;
        let powers_num = (0..=delta).map(|j| pow(u, j)).collect::<Result<Vec<_>, _>>()?;
        let powers_den = (0..=delta).map(|j| pow(v, j)).collect::<Result<Vec<_>, _>>()?;
        let mut degrees_left = vec![0usize; graph.left_vertices];
        let mut degrees_right = vec![0usize; graph.right_vertices];
        for &(left, right) in &graph.edges {
            degrees_left[left] += 1;
            degrees_right[right] += 1;
        }
        let mut result = Self {
            graph,
            matchings,
            d,
            b,
            r,
            a,
            k,
            delta,
            common_matching_denominator,
            powers_num,
            powers_den,
            degrees_left,
            degrees_right,
            port_den_left: 1,
            port_den_right: 1,
            number_ports: multiply(multiply(2, u128::from(a))?, u128::try_from(r).map_err(|_| overflow())?)?,
            common_denominator: 0,
        };
        let mut left_den = 1;
        for &degree in &result.degrees_left {
            left_den = multiply(left_den, result.prior_for_degree(degree)?)?;
        }
        let mut right_den = 1;
        for &degree in &result.degrees_right {
            right_den = multiply(right_den, result.prior_for_degree(degree)?)?;
        }
        result.port_den_left = left_den;
        result.port_den_right = right_den;
        result.common_denominator = multiply(
            multiply(multiply(u128::try_from(k).map_err(|_| overflow())?, d)?, common_matching_denominator)?,
            multiply(result.number_ports, multiply(left_den, right_den)?)?,
        )?;
        Ok(result)
    }

    fn matching_numerator(&self, left: &[Option<usize>], right: &[Option<usize>]) -> Result<u128, Error> {
        let mut total = 0;
        for matching in &self.matchings {
            let pad = pow(self.d + 1, self.matchings.iter().map(Vec::len).max().unwrap_or(0) - matching.len())?;
            for row_label in 0..self.b {
                for col_label in 0..self.b {
                    let mut term = pad;
                    for &edge_id in matching {
                        let (row, col) = self.graph.edges[edge_id];
                        let row_hit = left[row].map(|value| value == row_label);
                        let col_hit = right[col].map(|value| value == col_label);
                        let extra = match (row_hit, col_hit) {
                            (Some(false), _) | (_, Some(false)) => 0,
                            (Some(true), Some(true)) => self.d,
                            (None, None) => 1,
                            _ => u128::try_from(self.b).map_err(|_| overflow())?,
                        };
                        term = multiply(term, add(self.d, extra)?)?;
                    }
                    total = add(total, term)?;
                }
            }
        }
        Ok(total)
    }

    fn port_sum(
        &self,
        side_labels: &[Option<usize>],
        degrees: &[usize],
    ) -> Result<u128, Error> {
        let mut result = 0;
        let r = u128::try_from(self.r).map_err(|_| overflow())?;
        let mut place = 1usize;
        for _ in 0..self.a {
            for symbol in 0..self.r {
                let mut term = 1;
                for (&degree, &label) in degrees.iter().zip(side_labels) {
                    if degree == 0 {
                        continue;
                    }
                    let factor = match label {
                        None => self.prior_for_degree(degree)?,
                        Some(value) if (value / place) % self.r == symbol => {
                            multiply(r, self.powers_num[degree])?
                        }
                        Some(_) => multiply(r, self.powers_den[degree])?,
                    };
                    term = multiply(term, factor)?;
                }
                result = add(result, term)?;
            }
            place = place.checked_mul(self.r).ok_or_else(overflow)?;
        }
        Ok(result)
    }

    fn normalized_score(
        &self,
        left: &[Option<usize>],
        right: &[Option<usize>],
    ) -> Result<u128, Error> {
        let match_num = self.matching_numerator(left, right)?;
        let port_left = self.port_sum(left, &self.degrees_left)?;
        let port_right = self.port_sum(right, &self.degrees_right)?;
        let port_combined = add(
            multiply(port_left, self.port_den_right)?,
            multiply(port_right, self.port_den_left)?,
        )?;
        let pair_factor = multiply(
            multiply(u128::try_from(self.k).map_err(|_| overflow())?, self.d)?,
            self.common_matching_denominator,
        )?;
        add(
            multiply(match_num, multiply(self.number_ports, multiply(self.port_den_left, self.port_den_right)?)?)?,
            multiply(port_combined, pair_factor)?,
        )
    }

    fn verify_final_partial_bounds(
        &self,
        left: &[Option<usize>],
        right: &[Option<usize>],
    ) -> Result<(), Error> {
        let matched = self.matching_numerator(left, right)?;
        let limit = multiply(
            2,
            multiply(
                multiply(u128::try_from(self.k).map_err(|_| overflow())?, self.d)?,
                self.common_matching_denominator,
            )?,
        )?;
        if matched > limit {
            return Err(invalid("exact matching exponential potential above joint allowance"));
        }
        let port_bound = multiply(
            multiply(2, self.number_ports)?,
            multiply(self.port_den_left, self.port_den_right)?,
        )?;
        let left_den = self.port_den_right;
        let right_den = self.port_den_left;
        let mut place = 1usize;
        for _ in 0..self.a {
            for symbol in 0..self.r {
                for (labels, degrees, other_den) in [
                    (left, self.degrees_left.as_slice(), left_den),
                    (right, self.degrees_right.as_slice(), right_den),
                ] {
                    let mut term = 1u128;
                    for (&degree, &label) in degrees.iter().zip(labels) {
                        if degree == 0 {
                            continue;
                        }
                        let r = u128::try_from(self.r).map_err(|_| overflow())?;
                        let factor = match label {
                            None => self.prior_for_degree(degree)?,
                            Some(v) if (v / place) % self.r == symbol => {
                                multiply(r, self.powers_num[degree])?
                            }
                            Some(_) => multiply(r, self.powers_den[degree])?,
                        };
                        term = multiply(term, factor)?;
                    }
                    if multiply(term, other_den)? > port_bound {
                        return Err(invalid("exact port exponential potential above joint allowance"));
                    }
                }
            }
            place = place.checked_mul(self.r).ok_or_else(overflow)?;
        }
        Ok(())
    }
}

/// Exact conditional-expectation reference for a small bipartite multigraph.
///
/// A complete returned certificate verifies every b-way expectation
/// equality, monotonicity, final normalized potential and class bound.
/// Full source structural admission and counting semantics are distinct.
pub fn construct_joint_potential_labels_small(
    graph: &BipartiteGraph,
    r: usize,
    a: u32,
) -> Result<JointPotentialCertificate, Error> {
    if graph.edges.is_empty()
        || graph.edges.len() > MAX_EDGES
        || graph.left_vertices > MAX_VERTICES
        || graph.right_vertices > MAX_VERTICES
        || !(2..=3).contains(&r)
        || !(1..=2).contains(&a)
    {
        return Err(invalid(
            "exact joint potential supports 1..=5 edges, <=12 vertices per shore, 2<=r<=3, 1<=a<=2",
        ));
    }
    let (colors, k, delta) = greedy_edge_colors(graph)?;
    let evaluator = ExactPotential::new(graph, &colors, k, delta, r, a)?;
    let mut left = vec![None; graph.left_vertices];
    let mut right = vec![None; graph.right_vertices];
    let initial = evaluator.normalized_score(&left, &right)?;
    if initial != multiply(2, evaluator.common_denominator)? {
        return Err(invalid("initial combined normalized potential is not two"));
    }
    let mut current = initial;
    let mut evaluated = 1usize;
    for vertex in 0..graph.left_vertices + graph.right_vertices {
        let mut selected: Option<(usize, u128)> = None;
        let mut sum_candidates = 0u128;
        for label in 0..evaluator.b {
            if vertex < graph.left_vertices {
                left[vertex] = Some(label);
            } else {
                right[vertex - graph.left_vertices] = Some(label);
            }
            let value = evaluator.normalized_score(&left, &right)?;
            sum_candidates = add(sum_candidates, value)?;
            evaluated += 1;
            if selected.is_none_or(|(_, best)| value < best) {
                selected = Some((label, value));
            }
        }
        let mean_numerator = multiply(
            current,
            u128::try_from(evaluator.b).map_err(|_| overflow())?,
        )?;
        if sum_candidates != mean_numerator {
            return Err(invalid("conditional expectation candidate average failed"));
        }
        let (chosen, value) = selected.ok_or_else(|| invalid("empty label alphabet"))?;
        if value > current {
            return Err(invalid("normalized joint potential increased"));
        }
        if vertex < graph.left_vertices {
            left[vertex] = Some(chosen);
        } else {
            right[vertex - graph.left_vertices] = Some(chosen);
        }
        current = value;
    }
    evaluator.verify_final_partial_bounds(&left, &right)?;
    let left_labels = left.into_iter().map(|v| v.unwrap_or(0)).collect::<Vec<_>>();
    let right_labels = right.into_iter().map(|v| v.unwrap_or(0)).collect::<Vec<_>>();
    let d = usize::try_from(evaluator.d).map_err(|_| overflow())?;
    let mut pair_counts = vec![0usize; d];
    let mut real_edges = Vec::with_capacity(graph.edges.len());
    for &(i, j) in &graph.edges {
        pair_counts[left_labels[i] * evaluator.b + right_labels[j]] += 1;
        real_edges.push(BipartiteEdge { left: i, right: j });
    }
    let maximum_pair_class_load = pair_counts.into_iter().max().unwrap_or(0);
    let t = u128::from(u128::BITS - (evaluator.d - 1).leading_zeros()) + 1;
    let lhs = multiply(
        multiply(2, evaluator.d)?,
        u128::try_from(maximum_pair_class_load).map_err(|_| overflow())?,
    )?;
    let rhs = add(
        multiply(3, u128::try_from(graph.edges.len()).map_err(|_| overflow())?)?,
        multiply(multiply(multiply(2, evaluator.d)?, u128::try_from(k).map_err(|_| overflow())?)?, t)?,
    )?;
    if lhs > rhs {
        return Err(invalid("derived joint maximum ordered-class load bound failed"));
    }
    let source_degree_cap = delta.max(2usize.checked_shl(a).ok_or_else(overflow)?);
    let layout = construct_orbit_sparse_bounded(
        &real_edges,
        &left_labels,
        &right_labels,
        r,
        a,
        source_degree_cap,
    )?;
    let max_row = layout.row_ports.iter().flat_map(|loads| loads.iter()).copied().max().unwrap_or(0);
    let max_col = layout.column_ports.iter().flat_map(|loads| loads.iter()).copied().max().unwrap_or(0);
    let theorem = JointPotentialArithmetic::new(
        u128::try_from(graph.edges.len()).map_err(|_| overflow())?,
        u32::try_from(r).map_err(|_| overflow())?,
        a,
        u128::try_from(delta).map_err(|_| overflow())?,
        u128::try_from(source_degree_cap).map_err(|_| overflow())?,
    )?;
    if theorem.simultaneous_sufficient_arithmetic && !layout.original_packet_bounds_hold() {
        return Err(invalid("new combined potential theorem contradicted by constructed layout"));
    }
    Ok(JointPotentialCertificate {
        r,
        a,
        maximum_degree: delta,
        matching_count: k,
        left_labels,
        right_labels,
        edge_colors: colors,
        initial_potential_numerator: initial,
        final_potential_numerator: current,
        common_positive_denominator: evaluator.common_denominator,
        choices_evaluated: evaluated,
        all_conditional_average_identities_verified: true,
        pair_class_bound_verified: true,
        maximum_pair_class_load,
        maximum_row_symbol_load: max_row,
        maximum_column_symbol_load: max_col,
        threshold_audit: theorem,
        orbit_sparse_layout: layout,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_joint_potential_on_single_edge() {
        let graph = BipartiteGraph {
            left_vertices: 1,
            right_vertices: 1,
            edges: vec![(0, 0)],
        };
        for a in 1..=2 {
            let result = construct_joint_potential_labels_small(&graph, 2, a).unwrap();
            assert_eq!(result.initial_potential_numerator, 2*result.common_positive_denominator);
            assert!(result.final_potential_numerator <= result.initial_potential_numerator);
            assert_eq!(result.choices_evaluated, 1 + 2 * (1usize << a));
            assert_eq!(result.maximum_pair_class_load, 1);
            assert!(result.all_conditional_average_identities_verified);
            assert!(result.pair_class_bound_verified);
            assert!(!result.source_recursion_admitted());
        }
    }

    #[test]
    fn exact_joint_potential_handles_parallel_edges() {
        let graph = BipartiteGraph {
            left_vertices: 1,
            right_vertices: 1,
            edges: vec![(0, 0), (0, 0), (0, 0)],
        };
        let result = construct_joint_potential_labels_small(&graph, 2, 2).unwrap();
        assert_eq!(result.maximum_degree, 3);
        assert_eq!(result.matching_count, 3);
        assert_eq!(result.maximum_pair_class_load, 3);
        assert_eq!(result.orbit_sparse_layout.real_edges, 3);
        assert!(result.pair_class_bound_verified);
    }

    #[test]
    fn exhaustive_small_graphs_obey_exact_conditional_average() {
        for mask in 1..16usize {
            let edges = (0..4)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| (i / 2, i % 2))
                .collect::<Vec<_>>();
            let graph = BipartiteGraph {
                left_vertices: 2,
                right_vertices: 2,
                edges,
            };
            for a in 1..=2 {
                let result = construct_joint_potential_labels_small(&graph, 2, a).unwrap();
                assert!(result.final_potential_numerator <= result.initial_potential_numerator);
                assert_eq!(result.initial_potential_numerator, 2*result.common_positive_denominator);
                assert!(result.pair_class_bound_verified);
                assert!(result.all_conditional_average_identities_verified);
                assert_eq!(
                    result,
                    construct_joint_potential_labels_small(&graph, 2, a).unwrap()
                );
            }
        }
    }

    #[test]
    fn invalid_or_unrepresentable_inputs_refuse() {
        let graph = BipartiteGraph {
            left_vertices: 1,
            right_vertices: 1,
            edges: vec![(0, 0)],
        };
        assert!(construct_joint_potential_labels_small(&graph, 1, 1).is_err());
        assert!(construct_joint_potential_labels_small(&graph, 2, 0).is_err());
        assert!(construct_joint_potential_labels_small(&graph, 4, 1).is_err());
        assert!(construct_joint_potential_labels_small(&graph, 2, 3).is_err());
        let big = BipartiteGraph {
            left_vertices: 1,
            right_vertices: 1,
            edges: vec![(0, 0); 6],
        };
        assert!(construct_joint_potential_labels_small(&big, 2, 1).is_err());
    }
}
