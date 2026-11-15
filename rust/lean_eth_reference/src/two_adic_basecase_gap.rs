//! Optimistic *all-depth* feasibility analysis for any proposed direct-leaf
//! cutoff in the appendix's two-adic tensor contraction.
//!
//! We deliberately give a candidate every arithmetic advantage:
//! - each active depth has the smallest positive width u_d=1;
//! - a_d=2*(d+1), L_d=2^a_d and D_d=r^(2a_d);
//! - the degree cap may change at every depth and takes its minimum
//!   possible value delta_d=2*L_d (even if reality requires more);
//! - the current child edge count is replaced by its MAXIMUM permitted by
//!   the paper's 6M/r bound, so any actual child may be far smaller.
//!
//! If the matching-potential sufficient threshold exceeds even this
//! maximum possible M_d while M_d still exceeds the *proposed* leaf
//! budget, that depth has an uncovered range. The previous sufficient
//! packing theorem cannot certify an arbitrary active child in the range.
//! This is not a counterexample to actual packing, and child paths could
//! terminate earlier. The original source's fixed u_0 is zero for u128
//! roots and cannot be replaced by this optimistic schedule without a
//! new Lean proof. No SAT counting or expensive leaf enumeration occurs.

use crate::Error;
use crate::two_adic_depth::{child_upper_edges, matching_threshold};

const MAX_DEPTH: usize = 1024;
const MAX_DISPLAYED_STAGES: usize = 12;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptimisticStage {
    pub depth: usize,
    pub largest_possible_edges: u128,
    pub cumulative_a: u32,
    pub minimum_packet_slots_l: Option<u128>,
    pub label_pair_classes_d: Option<u128>,
    /// Minimum degree cap required to contain new packet vertices.
    pub minimum_degree_cap: Option<u128>,
    /// Minimum possible threshold for the new sufficient lemma.
    /// None means the positive threshold exceeds the u128 range.
    pub minimum_matching_required_edges: Option<u128>,
    /// This is a *necessary* arithmetic check for using the sufficient
    /// lemma, not a witness to the graph, labeling or recursive algorithm.
    pub could_meet_matching_sufficient_condition: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasecaseGapAudit {
    pub root_edges: u128,
    pub groups: u32,
    pub proposed_leaf_edge_budget: u128,
    pub lambda: u32,
    pub published_root_width_u: u32,
    /// Iterating the paper's conditional 6M/r bound reaches the target.
    pub hypothetical_guaranteed_leaf_depth: usize,
    /// The first depth where even maximally large children cannot meet
    /// the NEW matching-potential sufficient inequality with u>=1.
    /// None if the leaf budget is reached first.
    pub first_uncovered_active_depth: Option<usize>,
    /// Prefix of stages that could meet the sufficiency inequality in
    /// the most optimistic arithmetic envelope; no actual child is proved.
    pub optimistic_prefix_stages: usize,
    pub upper_edges_at_first_gap: Option<u128>,
    pub minimum_required_edges_at_first_gap: Option<u128>,
    pub minimum_degree_cap_at_first_gap: Option<u128>,
    /// First 12 levels, or all levels if the leaf budget is attained sooner.
    pub stages: Vec<OptimisticStage>,
}

fn stage_at(depth: usize, groups: u32, upper: u128) -> OptimisticStage {
    // MAX_DEPTH bounds this conversion; each hypothetical u_j is exactly 1.
    let a = u32::try_from(2 * (depth + 1)).expect("bounded hypothetical depth");
    let slots = 1u128.checked_shl(a);
    let classes = a
        .checked_mul(2)
        .and_then(|exponent| u128::from(groups).checked_pow(exponent));
    let minimum_degree = slots.and_then(|l| l.checked_mul(2));
    let threshold = minimum_degree.and_then(|delta| matching_threshold(groups, a, delta));
    OptimisticStage {
        depth,
        largest_possible_edges: upper,
        cumulative_a: a,
        minimum_packet_slots_l: slots,
        label_pair_classes_d: classes,
        minimum_degree_cap: minimum_degree,
        minimum_matching_required_edges: threshold,
        could_meet_matching_sufficient_condition: threshold.is_some_and(|needed| needed <= upper),
    }
}

impl BasecaseGapAudit {
    pub fn new(
        root_edges: u128,
        groups: u32,
        proposed_leaf_edge_budget: u128,
    ) -> Result<Self, Error> {
        if root_edges < 2 || proposed_leaf_edge_budget == 0 {
            return Err(Error::Invalid(
                "root edges >= 2 and a positive proposed leaf budget required".into(),
            ));
        }
        if groups < 7 {
            return Err(Error::Invalid(
                "groups >= 7 needed to guarantee the source 6M/r shrink".into(),
            ));
        }

        let lambda = u128::BITS - (root_edges - 1).leading_zeros();
        let mut upper = root_edges;
        let mut depth = 0usize;
        let mut first_gap: Option<OptimisticStage> = None;
        let mut optimistic_prefix_stages = 0;
        let mut stages = Vec::new();

        while upper > proposed_leaf_edge_budget {
            if depth >= MAX_DEPTH {
                return Err(Error::Capacity(
                    "conditional child bound did not reach the leaf budget".into(),
                ));
            }
            let stage = stage_at(depth, groups, upper);
            if first_gap.is_none() {
                if stage.could_meet_matching_sufficient_condition {
                    optimistic_prefix_stages += 1;
                } else {
                    first_gap = Some(stage.clone());
                }
            }
            if stages.len() < MAX_DISPLAYED_STAGES {
                stages.push(stage);
            }
            upper = child_upper_edges(upper, groups)?;
            depth += 1;
        }

        Ok(Self {
            root_edges,
            groups,
            proposed_leaf_edge_budget,
            lambda,
            published_root_width_u: lambda / 131_072,
            hypothetical_guaranteed_leaf_depth: depth,
            first_uncovered_active_depth: first_gap.as_ref().map(|stage| stage.depth),
            optimistic_prefix_stages,
            upper_edges_at_first_gap: first_gap.as_ref().map(|stage| stage.largest_possible_edges),
            minimum_required_edges_at_first_gap: first_gap
                .as_ref()
                .and_then(|stage| stage.minimum_matching_required_edges),
            minimum_degree_cap_at_first_gap: first_gap
                .as_ref()
                .and_then(|stage| stage.minimum_degree_cap),
            stages,
        })
    }

    /// Neither original source schedule nor an independently proven
    /// replacement is executable from this arithmetic alone.
    pub fn source_recursion_admitted(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_matching_gap_at_new_root_threshold() {
        let a = BasecaseGapAudit::new(6_106_906_624, 64, 64).unwrap();
        assert_eq!(a.published_root_width_u, 0);
        assert_eq!(a.stages[0].minimum_degree_cap, Some(8));
        assert_eq!(
            a.stages[0].minimum_matching_required_edges,
            Some(6_106_906_624)
        );
        assert_eq!(a.first_uncovered_active_depth, Some(1));
        assert_eq!(a.optimistic_prefix_stages, 1);
        assert_eq!(a.upper_edges_at_first_gap, Some(572_522_496));
        assert_eq!(
            a.minimum_required_edges_at_first_gap,
            Some(855_683_929_200_394_240)
        );
        assert_eq!(a.minimum_degree_cap_at_first_gap, Some(32));
        assert_eq!(a.hypothetical_guaranteed_leaf_depth, 8);
        assert!(!a.source_recursion_admitted());
    }

    #[test]
    fn changing_group_count_trades_shrink_for_packing() {
        let a = BasecaseGapAudit::new(10_000_000_000, 7, 64).unwrap();
        assert_eq!(a.stages[0].minimum_matching_required_edges, Some(441_784));
        assert_eq!(
            a.stages[1].minimum_matching_required_edges,
            Some(8_445_433_465)
        );
        assert_eq!(a.first_uncovered_active_depth, Some(2));
        assert_eq!(a.optimistic_prefix_stages, 2);
        assert_eq!(a.hypothetical_guaranteed_leaf_depth, 123);
        let b = BasecaseGapAudit::new(10_000_000_000, 64, 64).unwrap();
        assert_eq!(b.first_uncovered_active_depth, Some(1));
        assert_eq!(b.optimistic_prefix_stages, 1);
        assert_eq!(b.hypothetical_guaranteed_leaf_depth, 8);
    }

    #[test]
    fn no_small_leaf_budget_closes_gap_even_at_u128_limit() {
        let r64 = BasecaseGapAudit::new(u128::MAX, 64, 128).unwrap();
        assert_eq!(r64.first_uncovered_active_depth, Some(4));
        assert_eq!(r64.hypothetical_guaranteed_leaf_depth, 36);
        assert_eq!(r64.optimistic_prefix_stages, 4);
        let r7 = BasecaseGapAudit::new(u128::MAX, 7, 128).unwrap();
        assert_eq!(r7.first_uncovered_active_depth, Some(8));
        assert_eq!(r7.hypothetical_guaranteed_leaf_depth, 544);
        assert_eq!(r7.optimistic_prefix_stages, 8);
        assert!(r7.stages.len() <= MAX_DISPLAYED_STAGES);
        assert_eq!(r7.published_root_width_u, 0);
    }

    #[test]
    fn already_below_budget_does_not_start_recursion() {
        let a = BasecaseGapAudit::new(10_000, 64, 10_000).unwrap();
        assert_eq!(a.hypothetical_guaranteed_leaf_depth, 0);
        assert_eq!(a.first_uncovered_active_depth, None);
        assert_eq!(a.optimistic_prefix_stages, 0);
        assert!(a.stages.is_empty());
        assert!(BasecaseGapAudit::new(1, 64, 10).is_err());
        assert!(BasecaseGapAudit::new(10, 6, 8).is_err());
        assert!(BasecaseGapAudit::new(10, 64, 0).is_err());
    }
}
