//! Exact multi-level *necessary* arithmetic audit for the appendix's
//! tensor contraction. It does not construct tensor entries, run a count,
//! or certify a replacement recursive schedule.
//!
//! Root s has lambda=ceil(log2 s), H=ceil(s/floor(sqrt(lambda))).
//! A child produced using the matching-potential packing lemma has
//! at most 6*M/r edges. This integer upper bound is iterated exactly.
//! If its maximum is <= H, that depth is GUARANTEED a direct leaf.
//!
//! For an explicit hypothetical positive-width sequence u_0,u_1,...,
//! a_d=2*sum_{j<=d}u_j, L_d=2^a_d, D_d=r^(2a_d), and the
//! matching-potential sufficient condition is
//! M_d >= D_d*((2*Delta-1)*ceil(log2(D_d))+L_d)
//! with Delta>=2L_d. Checking it on an upper bound for M_d
//! can only disprove feasibility, never prove a real child exists
//! or that its graph meets the degree bound.
//!
//! The fixed published schedule gives u_0=0 for every u128 edge count;
//! hypothetical nonzero widths have no Lean proof, precision transfer,
//! or worst-case cost bound. No exponential leaf enumeration is performed.

use crate::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DepthGate {
    pub depth: usize,
    pub width_u: u32,
    pub source_fixed_width_u: u32,
    pub cumulative_a: Option<u32>,
    pub slots_l: Option<u128>,
    pub label_classes_d: Option<u128>,
    /// Largest possible child edge count from the source 6M/r bound.
    pub maximum_possible_edges: u128,
    /// The conservative matching-potential edge threshold for one call,
    /// using the caller's *unproved* uniform maximum-degree cap.
    pub matching_required_edges: Option<u128>,
    /// Delta >= 2L is a source packet-vertex degree requirement.
    pub degree_cap_sufficient_for_packet_vertices: bool,
    pub potentially_active: bool,
    pub matching_arithmetic_possible: bool,
    pub reason: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DepthAudit {
    pub root_edges: u128,
    pub lambda: u32,
    pub root_leaf_threshold: u128,
    pub groups: u32,
    pub proposed_maximum_degree: u128,
    pub stages: Vec<DepthGate>,
}

fn capacity(message: &'static str) -> Error {
    Error::Capacity(message.into())
}

/// Exact floor(6*m/r), without an overflowing 6*m intermediate.
/// For r>=7 this is a genuine decreasing upper bound on child edges.
pub fn child_upper_edges(m: u128, groups: u32) -> Result<u128, Error> {
    if groups < 7 {
        return Err(Error::Invalid(
            "groups >= 7 required for the source 6M/r child shrink".into(),
        ));
    }
    let r = u128::from(groups);
    let high = (m / r).checked_mul(6).ok_or_else(|| capacity("child edge bound overflow"))?;
    let low = ((m % r) * 6) / r;
    high.checked_add(low)
        .ok_or_else(|| capacity("child edge bound overflow"))
}

fn sqrt_floor(n: u32) -> u32 {
    let mut x = 0;
    while (x + 1) * (x + 1) <= n {
        x += 1;
    }
    x
}

fn ceil_div(n: u128, denominator: u128) -> u128 {
    n / denominator + u128::from(!n.is_multiple_of(denominator))
}

/// Checked exact threshold, with None interpreted as a refusal
/// (the required value is outside the supported 128-bit range).
pub fn matching_threshold(groups: u32, a: u32, degree_cap: u128) -> Option<u128> {
    let l = 1u128.checked_shl(a)?;
    let exponent = a.checked_mul(2)?;
    let d = u128::from(groups).checked_pow(exponent)?;
    let log_d = u128::from(u128::BITS - (d - 1).leading_zeros());
    let k = degree_cap.checked_mul(2)?.checked_sub(1)?;
    d.checked_mul(k.checked_mul(log_d)?.checked_add(l)?)
}

impl DepthAudit {
    pub fn new(
        root_edges: u128,
        groups: u32,
        proposed_maximum_degree: u128,
        widths: &[u32],
    ) -> Result<Self, Error> {
        if root_edges < 2 || proposed_maximum_degree == 0 || widths.is_empty() || widths.len() > 32 {
            return Err(Error::Invalid(
                "root edges >=2, positive degree cap and 1..=32 widths required".into(),
            ));
        }
        if groups < 7 {
            return Err(Error::Invalid(
                "groups >=7 required for a provable 6M/r contraction".into(),
            ));
        }
        let lambda = u128::BITS - (root_edges - 1).leading_zeros();
        let root_sqrt = sqrt_floor(lambda);
        let h = ceil_div(root_edges, u128::from(root_sqrt));
        let mut maximum_possible_edges = root_edges;
        let mut sum_widths = Some(0u32);
        let mut stages = Vec::with_capacity(widths.len());

        for (depth, &width_u) in widths.iter().enumerate() {
            if depth != 0 {
                maximum_possible_edges = child_upper_edges(maximum_possible_edges, groups)?;
            }
            sum_widths = sum_widths.and_then(|sum| sum.checked_add(width_u));
            let cumulative_a = sum_widths.and_then(|sum| sum.checked_mul(2));
            let slots_l = cumulative_a.and_then(|a| 1u128.checked_shl(a));
            let label_classes_d = cumulative_a
                .and_then(|a| a.checked_mul(2))
                .and_then(|exponent| u128::from(groups).checked_pow(exponent));
            let matching_required_edges = cumulative_a
                .and_then(|a| matching_threshold(groups, a, proposed_maximum_degree));
            let degree_cap_sufficient_for_packet_vertices = slots_l
                .and_then(|l| l.checked_mul(2))
                .is_some_and(|ports| ports <= proposed_maximum_degree);
            let potentially_active = maximum_possible_edges > h;
            let matching_arithmetic_possible = potentially_active
                && width_u != 0
                && degree_cap_sufficient_for_packet_vertices
                && matching_required_edges
                    .is_some_and(|required| maximum_possible_edges >= required);
            let reason = if !potentially_active {
                "guaranteed_leaf"
            } else if width_u == 0 {
                "zero_packet_width"
            } else if !degree_cap_sufficient_for_packet_vertices {
                "degree_cap_below_packet_ports"
            } else if matching_required_edges.is_none() {
                "packing_threshold_unrepresentable"
            } else if !matching_arithmetic_possible {
                "packing_threshold_exceeds_child_upper_bound"
            } else {
                "arithmetic_candidate_only"
            };
            let source_fixed_width_u = if depth >= 32 {
                0
            } else {
                (lambda / 131_072).checked_shr(depth as u32).unwrap_or(0)
            };
            stages.push(DepthGate {
                depth,
                width_u,
                source_fixed_width_u,
                cumulative_a,
                slots_l,
                label_classes_d,
                maximum_possible_edges,
                matching_required_edges,
                degree_cap_sufficient_for_packet_vertices,
                potentially_active,
                matching_arithmetic_possible,
                reason,
            });
        }
        Ok(Self {
            root_edges,
            lambda,
            root_leaf_threshold: h,
            groups,
            proposed_maximum_degree,
            stages,
        })
    }

    /// A paper-faithful schedule never starts on a u128 root;
    /// hypothetical schedules are not independently admitted.
    pub fn full_recursion_admitted(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_numerical_root_only_at_packing_threshold() {
        let a = DepthAudit::new(6_106_906_624, 64, 8, &[1, 1, 1]).unwrap();
        assert_eq!(a.lambda, 33);
        assert_eq!(a.root_leaf_threshold, 1_221_381_325);
        assert_eq!(a.stages[0].matching_required_edges, Some(6_106_906_624));
        assert_eq!(a.stages[0].reason, "arithmetic_candidate_only");
        assert_eq!(a.stages[1].reason, "guaranteed_leaf");
        assert_eq!(a.stages[2].reason, "guaranteed_leaf");
        assert!(a.stages.iter().all(|stage| stage.source_fixed_width_u == 0));
        assert!(!a.full_recursion_admitted());
    }

    #[test]
    fn first_child_cannot_be_active_at_lambda_at_most_120_for_r64() {
        for s in [2, 1_000_000, 1 << 52, 1 << 100, 1 << 120] {
            let a = DepthAudit::new(s, 64, 32, &[1, 1, 1]).unwrap();
            assert!(a.lambda <= 120);
            assert_eq!(a.stages[1].reason, "guaranteed_leaf");
        }
        let a = DepthAudit::new((1u128 << 120) + 1, 64, 32, &[1, 1, 1]).unwrap();
        assert_eq!(a.lambda, 121);
        assert!(a.stages[1].potentially_active);
        assert_eq!(a.stages[2].reason, "guaranteed_leaf");
    }

    #[test]
    fn u128_ceiling_and_child_rounding_do_not_overflow() {
        let a = DepthAudit::new(u128::MAX, 64, 32, &[1, 1, 1]).unwrap();
        assert_eq!(a.lambda, 128);
        assert_eq!(
            a.root_leaf_threshold,
            30_934_760_629_176_223_951_215_873_402_888_019_224
        );
        assert!(a.stages[0].matching_arithmetic_possible);
        assert!(a.stages[1].matching_arithmetic_possible);
        assert_eq!(a.stages[2].reason, "guaranteed_leaf");
        assert!(a.stages.iter().all(|stage| stage.source_fixed_width_u == 0));
        assert!(!a.full_recursion_admitted());
        assert_eq!(child_upper_edges(u128::MAX, 64).unwrap(), (u128::MAX / 64) * 6 + 5);
    }

    #[test]
    fn width_and_degree_requirements_accumulate_across_depths() {
        let a = DepthAudit::new(u128::MAX, 64, 8, &[1, 1, 1]).unwrap();
        assert_eq!(a.stages[0].cumulative_a, Some(2));
        assert_eq!(a.stages[1].cumulative_a, Some(4));
        assert_eq!(a.stages[1].slots_l, Some(16));
        assert_eq!(a.stages[1].reason, "degree_cap_below_packet_ports");
        assert_eq!(a.stages[2].cumulative_a, Some(6));
        assert_eq!(a.stages[2].reason, "guaranteed_leaf");
    }

    #[test]
    fn impossible_child_matching_threshold_refuses_at_128_bit_capacity() {
        let a = DepthAudit::new(u128::MAX, 64, 256, &[1, 1, 1, 1, 1]).unwrap();
        assert_eq!(a.stages[4].matching_required_edges, None);
        assert_eq!(a.stages[4].reason, "guaranteed_leaf");
        assert!(!a.full_recursion_admitted());
        assert!(DepthAudit::new(0, 64, 8, &[1]).is_err());
        assert!(DepthAudit::new(100, 6, 8, &[1]).is_err());
        assert!(DepthAudit::new(100, 64, 0, &[1]).is_err());
        assert!(DepthAudit::new(100, 64, 8, &[]).is_err());
    }
}
