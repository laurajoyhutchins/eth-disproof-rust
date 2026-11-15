//! Exact arithmetic for necessary root packing inequalities in the
//! appendix's tensor recursion, *not* a complete parameter admission proof.
//!
//! The root is taken to have M = s edges. The source's maximum-degree
//! envelope is Delta = ceil(s^(9/10)). Under that envelope and any u >= 1,
//! a = 2u >= 2, D_arr = r^(2a) >= r^4, so the first packing inequality gives
//! s >= 2*r^8*Delta. For 1 <= s <= u128::MAX, s^(1/10) < 2^13,
//! hence Delta >= s/2^13. When r >= 3, 2*r^8 >= 13122 > 8192,
//! a contradiction. This argument does NOT claim a lower bound on all
//! alternative packing algorithms or on instance-specific small degrees.
//!
//! Separate exact checks below allow a caller to test a *hypothetical*
//! improved degree invariant, without claiming that it is proved, that the
//! source's u >= lambda^(4/5) condition holds, or that counting runs.

use crate::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RootPackingAudit {
    /// Root tensor-network edges, M = s.
    pub edges: u128,
    pub lambda: u32,
    pub groups: u32,
    pub u: u32,
    /// Proposed upper bound on *all* vertex degrees, not yet certified.
    pub degree_cap: u128,
    pub a: Option<u32>,
    pub slots_l: Option<u128>,
    pub label_classes_d: Option<u128>,
    /// 2 * D_arr^2 * degree_cap.
    pub required_edges_collision: Option<u128>,
    /// L * D_arr.
    pub required_edges_slots: Option<u128>,
    /// 2 * L.
    pub required_new_degree: Option<u128>,
}

impl RootPackingAudit {
    pub fn new(edges: u128, groups: u32, u: u32, degree_cap: u128) -> Result<Self, Error> {
        if edges == 0 || groups < 2 || u == 0 || degree_cap == 0 {
            return Err(Error::Invalid(
                "root packing requires positive edges, groups >= 2, u >= 1, degree cap >= 1"
                    .into(),
            ));
        }
        let lambda = u128::BITS - (edges - 1).leading_zeros();
        let a = u.checked_mul(2);
        let slots_l = a.and_then(|exponent| 1u128.checked_shl(exponent));
        let label_classes_d = a
            .and_then(|exponent| exponent.checked_mul(2))
            .and_then(|exponent| u128::from(groups).checked_pow(exponent));
        let required_edges_collision = label_classes_d
            .and_then(|d| d.checked_mul(d))
            .and_then(|d_squared| d_squared.checked_mul(degree_cap))
            .and_then(|v| v.checked_mul(2));
        let required_edges_slots = slots_l
            .zip(label_classes_d)
            .and_then(|(l, d)| l.checked_mul(d));
        let required_new_degree = slots_l.and_then(|l| l.checked_mul(2));
        Ok(Self {
            edges,
            lambda,
            groups,
            u,
            degree_cap,
            a,
            slots_l,
            label_classes_d,
            required_edges_collision,
            required_edges_slots,
            required_new_degree,
        })
    }

    /// All three explicit inequalities of the packing lemma, evaluated
    /// exactly. None of their proofs transfers a proposed degree invariant.
    pub fn packet_inequalities_hold(&self) -> bool {
        self.required_edges_collision
            .is_some_and(|required| required <= self.edges)
            && self.required_edges_slots
                .is_some_and(|required| required <= self.edges)
            && self.required_new_degree
                .is_some_and(|ports| ports <= self.degree_cap)
    }

    /// The source estimates each child's edges by 6 M / r. To retain
    /// the original strict 1/8 factor, one needs r > 48.
    pub fn original_child_shrink_bound_holds(&self) -> bool {
        self.groups > 48
    }

    /// Exact version of u >= lambda^(4/5): u^5 >= lambda^4.
    /// This is a condition in the stated *asymptotic* analysis, not by
    /// itself a necessary condition for the packet algebraic identity.
    pub fn source_asymptotic_u_bound_holds(&self) -> bool {
        if self.u >= 128 {
            return true;
        }
        u128::from(self.u).pow(5) >= u128::from(self.lambda).pow(4)
    }

    /// A proof of impossibility for the *published* degree envelope and
    /// the root M=s, independent of any alternative cap passed to new().
    /// It applies for r >= 3, u >= 1, s within u128. The original r=64
    /// and every r allowing 1/8 child shrink are in this range.
    pub fn published_degree_envelope_obstructed(&self) -> bool {
        self.groups >= 3
    }

    /// This audit establishes arithmetic necessary conditions only.
    /// Replacing the degree envelope, proving a new shrink/precision
    /// schedule, and executing an actual contraction are still required.
    pub fn fully_source_admitted(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_envelope_obstructed_for_every_representable_root() {
        let edges = [1, 2, 3, 1_000_000, 1 << 52, 1 << 100, u128::MAX];
        for edges in edges {
            for groups in [3, 8, 49, 64] {
                for u in [1, 2, 128, u32::MAX] {
                    let candidate = RootPackingAudit::new(edges, groups, u, 8).unwrap();
                    assert!(candidate.published_degree_envelope_obstructed());
                    assert!(!candidate.fully_source_admitted());
                }
            }
        }
    }

    #[test]
    fn explicit_degree_cap_can_pass_packing_without_source_proof() {
        // 2 * (64^4)^2 * 8 = 2^52; L=4, D_arr=2^24.
        let audit = RootPackingAudit::new(1 << 52, 64, 1, 8).unwrap();
        assert_eq!(audit.lambda, 52);
        assert_eq!(audit.a, Some(2));
        assert_eq!(audit.slots_l, Some(4));
        assert_eq!(audit.label_classes_d, Some(1 << 24));
        assert_eq!(audit.required_edges_collision, Some(1 << 52));
        assert_eq!(audit.required_edges_slots, Some(1 << 26));
        assert_eq!(audit.required_new_degree, Some(8));
        assert!(audit.packet_inequalities_hold());
        assert!(audit.original_child_shrink_bound_holds());
        assert!(!audit.source_asymptotic_u_bound_holds());
        assert!(audit.published_degree_envelope_obstructed());
        assert!(!audit.fully_source_admitted());
        assert!(!RootPackingAudit::new((1 << 52) - 1, 64, 1, 8)
            .unwrap()
            .packet_inequalities_hold());
    }

    #[test]
    fn smaller_group_count_trades_packing_for_shrinkage() {
        // Here the original degree envelope is exactly 2^90.
        let audit = RootPackingAudit::new(1 << 100, 2, 1, 1 << 90).unwrap();
        assert!(audit.packet_inequalities_hold());
        assert!(!audit.original_child_shrink_bound_holds());
        assert!(!audit.published_degree_envelope_obstructed());
        assert!(!audit.fully_source_admitted());
    }

    #[test]
    fn overflow_and_invalid_inputs_fail_closed() {
        for args in [(0, 64, 1, 8), (1, 1, 1, 8), (1, 64, 0, 8), (1, 64, 1, 0)] {
            assert!(RootPackingAudit::new(args.0, args.1, args.2, args.3).is_err());
        }
        let huge = RootPackingAudit::new(u128::MAX, 64, u32::MAX, 8).unwrap();
        assert_eq!(huge.slots_l, None);
        assert_eq!(huge.label_classes_d, None);
        assert!(!huge.packet_inequalities_hold());
        assert!(huge.source_asymptotic_u_bound_holds());
        assert!(!huge.fully_source_admitted());
    }

    #[test]
    fn exact_u_power_boundary() {
        let small = RootPackingAudit::new(1 << 20, 64, 10, 8).unwrap();
        let large = RootPackingAudit::new(1 << 20, 64, 11, 8).unwrap();
        assert!(!small.source_asymptotic_u_bound_holds());
        assert!(large.source_asymptotic_u_bound_holds());
    }
}
