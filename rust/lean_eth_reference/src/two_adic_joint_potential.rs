//! Checked arithmetic audit for a *new* simultaneous existence theorem
//! for ordered-class concentration and orbit-sparse packet port balancing.
//!
//! For a bipartite multigraph with M real edges and ACTUAL maximum
//! degree delta, independently random vertex labels from [r]^a can
//! be derandomized by ONE combined conditional-expectation potential.
//! Every vertex label simultaneously controls:
//!   X_gamma <= 3M/(2D) + k*ceil(log2(2D)), k=2delta-1,
//!   C_(shore,coordinate,symbol) <= 3M/r,
//! provided M >= 4*r*delta*ceil(log2(4*a*r)).
//!
//! An occupied unordered-coordinate-pair orbit sigma has
//! q_sigma=2^(number of equal coords) slots per orientation class
//! in one packet, so P_sigma=ceil(max_gamma X_gamma/q_sigma).
//! Across ALL orbits, sum_sigma 1/q_sigma=D/L and
//! O=(r(r+1)/2)^a.  Thus
//!   P*L <= (3/2)M + k*D*ceil(log2(2D)) + L*O.
//! The source packet bound P*L<=3M therefore follows when
//!   3M >= 2*(k*D*ceil(log2(2D)) + L*O).
//!
//! The two inequalities and 2L<=degree_cap provide a sufficient
//! all-graphs *structural* theorem, conditional on a PROVED actual
//! degree bound and the modified orbit-sparse packet semantics.
//! This does not verify source nonzero Cauchy deformation, weighted
//! modes, all-depth degree preservation, precision or counting.
//!
//! This module checks only exact INTEGER inequalities. None is used
//! for an unknown or overflowing threshold. It does not label graphs.

use crate::Error;

fn invalid(message: &'static str) -> Error {
    Error::Invalid(message.into())
}

fn ceil_log2(value: u128) -> u32 {
    debug_assert!(value > 0);
    u128::BITS - (value - 1).leading_zeros()
}

fn ceiling_twothirds(value: u128) -> Option<u128> {
    (value / 3).checked_mul(2)?.checked_add(match value % 3 {
        0 => 0,
        1 => 1,
        _ => 2,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointPotentialArithmetic {
    pub root_edges: u128,
    pub groups: u32,
    pub coordinates: u32,
    /// This number MUST be a certified bound for the actual graph.
    pub proposed_actual_maximum_degree: u128,
    /// Must be >= both the actual degree and degree of packet vertices 2L.
    pub proposed_maximum_degree_cap: u128,
    pub labels_per_shore: Option<u128>,
    pub ordered_label_classes_d: Option<u128>,
    pub packet_slots_l: Option<u128>,
    pub all_coordinate_orbits_o: Option<u128>,
    pub greedy_matching_count_bound_k: Option<u128>,
    pub pair_log_ceiling: Option<u32>,
    pub port_log_ceiling: Option<u32>,
    /// Checked sufficient thresholds for the new combined potential.
    /// None means exact u128 arithmetic was not representable; NEVER
    /// infer impossibility of a graph from a None.
    pub minimum_edges_for_packet_cap: Option<u128>,
    pub minimum_edges_for_port_cap: Option<u128>,
    pub minimum_edges_for_both: Option<u128>,
    pub degree_cap_covers_source_packets: bool,
    pub source_packet_arithmetic_possible: bool,
    pub source_port_arithmetic_possible: bool,
    pub simultaneous_sufficient_arithmetic: bool,
}

impl JointPotentialArithmetic {
    pub fn new(
        root_edges: u128,
        groups: u32,
        coordinates: u32,
        proposed_actual_maximum_degree: u128,
        proposed_maximum_degree_cap: u128,
    ) -> Result<Self, Error> {
        if root_edges == 0
            || groups < 2
            || coordinates == 0
            || proposed_actual_maximum_degree == 0
            || proposed_actual_maximum_degree > root_edges
            || proposed_maximum_degree_cap < proposed_actual_maximum_degree
        {
            return Err(invalid(
                "M>=1, r>=2, a>=1, 1<=actual degree<=M and degree cap>=actual degree required",
            ));
        }
        let r = u128::from(groups);
        let a = coordinates;
        let degree = proposed_actual_maximum_degree;
        let b = r.checked_pow(a);
        let d = a
            .checked_mul(2)
            .and_then(|exponent| r.checked_pow(exponent));
        let l = 1u128.checked_shl(a);
        let o = r
            .checked_mul(r + 1)
            .map(|pairs| pairs / 2)
            .and_then(|pairs| pairs.checked_pow(a));
        let k = degree.checked_mul(2).and_then(|twice| twice.checked_sub(1));
        let pair_log = d.map(|d| ceil_log2(d) + 1);
        let ports = u128::from(a)
            .checked_mul(4)
            .and_then(|multiple| multiple.checked_mul(r));
        let port_log = ports.map(ceil_log2);

        let packet_threshold = k
            .zip(d)
            .zip(pair_log)
            .zip(l)
            .zip(o)
            .and_then(|((((k, d), log), l), o)| {
                k.checked_mul(d)?
                    .checked_mul(u128::from(log))?
                    .checked_add(l.checked_mul(o)?)
            })
            .and_then(ceiling_twothirds);
        let port_threshold = k
            .and_then(|_| r.checked_mul(4))
            .and_then(|v| v.checked_mul(degree))
            .zip(port_log)
            .and_then(|(v, log)| v.checked_mul(u128::from(log)));

        let degree_cap_covers_source_packets = l
            .and_then(|slots| slots.checked_mul(2))
            .is_some_and(|new_degree| proposed_maximum_degree_cap >= new_degree);
        let packet_possible = packet_threshold.is_some_and(|needed| root_edges >= needed);
        let port_possible = port_threshold.is_some_and(|needed| root_edges >= needed);
        let together = packet_threshold.zip(port_threshold).map(|(x, y)| x.max(y));

        Ok(Self {
            root_edges,
            groups,
            coordinates,
            proposed_actual_maximum_degree,
            proposed_maximum_degree_cap,
            labels_per_shore: b,
            ordered_label_classes_d: d,
            packet_slots_l: l,
            all_coordinate_orbits_o: o,
            greedy_matching_count_bound_k: k,
            pair_log_ceiling: pair_log,
            port_log_ceiling: port_log,
            minimum_edges_for_packet_cap: packet_threshold,
            minimum_edges_for_port_cap: port_threshold,
            minimum_edges_for_both: together,
            degree_cap_covers_source_packets,
            source_packet_arithmetic_possible: packet_possible,
            source_port_arithmetic_possible: port_possible,
            simultaneous_sufficient_arithmetic: packet_possible
                && port_possible
                && degree_cap_covers_source_packets,
        })
    }

    /// No source recursion or complete counting program is admitted by
    /// this arithmetic existence theorem.
    pub fn source_recursion_admitted(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_r64_beats_prior_concentration_bound_conditionally() {
        let audit = JointPotentialArithmetic::new(4_205_841_067, 64, 2, 8, 8).unwrap();
        assert_eq!(audit.labels_per_shore, Some(4096));
        assert_eq!(audit.ordered_label_classes_d, Some(16_777_216));
        assert_eq!(audit.all_coordinate_orbits_o, Some(4_326_400));
        assert_eq!(audit.packet_slots_l, Some(4));
        assert_eq!(audit.greedy_matching_count_bound_k, Some(15));
        assert_eq!(audit.pair_log_ceiling, Some(25));
        assert_eq!(audit.port_log_ceiling, Some(9));
        assert_eq!(audit.minimum_edges_for_packet_cap, Some(4_205_841_067));
        assert_eq!(audit.minimum_edges_for_port_cap, Some(18_432));
        assert!(audit.simultaneous_sufficient_arithmetic);
        assert!(!audit.source_recursion_admitted());
        let below = JointPotentialArithmetic::new(4_205_841_066, 64, 2, 8, 8).unwrap();
        assert!(!below.simultaneous_sufficient_arithmetic);
        assert!(!below.source_packet_arithmetic_possible);
        assert!(below.source_port_arithmetic_possible);
    }

    #[test]
    fn r7_threshold_and_source_degree_requirement_are_independent() {
        let a = JointPotentialArithmetic::new(314_221, 7, 2, 8, 8).unwrap();
        assert_eq!(a.ordered_label_classes_d, Some(2401));
        assert_eq!(a.minimum_edges_for_packet_cap, Some(314_221));
        assert_eq!(a.minimum_edges_for_port_cap, Some(1344));
        assert!(a.degree_cap_covers_source_packets);
        assert!(a.simultaneous_sufficient_arithmetic);
        let weak_cap = JointPotentialArithmetic::new(314_221, 7, 2, 8, 8).unwrap();
        assert!(weak_cap.degree_cap_covers_source_packets);
        let cap_fails = JointPotentialArithmetic::new(314_221, 7, 3, 8, 8).unwrap();
        assert!(!cap_fails.degree_cap_covers_source_packets);
        assert!(!cap_fails.simultaneous_sufficient_arithmetic);
    }

    #[test]
    fn small_base_case_has_distinct_port_and_packet_thresholds() {
        let a = JointPotentialArithmetic::new(24, 2, 1, 1, 2).unwrap();
        assert_eq!(a.minimum_edges_for_packet_cap, Some(12));
        assert_eq!(a.minimum_edges_for_port_cap, Some(24));
        assert!(a.simultaneous_sufficient_arithmetic);
        let b = JointPotentialArithmetic::new(78, 2, 2, 1, 8).unwrap();
        assert_eq!(b.minimum_edges_for_packet_cap, Some(78));
        assert_eq!(b.minimum_edges_for_port_cap, Some(32));
        assert!(b.simultaneous_sufficient_arithmetic);
    }

    #[test]
    fn checked_overflow_is_not_misreported_as_impossibility() {
        let a = JointPotentialArithmetic::new(u128::MAX, 64, 16, 8, u128::MAX).unwrap();
        assert!(a.minimum_edges_for_packet_cap.is_none());
        assert!(!a.simultaneous_sufficient_arithmetic);
        assert!(!a.source_recursion_admitted());
        assert!(JointPotentialArithmetic::new(0, 64, 2, 8, 8).is_err());
        assert!(JointPotentialArithmetic::new(10, 1, 2, 8, 8).is_err());
        assert!(JointPotentialArithmetic::new(10, 64, 0, 8, 8).is_err());
        assert!(JointPotentialArithmetic::new(10, 64, 2, 11, 11).is_err());
        assert!(JointPotentialArithmetic::new(10, 64, 2, 8, 7).is_err());
    }
}
