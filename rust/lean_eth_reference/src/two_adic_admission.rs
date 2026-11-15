//! Necessary-conditions audit for the *appendix* two-adic tensor recursion.
//!
//! This is distinct from the SqrtLogSpace BitProgram runtime. It is neither
//! a tensor contraction implementation nor a sufficient admissibility test.
//! The paper's fixed root schedule uses u_0 = floor(lambda / 2^17).
//! For every positive edge count representable in u128, lambda <= 128,
//! so u_0 = 0 and the active recursive root is impossible.
//!
//! Refuse rather than silently running an exponential direct leaf and
//! labelling it the proposed subexponential algorithm.

use crate::Error;

/// Denominator of the fixed epsilon = 2^(-17) used at the root.
pub const ROOT_DENOMINATOR: u32 = 1 << 17;

/// Necessary lower bound on lambda from
/// floor(lambda / 2^17) >= lambda^(4/5):
/// lambda / 2^17 >= lambda^(4/5) -> lambda >= 2^85.
/// This is NOT a sufficient bound for packing or the recursion.
pub const NECESSARY_ROOT_LAMBDA: u128 = 1u128 << 85;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScheduleAudit {
    /// Edges in the *encoded tensor network*, not CNF variables or clauses.
    pub edges: u128,
    pub lambda: u32,
    pub root_u: u32,
    /// The paper's field degree e = 4 lambda. No field is constructed.
    pub extension_degree: u32,
    /// The paper's direct-leaf edge count H; None if lambda = 0.
    pub leaf_threshold: Option<u128>,
}

impl ScheduleAudit {
    pub fn new(edges: u128) -> Result<Self, Error> {
        if edges == 0 {
            return Err(Error::Invalid(
                "the appendix schedule requires a positive tensor edge count".into(),
            ));
        }
        // ceil(log2 edges), exact even at u128::MAX.
        let lambda = u128::BITS - (edges - 1).leading_zeros();
        let root_u = lambda / ROOT_DENOMINATOR;
        let root_sqrt = integer_sqrt(lambda);
        let leaf_threshold = if root_sqrt == 0 {
            None
        } else {
            let divisor = u128::from(root_sqrt);
            Some(edges / divisor + u128::from(!edges.is_multiple_of(divisor)))
        };
        Ok(Self {
            edges,
            lambda,
            root_u,
            extension_degree: 4 * lambda,
            leaf_threshold,
        })
    }

    /// These are the only possible outcomes for a u128 edge count.
    /// No result may be interpreted as permission to start the recursion.
    pub fn refusal_reason(&self) -> &'static str {
        if self.lambda == 0 {
            "lambda_zero"
        } else {
            // lambda <= 128 < 131072 for all u128 edge counts.
            debug_assert_eq!(self.root_u, 0);
            "root_packet_width_zero"
        }
    }

    /// Explicitly false for every u128 edge count under the fixed schedule.
    pub fn permits_active_recursion(&self) -> bool {
        false
    }
}

fn integer_sqrt(n: u32) -> u32 {
    // lambda <= 128. No floating-point rounding at perfect squares.
    let mut root = 0;
    while (root + 1) * (root + 1) <= n {
        root += 1;
    }
    root
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn million_edge_audit_matches_published_schedule() {
        let report = ScheduleAudit::new(1_000_000).unwrap();
        assert_eq!(report.lambda, 20);
        assert_eq!(report.root_u, 0);
        assert_eq!(report.extension_degree, 80);
        assert_eq!(report.leaf_threshold, Some(250_000));
        assert_eq!(report.refusal_reason(), "root_packet_width_zero");
        assert!(!report.permits_active_recursion());
    }

    #[test]
    fn boundary_inputs_refuse_without_overflow() {
        assert!(ScheduleAudit::new(0).is_err());
        let one = ScheduleAudit::new(1).unwrap();
        assert_eq!(one.lambda, 0);
        assert_eq!(one.leaf_threshold, None);
        assert_eq!(one.refusal_reason(), "lambda_zero");

        let max = ScheduleAudit::new(u128::MAX).unwrap();
        assert_eq!(max.lambda, 128);
        assert_eq!(max.root_u, 0);
        assert_eq!(max.extension_degree, 512);
        assert!(!max.permits_active_recursion());
        assert_eq!(NECESSARY_ROOT_LAMBDA, 1u128 << 85);
    }

    #[test]
    fn log_and_sqrt_boundaries_are_exact() {
        for exponent in 1..=127 {
            let power = 1u128 << exponent;
            let here = ScheduleAudit::new(power).unwrap();
            let after = ScheduleAudit::new(power + 1).unwrap();
            assert_eq!(here.lambda, exponent);
            assert_eq!(after.lambda, exponent + 1);
            assert_eq!(here.root_u, 0);
            assert_eq!(after.root_u, 0);
            assert!(!here.permits_active_recursion());
        }
        assert_eq!(ScheduleAudit::new(15).unwrap().leaf_threshold, Some(8));
        assert_eq!(ScheduleAudit::new(16).unwrap().leaf_threshold, Some(8));
        assert_eq!(ScheduleAudit::new(17).unwrap().leaf_threshold, Some(9));
        assert_eq!(ScheduleAudit::new(257).unwrap().leaf_threshold, Some(86));
    }
}
