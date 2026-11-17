//! Bounded equality saturation for a two-output integer-polynomial DAG.
//! egg supplies candidates; the independently written canonical polynomial
//! normalizer checks each accepted improvement. This is NOT a Lean proof.

use egg::{define_language, Id};

define_language! {
    pub enum Arithmetic {
        Number(i64),
        Variable(egg::Symbol),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "pair" = Pair([Id; 2]),
    }
}

mod arith;
mod search;

pub use arith::{exact_polynomial_equivalent, Evaluation, Plan};
pub use search::{optimize, Report};

#[cfg(test)]
mod tests {
    use super::*;
    use egg::RecExpr;
    use num_bigint::BigInt;
    use std::collections::BTreeMap;

    #[test]
    fn shared_subexpression_beats_individual_tree_cost() {
        // Each output has two additions. The baseline shares none (4).
        // Reassociate output 1 to reuse (+ a b) in output 2 (3).
        let report = optimize("(pair (+ a (+ b c)) (+ (+ a b) d))", 100_000).unwrap();
        assert_eq!(report.baseline.operation_count(), 4);
        assert_eq!(report.optimized.operation_count(), 3);
        assert!(exact_polynomial_equivalent(&report.baseline, &report.optimized).unwrap());
    }

    #[test]
    fn factoring_can_share_an_entire_output() {
        let report = optimize("(pair (+ (* a b) (* a c)) (* a (+ b c)))", 100_000).unwrap();
        assert_eq!(report.baseline.operation_count(), 5);
        assert_eq!(report.optimized.operation_count(), 2);
        assert!(exact_polynomial_equivalent(&report.baseline, &report.optimized).unwrap());
    }

    #[test]
    fn independent_oracle_rejects_wrong_arithmetic() {
        let a: RecExpr<Arithmetic> = "(pair (+ a b) 0)".parse().unwrap();
        let b: RecExpr<Arithmetic> = "(pair (* a b) 0)".parse().unwrap();
        assert!(!exact_polynomial_equivalent(
            &Plan::from_expr(&a).unwrap(),
            &Plan::from_expr(&b).unwrap()
        ).unwrap());
    }

    #[test]
    fn zero_budget_is_explicitly_incomplete() {
        let report = optimize("(pair (+ a (+ b c)) (+ (+ a b) d))", 0).unwrap();
        assert!(!report.complete);
        assert_eq!(report.search_states, 0);
        assert_eq!(report.baseline.operation_count(), report.optimized.operation_count());
    }

    #[test]
    fn huge_integer_evaluation_is_exact() {
        let a: RecExpr<Arithmetic> =
            "(pair (* 1000000000 (* 1000000000 1000000000)) 0)".parse().unwrap();
        let value = Plan::from_expr(&a).unwrap().evaluate(&BTreeMap::new()).unwrap();
        assert_eq!(value.outputs[0].to_string(), "1000000000000000000000000000");
    }

    #[test]
    fn both_outputs_agree_on_signed_input_grid() {
        let report = optimize("(pair (+ a (+ b c)) (+ (+ a b) d))", 100_000).unwrap();
        for a in -2..=2 {
            for b in -2..=2 {
                for c in -2..=2 {
                    for d in -2..=2 {
                        let vars = BTreeMap::from([
                            ("a".to_string(), BigInt::from(a)),
                            ("b".to_string(), BigInt::from(b)),
                            ("c".to_string(), BigInt::from(c)),
                            ("d".to_string(), BigInt::from(d)),
                        ]);
                        let original = report.baseline.evaluate(&vars).unwrap();
                        let optimized = report.optimized.evaluate(&vars).unwrap();
                        assert_eq!(original.outputs, optimized.outputs);
                    }
                }
            }
        }
    }
}
