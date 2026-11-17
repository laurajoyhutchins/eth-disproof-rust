//! Source-derived finite #SAT contraction with an explicit Boolean boundary.
//!
//! This deliberately enumerates internal assignments during compilation.
//! It is a useful correctness and graph-sharing fixture, NOT a faster #SAT
//! algorithm. The independently written oracle evaluates CNF clauses as
//! booleans and never calls the algebraic compiler or the e-graph engine.

use crate::{optimize, Report};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Literal {
    pub name: &'static str,
    pub positive: bool,
}

impl Literal {
    pub const fn positive(name: &'static str) -> Self {
        Self { name, positive: true }
    }

    pub const fn negative(name: &'static str) -> Self {
        Self { name, positive: false }
    }
}

#[derive(Clone, Debug)]
pub struct Region {
    pub internal: Vec<&'static str>,
    pub boundary: Vec<&'static str>,
    // A conjunction of disjunctions. Empty conjunction = true;
    // empty clause = false. Duplicates and tautologies remain legal.
    pub clauses: Vec<Vec<Literal>>,
}

#[derive(Clone, Copy, Debug)]
pub enum Association {
    Left,
    Right,
}

impl Region {
    fn validate(&self) -> Result<(), String> {
        let mut declared = BTreeSet::new();
        for &name in self.internal.iter().chain(&self.boundary) {
            if !valid_symbol(name) {
                return Err(format!("invalid or reserved variable name: {name}"));
            }
            if !declared.insert(name) {
                return Err(format!("duplicate internal/boundary variable: {name}"));
            }
        }
        for clause in &self.clauses {
            for literal in clause {
                if !declared.contains(literal.name) {
                    return Err(format!("undeclared variable: {}", literal.name));
                }
            }
        }
        Ok(())
    }

    fn internal_states(&self, budget: usize) -> Result<usize, String> {
        self.validate()?;
        let count = 1usize
            .checked_shl(self.internal.len().try_into().map_err(|_| "too many internal variables")?)
            .ok_or("internal assignment count exceeds addressable range")?;
        if count > budget {
            return Err(format!("internal enumeration budget exceeded: {count} > {budget}"));
        }
        Ok(count)
    }

    fn compile_clause(&self, clause: &[Literal], mask: usize) -> String {
        let mut remaining = Vec::new();
        for lit in clause {
            if let Some(index) = self.internal.iter().position(|&v| v == lit.name) {
                let bit = self.internal.len() - 1 - index;
                let value = ((mask >> bit) & 1) == 1;
                if value == lit.positive {
                    // This clause is already true under the internal assignment.
                    return "1".to_owned();
                }
                continue;
            }
            let literal = if lit.positive {
                lit.name.to_string()
            } else {
                not_polynomial(lit.name)
            };
            remaining.push(literal);
        }
        match remaining.len() {
            0 => "0".to_owned(),
            1 => remaining.pop().expect("one clause literal"),
            _ => {
                // 1 - Product_i(1 - literal_i), an exact integer polynomial
                // representing Boolean OR on boundary bits.
                let complements = remaining.into_iter().map(|x| not_polynomial(&x));
                format!("(+ 1 (* -1 {}))", multiply(complements))
            }
        }
    }

    fn compile_term(&self, mask: usize) -> String {
        let mut factors = Vec::new();
        for clause in &self.clauses {
            let factor = self.compile_clause(clause, mask);
            if factor == "0" {
                return "0".to_owned();
            }
            if factor != "1" {
                factors.push(factor);
            }
        }
        // All factors true is one, including the empty CNF.
        multiply(factors)
    }

    /// Compute a symbolic boundary polynomial by explicit finite summation
    /// over *all* internal assignments, with only local constant propagation.
    pub fn compile_boundary(
        &self,
        association: Association,
        assignment_budget: usize,
    ) -> Result<String, String> {
        let count = self.internal_states(assignment_budget)?;
        let terms = (0..count)
            .map(|mask| self.compile_term(mask))
            .filter(|term| term != "0")
            .collect();
        Ok(sum(terms, association))
    }

    /// Independent CNF truth-table oracle; this does NOT evaluate the
    /// symbolic expression produced by compile_boundary.
    pub fn direct_count(
        &self,
        boundary_values: &BTreeMap<String, bool>,
        assignment_budget: usize,
    ) -> Result<u64, String> {
        let count = self.internal_states(assignment_budget)?;
        for name in &self.boundary {
            if !boundary_values.contains_key(*name) {
                return Err(format!("missing boundary assignment: {name}"));
            }
        }
        let mut satisfying = 0_u64;
        for mask in 0..count {
            let satisfies = self.clauses.iter().all(|clause| {
                clause.iter().any(|literal| {
                    let value = if let Some(index) =
                        self.internal.iter().position(|&name| name == literal.name)
                    {
                        ((mask >> (self.internal.len() - 1 - index)) & 1) == 1
                    } else {
                        boundary_values[literal.name]
                    };
                    value == literal.positive
                })
            });
            if satisfies {
                satisfying = satisfying.checked_add(1).ok_or("count exceeds u64")?;
            }
        }
        Ok(satisfying)
    }
}

fn valid_symbol(value: &str) -> bool {
    let mut chars = value.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && value != "pair"
}

fn not_polynomial(expr: &str) -> String {
    format!("(+ 1 (* -1 {expr}))")
}

fn multiply(terms: impl IntoIterator<Item = String>) -> String {
    let mut iter = terms.into_iter();
    let Some(mut result) = iter.next() else {
        return "1".to_owned();
    };
    for factor in iter {
        result = format!("(* {result} {factor})");
    }
    result
}

fn sum(mut terms: Vec<String>, association: Association) -> String {
    if terms.is_empty() {
        return "0".to_owned();
    }
    match association {
        Association::Left => {
            let mut out = terms.remove(0);
            for term in terms {
                out = format!("(+ {out} {term})");
            }
            out
        }
        Association::Right => {
            let mut out = terms.pop().expect("nonempty sum");
            while let Some(term) = terms.pop() {
                out = format!("(+ {term} {out})");
            }
            out
        }
    }
}

pub fn compile_pair(
    regions: [&Region; 2],
    association: [Association; 2],
    internal_assignment_budget: usize,
) -> Result<String, String> {
    if regions[0].boundary != regions[1].boundary {
        return Err("the two outputs must declare the same boundary variables".into());
    }
    let left = regions[0].compile_boundary(association[0], internal_assignment_budget)?;
    let right = regions[1].compile_boundary(association[1], internal_assignment_budget)?;
    Ok(format!("(pair {left} {right})"))
}

/// Two actual CNF regions. The third boundary variable is d or e; both
/// use b,c,d,e as the *same* external context, and internal variables u,v.
/// Internal states 00,01,10 contribute b,c,third respectively; 11 is
/// forbidden by (!u OR !v).
pub fn three_branch_region(third: &'static str) -> Region {
    let neg = Literal::negative;
    let pos = Literal::positive;
    Region {
        internal: vec!["u", "v"],
        boundary: vec!["b", "c", "d", "e"],
        clauses: vec![
            vec![neg("u"), neg("v")],
            vec![pos("u"), pos("v"), pos("b")],
            vec![pos("u"), neg("v"), pos("c")],
            vec![neg("u"), pos("v"), pos(third)],
        ],
    }
}

#[derive(Debug)]
pub struct BoundaryReceipt {
    pub boundary_assignments_checked: usize,
    pub internal_assignments_per_context: usize,
    pub baseline_arithmetic_evaluations: usize,
    pub optimized_arithmetic_evaluations: usize,
    pub baseline_operand_byte_proxy: u128,
    pub optimized_operand_byte_proxy: u128,
    pub weighted_outer_context_checked: bool,
}

#[derive(Debug)]
pub struct SatReport {
    pub source_expression: String,
    pub optimization: Report,
    pub boundary: BoundaryReceipt,
}

/// Check every boundary context, including two distinct outer weighted
/// continuations. Counts are independently recomputed from CNF truth.
pub fn optimize_and_verify(
    regions: [&Region; 2],
    association: [Association; 2],
    internal_assignment_budget: usize,
    boundary_assignment_budget: usize,
    extraction_budget: usize,
) -> Result<SatReport, String> {
    let source_expression = compile_pair(regions, association, internal_assignment_budget)?;
    let optimization = optimize(&source_expression, extraction_budget)?;
    let boundary_names = &regions[0].boundary;
    let boundary_count = 1usize
        .checked_shl(boundary_names.len().try_into().map_err(|_| "too many boundary variables")?)
        .ok_or("boundary assignment count exceeds addressable range")?;
    if boundary_count > boundary_assignment_budget {
        return Err(format!("boundary enumeration budget exceeded: {boundary_count} > {boundary_assignment_budget}"));
    }

    let mut weighted_oracle = [BigInt::from(0), BigInt::from(0)];
    let mut weighted_extracted = [BigInt::from(0), BigInt::from(0)];
    let (mut baseline_ops, mut optimized_ops) = (0_usize, 0_usize);
    let (mut baseline_proxy, mut optimized_proxy) = (0_u128, 0_u128);

    for mask in 0..boundary_count {
        let truth: BTreeMap<String, bool> = boundary_names.iter().enumerate()
            .map(|(i, &name)| {
                (name.to_owned(), ((mask >> (boundary_names.len() - 1 - i)) & 1) != 0)
            })
            .collect();
        let bindings: BTreeMap<String, BigInt> = truth.iter()
            .map(|(name, value)| (name.clone(), BigInt::from(u8::from(*value))))
            .collect();
        let expected = [
            BigInt::from(regions[0].direct_count(&truth, internal_assignment_budget)?),
            BigInt::from(regions[1].direct_count(&truth, internal_assignment_budget)?),
        ];
        let baseline = optimization.baseline.evaluate(&bindings)?;
        let extracted = optimization.optimized.evaluate(&bindings)?;
        if baseline.outputs != expected {
            return Err(format!("CNF-to-polynomial compilation mismatch at {truth:?}"));
        }
        if extracted.outputs != expected {
            return Err(format!("optimized boundary function mismatch at {truth:?}"));
        }
        baseline_ops = baseline_ops
            .checked_add(baseline.additions + baseline.multiplications)
            .ok_or("arithmetic operation count overflow")?;
        optimized_ops = optimized_ops
            .checked_add(extracted.additions + extracted.multiplications)
            .ok_or("arithmetic operation count overflow")?;
        baseline_proxy = baseline_proxy
            .checked_add(baseline.operand_byte_work_proxy)
            .ok_or("baseline proxy overflow")?;
        optimized_proxy = optimized_proxy
            .checked_add(extracted.operand_byte_work_proxy)
            .ok_or("optimized proxy overflow")?;

        // Nontrivial signed outer weights model an arbitrary downstream
        // contraction. Pointwise equality implies this identity for any
        // weights, but we independently check these two mixtures as well.
        for i in 0..2 {
            let weight = if (mask + i) % 3 == 0 { -2 } else if (mask + i) % 3 == 1 { 0 } else { 3 };
            weighted_oracle[i] += &expected[i] * BigInt::from(weight);
            weighted_extracted[i] += &extracted.outputs[i] * BigInt::from(weight);
        }
    }
    if weighted_oracle != weighted_extracted {
        return Err("downstream weighted contraction mismatch".into());
    }
    Ok(SatReport {
        source_expression,
        optimization,
        boundary: BoundaryReceipt {
            boundary_assignments_checked: boundary_count,
            internal_assignments_per_context:
                regions[0].internal_states(internal_assignment_budget)?
                + regions[1].internal_states(internal_assignment_budget)?,
            baseline_arithmetic_evaluations: baseline_ops,
            optimized_arithmetic_evaluations: optimized_ops,
            baseline_operand_byte_proxy: baseline_proxy,
            optimized_operand_byte_proxy: optimized_proxy,
            weighted_outer_context_checked: true,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo() -> (Region, Region) {
        (three_branch_region("d"), three_branch_region("e"))
    }

    #[test]
    fn actual_cnf_compiles_to_two_related_boundary_polynomials() {
        let (a, b) = demo();
        let expression = compile_pair([&a, &b], [Association::Right, Association::Left], 4).unwrap();
        assert_eq!(expression, "(pair (+ b (+ c d)) (+ (+ b c) e))");
    }

    #[test]
    fn all_boundary_contexts_match_direct_count_and_share_work() {
        let (a, b) = demo();
        let report = optimize_and_verify(
            [&a, &b], [Association::Right, Association::Left], 4, 16, 100_000
        ).unwrap();
        assert_eq!(report.boundary.boundary_assignments_checked, 16);
        assert_eq!(report.boundary.internal_assignments_per_context, 8);
        assert_eq!(report.optimization.baseline.operation_count(), 4);
        assert_eq!(report.optimization.optimized.operation_count(), 3);
        assert_eq!(report.boundary.baseline_arithmetic_evaluations, 64);
        assert_eq!(report.boundary.optimized_arithmetic_evaluations, 48);
        assert!(report.boundary.weighted_outer_context_checked);
    }

    #[test]
    fn matching_one_boundary_value_is_not_contextual_equivalence() {
        let (a, b) = demo();
        let mut values = BTreeMap::from([
            ("b".to_owned(), false), ("c".to_owned(), false),
            ("d".to_owned(), false), ("e".to_owned(), false),
        ]);
        assert_eq!(a.direct_count(&values, 4).unwrap(), b.direct_count(&values, 4).unwrap());
        values.insert("d".to_owned(), true);
        assert_eq!(a.direct_count(&values, 4).unwrap(), 1);
        assert_eq!(b.direct_count(&values, 4).unwrap(), 0);
    }

    #[test]
    fn budgets_report_refusal_without_partial_truth_table() {
        let (a, b) = demo();
        assert!(compile_pair([&a, &b], [Association::Right, Association::Left], 3)
            .unwrap_err().contains("budget exceeded"));
        assert!(optimize_and_verify([&a, &b], [Association::Right, Association::Left], 4, 15, 100)
            .unwrap_err().contains("budget exceeded"));
    }

    #[test]
    fn contradictory_tautological_and_unused_internal_clauses() {
        let region = Region {
            internal: vec!["u"],
            boundary: vec!["b"],
            clauses: vec![
                vec![Literal::positive("b"), Literal::negative("b")],
                vec![Literal::positive("u"), Literal::negative("u")],
            ],
        };
        let false_boundary = BTreeMap::from([("b".to_owned(), false)]);
        let true_boundary = BTreeMap::from([("b".to_owned(), true)]);
        assert_eq!(region.direct_count(&false_boundary, 2).unwrap(), 2);
        assert_eq!(region.direct_count(&true_boundary, 2).unwrap(), 2);
        let out = optimize_and_verify([&region, &region], [Association::Left, Association::Right], 2, 2, 1_000).unwrap();
        assert_eq!(out.boundary.boundary_assignments_checked, 2);

        let impossible = Region {
            internal: vec!["u"],
            boundary: vec!["b"],
            clauses: vec![
                vec![Literal::positive("u")],
                vec![Literal::negative("u")],
            ],
        };
        assert_eq!(impossible.direct_count(&false_boundary, 2).unwrap(), 0);
        let out = optimize_and_verify([&impossible, &impossible], [Association::Left, Association::Right], 2, 2, 1_000).unwrap();
        assert_eq!(out.optimization.baseline.evaluate(&BTreeMap::from([("b".to_owned(), BigInt::from(1))])).unwrap().outputs[0], BigInt::from(0));
    }

    #[test]
    fn seeded_cnf_families_match_independent_boolean_enumeration() {
        // Deterministic variety: 96 small CNFs, including empty clauses,
        // negative literals, repeated literals, tautologies, and cases with
        // multiple boundary literals. No randomness dependency or snapshots.
        fn draw(state: &mut u64) -> u64 {
            *state ^= *state << 13;
            *state ^= *state >> 7;
            *state ^= *state << 17;
            *state
        }

        let symbols = ["u", "v", "b", "c"];
        for case in 1..=96_u64 {
            let mut state = case;
            let clause_count = (draw(&mut state) % 6) as usize;
            let mut clauses = Vec::new();
            for _ in 0..clause_count {
                let length = (draw(&mut state) % 5) as usize;
                let mut clause = Vec::new();
                for _ in 0..length {
                    let var = symbols[(draw(&mut state) % symbols.len() as u64) as usize];
                    let sign = draw(&mut state) % 2 == 0;
                    clause.push(Literal { name: var, positive: sign });
                }
                clauses.push(clause);
            }
            let region = Region {
                internal: vec!["u", "v"],
                boundary: vec!["b", "c"],
                clauses,
            };
            let polynomial = region.compile_boundary(Association::Left, 4).unwrap();
            let paired: egg::RecExpr<crate::Arithmetic> =
                format!("(pair {polynomial} {polynomial})").parse().unwrap();
            let plan = crate::Plan::from_expr(&paired).unwrap();
            for mask in 0..4_u8 {
                let boundary = BTreeMap::from([
                    ("b".to_owned(), mask & 2 != 0),
                    ("c".to_owned(), mask & 1 != 0),
                ]);
                let integer_bindings = boundary.iter()
                    .map(|(name, bit)| (name.clone(), BigInt::from(u8::from(*bit))))
                    .collect();
                let direct = BigInt::from(region.direct_count(&boundary, 4).unwrap());
                let evaluated = plan.evaluate(&integer_bindings).unwrap();
                assert_eq!(evaluated.outputs, [direct.clone(), direct],
                    "failed CNF case {case}, boundary {boundary:?}");
            }
        }
    }

    #[test]
    fn invalid_or_undeclared_variable_is_refused() {
        let bad = Region {
            internal: vec!["u"],
            boundary: vec!["b"],
            clauses: vec![vec![Literal::positive("not_declared")]],
        };
        assert!(bad.compile_boundary(Association::Left, 2).unwrap_err().contains("undeclared"));
        let duplicate = Region {
            internal: vec!["b"],
            boundary: vec!["b"],
            clauses: vec![],
        };
        assert!(duplicate.compile_boundary(Association::Left, 2).unwrap_err().contains("duplicate"));
    }
}
