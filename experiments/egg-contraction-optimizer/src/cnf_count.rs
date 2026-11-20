//! A fail-closed, source-derived exact #SAT counter for a strictly recognized
//! affine fragment of DIMACS CNF. Nothing here solves arbitrary CNF.
//!
//! Recognized source clauses, in input order:
//! * an empty clause (contradiction) or a unit clause;
//! * an exact canonical pair encoding XOR of two distinct variables;
//! * an exact canonical four-clause block encoding XOR of three distinct variables.
//!
//! All other clause structures are refused. The source-to-affine recognizer
//! has independent small-CNF truth-table tests, not a Lean refinement proof.

use crate::affine::{AffineRegion, Equation};
use num_bigint::BigUint;
use std::collections::BTreeMap;
use std::time::Instant;

#[derive(Clone, Debug)]
pub struct Limits {
    pub max_input_bytes: usize,
    pub max_variables: usize,
    pub max_clauses: usize,
    pub max_literals: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_input_bytes: 32_000_000,
            max_variables: 100_000,
            max_clauses: 1_000_000,
            max_literals: 4_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Refusal {
    pub code: &'static str,
    pub stage: &'static str,
    pub detail: String,
}

impl Refusal {
    pub fn new(code: &'static str, stage: &'static str, detail: impl Into<String>) -> Self {
        Self { code, stage, detail: detail.into() }
    }

    pub fn to_json(&self) -> String {
        format!(
            r#"{{"status":"refused","code":"{}","stage":"{}","detail":"{}"}}"#,
            self.code, self.stage, escape_json(&self.detail)
        )
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {}: {}", self.code, self.stage, self.detail)
    }
}

impl std::error::Error for Refusal {}

fn escape_json(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

#[derive(Debug)]
pub struct Dimacs {
    pub variable_count: usize,
    pub clauses: Vec<Vec<i64>>,
    pub literal_count: usize,
}

pub fn parse_dimacs(input: &str, limits: &Limits) -> Result<Dimacs, Refusal> {
    if input.len() > limits.max_input_bytes {
        return Err(Refusal::new("resource", "parse", "input byte limit exceeded"));
    }
    let mut declared = None;
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    let mut literal_count = 0usize;
    for (line_num, line) in input.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') { continue; }
        let words = line.split_whitespace().collect::<Vec<_>>();
        if words[0] == "p" {
            if declared.is_some() || !clauses.is_empty() || !current.is_empty() {
                return Err(Refusal::new("input", "parse", "repeated or misplaced DIMACS header"));
            }
            if words.len() != 4 || words[1] != "cnf" {
                return Err(Refusal::new("input", "parse", "expected p cnf VARIABLES CLAUSES"));
            }
            let n = words[2].parse::<usize>()
                .map_err(|_| Refusal::new("input", "parse", "invalid variable count"))?;
            let m = words[3].parse::<usize>()
                .map_err(|_| Refusal::new("input", "parse", "invalid clause count"))?;
            if n > limits.max_variables || m > limits.max_clauses {
                return Err(Refusal::new("resource", "parse", "declared variable or clause limit exceeded"));
            }
            declared = Some((n, m));
            continue;
        }
        let Some((n, m)) = declared else {
            return Err(Refusal::new("input", "parse", "missing DIMACS header before clauses"));
        };
        for word in words {
            if word == "0" {
                if clauses.len() >= m {
                    return Err(Refusal::new("input", "parse", "more clauses than declared"));
                }
                clauses.push(std::mem::take(&mut current));
                continue;
            }
            let literal = word.parse::<i64>().map_err(|_| {
                Refusal::new("input", "parse", format!("invalid literal on line {}", line_num + 1))
            })?;
            if literal == 0 || literal == i64::MIN ||
                (literal.unsigned_abs() as u128) > n as u128
            {
                return Err(Refusal::new("input", "parse", format!("out-of-range literal on line {}", line_num + 1)));
            }
            literal_count = literal_count.checked_add(1)
                .ok_or_else(|| Refusal::new("resource", "parse", "literal count overflow"))?;
            if literal_count > limits.max_literals {
                return Err(Refusal::new("resource", "parse", "literal budget exceeded"));
            }
            current.push(literal);
        }
    }
    let Some((variable_count, expected)) = declared else {
        return Err(Refusal::new("input", "parse", "missing DIMACS header"));
    };
    if !current.is_empty() {
        return Err(Refusal::new("input", "parse", "unterminated clause (missing 0)"));
    }
    if clauses.len() != expected {
        return Err(Refusal::new("input", "parse", "clause count disagrees with header"));
    }
    Ok(Dimacs { variable_count, clauses, literal_count })
}

/// Canonical order is lexicographic Boolean assignments, excluding the
/// parity requested by rhs. Every clause forbids exactly one bad row.
fn canonical_parity_clauses(variables: &[i64], rhs: bool) -> Vec<Vec<i64>> {
    let mut clauses = Vec::new();
    for mask in 0..(1usize << variables.len()) {
        let bad_parity = (mask.count_ones() & 1) != 0;
        if bad_parity == rhs { continue; }
        let clause = variables.iter().enumerate().map(|(i, &v)| {
            if (mask >> (variables.len() - 1 - i)) & 1 != 0 { -v } else { v }
        }).collect();
        clauses.push(clause);
    }
    clauses
}

/// Converts only fully recognized source blocks; no enumeration or general
/// clause relaxation. The entire source must be consumed exactly once.
pub fn recognize_affine(source: &Dimacs) -> Result<AffineRegion, Refusal> {
    let mut equations = Vec::new();
    let mut i = 0usize;
    while i < source.clauses.len() {
        let clause = &source.clauses[i];
        match clause.len() {
            0 => {
                equations.push(Equation { variables: vec![], rhs: true });
                i += 1;
            }
            1 => {
                equations.push(Equation {
                    variables: vec![format!("v{}", clause[0].unsigned_abs())],
                    rhs: clause[0] > 0,
                });
                i += 1;
            }
            width @ (2 | 3) => {
                let size = 1usize << (width - 1);
                let end = i + size;
                if end > source.clauses.len() {
                    return Err(Refusal::new("unsupported", "recognize", "incomplete canonical parity block"));
                }
                let names = clause.iter().map(|x| x.abs()).collect::<Vec<_>>();
                if names.iter().any(|&v| v < 1 || v as usize > source.variable_count) ||
                    names.iter().enumerate().any(|(j, v)| names[..j].contains(v))
                {
                    return Err(Refusal::new("unsupported", "recognize", "parity block needs distinct declared variables"));
                }
                let block = &source.clauses[i..end];
                let rhs = if block == canonical_parity_clauses(&names, false) {
                    false
                } else if block == canonical_parity_clauses(&names, true) {
                    true
                } else {
                    return Err(Refusal::new("unsupported", "recognize",
                        format!("clauses {}..{} are not a canonical parity block", i + 1, end)));
                };
                equations.push(Equation {
                    variables: names.iter().map(|v| format!("v{v}")).collect(),
                    rhs,
                });
                i = end;
            }
            _ => {
                return Err(Refusal::new("unsupported", "recognize",
                    format!("clause {} has unsupported width {}", i + 1, clause.len())));
            }
        }
    }
    Ok(AffineRegion {
        internal: (1..=source.variable_count).map(|v| format!("v{v}")).collect(),
        boundary: Vec::new(),
        equations,
    })
}

#[derive(Debug)]
pub struct Timings {
    pub parse_ns: u128,
    pub recognize_ns: u128,
    pub eliminate_ns: u128,
    pub verify_ns: u128,
    pub reconstruct_ns: u128,
    pub total_ns: u128,
}

#[derive(Debug)]
pub struct Report {
    pub count: BigUint,
    pub variable_count: usize,
    pub clause_count: usize,
    pub literal_count: usize,
    pub equation_count: usize,
    pub rank: usize,
    pub free_variables: usize,
    pub row_xors: usize,
    pub certificate_steps: usize,
    pub residual_rows: usize,
    /// Storage counts, not a proof of bit complexity or peak allocation.
    pub packed_matrix_words: usize,
    pub verifier_boolean_cells: usize,
    /// Linux VmHWM includes the whole process; not a phase attribution.
    pub process_peak_rss_kib: Option<u64>,
    pub timings: Timings,
}

impl Report {
    pub fn to_json(&self) -> String {
        let peak = self.process_peak_rss_kib
            .map(|n| n.to_string()).unwrap_or_else(|| "null".into());
        format!(
            concat!(
                r#"{{"status":"exact","representation":"affine-gf2","verification":"independent-rust-replay","count":"{}","#,
                r#""variables":{},"clauses":{},"literals":{},"equations":{},"rank":{},"free_variables":{},"row_xors":{},"certificate_steps":{},"residual_rows":{},"packed_matrix_words":{},"verifier_boolean_cells":{},"count_bits":{},"process_peak_rss_kib":{},"timing_ns":{{"parse":{},"recognize":{},"eliminate":{},"verify":{},"reconstruct":{},"total":{}}}}}"#
            ),
            self.count, self.variable_count, self.clause_count, self.literal_count,
            self.equation_count, self.rank, self.free_variables, self.row_xors,
            self.certificate_steps, self.residual_rows, self.packed_matrix_words,
            self.verifier_boolean_cells, self.count.bits(), peak,
            self.timings.parse_ns, self.timings.recognize_ns,
            self.timings.eliminate_ns, self.timings.verify_ns,
            self.timings.reconstruct_ns, self.timings.total_ns,
        )
    }
}

fn process_peak_rss_kib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find_map(|line| {
        line.strip_prefix("VmHWM:")?
            .split_whitespace().next()?.parse::<u64>().ok()
    })
}

pub fn count_dimacs(input: &str, limits: &Limits) -> Result<Report, Refusal> {
    let total = Instant::now();
    let start = Instant::now();
    let source = parse_dimacs(input, limits)?;
    let parse_ns = start.elapsed().as_nanos();

    let start = Instant::now();
    let region = recognize_affine(&source)?;
    let recognize_ns = start.elapsed().as_nanos();

    let n = region.internal.len();
    let m = region.equations.len();
    let words = n.checked_add(63).and_then(|v| v.checked_div(64))
        .and_then(|v| v.checked_mul(m))
        .ok_or_else(|| Refusal::new("resource", "account", "packed matrix size overflow"))?;
    let cells = n.checked_add(1).and_then(|v| v.checked_mul(m))
        .ok_or_else(|| Refusal::new("resource", "account", "checker matrix size overflow"))?;

    let start = Instant::now();
    let (interface, certificate) = region.eliminate_with_certificate()
        .map_err(|e| Refusal::new("resource", "eliminate", e))?;
    let eliminate_ns = start.elapsed().as_nanos();

    let start = Instant::now();
    let verified = certificate.verify(&region, &interface)
        .map_err(|e| Refusal::new("verification", "verify", e))?;
    let verify_ns = start.elapsed().as_nanos();

    let start = Instant::now();
    if !interface.boundary.is_empty() || !region.boundary.is_empty() {
        return Err(Refusal::new("verification", "reconstruct", "unexpected exterior boundary"));
    }
    let count = interface.evaluate(&BTreeMap::new())
        .map_err(|e| Refusal::new("verification", "reconstruct", e))?;
    let reconstruct_ns = start.elapsed().as_nanos();

    Ok(Report {
        count,
        variable_count: source.variable_count,
        clause_count: source.clauses.len(),
        literal_count: source.literal_count,
        equation_count: m,
        rank: verified.rank,
        free_variables: verified.free_internal,
        row_xors: interface.elimination_xors,
        certificate_steps: verified.operations_checked,
        residual_rows: verified.residual_rows_checked,
        packed_matrix_words: words,
        verifier_boolean_cells: cells,
        process_peak_rss_kib: process_peak_rss_kib(),
        timings: Timings {
            parse_ns, recognize_ns, eliminate_ns, verify_ns, reconstruct_ns,
            total_ns: total.elapsed().as_nanos(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn oracle(source: &Dimacs) -> BigUint {
        assert!(source.variable_count <= 8);
        let mut answer = BigUint::from(0u8);
        for mask in 0..(1usize << source.variable_count) {
            if source.clauses.iter().all(|clause| clause.iter().any(|&literal| {
                let bit = mask & (1usize << ((literal.unsigned_abs() - 1) as usize)) != 0;
                bit == (literal > 0)
            })) {
                answer += 1u8;
            }
        }
        answer
    }

    fn text_formula(n: usize, clauses: &[Vec<i64>]) -> String {
        let mut out = format!("c independent test\np cnf {n} {}\n", clauses.len());
        for clause in clauses {
            for lit in clause { out.push_str(&format!("{lit} ")); }
            out.push_str("0\n");
        }
        out
    }

    #[test]
    fn empty_units_equalities_and_inequalities() {
        let cases = [
            (3, Vec::<Vec<i64>>::new(), 8u32),
            (3, vec![vec![1]], 4),
            (3, vec![vec![-1]], 4),
            (3, vec![vec![1, -2], vec![-1, 2]], 4),
            (3, vec![vec![1, 2], vec![-1, -2]], 4),
            (0, vec![vec![]], 0),
            (2, vec![vec![1], vec![-1]], 0),
            (0, vec![], 1),
        ];
        for (n, clauses, count) in cases {
            let input = text_formula(n, &clauses);
            let report = count_dimacs(&input, &Limits::default()).unwrap();
            assert_eq!(report.count, BigUint::from(count), "{input}");
            assert_eq!(report.count, oracle(&parse_dimacs(&input, &Limits::default()).unwrap()));
        }
    }

    #[test]
    fn xor3_mixed_and_128_variable_count() {
        let mut clauses = canonical_parity_clauses(&[1, 2, 3], false);
        clauses.extend(canonical_parity_clauses(&[2, 3], true));
        clauses.push(vec![1]);
        let formula = text_formula(4, &clauses);
        let parsed = parse_dimacs(&formula, &Limits::default()).unwrap();
        assert_eq!(count_dimacs(&formula, &Limits::default()).unwrap().count, oracle(&parsed));
        let report = count_dimacs(&text_formula(128, &[vec![1]]), &Limits::default()).unwrap();
        assert_eq!(report.count, BigUint::from(1u8) << 127);
        assert_eq!(report.rank, 1);
        assert_eq!(report.free_variables, 127);
        assert_eq!(report.packed_matrix_words, 2);
        assert_eq!(report.verifier_boolean_cells, 129);
    }

    #[test]
    fn seeded_affine_formulas_match_independent_cnf_oracle() {
        fn draw(s: &mut u64) -> u64 {
            *s ^= *s << 13;
            *s ^= *s >> 7;
            *s ^= *s << 17;
            *s
        }
        for seed in 1..=200u64 {
            let mut s = seed;
            let n = 3 + draw(&mut s) as usize % 4;
            let blocks = (draw(&mut s) % 9) as usize;
            let mut clauses = Vec::new();
            for _ in 0..blocks {
                let width = 1 + draw(&mut s) as usize % 3;
                let start = draw(&mut s) as usize % n;
                let mut vars = Vec::new();
                for i in 0..width { vars.push(1 + ((start + i) % n) as i64); }
                let rhs = draw(&mut s) & 1 != 0;
                if width == 1 {
                    clauses.push(vec![if rhs { vars[0] } else { -vars[0] }]);
                } else {
                    clauses.extend(canonical_parity_clauses(&vars, rhs));
                }
            }
            let formula = text_formula(n, &clauses);
            let parsed = parse_dimacs(&formula, &Limits::default()).unwrap();
            let result = count_dimacs(&formula, &Limits::default()).unwrap();
            assert_eq!(result.count, oracle(&parsed), "seed={seed}");
            assert_eq!(result.variable_count, n);
        }
    }

    #[test]
    fn unsupported_clauses_and_broken_blocks_refuse_without_a_fallback() {
        for clauses in [
            vec![vec![1, 2, 3]],
            vec![vec![1, 2, 3, 4]],
            vec![vec![1, 2], vec![1, 2]],
            vec![vec![1, 2], vec![2, -1]],
            vec![vec![1, 1], vec![-1, -1]],
            vec![vec![1, 2, 3], vec![-1, 2, 3], vec![1, -2, 3], vec![-1, -2, -3]],
        ] {
            let refusal = count_dimacs(&text_formula(4, &clauses), &Limits::default()).unwrap_err();
            assert_eq!(refusal.code, "unsupported");
            assert_eq!(refusal.stage, "recognize");
        }
    }

    #[test]
    fn input_validation_and_limits_are_explicit() {
        for source in [
            "1 0\n", "p cnf 2 1\n1 0\np cnf 2 0\n",
            "p cnf 2 1\n3 0\n", "p cnf 1 2\n1 0\n",
            "p cnf 2 1\n1\n", "p cnf 2 1\n-0 0\n",
            "p cnf 2 1\n1 0 2 0\n",
        ] {
            assert_eq!(count_dimacs(source, &Limits::default()).unwrap_err().code, "input");
        }
        let mut limits = Limits::default();
        limits.max_variables = 1;
        assert_eq!(count_dimacs("p cnf 2 0\n", &limits).unwrap_err().code, "resource");
        limits.max_variables = 10;
        limits.max_input_bytes = 4;
        assert_eq!(count_dimacs("p cnf 2 0\n", &limits).unwrap_err().code, "resource");
    }

    #[test]
    fn receipts_are_structured_without_claiming_proved_complexity() {
        let report = count_dimacs("p cnf 2 1\n1 0\n", &Limits::default()).unwrap();
        let json = report.to_json();
        assert!(json.contains(r#""status":"exact""#));
        assert!(json.contains(r#""count":"2""#));
        assert!(json.contains(r#""certificate_steps":"#));
        assert!(json.contains(r#""timing_ns":"#));
        let refusal = Refusal::new("unsupported", "recognize", "a \"quoted\" path");
        assert!(refusal.to_json().contains(r#"a \"quoted\" path"#));
    }
}
