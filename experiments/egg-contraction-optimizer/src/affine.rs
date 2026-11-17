//! Exact affine (XOR) #SAT boundary elimination over F₂.
//!
//! Internal columns are eliminated by Gaussian row operations, without
//! enumerating assignments. Residual equations constrain only boundary bits.
//! The multiplicity is 2^(internal dimension - rank), retained as BigUint.
//! Neither arbitrary CNF recognition nor general #SAT is implemented.

use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct Equation {
    pub variables: Vec<String>,
    pub rhs: bool,
}

#[derive(Clone, Debug)]
pub struct AffineRegion {
    pub internal: Vec<String>,
    pub boundary: Vec<String>,
    pub equations: Vec<Equation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundaryRow {
    pub boundary_indices: Vec<usize>,
    pub rhs: bool,
}

#[derive(Clone, Debug)]
pub struct AffineInterface {
    pub boundary: Vec<String>,
    pub residual: Vec<BoundaryRow>,
    pub free_internal: usize,
    pub rank: usize,
    pub elimination_xors: usize,
}

impl AffineRegion {
    fn validate(&self) -> Result<(), String> {
        let mut declared = BTreeSet::new();
        for name in self.internal.iter().chain(&self.boundary) {
            if name.is_empty() || !name.chars().next().unwrap().is_ascii_alphabetic()
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                || !declared.insert(name.clone())
            {
                return Err(format!("invalid or duplicated variable {name:?}"));
            }
        }
        for row in &self.equations {
            for var in &row.variables {
                if !declared.contains(var) {
                    return Err(format!("undeclared variable: {var}"));
                }
            }
        }
        Ok(())
    }

    /// Exact elimination; complexity is polynomial in the explicit matrix
    /// dimensions and the number of machine words per bit-vector row.
    /// Does not enumerate the 2^n internal assignments.
    pub fn eliminate(&self) -> Result<AffineInterface, String> {
        self.validate()?;
        let ni = self.internal.len();
        let nb = self.boundary.len();
        let width = ni.checked_add(nb).ok_or("matrix width overflow")?;
        let word_count = width.checked_add(63).ok_or("matrix width overflow")? / 64;
        let total_words = self.equations.len().checked_mul(word_count)
            .ok_or("matrix allocation size overflow")?;
        // A safe explicit memory budget, reported as an incomplete refusal.
        if total_words > 2_000_000 {
            return Err("affine row storage budget exceeded".into());
        }
        let mut names = BTreeMap::new();
        for (i, name) in self.internal.iter().chain(&self.boundary).enumerate() {
            names.insert(name.clone(), i);
        }
        let mut rows: Vec<(Vec<u64>, bool)> = self.equations.iter().map(|eq| {
            let mut words = vec![0_u64; word_count];
            for name in &eq.variables {
                let col = names[name];
                words[col / 64] ^= 1_u64 << (col % 64);
            }
            (words, eq.rhs)
        }).collect();

        let mut pivot = 0;
        let mut elimination_xors = 0;
        for col in 0..ni {
            let Some(found) = (pivot..rows.len())
                .find(|&r| rows[r].0[col / 64] & (1_u64 << (col % 64)) != 0)
            else { continue; };
            rows.swap(pivot, found);
            let pivot_words = rows[pivot].0.clone();
            let pivot_rhs = rows[pivot].1;
            for r in 0..rows.len() {
                if r == pivot || rows[r].0[col / 64] & (1_u64 << (col % 64)) == 0 {
                    continue;
                }
                for (word, &source) in rows[r].0.iter_mut().zip(&pivot_words) {
                    *word ^= source;
                }
                rows[r].1 ^= pivot_rhs;
                elimination_xors += 1;
            }
            pivot += 1;
        }
        let mut residual = Vec::new();
        for (words, rhs) in rows.into_iter().skip(pivot) {
            if (0..ni).any(|col| words[col / 64] & (1_u64 << (col % 64)) != 0) {
                return Err("internal elimination invariant violated".into());
            }
            let boundary_indices = (0..nb).filter(|&b| {
                let col = ni + b;
                words[col / 64] & (1_u64 << (col % 64)) != 0
            }).collect();
            residual.push(BoundaryRow { boundary_indices, rhs });
        }
        Ok(AffineInterface {
            boundary: self.boundary.clone(),
            residual,
            free_internal: ni - pivot,
            rank: pivot,
            elimination_xors,
        })
    }

    /// Independent brute-force oracle, deliberately bounded to small n.
    /// This function never uses the elimination matrix.
    pub fn direct_count(
        &self,
        boundary: &BTreeMap<String, bool>,
        cap: usize,
    ) -> Result<BigUint, String> {
        self.validate()?;
        let total = 1usize.checked_shl(
            self.internal.len().try_into().map_err(|_| "oracle dimension overflow")?
        ).ok_or("oracle dimension overflow")?;
        if total > cap { return Err("direct-count enumeration budget exceeded".into()); }
        let mut count = BigUint::from(0u8);
        for mask in 0..total {
            let mut vars = boundary.clone();
            for (i, key) in self.internal.iter().enumerate() {
                vars.insert(key.clone(), (mask >> i) & 1 == 1);
            }
            let mut valid = true;
            for equation in &self.equations {
                let mut parity = false;
                for name in &equation.variables {
                    parity ^= *vars.get(name).ok_or_else(|| format!("missing {name}"))?;
                }
                if parity != equation.rhs {
                    valid = false;
                    break;
                }
            }
            if valid { count += 1u8; }
        }
        Ok(count)
    }
}

impl AffineInterface {
    /// Entire exact boundary function; a free internal bit contributes ×2.
    pub fn evaluate(&self, boundary: &BTreeMap<String, bool>) -> Result<BigUint, String> {
        let mut bits = Vec::with_capacity(self.boundary.len());
        for name in &self.boundary {
            bits.push(*boundary.get(name).ok_or_else(|| format!("missing {name}"))?);
        }
        for row in &self.residual {
            let mut parity = false;
            for &index in &row.boundary_indices {
                parity ^= bits[index];
            }
            if parity != row.rhs { return Ok(BigUint::from(0u8)); }
        }
        Ok(BigUint::from(1u8) << self.free_internal)
    }

    /// Exact finite-sum composition of independent interiors with a shared
    /// boundary; the boundary is *not* summed out here.
    pub fn compose_at(
        &self, other: &AffineInterface, boundary: &BTreeMap<String, bool>,
    ) -> Result<BigUint, String> {
        if self.boundary != other.boundary {
            return Err("incompatible ordered boundary interfaces".into());
        }
        Ok(self.evaluate(boundary)? * other.evaluate(boundary)?)
    }

    /// Lower the residual parity constraints into exact integer polynomial
    /// indicators on Boolean boundary bits. The output is only for bounded
    /// small interfaces: textual tree expansion may be exponential, even
    /// though the affine-interface representation and evaluator are compact.
    pub fn lower_polynomial(&self, limit: usize) -> Result<String, String> {
        fn xor(a: &str, b: &str) -> String {
            format!("(+ (+ {a} {b}) (* -2 (* {a} {b})))")
        }
        fn checked(next: String, max: usize) -> Result<String, String> {
            if next.len() > max { Err("polynomial text budget exceeded".into()) }
            else { Ok(next) }
        }
        let mut result = (BigUint::from(1u8) << self.free_internal).to_string();
        for row in &self.residual {
            let mut parity = "0".to_string();
            for &index in &row.boundary_indices {
                parity = checked(xor(&parity, &self.boundary[index]), limit)?;
            }
            let factor = if row.rhs {
                parity
            } else {
                checked(format!("(+ 1 (* -1 {parity}))"), limit)?
            };
            result = checked(format!("(* {result} {factor})"), limit)?;
        }
        Ok(result)
    }
}

/// A compact 2-internal-variable affine region with a nontrivial
/// boundary consistency condition: u⊕v=b, u⊕v=c.
pub fn two_equations(first: &str, second: &str) -> AffineRegion {
    AffineRegion {
        internal: vec!["u".into(), "v".into()],
        boundary: vec!["b".into(), "c".into(), "d".into()],
        equations: [first, second].into_iter().map(|name| Equation {
            variables: vec!["u".into(), "v".into(), name.into()],
            rhs: false,
        }).collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assign(mask: usize) -> BTreeMap<String, bool> {
        ["b", "c", "d"].into_iter().enumerate()
            .map(|(i, s)| (s.into(), mask & (1 << i) != 0))
            .collect()
    }

    #[test]
    fn compact_consistency_is_exact_at_every_boundary_context() {
        let region = two_equations("b", "c");
        let iface = region.eliminate().unwrap();
        assert_eq!(iface.rank, 1);
        assert_eq!(iface.free_internal, 1);
        assert_eq!(iface.residual.len(), 1);
        for mask in 0..8 {
            let b = assign(mask);
            let count = iface.evaluate(&b).unwrap();
            assert_eq!(count, region.direct_count(&b, 4).unwrap());
            assert_eq!(count, if b["b"] == b["c"] { 2u8.into() } else { 0u8.into() });
        }
    }

    #[test]
    fn composition_with_distinct_boundary_constraints_matches_two_oracles() {
        let a = two_equations("b", "c");
        let b = two_equations("b", "d");
        let ia = a.eliminate().unwrap();
        let ib = b.eliminate().unwrap();
        for mask in 0..8 {
            let boundary = assign(mask);
            assert_eq!(
                ia.compose_at(&ib, &boundary).unwrap(),
                a.direct_count(&boundary, 4).unwrap()
                    * b.direct_count(&boundary, 4).unwrap()
            );
        }
    }

    #[test]
    fn large_free_dimension_does_not_enumerate_two_to_the_n() {
        let internal = (0..128).map(|i| format!("u{i}")).collect::<Vec<_>>();
        let all = internal.iter().cloned().chain(["b".to_owned()]).collect();
        let region = AffineRegion {
            internal,
            boundary: vec!["b".into()],
            equations: vec![Equation { variables: all, rhs: false }],
        };
        let iface = region.eliminate().unwrap();
        assert_eq!(iface.rank, 1);
        assert_eq!(iface.free_internal, 127);
        for bit in [false, true] {
            let b = BTreeMap::from([("b".to_string(), bit)]);
            assert_eq!(iface.evaluate(&b).unwrap(), BigUint::from(1u8) << 127);
        }
        assert!(region.direct_count(&BTreeMap::new(), 4).is_err());
    }

    #[test]
    fn inconsistent_empty_residual_is_zero_and_unused_variables_count() {
        let region = AffineRegion {
            internal: vec!["u".into(), "v".into()],
            boundary: vec!["b".into()],
            equations: vec![Equation { variables: vec![], rhs: true }],
        };
        let iface = region.eliminate().unwrap();
        assert_eq!(iface.evaluate(&BTreeMap::from([("b".to_string(), false)])).unwrap(),
            BigUint::from(0u8));
        let unconstrained = AffineRegion { equations: vec![], ..region };
        assert_eq!(unconstrained.eliminate().unwrap()
            .evaluate(&BTreeMap::from([("b".to_string(), true)])).unwrap(),
            BigUint::from(4u8));
    }

    #[test]
    fn duplicate_variable_in_equation_cancels_over_f2() {
        let region = AffineRegion {
            internal: vec!["u".into()],
            boundary: vec!["b".into()],
            equations: vec![Equation { variables: vec!["u".into(), "u".into(), "b".into()], rhs: false }],
        };
        let iface = region.eliminate().unwrap();
        assert_eq!(iface.evaluate(&BTreeMap::from([("b".to_string(), false)])).unwrap(), 2u8.into());
        assert_eq!(iface.evaluate(&BTreeMap::from([("b".to_string(), true)])).unwrap(), 0u8.into());
    }

    #[test]
    fn lowered_polynomial_matches_boolean_interface_and_direct_oracle() {
        let a = two_equations("b", "c");
        let b = two_equations("b", "d");
        let ia = a.eliminate().unwrap();
        let ib = b.eliminate().unwrap();
        let source = format!("(pair {} {})",
            ia.lower_polynomial(30_000).unwrap(),
            ib.lower_polynomial(30_000).unwrap());
        let report = crate::optimize(&source, 20_000).unwrap();
        for mask in 0..8 {
            let boundary = assign(mask);
            let vars = boundary.iter().map(|(k,v)| (k.clone(), num_bigint::BigInt::from(u8::from(*v)))).collect();
            let expected = [
                num_bigint::BigInt::from(ia.evaluate(&boundary).unwrap()),
                num_bigint::BigInt::from(ib.evaluate(&boundary).unwrap()),
            ];
            assert_eq!(report.baseline.evaluate(&vars).unwrap().outputs, expected);
            assert_eq!(report.optimized.evaluate(&vars).unwrap().outputs, expected);
        }
    }
}
