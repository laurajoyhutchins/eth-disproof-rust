//! Exact quadratic-sign interfaces over F2, with integer-valued semantics.
//! This Rust research kernel is not yet formally refined against the Lean module.
//! No production operation enumerates Boolean assignments; only tests do.

use std::collections::BTreeSet;

/// Sorted, squarefree variable indices; [] denotes the constant monomial.
pub type Monomial = Vec<usize>;
/// XOR of monomials in algebraic normal form.
pub type Anf = BTreeSet<Monomial>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Equation {
    pub coefficients: Vec<bool>,
    pub rhs: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryError {
    InvalidDimension,
    InvalidMonomial,
    ExponentOverflow,
}

/// A signed power of two never overflows a fixed-width machine integer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignedPower {
    Zero,
    Positive(usize),
    Negative(usize),
}

impl SignedPower {
    #[must_use]
    pub fn to_i128(self) -> Option<i128> {
        match self {
            Self::Zero => Some(0),
            Self::Positive(k) if k < 127 => Some(1_i128 << k),
            Self::Negative(k) if k < 127 => Some(-(1_i128 << k)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticMode {
    variables: usize,
    equations: Vec<Equation>,
    phase: Anf,
    exponent: usize,
    zero: bool,
}

fn toggle(poly: &mut Anf, monomial: Monomial) {
    if !poly.insert(monomial.clone()) {
        poly.remove(&monomial);
    }
}

fn xor_polys(a: &Anf, b: &Anf) -> Anf {
    let mut result = a.clone();
    for term in b {
        toggle(&mut result, term.clone());
    }
    result
}

fn multiply_polys(a: &Anf, b: &Anf) -> Anf {
    let mut result = Anf::new();
    for left in a {
        for right in b {
            let mut term = left.clone();
            term.extend(right);
            term.sort_unstable();
            term.dedup();
            toggle(&mut result, term);
        }
    }
    result
}

fn substitute(poly: &Anf, variable: usize, replacement: &Anf) -> Anf {
    let mut result = Anf::new();
    for term in poly {
        if term.binary_search(&variable).is_ok() {
            let rest = term.iter().copied().filter(|&i| i != variable).collect();
            let mut single = Anf::new();
            single.insert(rest);
            result = xor_polys(&result, &multiply_polys(&single, replacement));
        } else {
            toggle(&mut result, term.clone());
        }
    }
    result
}

fn affine_replacement(eq: &Equation, variable: usize) -> Anf {
    let mut result = Anf::new();
    if eq.rhs {
        result.insert(vec![]);
    }
    for (index, enabled) in eq.coefficients.iter().enumerate() {
        if index != variable && *enabled {
            result.insert(vec![index]);
        }
    }
    result
}

fn xor_equation(target: &mut Equation, source: &Equation) {
    for (x, y) in target.coefficients.iter_mut().zip(&source.coefficients) {
        *x ^= *y;
    }
    target.rhs ^= source.rhs;
}

fn drop_variable(term: &[usize], variable: usize) -> Monomial {
    term.iter()
        .copied()
        .filter(|&i| i != variable)
        .map(|i| if i > variable { i - 1 } else { i })
        .collect()
}

impl QuadraticMode {
    /// Canonicalize constraints by binary RREF and substitute pivot variables
    /// into the quadratic phase, reducing redundant phase syntax.
    pub fn new(
        variables: usize,
        mut equations: Vec<Equation>,
        phase: Anf,
        exponent: usize,
    ) -> Result<Self, BoundaryError> {
        if equations.iter().any(|e| e.coefficients.len() != variables) {
            return Err(BoundaryError::InvalidDimension);
        }
        if phase.iter().any(|term| {
            term.len() > 2
                || term.iter().any(|&i| i >= variables)
                || term.windows(2).any(|w| w[0] >= w[1])
        }) {
            return Err(BoundaryError::InvalidMonomial);
        }

        let mut rank = 0;
        for col in 0..variables {
            if let Some(pivot) = (rank..equations.len()).find(|&i| equations[i].coefficients[col]) {
                equations.swap(rank, pivot);
                let row = equations[rank].clone();
                for (i, eq) in equations.iter_mut().enumerate() {
                    if i != rank && eq.coefficients[col] {
                        xor_equation(eq, &row);
                    }
                }
                rank += 1;
            }
        }
        if equations[rank..].iter().any(|e| e.rhs) {
            return Ok(Self::zero(variables));
        }
        equations.truncate(rank);
        let mut phase = phase;
        for eq in &equations {
            if let Some(pivot) = eq.coefficients.iter().position(|&x| x) {
                phase = substitute(&phase, pivot, &affine_replacement(eq, pivot));
            }
        }
        debug_assert!(phase.iter().all(|term| term.len() <= 2));
        Ok(Self {
            variables,
            equations,
            phase,
            exponent,
            zero: false,
        })
    }

    #[must_use]
    pub fn zero(variables: usize) -> Self {
        Self {
            variables,
            equations: vec![],
            phase: Anf::new(),
            exponent: 0,
            zero: true,
        }
    }

    #[must_use]
    pub fn equations(&self) -> &[Equation] {
        &self.equations
    }

    #[must_use]
    pub fn phase(&self) -> &Anf {
        &self.phase
    }

    pub fn value(&self, assignment: &[bool]) -> Result<SignedPower, BoundaryError> {
        if assignment.len() != self.variables {
            return Err(BoundaryError::InvalidDimension);
        }
        if self.zero
            || self.equations.iter().any(|eq| {
                eq.coefficients
                    .iter()
                    .zip(assignment)
                    .fold(false, |acc, (&c, &b)| acc ^ (c && b))
                    != eq.rhs
            })
        {
            return Ok(SignedPower::Zero);
        }
        let negative = self
            .phase
            .iter()
            .fold(false, |acc, term| acc ^ term.iter().all(|&i| assignment[i]));
        Ok(if negative {
            SignedPower::Negative(self.exponent)
        } else {
            SignedPower::Positive(self.exponent)
        })
    }

    pub fn product(&self, other: &Self) -> Result<Self, BoundaryError> {
        if self.variables != other.variables {
            return Err(BoundaryError::InvalidDimension);
        }
        if self.zero || other.zero {
            return Ok(Self::zero(self.variables));
        }
        let exponent = self
            .exponent
            .checked_add(other.exponent)
            .ok_or(BoundaryError::ExponentOverflow)?;
        let mut equations = self.equations.clone();
        equations.extend(other.equations.iter().cloned());
        Self::new(
            self.variables,
            equations,
            xor_polys(&self.phase, &other.phase),
            exponent,
        )
    }

    /// Sum over one variable. This handles both an affine-constrained pivot
    /// and an unconstrained variable whose mixed phase is affine.
    pub fn eliminate(&self, variable: usize) -> Result<Self, BoundaryError> {
        if variable >= self.variables {
            return Err(BoundaryError::InvalidDimension);
        }
        if self.zero {
            return Ok(Self::zero(self.variables - 1));
        }
        let (equations, phase, exponent) = self.eliminate_before_normalization(variable)?;
        Self::new(self.variables - 1, equations, phase, exponent)
    }

    fn eliminate_before_normalization(
        &self,
        variable: usize,
    ) -> Result<(Vec<Equation>, Anf, usize), BoundaryError> {
        let mut equations = self.equations.clone();
        let (phase, exponent) =
            if let Some(pivot) = equations.iter().position(|eq| eq.coefficients[variable]) {
                let pivot_eq = equations.remove(pivot);
                let phase = substitute(
                    &self.phase,
                    variable,
                    &affine_replacement(&pivot_eq, variable),
                );
                for eq in &mut equations {
                    if eq.coefficients[variable] {
                        xor_equation(eq, &pivot_eq);
                    }
                }
                (phase, self.exponent)
            } else {
                let mut base = Anf::new();
                let mut mixed = Anf::new();
                for term in &self.phase {
                    if term.binary_search(&variable).is_ok() {
                        toggle(
                            &mut mixed,
                            term.iter().copied().filter(|&i| i != variable).collect(),
                        );
                    } else {
                        toggle(&mut base, term.clone());
                    }
                }
                debug_assert!(mixed.iter().all(|term| term.len() <= 1));
                let mut coefficients = vec![false; self.variables];
                for term in &mixed {
                    if let [index] = term.as_slice() {
                        coefficients[*index] = true;
                    }
                }
                equations.push(Equation {
                    coefficients,
                    rhs: mixed.contains(&vec![]),
                });
                let exponent = self
                    .exponent
                    .checked_add(1)
                    .ok_or(BoundaryError::ExponentOverflow)?;
                (base, exponent)
            };
        let equations = equations
            .into_iter()
            .map(|mut eq| {
                eq.coefficients.remove(variable);
                eq
            })
            .collect();
        let phase = phase
            .into_iter()
            .map(|term| drop_variable(&term, variable))
            .collect();
        Ok((equations, phase, exponent))
    }

    /// Certified two-to-one Shannon interpolation. A cubic result refuses.
    pub fn stitch(&self, other: &Self) -> Result<Option<Self>, BoundaryError> {
        if self.zero
            || other.zero
            || self.variables != other.variables
            || self.exponent != other.exponent
            || self.equations.len() != other.equations.len()
        {
            return Ok(None);
        }
        let differences = self
            .equations
            .iter()
            .zip(&other.equations)
            .enumerate()
            .filter(|(_, (a, b))| a != b)
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        if differences.len() != 1 {
            return Ok(None);
        }
        let index = differences[0];
        let (a, b) = (&self.equations[index], &other.equations[index]);
        if a.coefficients != b.coefficients || a.rhs == b.rhs {
            return Ok(None);
        }
        let mut selector = Anf::new();
        if a.rhs {
            selector.insert(vec![]);
        }
        for (i, &enabled) in a.coefficients.iter().enumerate() {
            if enabled {
                selector.insert(vec![i]);
            }
        }
        let delta = xor_polys(&self.phase, &other.phase);
        let mut phase = xor_polys(&self.phase, &multiply_polys(&selector, &delta));
        let common = self
            .equations
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != index)
            .map(|(_, eq)| eq.clone())
            .collect::<Vec<_>>();
        for eq in &common {
            if let Some(pivot) = eq.coefficients.iter().position(|&x| x) {
                phase = substitute(&phase, pivot, &affine_replacement(eq, pivot));
            }
        }
        if phase.iter().any(|term| term.len() > 2) {
            return Ok(None);
        }
        Self::new(self.variables, common, phase, self.exponent).map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms(ms: &[&[usize]]) -> Anf {
        ms.iter().map(|term| term.to_vec()).collect()
    }

    fn bits(n: usize, word: usize) -> Vec<bool> {
        (0..n).map(|i| word & (1 << i) != 0).collect()
    }

    fn next(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        *seed
    }

    fn random_mode(n: usize, seed: &mut u64) -> QuadraticMode {
        let mut phase = Anf::new();
        if next(seed) & 1 != 0 {
            phase.insert(vec![]);
        }
        for i in 0..n {
            if next(seed) & 1 != 0 {
                phase.insert(vec![i]);
            }
            for j in (i + 1)..n {
                if next(seed) & 1 != 0 {
                    phase.insert(vec![i, j]);
                }
            }
        }
        let mut equations = Vec::new();
        for _ in 0..n {
            if next(seed) & 3 == 0 {
                equations.push(Equation {
                    coefficients: (0..n).map(|_| next(seed) & 1 != 0).collect(),
                    rhs: next(seed) & 1 != 0,
                });
            }
        }
        QuadraticMode::new(n, equations, phase, 0).unwrap()
    }

    #[test]
    fn all_context_projection_and_product_agree_with_enumeration() {
        let mut seed = 20261117_u64;
        for n in 1..=6 {
            for _ in 0..48 {
                let a = random_mode(n, &mut seed);
                let b = random_mode(n, &mut seed);
                let product = a.product(&b).unwrap();
                for word in 0..(1 << n) {
                    let assignment = bits(n, word);
                    assert_eq!(
                        product.value(&assignment).unwrap().to_i128().unwrap(),
                        a.value(&assignment).unwrap().to_i128().unwrap()
                            * b.value(&assignment).unwrap().to_i128().unwrap()
                    );
                }
                for variable in 0..n {
                    let projected = a.eliminate(variable).unwrap();
                    for word in 0..(1 << (n - 1)) {
                        let exterior = bits(n - 1, word);
                        let expected = [false, true]
                            .into_iter()
                            .map(|x| {
                                let mut full = exterior.clone();
                                full.insert(variable, x);
                                a.value(&full).unwrap().to_i128().unwrap()
                            })
                            .sum::<i128>();
                        assert_eq!(
                            projected.value(&exterior).unwrap().to_i128(),
                            Some(expected)
                        );
                        assert!(projected.equations().len() < n);
                    }
                }
            }
        }
    }

    #[test]
    fn constrained_projection_witness() {
        // Input order is (y, z, x, u, v). Both stored rows contain x.
        let rows = vec![
            Equation {
                coefficients: vec![true, false, true, true, false],
                rhs: true,
            },
            Equation {
                coefficients: vec![false, true, true, false, true],
                rhs: false,
            },
        ];
        let phase = terms(&[&[2, 3]]);
        let input = QuadraticMode::new(5, rows.clone(), phase.clone(), 130).unwrap();
        assert_eq!(input.equations(), rows.as_slice());
        assert_eq!(input.phase(), &phase);

        let (residual, substituted, exponent) = input.eliminate_before_normalization(2).unwrap();
        assert_eq!(
            residual,
            vec![Equation {
                coefficients: vec![true, true, true, true],
                rhs: true,
            }]
        );
        // In (y, z, u, v), (1 ^ y ^ u) * u = y * u.
        assert_eq!(substituted, terms(&[&[0, 2]]));
        assert_eq!(exponent, 130);

        let output = input.eliminate(2).unwrap();
        assert_eq!(output.equations(), residual.as_slice());
        assert_eq!(output.phase(), &terms(&[&[1, 2], &[2, 3]]));
        for word in 0..16 {
            let exterior = bits(4, word);
            let [y, z, u, v] = exterior.as_slice() else {
                unreachable!("four exterior coordinates");
            };
            let mut expected = SignedPower::Zero;
            for x in [false, true] {
                if *y ^ x ^ *u && !(*z ^ x ^ *v) {
                    assert_eq!(expected, SignedPower::Zero, "unique extension");
                    expected = if x && *u {
                        SignedPower::Negative(130)
                    } else {
                        SignedPower::Positive(130)
                    };
                }
            }
            assert_eq!(output.value(&exterior).unwrap(), expected, "{exterior:?}");
        }
    }

    #[test]
    fn exact_two_mode_stitch_and_cubic_refusal() {
        let support0 = Equation {
            coefficients: vec![true, false],
            rhs: false,
        };
        let support1 = Equation {
            coefficients: vec![true, false],
            rhs: true,
        };
        let a = QuadraticMode::new(2, vec![support0], Anf::new(), 0).unwrap();
        let b = QuadraticMode::new(2, vec![support1], terms(&[&[1]]), 0).unwrap();
        let joined = a.stitch(&b).unwrap().expect("quadratic stitch");
        assert!(joined.phase().contains(&vec![0, 1]));
        for word in 0..4 {
            let v = bits(2, word);
            assert_eq!(
                joined.value(&v).unwrap().to_i128().unwrap(),
                a.value(&v).unwrap().to_i128().unwrap() + b.value(&v).unwrap().to_i128().unwrap()
            );
        }
        let a = QuadraticMode::new(
            3,
            vec![Equation {
                coefficients: vec![true, false, false],
                rhs: false,
            }],
            Anf::new(),
            0,
        )
        .unwrap();
        let b = QuadraticMode::new(
            3,
            vec![Equation {
                coefficients: vec![true, false, false],
                rhs: true,
            }],
            terms(&[&[1, 2]]),
            0,
        )
        .unwrap();
        assert_eq!(a.stitch(&b), Ok(None));
    }

    #[test]
    fn invalid_terms_and_integer_overflow_refuse() {
        assert_eq!(
            QuadraticMode::new(2, vec![], terms(&[&[0, 1, 2]]), 0),
            Err(BoundaryError::InvalidMonomial)
        );
        assert_eq!(SignedPower::Positive(200).to_i128(), None);
    }
}
