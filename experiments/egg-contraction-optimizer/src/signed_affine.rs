//! Signed quadratic boundary projection atop the existing affine receipt.
//!
//! No second Gaussian eliminator: all affine constraints pass through the
//! packed producer and independently replayed dense Boolean certificate.
//! A separate phase checker reconstructs every degree-two coefficient from
//! evaluations at Hamming weights 0, 1 and 2, rather than copying the
//! producer's symbolic substitution routine.
//!
//! Current scope: exactly ONE internal bit, arbitrary boundary dimension.
//! This is a checked Rust implementation of a mathematically local rule,
//! not a kernel-verified Lean-to-Rust refinement or general #SAT solver.

use crate::affine::{AffineInterface, AffineRegion, BoundaryRow};
use crate::affine_cert::{EliminationCertificate, VerificationReceipt};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

/// Each monomial is a sorted squarefree sequence of indices.
/// Index 0 is the internal bit; 1..=boundary.len() are boundary bits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuadraticPhase {
    width: usize,
    terms: BTreeSet<Vec<usize>>,
}

fn toggle(terms: &mut BTreeSet<Vec<usize>>, term: Vec<usize>) {
    if !terms.insert(term.clone()) {
        terms.remove(&term);
    }
}

impl QuadraticPhase {
    pub fn new(width: usize, monomials: Vec<Vec<usize>>) -> Result<Self, String> {
        let mut terms = BTreeSet::new();
        for mut term in monomials {
            if term.iter().any(|&index| index >= width) {
                return Err("phase references an undeclared coordinate".into());
            }
            term.sort_unstable();
            term.dedup(); // Boolean idempotence x*x=x.
            if term.len() > 2 {
                return Err("phase requires a monomial above quadratic degree".into());
            }
            toggle(&mut terms, term);
        }
        Ok(Self { width, terms })
    }

    #[must_use]
    pub fn terms(&self) -> &BTreeSet<Vec<usize>> {
        &self.terms
    }

    fn eval(&self, bits: &[bool]) -> bool {
        debug_assert_eq!(self.width, bits.len());
        self.terms.iter().fold(false, |parity, term| {
            parity ^ term.iter().all(|&index| bits[index])
        })
    }

    /// Producer: substitute x by an affine expression if constrained, or
    /// split off its affine coefficient if unconstrained. Never enumerate.
    fn remove_first(
        &self,
        replacement: Option<&(bool, Vec<bool>)>,
    ) -> Result<(Self, Option<BoundaryRow>), String> {
        if self.width == 0 {
            return Err("no internal phase coordinate".into());
        }
        let boundary_width = self.width - 1;
        let mut base = BTreeSet::new();
        let mut mixed = BTreeSet::new();
        for term in &self.terms {
            let has_internal = term.binary_search(&0).is_ok();
            let tail = term
                .iter()
                .filter(|&&i| i != 0)
                .map(|i| i - 1)
                .collect::<Vec<_>>();
            if has_internal {
                toggle(&mut mixed, tail);
            } else {
                toggle(&mut base, tail);
            }
        }

        if let Some((constant, linear)) = replacement {
            if linear.len() != boundary_width {
                return Err("affine replacement has wrong boundary dimension".into());
            }
            let mut output = base;
            for term in mixed {
                if *constant {
                    toggle(&mut output, term.clone());
                }
                for (index, &coefficient) in linear.iter().enumerate() {
                    if !coefficient {
                        continue;
                    }
                    let mut product = term.clone();
                    product.push(index);
                    product.sort_unstable();
                    product.dedup();
                    if product.len() > 2 {
                        return Err("quadratic substitution raised degree".into());
                    }
                    toggle(&mut output, product);
                }
            }
            Ok((
                Self {
                    width: boundary_width,
                    terms: output,
                },
                None,
            ))
        } else {
            // Q(x,b) = Q(0,b) XOR x*L(b), with L affine.
            if mixed.iter().any(|term| term.len() > 1) {
                return Err("free-variable coefficient is not affine".into());
            }
            let rhs = mixed.contains(&Vec::new());
            let boundary_indices = mixed
                .iter()
                .filter_map(|term| term.first().copied())
                .collect();
            Ok((
                Self {
                    width: boundary_width,
                    terms: base,
                },
                Some(BoundaryRow {
                    boundary_indices,
                    rhs,
                }),
            ))
        }
    }
}

/// Concrete degree-two coefficients of a checked exterior phase. This
/// deliberately matches the constant / linear / ordered-pair mathematical
/// interface used by the Lean low-weight checker.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuadraticCoefficientWitness {
    pub constant: bool,
    pub linear: Vec<bool>,
    pub ordered_pairs: Vec<(usize, usize)>,
}

impl QuadraticCoefficientWitness {
    /// Check structural validity instead of trusting caller-provided pairs.
    /// This is a second representation of the phase for future Lean replay.
    pub fn evaluate(&self, bits: &[bool]) -> Result<bool, String> {
        if bits.len() != self.linear.len() {
            return Err("coefficient witness boundary width mismatch".into());
        }
        let mut result = self.constant;
        for (&coefficient, &bit) in self.linear.iter().zip(bits) {
            result ^= coefficient && bit;
        }
        let mut previous = None;
        for &(i, j) in &self.ordered_pairs {
            if i >= bits.len() || j >= bits.len() || i >= j
                || previous.is_some_and(|prior| prior >= (i, j))
            {
                return Err("quadratic witness pair is out of range or noncanonical".into());
            }
            result ^= bits[i] && bits[j];
            previous = Some((i, j));
        }
        Ok(result)
    }
}

impl QuadraticPhase {
    fn coefficient_witness(&self) -> Result<QuadraticCoefficientWitness, String> {
        let mut linear = vec![false; self.width];
        let mut ordered_pairs = Vec::new();
        for term in &self.terms {
            match term.as_slice() {
                [] => {}
                [i] if *i < self.width => linear[*i] = true,
                [i, j] if *i < *j && *j < self.width => {
                    ordered_pairs.push((*i, *j));
                }
                _ => return Err("invalid canonical phase term in witness".into()),
            }
        }
        Ok(QuadraticCoefficientWitness {
            constant: self.terms.contains(&Vec::new()),
            linear,
            ordered_pairs,
        })
    }
}

/// Configurable verification budget. A budget refusal is never a successful
/// count or a claim of incomplete values having been fully checked.
#[derive(Clone, Copy, Debug)]
pub struct PhaseVerificationPolicy {
    pub max_interpolation_samples: usize,
}

impl Default for PhaseVerificationPolicy {
    fn default() -> Self {
        Self {
            max_interpolation_samples: 1_000_000,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignedOneBitRegion {
    pub affine: AffineRegion,
    pub phase: QuadraticPhase,
    pub exponent: usize,
}

#[derive(Clone, Debug)]
pub struct SignedBoundaryInterface {
    pub affine: AffineInterface,
    pub phase: QuadraticPhase,
    pub added_constraint: Option<BoundaryRow>,
    pub exponent: usize,
}

/// The extra phase rule is tied to a source row or a free internal bit.
/// An arbitrary output phase or constraint cannot be accepted by the checker.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignedRule {
    FixedBySourceRow(usize),
    Free,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedCertificate {
    pub affine: EliminationCertificate,
    pub rule: SignedRule,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedVerificationReceipt {
    pub affine: VerificationReceipt,
    pub interpolation_samples: usize,
    pub phase_coefficients: QuadraticCoefficientWitness,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignedValue {
    Zero,
    Positive(usize),
    Negative(usize),
}

impl SignedValue {
    /// Materialization is an explicit potentially large allocation.
    #[must_use]
    pub fn to_bigint(&self) -> BigInt {
        match self {
            Self::Zero => BigInt::from(0),
            Self::Positive(k) => BigInt::from(1u8) << *k,
            Self::Negative(k) => -(BigInt::from(1u8) << *k),
        }
    }
}

fn assignment(boundary: &[bool], x: bool) -> Vec<bool> {
    let mut full = Vec::with_capacity(boundary.len() + 1);
    full.push(x);
    full.extend_from_slice(boundary);
    full
}

fn source_pivot(
    source: &AffineRegion,
    source_row: usize,
) -> Result<(bool, Vec<bool>), String> {
    let row = source.equations.get(source_row).ok_or("pivot row outside source")?;
    let name = source.internal.first().ok_or("expected one internal bit")?;
    let mut internal = false;
    let mut coefficients = vec![false; source.boundary.len()];
    let by_name: BTreeMap<&str, usize> = source
        .boundary
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    for variable in &row.variables {
        if variable == name {
            internal ^= true;
        } else {
            let &index = by_name
                .get(variable.as_str())
                .ok_or("unknown source equation variable")?;
            coefficients[index] ^= true;
        }
    }
    if !internal {
        return Err("selected source row does not determine internal bit".into());
    }
    Ok((row.rhs, coefficients))
}

fn source_has_internal(source: &AffineRegion, row: usize) -> bool {
    source.equations[row]
        .variables
        .iter()
        .fold(false, |parity, name| parity ^ (name == &source.internal[0]))
}

impl SignedOneBitRegion {
    fn validate_phase(&self) -> Result<(), String> {
        if self.affine.internal.len() != 1 {
            return Err("signed affine receipt currently supports one internal bit".into());
        }
        let width = self
            .affine
            .boundary
            .len()
            .checked_add(1)
            .ok_or("phase width overflow")?;
        if self.phase.width != width {
            return Err("phase and affine coordinate orders differ".into());
        }
        Ok(())
    }

    pub fn eliminate_with_certificate(
        &self,
    ) -> Result<(SignedBoundaryInterface, SignedCertificate), String> {
        self.validate_phase()?;
        // This is the *existing* packed affine producer and receipt.
        let (affine, certificate) = self.affine.eliminate_with_certificate()?;
        let pivot = self
            .affine
            .equations
            .iter()
            .enumerate()
            .find_map(|(i, _)| source_has_internal(&self.affine, i).then_some(i));
        let (rule, replacement) = if let Some(i) = pivot {
            (SignedRule::FixedBySourceRow(i), Some(source_pivot(&self.affine, i)?))
        } else {
            (SignedRule::Free, None)
        };
        let (phase, added_constraint) = self.phase.remove_first(replacement.as_ref())?;
        let exponent = if replacement.is_some() {
            self.exponent
        } else {
            self.exponent.checked_add(1).ok_or("signed exponent overflow")?
        };
        Ok((
            SignedBoundaryInterface {
                affine,
                phase,
                added_constraint,
                exponent,
            },
            SignedCertificate {
                affine: certificate,
                rule,
            },
        ))
    }

    /// Public entry point accepts only a separately checked result.
    pub fn eliminate(&self) -> Result<SignedBoundaryInterface, String> {
        let (result, certificate) = self.eliminate_with_certificate()?;
        certificate.verify(self, &result)?;
        Ok(result)
    }

    /// Independent bounded oracle, used in tests only.
    #[cfg(test)]
    fn direct_at(&self, boundary: &[bool]) -> Result<BigInt, String> {
        self.validate_phase()?;
        if boundary.len() != self.affine.boundary.len() {
            return Err("wrong oracle boundary width".into());
        }
        let mut result = BigInt::from(0);
        for x in [false, true] {
            let all = assignment(boundary, x);
            let variables: BTreeMap<_, _> = self
                .affine
                .internal
                .iter()
                .chain(&self.affine.boundary)
                .cloned()
                .zip(all.iter().copied())
                .collect();
            let satisfied = self.affine.equations.iter().all(|eq| {
                eq.variables.iter().fold(false, |p, name| p ^ variables[name]) == eq.rhs
            });
            if satisfied {
                let signed = if self.phase.eval(&all) {
                    SignedValue::Negative(self.exponent)
                } else {
                    SignedValue::Positive(self.exponent)
                };
                result += signed.to_bigint();
            }
        }
        Ok(result)
    }
}

impl SignedBoundaryInterface {
    pub fn evaluate(&self, boundary: &[bool]) -> Result<SignedValue, String> {
        if boundary.len() != self.affine.boundary.len()
            || self.phase.width != boundary.len()
        {
            return Err("signed boundary shape mismatch".into());
        }
        if self.affine.residual.iter().chain(self.added_constraint.iter()).any(|eq| {
            eq.boundary_indices.iter().any(|&index| index >= boundary.len())
        }) {
            return Err("signed boundary constraint references an invalid coordinate".into());
        }
        let admissible = self
            .affine
            .residual
            .iter()
            .chain(self.added_constraint.iter())
            .all(|eq| {
                eq.boundary_indices
                    .iter()
                    .fold(false, |p, &index| p ^ boundary[index])
                    == eq.rhs
            });
        if !admissible {
            return Ok(SignedValue::Zero);
        }
        if self.phase.eval(boundary) {
            Ok(SignedValue::Negative(self.exponent))
        } else {
            Ok(SignedValue::Positive(self.exponent))
        }
    }
}

/// Independently reconstruct degree-two ANF coefficients with samples of
/// Hamming weight at most 2; complexity O(n²) phase evaluations, not 2^n.
/// Soundness relies on both input and output being quadratic.
fn interpolate_quadratic(
    n: usize,
    policy: PhaseVerificationPolicy,
    mut eval: impl FnMut(&[bool]) -> bool,
) -> Result<(QuadraticPhase, usize), String> {
    let samples = n
        .checked_add(1)
        .and_then(|plus_one| n.checked_mul(plus_one))
        .map(|product| product / 2)
        .and_then(|half| half.checked_add(1))
        .ok_or("interpolation sample count overflow")?;
    if samples > policy.max_interpolation_samples {
        return Err("signed phase interpolation budget exceeded".into());
    }
    let mut bits = vec![false; n];
    let mut terms = BTreeSet::new();
    let constant = eval(&bits);
    if constant {
        terms.insert(vec![]);
    }
    let mut linear_samples = Vec::with_capacity(n);
    for i in 0..n {
        bits[i] = true;
        let at_single = eval(&bits);
        linear_samples.push(at_single);
        if at_single ^ constant {
            terms.insert(vec![i]);
        }
        bits[i] = false;
    }
    for i in 0..n {
        bits[i] = true;
        for j in (i + 1)..n {
            bits[j] = true;
            let at_pair = eval(&bits);
            if at_pair ^ linear_samples[i] ^ linear_samples[j] ^ constant {
                terms.insert(vec![i, j]);
            }
            bits[j] = false;
        }
        bits[i] = false;
    }
    Ok((QuadraticPhase { width: n, terms }, samples))
}

impl SignedCertificate {
    pub fn verify(
        &self,
        source: &SignedOneBitRegion,
        claimed: &SignedBoundaryInterface,
    ) -> Result<SignedVerificationReceipt, String> {
        self.verify_with_policy(source, claimed, PhaseVerificationPolicy::default())
    }

    pub fn verify_with_policy(
        &self,
        source: &SignedOneBitRegion,
        claimed: &SignedBoundaryInterface,
        policy: PhaseVerificationPolicy,
    ) -> Result<SignedVerificationReceipt, String> {
        source.validate_phase()?;
        let affine = self.affine.verify(&source.affine, &claimed.affine)?;
        let n = source.affine.boundary.len();
        if claimed.phase.width != n {
            return Err("claimed phase has wrong boundary shape".into());
        }
        let replacement = match self.rule {
            SignedRule::FixedBySourceRow(index) => {
                if affine.rank != 1 || affine.free_internal != 0 {
                    return Err("fixed-phase rule disagrees with affine rank".into());
                }
                Some(source_pivot(&source.affine, index)?)
            }
            SignedRule::Free => {
                if affine.rank != 0 || affine.free_internal != 1 {
                    return Err("free-phase rule disagrees with affine rank".into());
                }
                None
            }
        };
        let (expected_phase, samples) = interpolate_quadratic(n, policy, |boundary| {
            let x = replacement.as_ref().is_some_and(|(constant, linear)| {
                linear
                    .iter()
                    .zip(boundary)
                    .fold(*constant, |value, (&coefficient, &bit)| value ^ (coefficient && bit))
            });
            source.phase.eval(&assignment(boundary, x))
        })?;
        if claimed.phase != expected_phase {
            return Err("quadratic phase coefficients disagree with independent samples".into());
        }

        let expected_added = if replacement.is_some() {
            None
        } else {
            let zeros = vec![false; n];
            let at_difference = |boundary: &[bool]| {
                source.phase.eval(&assignment(boundary, true))
                    ^ source.phase.eval(&assignment(boundary, false))
            };
            let constant = at_difference(&zeros);
            let mut coefficients = Vec::new();
            for index in 0..n {
                let mut singleton = vec![false; n];
                singleton[index] = true;
                if at_difference(&singleton) ^ constant {
                    coefficients.push(index);
                }
            }
            Some(BoundaryRow {
                boundary_indices: coefficients,
                rhs: constant,
            })
        };
        if claimed.added_constraint != expected_added {
            return Err("signed cancellation constraint does not match phase".into());
        }
        let expected_exp = if replacement.is_some() {
            source.exponent
        } else {
            source
                .exponent
                .checked_add(1)
                .ok_or("signed exponent overflow")?
        };
        if claimed.exponent != expected_exp {
            return Err("signed multiplicity disagrees with elimination rule".into());
        }
        Ok(SignedVerificationReceipt {
            affine,
            interpolation_samples: samples,
            phase_coefficients: expected_phase.coefficient_witness()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affine::Equation;
    use crate::affine_cert::RowOperation;

    fn phase(width: usize, terms: &[&[usize]]) -> QuadraticPhase {
        QuadraticPhase::new(width, terms.iter().map(|t| t.to_vec()).collect()).unwrap()
    }

    fn bits(width: usize, value: usize) -> Vec<bool> {
        (0..width).map(|i| value & (1 << i) != 0).collect()
    }

    fn source(
        boundary: usize,
        equations: Vec<Equation>,
        phase: QuadraticPhase,
        exponent: usize,
    ) -> SignedOneBitRegion {
        SignedOneBitRegion {
            affine: AffineRegion {
                internal: vec!["x".into()],
                boundary: (0..boundary).map(|i| format!("b{i}")).collect(),
                equations,
            },
            phase,
            exponent,
        }
    }

    fn next(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        *seed
    }

    #[test]
    fn reconstructs_quadratic_coefficients_independently() {
        let mut seed = 20261118_u64;
        for n in 0..=5 {
            for _ in 0..80 {
                let mut monomials = Vec::new();
                for i in 0..n {
                    if next(&mut seed) & 1 != 0 {
                        monomials.push(vec![i]);
                    }
                    for j in (i + 1)..n {
                        if next(&mut seed) & 1 != 0 {
                            monomials.push(vec![i, j]);
                        }
                    }
                }
                if next(&mut seed) & 1 != 0 {
                    monomials.push(vec![]);
                }
                let original = QuadraticPhase::new(n, monomials).unwrap();
                let (recovered, samples) =
                    interpolate_quadratic(n, PhaseVerificationPolicy::default(), |b| {
                        original.eval(b)
                    })
                    .unwrap();
                assert_eq!(original, recovered);
                assert_eq!(samples, 1 + n * (n + 1) / 2);
                for word in 0..(1 << n) {
                    let b = bits(n, word);
                    assert_eq!(original.eval(&b), recovered.eval(&b));
                }
            }
        }
    }

    #[test]
    fn sparse_coefficient_witness_matches_source_and_refuses_invalid_pairs() {
        // Cover empty, linear and mixed quadratic records. The reference
        // interpreter is the original ANF term evaluator, not the witness
        // evaluator or its low-weight interpolation procedure.
        let mut seed = 20261120_u64;
        for width in 0..=9 {
            for _case in 0..16 {
                let mut terms = vec![];
                if next(&mut seed) & 1 != 0 {
                    terms.push(vec![]);
                }
                for i in 0..width {
                    if next(&mut seed) & 1 != 0 {
                        terms.push(vec![i]);
                    }
                    for j in (i + 1)..width {
                        if next(&mut seed) & 1 != 0 {
                            terms.push(vec![i, j]);
                        }
                    }
                }
                let source = QuadraticPhase::new(width, terms).unwrap();
                let witness = source.coefficient_witness().unwrap();
                assert_eq!(witness.linear.len(), width);
                for word in 0..(1usize << width) {
                    let bits = bits(width, word);
                    assert_eq!(
                        witness.evaluate(&bits).unwrap(),
                        source.eval(&bits),
                        "coefficient witness disagreed at width {width}, word {word}"
                    );
                }
                if width > 0 {
                    let mut wrong_width = witness.clone();
                    wrong_width.linear.pop();
                    assert!(wrong_width.evaluate(&vec![false; width]).is_err());
                }
            }
        }

        let canonical = QuadraticCoefficientWitness {
            constant: false,
            linear: vec![true, false, false],
            ordered_pairs: vec![(0, 1), (0, 2), (1, 2)],
        };
        assert!(canonical.evaluate(&[true, true, false]).is_ok());
        for pairs in [
            vec![(1, 0)],                 // reversed endpoints
            vec![(0, 3)],                 // index out of range
            vec![(1, 1)],                 // diagonal pair
            vec![(0, 1), (0, 1)],         // duplicate
            vec![(0, 2), (0, 1)],         // unsorted
            vec![(1, 2), (0, 1)],         // reordered
        ] {
            let bad = QuadraticCoefficientWitness {
                ordered_pairs: pairs,
                ..canonical.clone()
            };
            assert!(bad.evaluate(&[true, true, false]).is_err());
        }
    }

    #[test]
    fn exact_forced_projection_and_tampering_are_detected() {
        let input = source(
            2,
            vec![
                Equation {
                    variables: vec!["x".into(), "b0".into()],
                    rhs: true,
                },
                Equation {
                    variables: vec!["x".into(), "b1".into()],
                    rhs: false,
                },
            ],
            phase(3, &[&[0, 2], &[1, 2]]),
            130,
        );
        let (output, receipt) = input.eliminate_with_certificate().unwrap();
        assert_eq!(receipt.rule, SignedRule::FixedBySourceRow(0));
        assert_eq!(output.exponent, 130);
        assert!(output.added_constraint.is_none());
        receipt.verify(&input, &output).unwrap();
        for word in 0..4 {
            let b = bits(2, word);
            assert_eq!(output.evaluate(&b).unwrap().to_bigint(), input.direct_at(&b).unwrap());
            assert_eq!(
                receipt.verify(&input, &output).unwrap().phase_coefficients.evaluate(&b).unwrap(),
                output.phase.eval(&b)
            );
        }
        let mut bad = output.clone();
        bad.exponent += 1;
        assert!(receipt.verify(&input, &bad).is_err());
        let mut bad = output.clone();
        bad.phase = phase(2, &[&[0]]);
        assert!(receipt.verify(&input, &bad).is_err());
        let mut bad = receipt.clone();
        bad.rule = SignedRule::FixedBySourceRow(99);
        assert!(bad.verify(&input, &output).is_err());
        let mut bad = receipt.clone();
        bad.affine.steps.push(RowOperation::Xor { target: 0, source: 0 });
        assert!(bad.verify(&input, &output).is_err());
        assert!(input.eliminate().is_ok());
    }

    #[test]
    fn free_signed_cancellation_and_constant_obstruction() {
        let input = source(
            2,
            vec![],
            phase(3, &[&[0, 1], &[0, 2], &[1, 2]]),
            6,
        );
        let (output, receipt) = input.eliminate_with_certificate().unwrap();
        assert_eq!(receipt.rule, SignedRule::Free);
        assert_eq!(output.exponent, 7);
        assert_eq!(output.added_constraint.as_ref().unwrap().boundary_indices, vec![0, 1]);
        receipt.verify(&input, &output).unwrap();
        for word in 0..4 {
            let b = bits(2, word);
            assert_eq!(output.evaluate(&b).unwrap().to_bigint(), input.direct_at(&b).unwrap());
        }
        let mut bad = output.clone();
        bad.added_constraint.as_mut().unwrap().rhs ^= true;
        assert!(receipt.verify(&input, &bad).is_err());

        // Sum_x (-1)^x = 0, for every boundary assignment.
        let impossible = source(0, vec![], phase(1, &[&[0]]), 0);
        let result = impossible.eliminate().unwrap();
        assert_eq!(result.evaluate(&[]).unwrap(), SignedValue::Zero);
    }

    #[test]
    fn independently_checked_random_one_bit_regions() {
        let mut seed = 98421_u64;
        for n in 0..=4 {
            for _ in 0..120 {
                let mut monomials = Vec::new();
                if next(&mut seed) & 1 != 0 {
                    monomials.push(vec![]);
                }
                for i in 0..(n + 1) {
                    if next(&mut seed) & 1 != 0 {
                        monomials.push(vec![i]);
                    }
                    for j in (i + 1)..(n + 1) {
                        if next(&mut seed) & 1 != 0 {
                            monomials.push(vec![i, j]);
                        }
                    }
                }
                let mut equations = Vec::new();
                for _ in 0..4 {
                    if next(&mut seed) & 1 != 0 {
                        let mut names = Vec::new();
                        if next(&mut seed) & 1 != 0 {
                            names.push("x".into());
                        }
                        for i in 0..n {
                            if next(&mut seed) & 1 != 0 {
                                names.push(format!("b{i}"));
                            }
                        }
                        equations.push(Equation {
                            variables: names,
                            rhs: next(&mut seed) & 1 != 0,
                        });
                    }
                }
                let mode = source(n, equations, QuadraticPhase::new(n + 1, monomials).unwrap(), 3);
                let (output, receipt) = mode.eliminate_with_certificate().unwrap();
                receipt.verify(&mode, &output).unwrap();
                for word in 0..(1 << n) {
                    let b = bits(n, word);
                    assert_eq!(
                        output.evaluate(&b).unwrap().to_bigint(),
                        mode.direct_at(&b).unwrap(),
                        "n={n}, word={word}"
                    );
                }
            }
        }
    }

    #[test]
    fn large_boundary_uses_polynomial_samples_and_budget_refuses() {
        let input = source(
            130,
            vec![],
            phase(131, &[&[0, 64], &[0, 65], &[128, 129]]),
            127,
        );
        let (output, receipt) = input.eliminate_with_certificate().unwrap();
        let checked = receipt.verify(&input, &output).unwrap();
        assert_eq!(checked.interpolation_samples, 8516);
        assert_eq!(checked.phase_coefficients.linear.len(), 130);
        assert_eq!(output.exponent, 128);
        assert!(receipt
            .verify_with_policy(
                &input,
                &output,
                PhaseVerificationPolicy {
                    max_interpolation_samples: 8515,
                }
            )
            .is_err());
        for word in 0..16 {
            let mut b = vec![false; 130];
            for i in 0..4 {
                b[63 + i] = word & (1 << i) != 0;
            }
            assert_eq!(output.evaluate(&b).unwrap().to_bigint(), input.direct_at(&b).unwrap());
        }
    }

    #[test]
    fn malformed_inputs_refuse_without_hidden_fallback() {
        assert!(QuadraticPhase::new(3, vec![vec![0, 1, 2]]).is_err());
        assert!(QuadraticPhase::new(3, vec![vec![3]]).is_err());
        let wrong = source(2, vec![], phase(2, &[]), 0);
        assert!(wrong.eliminate().is_err());
        let two_internal = SignedOneBitRegion {
            affine: AffineRegion {
                internal: vec!["x".into(), "y".into()],
                boundary: vec![],
                equations: vec![],
            },
            phase: phase(2, &[]),
            exponent: 0,
        };
        assert!(two_internal.eliminate().is_err());
    }
}


/// Several ordered internal bits with one shared quadratic phase.  Each
/// stage eliminates the first surviving internal bit; the others are
/// temporarily exposed as *ports* to the existing one-bit verifier.
#[derive(Clone, Debug)]
pub struct SignedMultiRegion {
    pub affine: AffineRegion,
    pub phase: QuadraticPhase,
    pub exponent: usize,
}

#[derive(Clone, Debug)]
pub struct SignedChainStep {
    pub output: SignedBoundaryInterface,
    pub certificate: SignedCertificate,
}

#[derive(Clone, Debug)]
pub struct SignedChain {
    pub steps: Vec<SignedChainStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedChainReceipt {
    pub stages_checked: usize,
    pub total_interpolation_samples: usize,
    pub affine_operations_checked: usize,
    /// Every stage's independently checked phase coefficients and affine
    /// replay receipt, in the same order as the original internal ports.
    pub checked_steps: Vec<SignedVerificationReceipt>,
}

impl SignedMultiRegion {
    fn first_stage(&self) -> Result<SignedOneBitRegion, String> {
        let first = self
            .affine
            .internal
            .first()
            .ok_or("signed chain requires at least one internal variable")?
            .clone();
        let expected_width = self
            .affine
            .internal
            .len()
            .checked_add(self.affine.boundary.len())
            .ok_or("signed chain phase width overflow")?;
        if self.phase.width != expected_width {
            return Err("signed chain phase and source coordinate order differ".into());
        }
        Ok(SignedOneBitRegion {
            affine: AffineRegion {
                internal: vec![first],
                boundary: self.affine.internal[1..]
                    .iter()
                    .chain(&self.affine.boundary)
                    .cloned()
                    .collect(),
                equations: self.affine.equations.clone(),
            },
            phase: self.phase.clone(),
            exponent: self.exponent,
        })
    }

    /// Returns a *complete*, already replay-checked chain, never a partial
    /// prefix on budget refusal or malformed input.
    pub fn eliminate_with_certificate(&self) -> Result<SignedChain, String> {
        let mut current = self.first_stage()?;
        let mut steps = Vec::new();
        for stage in 0..self.affine.internal.len() {
            let (output, certificate) = current.eliminate_with_certificate()?;
            certificate.verify(&current, &output)?;
            if stage + 1 < self.affine.internal.len() {
                current = output.as_next_stage()?;
            }
            steps.push(SignedChainStep { output, certificate });
        }
        let chain = SignedChain { steps };
        chain.verify(self)?;
        Ok(chain)
    }

    /// A checked final boundary interface; all intermediate certificates
    /// have been verified independently from their original input.
    pub fn eliminate(&self) -> Result<SignedBoundaryInterface, String> {
        let chain = self.eliminate_with_certificate()?;
        chain
            .steps
            .last()
            .map(|step| step.output.clone())
            .ok_or_else(|| "signed chain produced no stages".into())
    }
}

impl SignedBoundaryInterface {
    /// Rebind the first remaining boundary port as the next internal bit.
    /// This is a *coordinate reinterpretation*, with no new Gaussian solver.
    /// Both residual rows and the signed cancellation row are carried forward.
    fn as_next_stage(&self) -> Result<SignedOneBitRegion, String> {
        if self.phase.width != self.affine.boundary.len() {
            return Err("signed chain intermediate phase width changed".into());
        }
        let internal = self
            .affine
            .boundary
            .first()
            .ok_or("signed chain has no internal port left")?
            .clone();
        let boundary = self.affine.boundary[1..].to_vec();
        let equations = self
            .affine
            .residual
            .iter()
            .chain(self.added_constraint.iter())
            .map(|row| {
                let mut variables = Vec::with_capacity(row.boundary_indices.len());
                for &index in &row.boundary_indices {
                    let name = self
                        .affine
                        .boundary
                        .get(index)
                        .ok_or("signed chain residual row index out of bounds")?;
                    variables.push(name.clone());
                }
                Ok(crate::affine::Equation {
                    variables,
                    rhs: row.rhs,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(SignedOneBitRegion {
            affine: AffineRegion {
                internal: vec![internal],
                boundary,
                equations,
            },
            phase: self.phase.clone(),
            exponent: self.exponent,
        })
    }
}

impl SignedChain {
    /// Independently replay *each* stage against the verified prior output.
    /// A substituted intermediate phase, changed row, missing stage,
    /// incorrectly ordered port or invalid exponent cannot be skipped.
    pub fn verify(&self, source: &SignedMultiRegion) -> Result<SignedChainReceipt, String> {
        self.verify_with_policy(source, PhaseVerificationPolicy::default())
    }

    pub fn verify_with_policy(
        &self,
        source: &SignedMultiRegion,
        policy: PhaseVerificationPolicy,
    ) -> Result<SignedChainReceipt, String> {
        if self.steps.len() != source.affine.internal.len() || self.steps.is_empty() {
            return Err("signed chain stage count does not match internal variables".into());
        }
        let mut current = source.first_stage()?;
        let mut samples = 0usize;
        let mut operations = 0usize;
        let mut checked_steps = Vec::with_capacity(self.steps.len());
        for (stage, step) in self.steps.iter().enumerate() {
            // Pass the *remaining* allowance to the stage verifier. Checking
            // the aggregate only after a stage returns would allow that stage
            // to spend samples beyond the caller's hard budget before refusing.
            let remaining = policy.max_interpolation_samples
                .checked_sub(samples)
                .ok_or("signed chain aggregate interpolation budget exceeded")?;
            let receipt = step.certificate.verify_with_policy(
                &current,
                &step.output,
                PhaseVerificationPolicy { max_interpolation_samples: remaining },
            )?;
            samples = samples
                .checked_add(receipt.interpolation_samples)
                .ok_or("signed chain sample counter overflow")?;
            if samples > policy.max_interpolation_samples {
                return Err("signed chain aggregate interpolation budget exceeded".into());
            }
            operations = operations
                .checked_add(receipt.affine.operations_checked)
                .ok_or("signed chain row-operation counter overflow")?;
            if stage + 1 < self.steps.len() {
                current = step.output.as_next_stage()?;
            } else if step.output.affine.boundary != source.affine.boundary {
                return Err("signed chain final boundary order differs from source".into());
            }
            checked_steps.push(receipt);
        }
        Ok(SignedChainReceipt {
            stages_checked: self.steps.len(),
            total_interpolation_samples: samples,
            affine_operations_checked: operations,
            checked_steps,
        })
    }

    pub fn final_interface(&self) -> Result<&SignedBoundaryInterface, String> {
        self.steps
            .last()
            .map(|step| &step.output)
            .ok_or_else(|| "signed chain has no final boundary".into())
    }
}

#[cfg(test)]
mod chain_tests {
    use super::*;
    use crate::affine::Equation;

    fn bits(n: usize, word: usize) -> Vec<bool> {
        (0..n).map(|i| (word & (1 << i)) != 0).collect()
    }

    fn next(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        *seed
    }

    fn brute_force(source: &SignedMultiRegion, boundary: &[bool]) -> BigInt {
        let n = source.affine.internal.len();
        let mut result = BigInt::from(0);
        for word in 0..(1 << n) {
            let mut full = bits(n, word);
            full.extend_from_slice(boundary);
            let variables = source
                .affine
                .internal
                .iter()
                .chain(&source.affine.boundary)
                .cloned()
                .zip(full.iter().copied())
                .collect::<BTreeMap<_, _>>();
            let feasible = source.affine.equations.iter().all(|eq| {
                eq.variables
                    .iter()
                    .fold(false, |parity, name| parity ^ variables[name])
                    == eq.rhs
            });
            if feasible {
                let v = if source.phase.eval(&full) {
                    SignedValue::Negative(source.exponent)
                } else {
                    SignedValue::Positive(source.exponent)
                };
                result += v.to_bigint();
            }
        }
        result
    }

    fn sample(n: usize, boundary: usize, seed: &mut u64) -> SignedMultiRegion {
        let width = n + boundary;
        let mut monomials = Vec::new();
        if next(seed) & 1 != 0 {
            monomials.push(vec![]);
        }
        for i in 0..width {
            if next(seed) & 1 != 0 {
                monomials.push(vec![i]);
            }
            for j in (i + 1)..width {
                if next(seed) & 1 != 0 {
                    monomials.push(vec![i, j]);
                }
            }
        }
        let mut equations = Vec::new();
        for _ in 0..(n + 2) {
            if next(seed) & 1 != 0 {
                let variables = (0..width)
                    .filter(|_| next(seed) & 1 != 0)
                    .map(|i| {
                        if i < n {
                            format!("u{i}")
                        } else {
                            format!("b{}", i - n)
                        }
                    })
                    .collect();
                equations.push(Equation {
                    variables,
                    rhs: next(seed) & 1 != 0,
                });
            }
        }
        SignedMultiRegion {
            affine: AffineRegion {
                internal: (0..n).map(|i| format!("u{i}")).collect(),
                boundary: (0..boundary).map(|i| format!("b{i}")).collect(),
                equations,
            },
            phase: QuadraticPhase::new(width, monomials).unwrap(),
            exponent: 2,
        }
    }

    #[test]
    fn exact_repeated_elimination_against_independent_enumeration() {
        let mut seed = 20261119;
        for n in 1..=5 {
            for boundary in 0..=3 {
                for _ in 0..24 {
                    let source = sample(n, boundary, &mut seed);
                    let chain = source.eliminate_with_certificate().unwrap();
                    let receipt = chain.verify(&source).unwrap();
                    assert_eq!(receipt.stages_checked, n);
                    assert_eq!(receipt.checked_steps.len(), n);
                    assert!(receipt.total_interpolation_samples >= n);
                    assert_eq!(
                        receipt.total_interpolation_samples,
                        receipt.checked_steps.iter().map(|r| r.interpolation_samples).sum()
                    );
                    for (step, checked) in chain.steps.iter().zip(&receipt.checked_steps) {
                        let width = step.output.affine.boundary.len();
                        for word in 0..(1 << width) {
                            let ports = bits(width, word);
                            assert_eq!(
                                checked.phase_coefficients.evaluate(&ports).unwrap(),
                                step.output.phase.eval(&ports)
                            );
                        }
                    }
                    for word in 0..(1 << boundary) {
                        let exterior = bits(boundary, word);
                        assert_eq!(
                            chain.final_interface().unwrap().evaluate(&exterior).unwrap().to_bigint(),
                            brute_force(&source, &exterior),
                            "n={n}, boundary={boundary}, word={word}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn chained_free_cancellation_becomes_a_later_affine_pivot() {
        // Sum_x,y (-1)^(xy + xb + y) = 2(-1)^b:
        // summing x forces y=b, then y contributes its boundary sign.
        let source = SignedMultiRegion {
            affine: AffineRegion {
                internal: vec!["x".into(), "y".into()],
                boundary: vec!["b".into()],
                equations: vec![],
            },
            phase: QuadraticPhase::new(3, vec![vec![0, 1], vec![0, 2], vec![1]]).unwrap(),
            exponent: 0,
        };
        let chain = source.eliminate_with_certificate().unwrap();
        assert_eq!(chain.steps.len(), 2);
        assert_eq!(chain.steps[0].certificate.rule, SignedRule::Free);
        assert!(chain.steps[0].output.added_constraint.is_some());
        assert_eq!(chain.steps[1].certificate.rule, SignedRule::FixedBySourceRow(0));
        for b in [false, true] {
            let val = chain.final_interface().unwrap().evaluate(&[b]).unwrap().to_bigint();
            assert_eq!(val, if b { BigInt::from(-2) } else { BigInt::from(2) });
        }
    }

    #[test]
    fn chain_refuses_tampering_truncation_and_budgets() {
        let mut seed = 913;
        let source = sample(3, 2, &mut seed);
        let chain = source.eliminate_with_certificate().unwrap();
        assert_eq!(chain.verify(&source).unwrap().stages_checked, 3);
        let mut bad = chain.clone();
        bad.steps[0].output.exponent += 1;
        assert!(bad.verify(&source).is_err());
        let mut bad = chain.clone();
        bad.steps[0].output.phase =
            QuadraticPhase::new(4, vec![vec![0, 1]]).unwrap();
        assert!(bad.verify(&source).is_err());
        let mut bad = chain.clone();
        bad.steps.pop();
        assert!(bad.verify(&source).is_err());
        let mut bad = chain.clone();
        bad.steps.swap(0, 1);
        assert!(bad.verify(&source).is_err());
        assert!(chain.verify_with_policy(&source, PhaseVerificationPolicy {
            max_interpolation_samples: 0,
        }).is_err());
        let mut source = source.clone();
        source.affine.internal.clear();
        assert!(source.eliminate().is_err());
    }

    #[test]
    fn phase_budget_is_global_across_chain_not_just_per_step() {
        let source = SignedMultiRegion {
            affine: AffineRegion {
                internal: vec!["x".into(), "y".into()],
                boundary: vec!["b".into()],
                equations: vec![],
            },
            phase: QuadraticPhase::new(3, vec![]).unwrap(),
            exponent: 0,
        };
        let chain = source.eliminate_with_certificate().unwrap();
        let receipt = chain.verify(&source).unwrap();
        // First stage: two exterior ports, 4 interpolation samples.
        // Second stage: one exterior port, 2 interpolation samples.
        assert_eq!(receipt.total_interpolation_samples, 6);
        // The next stage must refuse before its two interpolation evaluations,
        // not run them and notice the aggregate excess afterward.
        for budget in [4, 5] {
            assert_eq!(
                chain.verify_with_policy(
                    &source,
                    PhaseVerificationPolicy { max_interpolation_samples: budget },
                ).unwrap_err(),
                "signed phase interpolation budget exceeded",
            );
        }
        assert!(chain
            .verify_with_policy(
                &source,
                PhaseVerificationPolicy {
                    max_interpolation_samples: 6,
                },
            )
            .is_ok());
    }

    #[test]
    fn two_powers_of_two_and_symmetric_phase_survive_three_steps() {
        let source = SignedMultiRegion {
            affine: AffineRegion {
                internal: vec!["a".into(), "b".into(), "c".into()],
                boundary: vec!["z".into()],
                equations: vec![
                    Equation { variables: vec!["a".into(), "b".into()], rhs: true },
                    Equation { variables: vec!["b".into(), "z".into()], rhs: false },
                ],
            },
            phase: QuadraticPhase::new(4, vec![vec![0, 3], vec![1, 2], vec![2]]).unwrap(),
            exponent: 130,
        };
        let chain = source.eliminate_with_certificate().unwrap();
        for z in [false, true] {
            assert_eq!(
                chain.final_interface().unwrap().evaluate(&[z]).unwrap().to_bigint(),
                brute_force(&source, &[z])
            );
        }
    }
}
