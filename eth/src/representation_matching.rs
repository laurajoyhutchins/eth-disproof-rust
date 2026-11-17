//! Exact disjoint-pair contraction with an explicit representation boundary.
//!
//! This is a *bounded-integer* implementation of the matching example from
//! ACC.CrossCutClosure.matching_contract, NOT a compiler for arbitrary #SAT
//! networks. Each port has a unary weight and participates in at most one
//! equality edge. An overlapping edge refuses instead of being dropped or
//! silently misrepresented. All arithmetic is checked i128, not a proven
//! arbitrary-precision bit-cost implementation.

use crate::Error;

/// A closed region: each variable has exactly one unary factor and can
/// participate in zero or one equality constraint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchingRegion {
    unary: Vec<[i128; 2]>,
    partner: Vec<Option<usize>>,
}

/// Arithmetic counts are observed from the selected factorized schedule.
/// They exclude allocation, validation, and integer bit complexity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContractionReceipt {
    pub value: i128,
    pub additions: usize,
    pub multiplications: usize,
    pub variable_count: usize,
    pub equality_pairs: usize,
}

fn checked_add(a: i128, b: i128) -> Result<i128, Error> {
    a.checked_add(b).ok_or(Error::Overflow)
}

fn checked_mul(a: i128, b: i128) -> Result<i128, Error> {
    a.checked_mul(b).ok_or(Error::Overflow)
}

impl MatchingRegion {
    pub fn new(unary: Vec<[i128; 2]>) -> Self {
        let partner = vec![None; unary.len()];
        Self { unary, partner }
    }

    pub fn len(&self) -> usize {
        self.unary.len()
    }

    pub fn is_empty(&self) -> bool {
        self.unary.is_empty()
    }

    /// Apply the equality indicator [x_left = x_right].
    ///
    /// Overlaps cannot be represented as a disjoint matching. A general
    /// factor graph or a separate certified rewrite is required instead.
    pub fn apply_equality(&mut self, left: usize, right: usize) -> Result<(), Error> {
        if left >= self.len() || right >= self.len() {
            return Err(Error::Invalid(
                "equality port outside declared region".into(),
            ));
        }
        if left == right {
            return Err(Error::Invalid(
                "self-equality is not a matching edge".into(),
            ));
        }
        if self.partner[left].is_some() || self.partner[right].is_some() {
            return Err(Error::Capacity(
                "overlapping equality edges require a richer representation".into(),
            ));
        }
        self.partner[left] = Some(right);
        self.partner[right] = Some(left);
        Ok(())
    }

    /// Conservative exact conversion back to unary product form.
    /// Some degenerate correlated regions might also be products, but
    /// this operation does not attempt expensive equivalence discovery.
    pub fn as_unary_product_if_unconstrained(&self) -> Result<&[[i128; 2]], Error> {
        if self.partner.iter().any(Option::is_some) {
            return Err(Error::Capacity(
                "cannot certify unary product after equality interaction".into(),
            ));
        }
        Ok(&self.unary)
    }

    /// Direct point semantics, useful as an independent small-instance oracle.
    pub fn value_at(&self, assignment: &[bool]) -> Result<i128, Error> {
        if assignment.len() != self.len() {
            return Err(Error::Invalid("assignment width mismatch".into()));
        }
        for (i, partner) in self.partner.iter().enumerate() {
            if let Some(j) = partner {
                if assignment[i] != assignment[*j] {
                    return Ok(0);
                }
            }
        }
        assignment
            .iter()
            .enumerate()
            .try_fold(1i128, |acc, (i, bit)| {
                checked_mul(acc, self.unary[i][usize::from(*bit)])
            })
    }

    /// Contract every assignment exactly via disjoint one/two-port components.
    /// This evaluates O(n) checked arithmetic operations rather than 2^n
    /// assignments; coefficient bit lengths still matter.
    pub fn contract(&self) -> Result<ContractionReceipt, Error> {
        let mut value = 1i128;
        let mut additions = 0usize;
        let mut multiplications = 0usize;
        let mut equality_pairs = 0usize;

        for i in 0..self.len() {
            let local = match self.partner[i] {
                Some(j) if i < j => {
                    equality_pairs += 1;
                    let false_term = checked_mul(self.unary[i][0], self.unary[j][0])?;
                    let true_term = checked_mul(self.unary[i][1], self.unary[j][1])?;
                    multiplications += 2;
                    additions += 1;
                    checked_add(false_term, true_term)?
                }
                Some(_) => continue, // Pair was accounted for at the smaller index.
                None => {
                    additions += 1;
                    checked_add(self.unary[i][0], self.unary[i][1])?
                }
            };
            value = checked_mul(value, local)?;
            multiplications += 1;
        }

        Ok(ContractionReceipt {
            value,
            additions,
            multiplications,
            variable_count: self.len(),
            equality_pairs,
        })
    }
}
