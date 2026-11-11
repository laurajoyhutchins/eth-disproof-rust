//! Experimental precision-aware contraction-mode pruning, separate from the
//! literal BitProgram port. Source: `quantitative-contraction.tex`, equations
//! `tensor-mode-expansion` and `tensor-mode-budget` in openai/math.
//!
//! The source uses a conservative per-mode weight `b+1`. For a crossing at
//! valuation level `i <= a`, the same expansion proves the stronger lower
//! bound `a+1-i+b` on the mode coefficient's 2-adic valuation. This kernel
//! enumerates only exponent tuples whose guaranteed total weight is below p.
//! It does not construct a tensor or assert a complete contraction algorithm.

use crate::Error;

/// Explicit experimental envelope, not a bound derived from the theorem.
const MAX_PRECISION: usize = 1_000_000;
const MAX_MODES: usize = 256;

fn admit(modes: &[CrossingMode], precision: usize) -> Result<(), Error> {
    if precision > MAX_PRECISION || modes.len() > MAX_MODES {
        return Err(Error::Capacity(
            "experimental mode enumeration envelope".into(),
        ));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrossingMode {
    pub b: usize,
    pub a: usize,
    pub i: usize,
}

impl CrossingMode {
    pub fn original_weight(self) -> Result<usize, Error> {
        self.b.checked_add(1).ok_or(Error::Overflow)
    }

    /// Valid when the cited crossing-tile valuation inequality holds.
    pub fn stronger_weight(self) -> Result<usize, Error> {
        if self.i > self.a {
            return Err(Error::Invalid("crossing requires i <= a".into()));
        }
        (self.a - self.i)
            .checked_add(1)
            .and_then(|x| x.checked_add(self.b))
            .ok_or(Error::Overflow)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Policy {
    Original,
    Stronger,
}

fn weights(modes: &[CrossingMode], policy: Policy) -> Result<Vec<usize>, Error> {
    modes
        .iter()
        .map(|mode| match policy {
            Policy::Original => mode.original_weight(),
            Policy::Stronger => mode.stronger_weight(),
        })
        .collect()
}

/// Count admissible multi-indices using the coefficient recurrence of
/// `prod_j (1-z^weight_j)^(-1)`, truncated before degree `precision`.
/// This counts *candidate branches*, not their algebraic values.
/// Checked arithmetic refuses if the count exceeds u128.
pub fn count_tuples(
    modes: &[CrossingMode],
    precision: usize,
    policy: Policy,
) -> Result<u128, Error> {
    admit(modes, precision)?;
    if precision == 0 {
        return Ok(0);
    }
    let mut by_degree = vec![0u128; precision];
    by_degree[0] = 1;
    for weight in weights(modes, policy)? {
        for d in weight..precision {
            by_degree[d] = by_degree[d]
                .checked_add(by_degree[d - weight])
                .ok_or(Error::Overflow)?;
        }
    }
    by_degree
        .into_iter()
        .try_fold(0u128, |a, b| a.checked_add(b).ok_or(Error::Overflow))
}

/// Visit every admissible exponent tuple, retaining source mode order.
/// `max_visits` refuses large experiments. On refusal, prior callbacks may
/// already have executed, so this is NOT a transactional operation.
pub fn visit_tuples(
    modes: &[CrossingMode],
    precision: usize,
    policy: Policy,
    max_visits: u128,
    mut emit: impl FnMut(&[usize]),
) -> Result<u128, Error> {
    admit(modes, precision)?;
    let w = weights(modes, policy)?;
    let mut exponents = vec![0usize; w.len()];
    let mut visited = 0u128;
    fn rec(
        idx: usize,
        budget: usize,
        weights: &[usize],
        exponents: &mut [usize],
        visited: &mut u128,
        max_visits: u128,
        emit: &mut impl FnMut(&[usize]),
    ) -> Result<(), Error> {
        if idx == weights.len() {
            if *visited >= max_visits {
                return Err(Error::Capacity("contraction mode visit budget".into()));
            }
            *visited = visited.checked_add(1).ok_or(Error::Overflow)?;
            emit(exponents);
            return Ok(());
        }
        let weight = weights[idx];
        for count in 0..=(budget / weight) {
            exponents[idx] = count;
            rec(
                idx + 1,
                budget - count * weight,
                weights,
                exponents,
                visited,
                max_visits,
                emit,
            )?;
        }
        Ok(())
    }
    if precision > 0 {
        rec(
            0,
            precision - 1,
            &w,
            &mut exponents,
            &mut visited,
            max_visits,
            &mut emit,
        )?;
    }
    Ok(visited)
}
