//! Conditional, whole-mode valuations for the manuscript's tensor contraction.
//!
//! A source mode Z is shared by *all* crossing rows of one packet/tile/b.
//! A single row's valuation must never be used to prune Z^beta globally.
//!
//! Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! quantitative-contraction.tex, tensor-mode-expansion/budget.

use crate::Error;
use crate::valuation_witness::CrossingWitness;

/// A single (packet, tile, interpolation point, geometric exponent) mode.
/// `target_rows` MUST be the complete set of contributing real target rows.
/// The caller must still prove its packet labels and group incidence match
/// the source; this constructor can only validate numeric crossing geometry.
#[derive(Clone, Copy, Debug)]
pub struct ModeRows<'a> {
    pub a: u32,
    pub u: u32,
    pub t: i64,
    pub y0: u64,
    pub b: u32,
    pub target_rows: &'a [u64],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ModeWeightCertificate {
    /// Original paper bound: b+1.
    pub source_weight: u64,
    /// From its stated a+1-i and ratio valuation >=b.
    pub coarse_weight: u64,
    /// Minimum of the more precise bounds recorded by experiment 005.
    pub prior_geometry_weight: u64,
    /// Exact z-linear coefficient valuation for the *least* divisible row.
    /// Also a coefficientwise lower bound for every row's full power series.
    pub whole_mode_weight: u64,
    pub least_divisible_row: u64,
    pub maximum_denominator_v2: u32,
    pub row_count: usize,
}

impl ModeRows<'_> {
    pub fn certify_assuming_complete_rows(self) -> Result<ModeWeightCertificate, Error> {
        if self.target_rows.is_empty() {
            return Err(Error::Invalid(
                "mode needs contributing rows; empty group is a distinct zero case".into(),
            ));
        }
        if self.target_rows.len() > 1_000_000 {
            return Err(Error::Capacity("experimental mode row inventory".into()));
        }
        let mut max_v = 0;
        let mut worst_row = 0;
        let mut prior_min = u64::MAX;
        let mut whole_min = u64::MAX;
        let mut source = 0;
        let mut coarse = 0;
        for &x in self.target_rows {
            let witness = CrossingWitness {
                a: self.a,
                u: self.u,
                t: self.t,
                x,
                y0: self.y0,
                b: self.b,
            };
            let row = witness.certify()?;
            let bit = 1u64 << row.i;
            if (x & bit) != (self.y0 & bit) {
                return Err(Error::Invalid(
                    "target row and tile do not share the crossing bit".into(),
                ));
            }
            // At T=t+2^(a+1)z, C(T)=2^(a+1)z*C'(t)+O(z^2),
            // and v2(C'(t))=v2(C'(0)) on the source's complete grid S.
            // Therefore v2([z] A_Z) = a+1-v + b*(i+1-v), v=v2(t-y0+x).
            let exact = row
                .geometry_refined
                .checked_add(u64::from(row.i - row.denominator_v2))
                .ok_or(Error::Overflow)?;
            if exact < whole_min {
                whole_min = exact;
                worst_row = x;
                max_v = row.denominator_v2;
            }
            prior_min = prior_min.min(row.geometry_refined);
            source = row.original;
            coarse = row.paper_coarse;
        }
        Ok(ModeWeightCertificate {
            source_weight: source,
            coarse_weight: coarse,
            prior_geometry_weight: prior_min,
            whole_mode_weight: whole_min,
            least_divisible_row: worst_row,
            maximum_denominator_v2: max_v,
            row_count: self.target_rows.len(),
        })
    }
}
