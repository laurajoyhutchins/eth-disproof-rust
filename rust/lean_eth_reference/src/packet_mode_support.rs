//! A finite source-packet occupancy model, not the original packet builder.
//!
//! The manuscript's packing lemma places each real edge in the *same* row
//! and column slot. For unequal labels, the source says a row crosses a
//! column tile iff their slot bits at i=v2(t) agree. Hence any real source
//! column in that tile contributes a paired target row with v2(D)=i.
//! This defeats any row-by-row geometric strengthening beyond a+1-i+b.
//!
//! See openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! quantitative-contraction.tex, lem:tensor-packets and tensor-modes.

use crate::Error;
use crate::valuation_mode_certificate::{ModeRows, ModeWeightCertificate};

/// Explicit packet shape from the paper. The caller is responsible for
/// proving that these real slots and coordinate labels were emitted by the
/// original packing construction. Each occupied slot stands for *both*
/// its row and column port, as guaranteed by that construction.
#[derive(Clone, Copy, Debug)]
pub struct PacketSlots<'a> {
    pub a: u32,
    pub u: u32,
    pub t: i64,
    pub labels: (u8, u8),
    pub real_slots: &'a [u64],
}

#[derive(Debug, PartialEq, Eq)]
pub enum TileMode {
    /// Equal packet symbols mean there are no cross-group mode variables.
    LocalOnly,
    /// No real columns in this tile, so its mode form L_Z is zero.
    EmptySourceTile,
    /// Rows and columns are *derived* from the same source real slots.
    Contributing {
        source_columns: Vec<u64>,
        target_rows: Vec<u64>,
        certificate: ModeWeightCertificate,
    },
}

impl PacketSlots<'_> {
    pub fn certify_tile(self, y0: u64, b: u32) -> Result<TileMode, Error> {
        if self.a == 0 || self.a > 60 || self.u == 0 || self.u > self.a {
            return Err(Error::Invalid("invalid source packet parameters".into()));
        }
        let l = 1u64 << self.a;
        if self.t == 0 || i128::from(self.t) < -i128::from(l) || self.t as i128 >= i128::from(l) {
            return Err(Error::Invalid("invalid source Hermite point".into()));
        }
        let i = self.t.unsigned_abs().trailing_zeros();
        if i >= self.u || self.labels.0 >= 64 || self.labels.1 >= 64 {
            return Err(Error::Invalid("source coordinate or labels invalid".into()));
        }
        let width = 1u64 << (i + 1);
        if y0 >= width || self.real_slots.len() > 1_000_000 {
            return Err(Error::Capacity(
                "packet tile residue or occupancy envelope".into(),
            ));
        }
        let mut sorted = self.real_slots.to_vec();
        sorted.sort_unstable();
        if sorted.iter().any(|&x| x >= l) || sorted.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(Error::Invalid(
                "packet slots must be unique and in range".into(),
            ));
        }
        if self.labels.0 == self.labels.1 {
            return Ok(TileMode::LocalOnly);
        }
        let source_columns: Vec<_> = sorted
            .iter()
            .copied()
            .filter(|&y| y % width == y0)
            .collect();
        if source_columns.is_empty() {
            return Ok(TileMode::EmptySourceTile);
        }
        let bit = 1u64 << i;
        let target_rows: Vec<_> = sorted
            .iter()
            .copied()
            .filter(|&x| x & bit == y0 & bit)
            .collect();
        let certificate = ModeRows {
            a: self.a,
            u: self.u,
            t: self.t,
            y0,
            b,
            target_rows: &target_rows,
        }
        .certify_assuming_complete_rows()?;
        // Each source column y has an occupied row at x=y. Since
        // y=y0+2^(i+1)*j, D=t-y0+x=t+2^(i+1)*j and v2(D)=i.
        // Thus the minimum row weight is the uniform coarse source bound.
        if certificate.whole_mode_weight != certificate.coarse_weight
            || !source_columns.iter().all(|y| target_rows.contains(y))
        {
            return Err(Error::Invalid(
                "paired-slot valuation invariant violated".into(),
            ));
        }
        Ok(TileMode::Contributing {
            source_columns,
            target_rows,
            certificate,
        })
    }
}
