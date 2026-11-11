//! Geometry-derived lower bounds for the manuscript's crossing-mode coefficients.
//!
//! Pinned source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
//! quantitative-contraction.tex, equations tensor-mode-expansion and
//! tensor-mode-budget. This is an experimental proof-bound calculator,
//! NOT a replacement for the Lean BitProgram and NOT a packet generator.

use crate::Error;
use crate::valuation_modes::CrossingMode;

/// One source crossing term at T=t+2^(a+1) z, tile y=y0+2^(i+1) j.
/// The parent caller must independently establish that this is a real
/// crossing packet. We verify the *numeric consequence* v2(t-y0+x)<=i.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrossingWitness {
    pub a: u32,
    pub u: u32,
    pub t: i64,
    pub x: u64,
    pub y0: u64,
    pub b: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertifiedWeights {
    pub i: u32,
    pub denominator_v2: u32,
    pub original: u64,
    pub paper_coarse: u64,
    pub geometry_refined: u64,
}

impl CrossingWitness {
    /// Validate bounded integer geometry, then derive a coefficient weight.
    /// For D=t-y0+x, the source proves:
    ///
    /// v2(C(T)/(C'(0)*D)) >= a+1-i,
    /// v2((2^(i+1)/D)^b) = b*(i+1-v2(D)).
    ///
    /// Their product therefore has valuation at least the returned weight.
    pub fn certify(self) -> Result<CertifiedWeights, Error> {
        if self.a == 0 || self.a > 60 || self.u == 0 || self.u > self.a {
            return Err(Error::Invalid("unsupported deformation dimensions".into()));
        }
        let l = 1i128 << self.a;
        let t = i128::from(self.t);
        if t == 0 || t < -l || t >= l || i128::from(self.x) >= l {
            return Err(Error::Invalid("point/row is outside S or tile".into()));
        }
        let i = self.t.unsigned_abs().trailing_zeros();
        if i >= self.u {
            return Err(Error::Invalid("Hermite point has zero multiplicity".into()));
        }
        let tile_width = 1u128 << (i + 1);
        if u128::from(self.y0) >= tile_width {
            return Err(Error::Invalid("tile residue exceeds its width".into()));
        }
        let d = t - i128::from(self.y0) + i128::from(self.x);
        if d == 0 {
            return Err(Error::Invalid("crossing denominator is zero".into()));
        }
        let v = d.unsigned_abs().trailing_zeros();
        if v > i {
            return Err(Error::Invalid("crossing valuation inequality fails".into()));
        }
        let base = u64::from(self.a + 1 - i);
        let b = u64::from(self.b);
        let ratio = u64::from(i + 1 - v);
        let improved = base
            .checked_add(b.checked_mul(ratio).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?;
        Ok(CertifiedWeights {
            i,
            denominator_v2: v,
            original: b + 1,
            paper_coarse: base + b,
            geometry_refined: improved,
        })
    }

    pub fn source_coarse_mode(self) -> Result<CrossingMode, Error> {
        let certificate = self.certify()?;
        Ok(CrossingMode {
            a: self.a as usize,
            i: certificate.i as usize,
            b: self.b as usize,
        })
    }
}

/// The source precision budget of tapered Hermite recovery:
/// h=ceil(3*M/u), D_t=2^(a-i), p_t=p+8*h*D_t+8*M*(a+1).
/// This is a source parameter calculator, not a claim that the
/// theorem's active-call packing conditions hold for these inputs.
pub fn source_precision(a: u32, u: u32, i: u32, m: u64, p: u64) -> Result<u128, Error> {
    if a == 0 || a > 60 || u == 0 || u > a || i >= u || m < u64::from(u) {
        return Err(Error::Invalid("invalid tapered Hermite parameters".into()));
    }
    let m = u128::from(m);
    let u = u128::from(u);
    let h = m
        .checked_mul(3)
        .and_then(|v| v.checked_add(u - 1))
        .ok_or(Error::Overflow)?
        / u;
    let d = 1u128 << (a - i);
    let hermite = h
        .checked_mul(d)
        .and_then(|v| v.checked_mul(8))
        .ok_or(Error::Overflow)?;
    let baseline = m
        .checked_mul(u128::from(a + 1))
        .and_then(|v| v.checked_mul(8))
        .ok_or(Error::Overflow)?;
    u128::from(p)
        .checked_add(hermite)
        .and_then(|v| v.checked_add(baseline))
        .ok_or(Error::Overflow)
}
