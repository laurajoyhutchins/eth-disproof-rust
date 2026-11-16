import Mathlib

/-!
# Source Cauchy tile: normalized denominator and geometric modes

Original source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/
build/quantitative-contraction.tex, "Modes for interactions between groups".

For a crossing tile y = y₀ + 2^(i+1) j and
v = v₂(t-y₀+x) ≤ i ≤ a, the original Cauchy entry at T=t+2^(a+1)ζ
can be written

  W = 2^(a+1-v) N / (D - 2^(i+1-v) j),

where N = C(T)/(2^(a+1) C'(0)) and
D = (T-y₀+x)/2^v.
The intended source normalization makes N integral and D a unit.

This file verifies the complete truncated geometric identity in ANY
commutative ring with 2^p=0, using an explicit unit D. In particular
the finite inverse is an actual right inverse, its product is the
unique normalized Cauchy entry, and every coefficient of degree b
has the required factor 2^(b+1). No power-series inversion over a
field or informal p-adic estimate is used.

Still open: independently prove that the original C(T), C'(0), and
the complete-residue grid supply integral N and unit D in the
specific coefficient ring A_p. No such property is assumed silently.
-/

namespace IndependentETH.CauchyTileMode

open scoped BigOperators

private theorem geometric_sum_identity
    {R : Type*} [CommRing R] (r : R) (p : ℕ) :
    (1 - r) * (∑ b ∈ Finset.range p, r ^ b) = 1 - r ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- The finite inverse of the odd normalized Cauchy denominator. -/
noncomputable def finiteTileInverse
    {R : Type*} [CommRing R] (p i v : ℕ) (j : R) (D : Rˣ) : R :=
  ((D⁻¹ : Rˣ) : R) *
    (∑ b ∈ Finset.range p,
      ((2 : R) ^ (i + 1 - v) * j * ((D⁻¹ : Rˣ) : R)) ^ b)

/--
The normalized denominator has an exact inverse modulo 2^p
once v ≤ i. This proves the geometric expansion terminates.
-/
theorem finite_tile_inverse_correct
    {R : Type*} [CommRing R]
    (p i v : ℕ) (j : R) (D : Rˣ)
    (hvi : v ≤ i) (hmod : (2 : R) ^ p = 0) :
    ((D : R) - (2 : R) ^ (i + 1 - v) * j) *
      finiteTileInverse p i v j D = 1 := by
  let s : R := ((D⁻¹ : Rˣ) : R)
  let q : R := (2 : R) ^ (i + 1 - v) * j
  let r : R := q * s
  have hip : i + 1 - v = (i - v) + 1 := by omega
  have hr2 : r = (2 : R) * ((2 : R) ^ (i - v) * j * s) := by
    dsimp [r, q]
    rw [hip, pow_succ]
    ring
  have hrpow : r ^ p = 0 := by
    rw [hr2, mul_pow, hmod, zero_mul]
  have hunit : (D : R) * s = 1 := by
    dsimp [s]
    simp
  have hden : ((D : R) - q) * s = 1 - r := by
    calc
      ((D : R) - q) * s = (D : R) * s - q * s := by ring
      _ = 1 - r := by rw [hunit]
  change ((D : R) - q) *
    (s * (∑ b ∈ Finset.range p, r ^ b)) = 1
  calc
    ((D : R) - q) * (s * (∑ b ∈ Finset.range p, r ^ b)) =
        (((D : R) - q) * s) * (∑ b ∈ Finset.range p, r ^ b) := by ring
    _ = (1 - r) * (∑ b ∈ Finset.range p, r ^ b) := by rw [hden]
    _ = 1 - r ^ p := geometric_sum_identity r p
    _ = 1 := by rw [hrpow]; ring

/-- Explicit finite expansion of the normalized source Cauchy term. -/
noncomputable def finiteTileSeries
    {R : Type*} [CommRing R]
    (p a i v : ℕ) (N j : R) (D : Rˣ) : R :=
  ∑ b ∈ Finset.range p,
    (2 : R) ^ (a + 1 - v) * N * ((D⁻¹ : Rˣ) : R) *
      ((2 : R) ^ (i + 1 - v) * j * ((D⁻¹ : Rˣ) : R)) ^ b

theorem finite_tile_series_eq
    {R : Type*} [CommRing R]
    (p a i v : ℕ) (N j : R) (D : Rˣ) :
    finiteTileSeries p a i v N j D =
      ((2 : R) ^ (a + 1 - v) * N) *
        finiteTileInverse p i v j D := by
  unfold finiteTileSeries finiteTileInverse
  let A : R := (2 : R) ^ (a + 1 - v) * N
  let s : R := ((D⁻¹ : Rˣ) : R)
  let r : R := (2 : R) ^ (i + 1 - v) * j * s
  change (∑ b ∈ Finset.range p, (A * s) * r ^ b) =
    A * (s * (∑ b ∈ Finset.range p, r ^ b))
  calc
    (∑ b ∈ Finset.range p, (A * s) * r ^ b) =
        (A * s) * (∑ b ∈ Finset.range p, r ^ b) := by
      rw [Finset.mul_sum]
    _ = A * (s * (∑ b ∈ Finset.range p, r ^ b)) := by ring

/--
The Cauchy numerator is reconstructed by the mode expansion.
Every identity is *inside* the quotient coefficient ring.
-/
theorem finite_tile_series_reconstructs
    {R : Type*} [CommRing R]
    (p a i v : ℕ) (N j : R) (D : Rˣ)
    (hvi : v ≤ i) (hmod : (2 : R) ^ p = 0) :
    ((D : R) - (2 : R) ^ (i + 1 - v) * j) *
      finiteTileSeries p a i v N j D =
        (2 : R) ^ (a + 1 - v) * N := by
  rw [finite_tile_series_eq]
  have hinv := finite_tile_inverse_correct p i v j D hvi hmod
  calc
    (((D : R) - (2 : R) ^ (i + 1 - v) * j) *
      (((2 : R) ^ (a + 1 - v) * N) *
        finiteTileInverse p i v j D)) =
      ((2 : R) ^ (a + 1 - v) * N) *
      (((D : R) - (2 : R) ^ (i + 1 - v) * j) *
        finiteTileInverse p i v j D) := by ring
    _ = (2 : R) ^ (a + 1 - v) * N := by rw [hinv]; ring

/-- The unique solution of the normalized Cauchy denominator equation. -/
theorem finite_tile_series_unique
    {R : Type*} [CommRing R]
    (p a i v : ℕ) (N j W : R) (D : Rˣ)
    (hvi : v ≤ i) (hmod : (2 : R) ^ p = 0)
    (hW : ((D : R) - (2 : R) ^ (i + 1 - v) * j) * W =
      (2 : R) ^ (a + 1 - v) * N) :
    W = finiteTileSeries p a i v N j D := by
  have hinv := finite_tile_inverse_correct p i v j D hvi hmod
  calc
    W = 1 * W := by ring
    _ = (((D : R) - (2 : R) ^ (i + 1 - v) * j) *
          finiteTileInverse p i v j D) * W := by rw [hinv]
    _ = ((2 : R) ^ (a + 1 - v) * N) *
          finiteTileInverse p i v j D := by
      calc
        (((D : R) - (2 : R) ^ (i + 1 - v) * j) *
            finiteTileInverse p i v j D) * W =
          finiteTileInverse p i v j D *
            (((D : R) - (2 : R) ^ (i + 1 - v) * j) * W) := by ring
        _ = ((2 : R) ^ (a + 1 - v) * N) *
              finiteTileInverse p i v j D := by rw [hW]; ring
    _ = finiteTileSeries p a i v N j D :=
      (finite_tile_series_eq p a i v N j D).symm

/--
Each exact source tile-mode coefficient is divisible by 2^(b+1),
including signs and normalization inside N. The only arithmetic
hypotheses are v ≤ i ≤ a, as in the crossing-tile source.
-/
theorem tile_mode_coefficient_has_weight
    {R : Type*} [CommRing R]
    (a i v b : ℕ) (N j : R) (D : Rˣ)
    (hvi : v ≤ i) (hia : i ≤ a) :
    ((2 : R) ^ (a + 1 - v) * N * ((D⁻¹ : Rˣ) : R)) *
      ((2 : R) ^ (i + 1 - v) * j * ((D⁻¹ : Rˣ) : R)) ^ b =
      (2 : R) ^ (b + 1) *
        ((2 : R) ^ (a - v) * N * ((D⁻¹ : Rˣ) : R) *
          ((2 : R) ^ (i - v) * j * ((D⁻¹ : Rˣ) : R)) ^ b) := by
  have hva : v ≤ a := le_trans hvi hia
  have ha : a + 1 - v = (a - v) + 1 := by omega
  have hi : i + 1 - v = (i - v) + 1 := by omega
  rw [ha, hi, pow_succ, pow_succ, mul_pow, pow_succ]
  ring

/--
All omitted heavy modes vanish modulo 2^p, including b=p-1.
The source writes b+1<p, rather than merely b<p.
-/
theorem finite_tile_series_cutoff
    {R : Type*} [CommRing R]
    (p a i v : ℕ) (N j : R) (D : Rˣ)
    (hvi : v ≤ i) (hia : i ≤ a)
    (hmod : (2 : R) ^ p = 0) :
    finiteTileSeries p a i v N j D =
      ∑ b ∈ (Finset.range p).filter (fun b => b + 1 < p),
        (2 : R) ^ (a + 1 - v) * N * ((D⁻¹ : Rˣ) : R) *
          ((2 : R) ^ (i + 1 - v) * j * ((D⁻¹ : Rˣ) : R)) ^ b := by
  classical
  unfold finiteTileSeries
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b + 1 < p
  · simp [hb]
  · have hle : p ≤ b + 1 := Nat.le_of_not_gt hb
    have hz : (2 : R) ^ (b + 1) = 0 := by
      calc
        (2 : R) ^ (b + 1) =
          (2 : R) ^ (p + ((b + 1) - p)) := by
            rw [Nat.add_sub_of_le hle]
        _ = (2 : R) ^ p * (2 : R) ^ ((b + 1) - p) := by
          rw [pow_add]
        _ = 0 := by rw [hmod, zero_mul]
    have hterm :=
      tile_mode_coefficient_has_weight a i v b N j D hvi hia
    rw [hterm, hz]
    simp [hb]

#print axioms IndependentETH.CauchyTileMode.finite_tile_inverse_correct
#print axioms IndependentETH.CauchyTileMode.finite_tile_series_reconstructs
#print axioms IndependentETH.CauchyTileMode.finite_tile_series_unique
#print axioms IndependentETH.CauchyTileMode.tile_mode_coefficient_has_weight
#print axioms IndependentETH.CauchyTileMode.finite_tile_series_cutoff

end IndependentETH.CauchyTileMode
