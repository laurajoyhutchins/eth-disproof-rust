import Mathlib
import IndependentCauchySourceGrid
import IndependentCauchyFactorial
import IndependentCauchyTwoLocal

/-!
# The fixed denominator in the original Cauchy deformation

The source first proves its shifted numerator is divisible by
α D(t), but W(T) is normalized using D(0)=C'(0), not D(t).

Here we prove the exact bridge. The indexed binomial coefficient
at t is odd by the imported Lucas theorem and therefore invertible
whenever odd integers act by units. The two exact integer identities

  D(t) choose(n,k) = (-1)^(n-k) n!
  D(0) choose(n,k0) = (-1)^(n-k0) n!

then show D(t) is a multiple of D(0) in that ring, without
ever inverting the generally nonunit D(0).

The resulting theorem constructs a polynomial with
  C(t+αX) = α D(0) P(X)
in every such ring. This is the source-normalization
divisibility identity, not a field cancellation or a complete
implementation of the original packet recursion.
-/

namespace IndependentETH.CauchyNormalization

open IndependentETH.CauchySourceGrid
open IndependentETH.CauchyFactorial
open IndependentETH.CauchyTwoLocal

private theorem sign_power_self
    {R : Type*} [CommRing R] (e : ℕ) :
    (-1 : R) ^ e * (-1 : R) ^ e = 1 := by
  calc
    (-1 : R) ^ e * (-1 : R) ^ e = (-1 : R) ^ (e + e) :=
      (pow_add _ _ _).symm
    _ = ((-1 : R) ^ 2) ^ e := by
      rw [show e + e = 2 * e by omega, pow_mul]
    _ = 1 := by simp

/-- Solve a common-factor relation without cancelling that factor. -/
private theorem common_signed_numerator
    {R : Type*} [CommRing R]
    (x y n c s t : R) (b : Rˣ)
    (hx : x * (b : R) = s * n)
    (hy : y * c = t * n)
    (ht : t * t = 1) :
    x = y * (s * t * c * ((b⁻¹ : Rˣ) : R)) := by
  have hn : n = y * c * t := by
    calc
      n = (t * t) * n := by rw [ht]; ring
      _ = t * (t * n) := by ring
      _ = t * (y * c) := by rw [← hy]
      _ = y * c * t := by ring
  calc
    x = x * ((b : R) * ((b⁻¹ : Rˣ) : R)) := by simp
    _ = (x * (b : R)) * ((b⁻¹ : Rˣ) : R) := by ring
    _ = (s * n) * ((b⁻¹ : Rˣ) : R) := by rw [hx]
    _ = y * (s * t * c * ((b⁻¹ : Rˣ) : R)) := by rw [hn]; ring

/--
Every original source derivative D(t) is a multiple of D(0)
in any coefficient ring where odd integers are units. This
uses the pinned source grid and the verified Lucas parity,
not an abstract assumption that the derivative valuations match.
-/
theorem source_derivative_multiple_of_at_zero
    {R : Type*} [CommRing R]
    (a : ℕ) (t : ℤ) (ht : t ∈ sourceGrid a)
    (hoddUnits : ∀ d : ℤ, Odd d → IsUnit (d : R)) :
    ∃ u : R,
      (sourceDerivativeAt a t : R) =
        (sourceDerivativeAt a 0 : R) * u := by
  let n : ℕ := 2 ^ (a + 1) - 1
  let k : ℕ := gridIndex a t
  let k0 : ℕ := gridIndex a 0
  have h0 : (0 : ℤ) ∈ sourceGrid a := zero_mem_sourceGrid a
  have hodd : Odd ((n.choose k : ℕ) : ℤ) := by
    exact (source_derivative_binomial_odd a t ht).natCast
  obtain ⟨b, hb⟩ := hoddUnits ((n.choose k : ℕ) : ℤ) hodd
  have htx : (sourceDerivativeAt a t : R) *
      (n.choose k : R) =
        (-1 : R) ^ (n - k) * (n.factorial : R) := by
    have h := congrArg (fun z : ℤ => (z : R))
      (source_derivative_mul_choose a t ht)
    simpa [n, k] using h
  have hzero : (sourceDerivativeAt a 0 : R) *
      (n.choose k0 : R) =
        (-1 : R) ^ (n - k0) * (n.factorial : R) := by
    have h := congrArg (fun z : ℤ => (z : R))
      (source_derivative_mul_choose a 0 h0)
    simpa [n, k0] using h
  have htxb : (sourceDerivativeAt a t : R) * (b : R) =
      (-1 : R) ^ (n - k) * (n.factorial : R) := by
    rw [hb]
    exact htx
  refine ⟨(-1 : R) ^ (n - k) * (-1 : R) ^ (n - k0) *
    (n.choose k0 : R) * ((b⁻¹ : Rˣ) : R), ?_⟩
  exact common_signed_numerator
    (sourceDerivativeAt a t : R)
    (sourceDerivativeAt a 0 : R)
    (n.factorial : R)
    (n.choose k0 : R)
    ((-1 : R) ^ (n - k))
    ((-1 : R) ^ (n - k0))
    b htxb hzero (sign_power_self (n - k0))

/--
An actual source Cauchy numerator is divisible by αD(0), not
merely αD(t). The witness is an element of R and is valid
before reducing to any particular 2-adic precision.
-/
theorem source_cauchy_product_divides_alpha_at_zero
    {R : Type*} [CommRing R]
    (a : ℕ) (t : ℤ) (ht : t ∈ sourceGrid a)
    (z : R) (hoddUnits : ∀ d : ℤ, Odd d → IsUnit (d : R)) :
    ∃ w : R,
      cauchyProduct a ((t : R) + (sourceAlpha a : R) * z) =
        (sourceAlpha a : R) * (sourceDerivativeAt a 0 : R) * w := by
  obtain ⟨v, hv⟩ :=
    source_cauchy_product_divides_alpha_derivative_of_odd_units
      a t ht z hoddUnits
  obtain ⟨u, hu⟩ :=
    source_derivative_multiple_of_at_zero a t ht hoddUnits
  refine ⟨u * v, ?_⟩
  calc
    cauchyProduct a ((t : R) + (sourceAlpha a : R) * z) =
      (sourceAlpha a : R) * (sourceDerivativeAt a t : R) * v := hv
    _ = (sourceAlpha a : R) * (sourceDerivativeAt a 0 : R) * (u * v) := by
      rw [hu]
      ring

/--
The precise polynomial integrality shape of the source, with
Cauchy deformation variable X. This is true in every ring
receiving odd integers as units. Instantiating the original
O=Z_(2)[U]/(f) requires the explicit localization/quotient bridge.
-/
theorem source_cauchy_polynomial_normalization
    {R : Type*} [CommRing R]
    (a : ℕ) (t : ℤ) (ht : t ∈ sourceGrid a)
    (hoddUnits : ∀ d : ℤ, Odd d → IsUnit (d : R)) :
    ∃ P : Polynomial R,
      cauchyProduct a
        ((t : Polynomial R) + (sourceAlpha a : Polynomial R) * Polynomial.X) =
      (sourceAlpha a : Polynomial R) *
        (sourceDerivativeAt a 0 : Polynomial R) * P := by
  have hoddPoly :
      ∀ d : ℤ, Odd d → IsUnit (d : Polynomial R) := by
    intro d hd
    have h : IsUnit (d : R) := hoddUnits d hd
    simpa using h.map (Polynomial.C : R →+* Polynomial R)
  exact source_cauchy_product_divides_alpha_at_zero
    a t ht Polynomial.X hoddPoly

#print axioms IndependentETH.CauchyNormalization.source_derivative_multiple_of_at_zero
#print axioms IndependentETH.CauchyNormalization.source_cauchy_product_divides_alpha_at_zero
#print axioms IndependentETH.CauchyNormalization.source_cauchy_polynomial_normalization

end IndependentETH.CauchyNormalization
