import Mathlib
import IndependentCauchyNormalization

/-!
# The original two-local Cauchy coefficient ring

The October 25 appendix defines O = ℤ_(2)[U]/(f), where ℤ_(2)
contains fractions with odd denominators.

This file constructs ℤ_(2) directly as a localization of ℤ
at the submonoid of *all odd integers*. The source's O is
then the polynomial quotient by the distinguished monic f.
The scalar Cauchy normalization requires no irreducibility
or degree assumption on f, so we establish it for every f.

The theorem constructs an integral polynomial P in O[X] with

  C(t+αX) = α D(0) P(X).

This is an exact equality in the original coefficient-ring
shape, not a test in a finite residue ring. The separate
identification of D(0) with the formal polynomial derivative
C'(0), and the map into K=ℚ[U]/(f), remain explicit
follow-up obligations.
-/

namespace IndependentETH.CauchyLocalRing

open IndependentETH.CauchySourceGrid
open IndependentETH.CauchyNormalization

/-- Precisely the integer denominators invertible in ℤ_(2). -/
def oddIntegerSubmonoid : Submonoid ℤ where
  carrier := {d | Odd d}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    exact ha.mul hb

/-- The source's ℤ_(2), obtained by inverting all odd integers. -/
abbrev TwoLocalIntegers : Type := Localization oddIntegerSubmonoid

/-- Every odd integer is a unit of ℤ_(2), by localization. -/
theorem odd_unit_two_local (d : ℤ) (hd : Odd d) :
    IsUnit (d : TwoLocalIntegers) := by
  simpa using
    (IsLocalization.map_units TwoLocalIntegers
      (⟨d, hd⟩ : oddIntegerSubmonoid))

/--
The source O with its free polynomial coordinate U modulo f.
The integral Cauchy lemma itself does not depend on f being
irreducible, so f remains a parameter.
-/
abbrev SourceO (f : Polynomial TwoLocalIntegers) : Type :=
  Polynomial TwoLocalIntegers ⧸ Ideal.span {f}

/-- Make the quotient's commutative ring instance explicit at the dependent alias. -/
instance sourceOCommRing (f : Polynomial TwoLocalIntegers) : CommRing (SourceO f) :=
  Ideal.Quotient.commRing (Ideal.span {f})

/-- An odd scalar remains invertible after adjoining U and quotienting by f. -/
theorem odd_unit_source_O
    (f : Polynomial TwoLocalIntegers)
    (d : ℤ) (hd : Odd d) :
    IsUnit (d : SourceO f) := by
  have hloc : IsUnit (d : TwoLocalIntegers) :=
    odd_unit_two_local d hd
  have hpoly : IsUnit (d : Polynomial TwoLocalIntegers) := by
    simpa using hloc.map
      (Polynomial.C : TwoLocalIntegers →+* Polynomial TwoLocalIntegers)
  simpa using hpoly.map (Ideal.Quotient.mk (Ideal.span {f}))

/--
Original source-grid scalar Cauchy normalization in O[z].
This holds for every permitted interpolation center t and
every source-shaped coefficient polynomial f. No precision
hypothesis and no unnamed unit assumptions remain.
-/
theorem source_O_cauchy_normalization
    (f : Polynomial TwoLocalIntegers) (a : ℕ)
    (t : ℤ) (ht : t ∈ sourceGrid a) :
    ∃ P : Polynomial (SourceO f),
      cauchyProduct a
        ((t : Polynomial (SourceO f)) +
          (sourceAlpha a : Polynomial (SourceO f)) * Polynomial.X) =
      (sourceAlpha a : Polynomial (SourceO f)) *
        (sourceDerivativeAt a 0 : Polynomial (SourceO f)) * P := by
  exact source_cauchy_polynomial_normalization a t ht
    (fun d hd => odd_unit_source_O f d hd)

#print axioms IndependentETH.CauchyLocalRing.odd_unit_two_local
#print axioms IndependentETH.CauchyLocalRing.odd_unit_source_O
#print axioms IndependentETH.CauchyLocalRing.source_O_cauchy_normalization

end IndependentETH.CauchyLocalRing
