import Mathlib
import IndependentCauchySourceGrid

/-!
# Formal derivative identity for the original Cauchy grid polynomial

The manuscript writes C'(0). Prior arithmetic lemmas had proved
an exact integer product D(0). This module identifies those
expressions without a new normalization or valuation assumption.

The proof reuses Mathlib's derivative-of-nodal-polynomial theorem
on the *literal source grid*. It does not infer the identity from
numerical interpolation samples.
-/

namespace IndependentETH.CauchyFormalDerivative

open IndependentETH.CauchySourceGrid

/-- The original Cauchy polynomial, not just its evaluation formula. -/
noncomputable def sourceCauchyPolynomial (a : ℕ) : Polynomial ℤ :=
  Lagrange.nodal (sourceGrid a) (fun q : ℤ => q)

/-- The nodal definition agrees with the original source product. -/
theorem sourceCauchyPolynomial_eq_product (a : ℕ) :
    sourceCauchyPolynomial a =
      cauchyProduct a (Polynomial.X : Polynomial ℤ) := by
  simp [sourceCauchyPolynomial, Lagrange.nodal, cauchyProduct]

/-- Exact derivative at zero equals the product of distinct differences. -/
theorem source_derivative_at_zero_eq_formal_derivative (a : ℕ) :
    Polynomial.eval 0 (Polynomial.derivative (sourceCauchyPolynomial a)) =
      sourceDerivativeAt a 0 := by
  have hzero : (0 : ℤ) ∈ sourceGrid a := zero_mem_sourceGrid a
  have h := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := sourceGrid a) (v := fun q : ℤ => q) (i := 0) hzero
  calc
    Polynomial.eval 0 (Polynomial.derivative (sourceCauchyPolynomial a)) =
      Polynomial.eval 0
        (Lagrange.nodal ((sourceGrid a).erase 0) (fun q : ℤ => q)) := by
          simpa only [sourceCauchyPolynomial] using h
    _ = sourceDerivativeAt a 0 := by
      simp [Lagrange.eval_nodal, sourceDerivativeAt]

#print axioms IndependentETH.CauchyFormalDerivative.sourceCauchyPolynomial_eq_product
#print axioms IndependentETH.CauchyFormalDerivative.source_derivative_at_zero_eq_formal_derivative

end IndependentETH.CauchyFormalDerivative
