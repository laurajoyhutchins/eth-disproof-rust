import Mathlib
import ACC.ArrayFinishSimulation

/-!
# Signed 128-bit words and checked integer arithmetic

The existing arithmetic interpreter uses arbitrary-precision integers and
a signed-i128 range guard. This module introduces actual 128-bit two's
complement *Lean bitvectors*. Arithmetic uses BitVec's signed-overflow
predicates and wrapped word operations. The proofs establish equivalence of
both the result and the refusal decision to the mathematical interpreter.

This is a word-level specification, not a theorem about Rust's compiler,
the implementation of Rust's checked_add/checked_mul, or CPU instructions.
-/

namespace ACC.CheckedI128BitVec

open ACC.CheckedComponentArithmetic

/-- A 128-bit two's-complement machine-word representation. -/
abbrev Word := BitVec 128

/-- A word decodes into exactly the signed 128-bit range. -/
theorem word_within_range (a : Word) : WithinI128 a.toInt := by
  constructor
  · exact BitVec.le_toInt a
  · exact BitVec.toInt_lt

/-- Every mathematical signed-i128 integer round-trips through the word. -/
theorem encode_decode (z : ℤ) (h : WithinI128 z) :
    (BitVec.ofInt 128 z).toInt = z := by
  exact BitVec.toInt_ofInt_eq_self (by decide) h.1 h.2

/-- Native-shaped signed addition: a real bitvector addition, with its
    bitvector overflow flag tested *before* retaining the result. -/
def checkedWordAdd (a b : Word) : Option Word :=
  if a.saddOverflow b then none else some (a + b)

/-- Native-shaped signed multiplication, using the bitvector's own
    signed-multiplication overflow predicate. -/
def checkedWordMul (a b : Word) : Option Word :=
  if a.smulOverflow b then none else some (a * b)

/-- The bitvector addition-overflow flag is exactly the complement of the
    mathematical signed-i128 representability predicate. -/
theorem add_overflow_iff (a b : Word) :
    a.saddOverflow b = true ↔
      ¬ WithinI128 (a.toInt + b.toInt) := by
  simp only [BitVec.saddOverflow, Bool.or_eq_true,
    decide_eq_true_eq, WithinI128]
  omega

/-- The corresponding result for multiplication, including the asymmetric
    signed minimum and the overflow of i128::MIN * (-1). -/
theorem mul_overflow_iff (a b : Word) :
    a.smulOverflow b = true ↔
      ¬ WithinI128 (a.toInt * b.toInt) := by
  simp only [BitVec.smulOverflow, Bool.or_eq_true,
    decide_eq_true_eq, WithinI128]
  omega

/-- Exact equality of successful results and overflow refusals, not merely
    one-way arithmetic soundness. No wrapping result can be accepted. -/
theorem checkedWordAdd_eq_checkedAdd (a b : Word) :
    Option.map BitVec.toInt (checkedWordAdd a b) =
      checkedAdd a.toInt b.toInt := by
  by_cases h : WithinI128 (a.toInt + b.toInt)
  · have hov : a.saddOverflow b = false := by
      cases hh : a.saddOverflow b with
      | false => rfl
      | true => exact False.elim ((add_overflow_iff a b).mp hh h)
    have heq : (a + b).toInt = a.toInt + b.toInt :=
      BitVec.toInt_add_of_not_saddOverflow (by simp [hov])
    simp [checkedWordAdd, checkedAdd, hov, h, heq]
  · have hov : a.saddOverflow b = true :=
      (add_overflow_iff a b).mpr h
    simp [checkedWordAdd, checkedAdd, hov, h]

/-- Multiplication is equally exact and refusal-equivalent. -/
theorem checkedWordMul_eq_checkedMul (a b : Word) :
    Option.map BitVec.toInt (checkedWordMul a b) =
      checkedMul a.toInt b.toInt := by
  by_cases h : WithinI128 (a.toInt * b.toInt)
  · have hov : a.smulOverflow b = false := by
      cases hh : a.smulOverflow b with
      | false => rfl
      | true => exact False.elim ((mul_overflow_iff a b).mp hh h)
    have heq : (a * b).toInt = a.toInt * b.toInt :=
      BitVec.toInt_mul_of_not_smulOverflow (by simp [hov])
    simp [checkedWordMul, checkedMul, hov, h, heq]
  · have hov : a.smulOverflow b = true :=
      (mul_overflow_iff a b).mpr h
    simp [checkedWordMul, checkedMul, hov, h]

/-- Example: the minimum signed value is representable by its exact
    two's-complement word, including negative powers of two. -/
example :
    (BitVec.ofInt 128 (-(2 ^ 127 : ℤ))).toInt =
      -(2 ^ 127 : ℤ) := by
  apply encode_decode
  norm_num [WithinI128]

/-- Example: the mathematical minimum times negative one is refused. -/
example :
    checkedWordMul
      (BitVec.ofInt 128 (-(2 ^ 127 : ℤ)))
      (BitVec.ofInt 128 (-1)) = none := by decide

/-- Example: a one-unit addition beyond the positive limit is refused. -/
example :
    checkedWordAdd
      (BitVec.ofInt 128 ((2 ^ 127 : ℤ) - 1))
      (BitVec.ofInt 128 1) = none := by decide

#print axioms ACC.CheckedI128BitVec.word_within_range
#print axioms ACC.CheckedI128BitVec.encode_decode
#print axioms ACC.CheckedI128BitVec.add_overflow_iff
#print axioms ACC.CheckedI128BitVec.mul_overflow_iff
#print axioms ACC.CheckedI128BitVec.checkedWordAdd_eq_checkedAdd
#print axioms ACC.CheckedI128BitVec.checkedWordMul_eq_checkedMul

end ACC.CheckedI128BitVec
