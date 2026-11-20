import Mathlib
import ACC.CheckedI128BitVec

/-!
# Independently checked finite arithmetic receipts

A Rust execution can report concrete input word pairs and observed checked
arithmetic outcomes. These reports are UNTRUSTED. This small checker
recomputes the signed 128-bit operation with the independently proved Lean
word specification, including overflow refusal. A successful check therefore
validates every *reported* operation and its observed result.

No claim is made that Rust recorded all operations of a larger execution,
that reported inputs correspond to a particular source graph, or that the
Rust compiler and target machine implement the language specification.
-/

namespace ACC.ArithmeticReceipts

open ACC.CheckedI128BitVec

inductive Kind where
  | add
  | mul
  deriving DecidableEq, Repr

structure Receipt where
  kind : Kind
  left : Word
  right : Word
  observed : Option Word
  deriving Repr

/-- Independently compute the signed-word answer for a claimed operation. -/
def expected (kind : Kind) (left right : Word) : Option Word :=
  match kind with
  | .add => checkedWordAdd left right
  | .mul => checkedWordMul left right

/-- A receipt is accepted only when its observed result and overflow
    decision agree exactly with the independent word operation. -/
def checkReceipt (receipt : Receipt) : Bool :=
  decide (receipt.observed = expected receipt.kind receipt.left receipt.right)

/-- Every accepted receipt contains the correct word or the correct refusal. -/
theorem checkReceipt_sound (receipt : Receipt)
    (h : checkReceipt receipt = true) :
    receipt.observed = expected receipt.kind receipt.left receipt.right := by
  simpa [checkReceipt] using h

/-- Check an entire *finite* transcript, without trusting its outcome fields. -/
def checkTrace (receipts : List Receipt) : Bool :=
  receipts.all checkReceipt

theorem checkTrace_sound (receipts : List Receipt)
    (h : checkTrace receipts = true) :
    ∀ receipt ∈ receipts,
      receipt.observed =
        expected receipt.kind receipt.left receipt.right := by
  induction receipts with
  | nil =>
      intro receipt hmem
      simp at hmem
  | cons head tail ih =>
      have hhead : checkReceipt head = true := by
        cases hh : checkReceipt head with
        | true => exact hh
        | false => simp [checkTrace, hh] at h
      have htail : checkTrace tail = true := by
        simpa [checkTrace, hhead] using h
      intro receipt hmem
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst receipt
        exact checkReceipt_sound head hhead
      · exact ih htail receipt hrest

/-- An untrusted false claim of acceptance is detected. -/
example :
    checkReceipt {
      kind := .mul
      left := BitVec.ofInt 128 (-(2 ^ 127 : ℤ))
      right := BitVec.ofInt 128 (-1)
      observed := some (BitVec.ofInt 128 (-(2 ^ 127 : ℤ)))
    } = false := by decide

/-- The corresponding genuine overflow refusal is accepted. -/
example :
    checkReceipt {
      kind := .mul
      left := BitVec.ofInt 128 (-(2 ^ 127 : ℤ))
      right := BitVec.ofInt 128 (-1)
      observed := none
    } = true := by decide

/-- A false overflow refusal of a representable result is detected. -/
example :
    checkReceipt {
      kind := .add
      left := BitVec.ofInt 128 2
      right := BitVec.ofInt 128 3
      observed := none
    } = false := by decide

#print axioms ACC.ArithmeticReceipts.checkReceipt_sound
#print axioms ACC.ArithmeticReceipts.checkTrace_sound

end ACC.ArithmeticReceipts
