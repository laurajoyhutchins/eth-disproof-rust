import Mathlib

/-!
Reference propositions transcribed from independently published mathematics.
These are *not* compiler output. Their correspondence with the cited text
requires an additional source review; Lean only checks their types and the
equivalence of generated statements to these reference propositions.

D02 is deliberately omitted: the DLMF generalized complex binomial convention
needs a context-sensitive formalization. Do not replace it with Nat.choose.
-/
namespace ExternalGold

def O01 : Prop := ∀ (a b : ℝ), a + b = b + a
def O02 : Prop := ∀ (a b c : ℝ), a + (b + c) = (a + b) + c
def O03 : Prop := ∀ (a b : ℝ), a * b = b * a
def O04 : Prop := ∀ (a b c : ℝ), a * (b + c) = a * b + a * c
def O05 : Prop := ∀ (a : ℝ), a + 0 = a
def O06 : Prop := ∀ (a : ℝ), a * 1 = a
def O07 : Prop := ∀ (a : ℝ), a + (-a) = 0

def D01 : Prop :=
  ∀ (n : ℕ), (Finset.range (n + 1)).sum (fun k => Nat.choose n k) = 2 ^ n

def D03 : Prop :=
  ∀ (m n p : ℕ) (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ),
    (A * B).transpose = B.transpose * A.transpose

def N01 : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
    A.transpose.transpose = A

def N02 : Prop :=
  ∀ (m n : ℕ) (A B : Matrix (Fin m) (Fin n) ℝ),
    (A + B).transpose = A.transpose + B.transpose

end ExternalGold
