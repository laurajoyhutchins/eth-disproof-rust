import Mathlib

/-!
# A connected non-affine CNF family: exact finite-state semantics

For a list of parity right-hand sides d, a three-bit seed determines all
variables by the recurrence x_(i+3) = x_i xor x_(i+1) xor d_i.
Each parity equation has a four-clause, assignment-preserving 3-CNF gadget.

The additional positive sliding-window clauses reject the zero three-bit
window. We prove that the resulting *seed-level* formula is identical at
every seed to a finite forbidden-state mask and that for homogeneous RHS
the count is seven, for every recurrence length.

This is a restricted family, not a theorem about arbitrary CNF, and not
a formal refinement of the separate Rust CSR recognizer.
-/

namespace IndependentETH.NonAffine

abbrev State := Bool × Bool × Bool

def zeroState : State := (false, false, false)

def next (d : Bool) : State → State
  | (a, b, c) => (b, c, Bool.xor (Bool.xor a b) d)

def previous (d : Bool) : State → State
  | (b, c, w) => (Bool.xor (Bool.xor w b) d, b, c)

theorem previous_next (d : Bool) (s : State) :
    previous d (next d s) = s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem next_previous (d : Bool) (s : State) :
    next d (previous d s) = s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Exact satisfaction of the four clauses forbidding odd-parity triples. -/
def evenGadget (a b c : Bool) : Bool :=
  (a || b || !c) &&
  (a || !b || c) &&
  (!a || b || c) &&
  (!a || !b || !c)

/-- Exact satisfaction of the four clauses forbidding even-parity triples. -/
def oddGadget (a b c : Bool) : Bool :=
  (a || b || c) &&
  (a || !b || !c) &&
  (!a || b || !c) &&
  (!a || !b || c)

def parityGadget (d a b c : Bool) : Bool :=
  if d then oddGadget a b c else evenGadget a b c

theorem gadget_exact (d a b c : Bool) :
    parityGadget d a b c =
      decide (Bool.xor (Bool.xor a b) c = d) := by
  cases d <;> cases a <;> cases b <;> cases c <;> decide

/-- The Boolean OR on three ports is exactly nonzeroness of their state. -/
def nonzero (s : State) : Bool := decide (s ≠ zeroState)

def orWindow : State → Bool
  | (a, b, c) => a || b || c

theorem orWindow_exact (s : State) : orWindow s = nonzero s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- Enforce every sliding OR window, including the last window. -/
def accepts : State → List Bool → Bool
  | s, [] => nonzero s
  | s, d :: ds => nonzero s && accepts (next d s) ds

/-- The forbidden mask is a set of at most eight states, *not* a table
    of assignments to every original variable. -/
def forbidden (ds : List Bool) : Finset State :=
  Finset.univ.filter (fun s => accepts s ds = false)

def accepted (ds : List Bool) : Finset State :=
  Finset.univ.filter (fun s => accepts s ds = true)

/-- The mask is extensionally equivalent to the whole recurrence/OR
    evaluation at every externally visible initial state. -/
theorem accepted_iff_not_forbidden (ds : List Bool) (s : State) :
    accepts s ds = true ↔ s ∉ forbidden ds := by
  simp only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and]
  cases accepts s ds <;> simp

theorem accepted_complement (ds : List Bool) :
    accepted ds = (forbidden ds)ᶜ := by
  ext s
  simpa [accepted] using (accepted_iff_not_forbidden ds s)

/-- In the semantic seed space there are eight possible inputs; the
    exact number of satisfying assignments is 8 minus forbidden seeds. -/
theorem count_eq_eight_sub_forbidden (ds : List Bool) :
    (accepted ds).card = 8 - (forbidden ds).card := by
  rw [accepted_complement]
  simp [Finset.card_compl, Fintype.card_prod]

def zeros : Nat → List Bool
  | 0 => []
  | k + 1 => false :: zeros k

theorem nonzero_next_false (s : State) :
    nonzero (next false s) = nonzero s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem accepts_zeros (k : Nat) (s : State) :
    accepts s (zeros k) = nonzero s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change (nonzero s && accepts (next false s) (zeros k)) = nonzero s
      rw [ih, nonzero_next_false]
      cases nonzero s <;> rfl

/-- The homogeneous connected non-affine family has seven satisfying
    three-bit seeds at *every* size n=k+4. By the recurrence, each seed
    has exactly one corresponding n-bit assignment. -/
theorem homogeneous_count_seven (k : Nat) :
    (accepted (zeros k)).card = 7 := by
  have h : accepted (zeros k) =
      (Finset.univ : Finset State).filter (fun s => s ≠ zeroState) := by
    ext s
    simp [accepted, accepts_zeros, nonzero]
  rw [h]
  decide

#print axioms IndependentETH.NonAffine.previous_next
#print axioms IndependentETH.NonAffine.next_previous
#print axioms IndependentETH.NonAffine.gadget_exact
#print axioms IndependentETH.NonAffine.orWindow_exact
#print axioms IndependentETH.NonAffine.accepted_iff_not_forbidden
#print axioms IndependentETH.NonAffine.count_eq_eight_sub_forbidden
#print axioms IndependentETH.NonAffine.homogeneous_count_seven

end IndependentETH.NonAffine
