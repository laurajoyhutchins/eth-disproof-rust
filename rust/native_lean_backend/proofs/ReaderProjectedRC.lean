import Lean

/-!
# Projection ownership: source credits versus implementation Rc handles

This is a small, exact source-reference *accounting* model for a constructor
holding a single object field. It isolates a subtle compiler pitfall:
Lean IR's object projection does not grant an owned reference to the field,
whereas the Rust implementation's Rc alias can keep the allocation resident.

The source rules here are intentionally different from Rust memory safety.
The existing source IR lifetime pass is the admission gate. These algebraic
lemmas justify the guard tested on the *canonical* generated Rust runtime;
they do not prove that the complete C or Rust heaps implement the model.
-/

namespace ReaderProjectedRC

/-- Source count of the constructor shell, count of the referenced child,
and the independently tracked number of *Rust* handles to the child.
An Rc handle is never a source ownership credit. -/
structure State where
  parentRefs : Nat
  fieldRefs : Nat
  rustHandles : Nat
  deriving Repr, DecidableEq

def fresh (rustHandles : Nat) : State :=
  ⟨1, 1, rustHandles⟩

/-- A borrowed Lean IR .proj creates a compiler alias in the Rust runtime.
It must NOT increment the logical source count. -/
def project (s : State) : State :=
  { s with rustHandles := s.rustHandles + 1 }

/-- Source IR .inc explicitly creates an owned child reference, but cannot
resurrect a child whose last source reference was already released. -/
def retainChild (s : State) : Option State :=
  if s.fieldRefs == 0 then none
  else some { s with fieldRefs := s.fieldRefs + 1 }

/-- Releasing the last constructor owner releases its *one owned* pointer
field. More constructor aliases protect the field until the final release.
No Rust handle participates in this transition. -/
def releaseParent (s : State) : Option State :=
  if s.parentRefs == 0 then none else
  some { s with
    parentRefs := s.parentRefs - 1
    fieldRefs := if s.parentRefs == 1 then s.fieldRefs - 1
                 else s.fieldRefs }

/-- Source usability versus Rust allocation residency. They are different
predicates even though both might be checked on the same Rust value. -/
def sourceReadable (s : State) : Bool := s.fieldRefs > 0
def rustResident (s : State) : Bool := s.rustHandles > 0

theorem projection_does_not_retain_source (s : State) :
    (project s).parentRefs = s.parentRefs ∧
    (project s).fieldRefs = s.fieldRefs := by
  simp [project]

theorem projection_creates_rc_alias (s : State) :
    (project s).rustHandles = s.rustHandles + 1 := rfl

theorem dropping_only_parent_invalidates_unretained_projection
    (rustCopies : Nat) :
    releaseParent (project (fresh rustCopies)) =
      some ⟨0, 0, rustCopies + 1⟩ := rfl

theorem rc_alias_does_not_authorize_source_read (rustCopies : Nat) :
    ∃ released,
      releaseParent (project (fresh rustCopies)) = some released ∧
      sourceReadable released = false ∧ rustResident released = true := by
  refine ⟨⟨0, 0, rustCopies + 1⟩, rfl, rfl, ?_⟩
  simp [rustResident]

/-- One explicit source inc before parent destruction protects the child.
The lifetime result depends on source credits, not the number of aliases. -/
theorem retained_field_survives_parent_release (rustCopies : Nat) :
    ∃ retained,
      retainChild (project (fresh rustCopies)) = some retained ∧
      releaseParent retained = some ⟨0, 1, rustCopies + 1⟩ ∧
      sourceReadable ⟨0, 1, rustCopies + 1⟩ = true := by
  refine ⟨⟨1, 2, rustCopies + 1⟩, rfl, rfl, rfl⟩

theorem cannot_retain_after_last_owner_released (rustCopies : Nat) :
    ∀ released,
      releaseParent (project (fresh rustCopies)) = some released →
      retainChild released = none := by
  intro released h
  have he : released = ⟨0, 0, rustCopies + 1⟩ := by
    simpa [dropping_only_parent_invalidates_unretained_projection] using h
  subst released
  rfl

/-- A two-level release cascade with its own independently owned grandchild:
the parent holds the fork, and the fork holds the grandchild. -/
structure Nested where
  rootRefs : Nat
  forkRefs : Nat
  leafRefs : Nat
  leafRustHandles : Nat
  deriving Repr, DecidableEq

def freshNested (rustCopies : Nat) : Nested := ⟨1, 1, 1, rustCopies⟩

def projectNested (s : Nested) : Nested :=
  { s with leafRustHandles := s.leafRustHandles + 1 }

def retainLeaf (s : Nested) : Option Nested :=
  if s.leafRefs == 0 then none
  else some { s with leafRefs := s.leafRefs + 1 }

/-- Deleting the last root credit releases the owned fork, which recursively
releases its leaf if that fork has no other owned source references. -/
def releaseRoot (s : Nested) : Option Nested :=
  if s.rootRefs == 0 then none else
  some { s with
    rootRefs := s.rootRefs - 1
    forkRefs := if s.rootRefs == 1 then s.forkRefs - 1 else s.forkRefs
    leafRefs := if s.rootRefs == 1 && s.forkRefs == 1 then
                  s.leafRefs - 1 else s.leafRefs }

theorem unretained_nested_projection_is_released (rustCopies : Nat) :
    releaseRoot (projectNested (freshNested rustCopies)) =
      some ⟨0, 0, 0, rustCopies + 1⟩ := rfl

theorem explicitly_retained_grandchild_survives (rustCopies : Nat) :
    ∃ retained,
      retainLeaf (projectNested (freshNested rustCopies)) = some retained ∧
      releaseRoot retained = some ⟨0, 0, 1, rustCopies + 1⟩ := by
  exact ⟨⟨1, 1, 2, rustCopies + 1⟩, rfl, rfl⟩

end ReaderProjectedRC

#print axioms ReaderProjectedRC.projection_does_not_retain_source
#print axioms ReaderProjectedRC.rc_alias_does_not_authorize_source_read
#print axioms ReaderProjectedRC.retained_field_survives_parent_release
#print axioms ReaderProjectedRC.cannot_retain_after_last_owner_released
#print axioms ReaderProjectedRC.unretained_nested_projection_is_released
#print axioms ReaderProjectedRC.explicitly_retained_grandchild_survives
