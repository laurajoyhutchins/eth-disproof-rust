module
public import Aeneas
public import CheckedCsrSource.Code.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open CheckedCsrSource

/-!
Concrete, total models for the four Rust core library calls that the pinned
Charon/Aeneas extraction leaves external. No axioms, no sorry, and no
unspecified result substitution are permitted here.

These are *explicit library models*, not a proof of the Rust standard
library implementation. Typechecking the source-derived program under
these models is a smaller, still conditional, source-to-semantics step.
-/

/-- Rust Option<T>::branch for the ? operator. -/
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
    {T : Type _} (value : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match value with
  | some x => ok (.Continue x)
  | none => ok (.Break none)

/-- A broken Option<Never> can contain only none. -/
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type _) (_residual : Option Never) : Result (Option T) :=
  ok none

/-- Rust Result<T,E>::ok returns Some on Ok and None on Err. -/
def core.result.Result.ok {T : Type _} {E : Type _}
    (value : core.result.Result T E) : Result (Option T) :=
  match value with
  | .Ok x => ok (some x)
  | .Err _ => ok none

/-- Model Iterator::all over the actual Aeneas slice iterator state.
Each visited item calls the supplied FnMut closure exactly once.
False stops immediately, leaving the iterator after that item;
true consumes the whole remaining suffix. -/
def checkedCsrAllAux {T : Type _} {F : Type _}
    (fnMut : core.ops.function.FnMut F T Bool)
    (it : core.slice.iter.Iter T) (remaining : List T) (state : F) :
    Result (Bool × core.slice.iter.Iter T) :=
  match remaining with
  | [] => ok (true, it)
  | hd :: tl => do
      let (b, nextState) ← fnMut.call_mut state hd
      let nextIt := {it with i := it.i + 1}
      if b then
        checkedCsrAllAux fnMut nextIt tl nextState
      else
        ok (false, nextIt)

/-- The exact external signature expected by the pinned generated file. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    {T : Type _} {F : Type _}
    (fnMut : core.ops.function.FnMut F T Bool)
    (it : core.slice.iter.Iter T) (state : F) :
    Result (Bool × core.slice.iter.Iter T) :=
  checkedCsrAllAux fnMut it (it.slice.val.drop it.i) state

#print axioms core.option.Option.Insts.CoreOpsTry_traitTry.branch
#print axioms core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
#print axioms core.result.Result.ok
#print axioms core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
