import Mathlib

/-! Lightweight syntax/elaboration canary for full trace observer state setup.
    Run before compiling the original ~9k-module dependency closure. -/
structure ObserverSyntaxState where
  pc : Option Nat
  regs : Fin 2 → Bool
  «stacks» : Fin 2 → List Bool

def observerSyntaxDirty (init : ObserverSyntaxState) (dirty : Bool) : ObserverSyntaxState :=
  let dirtyRegs := { init with regs := (fun _ => true) }
  let dirtyState := { dirtyRegs with
    «stacks» := Function.update init.stacks (1 : Fin 2) [true, false] }
  if dirty then dirtyState else init
