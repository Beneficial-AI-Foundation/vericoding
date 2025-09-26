import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- A slice object representing a range of indices for array slicing.
    Contains start, stop, and step parameters for creating slices. -/
structure Slice where
  /-- The starting index of the slice (inclusive). If None, starts from the beginning. -/
  start : Option Nat
  /-- The stopping index of the slice (exclusive). If None, goes to the end. -/
  stop : Option Nat
  /-- The step size for the slice. If None, defaults to 1. -/
  step : Option Nat
  deriving Repr, DecidableEq
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- A predicate to check if the components of a slice are valid.
    A slice is valid if the step is positive (if provided) and
    the start is less than or equal to the stop (if both are provided). -/
def IsValidSlice (start stop step : Option Nat) : Prop :=
  (step.isSome → step.get! > 0) ∧
  ((start.isSome ∧ stop.isSome) → start.get! ≤ stop.get!)

-- LLM HELPER
/-- A predicate to check if a slice object is valid.
    A slice is valid if the step is positive (if provided) and
    the start is less than or equal to the stop (if both are provided). -/
def Slice.IsValid (s : Slice) : Prop := IsValidSlice s.start s.stop s.step
-- </vc-helpers>

-- <vc-definitions>
def s_ (start : Option Nat) (stop : Option Nat) (step : Option Nat := none) : Id Slice :=
  pure { start, stop, step }
-- </vc-definitions>

-- <vc-theorems>
theorem s_spec (start : Option Nat) (stop : Option Nat) (step : Option Nat := none) :
    ⦃⌜(step.isSome → step.get! > 0) ∧ 
     ((start.isSome ∧ stop.isSome) → start.get! ≤ stop.get!)⌝⦄
    s_ start stop step
    ⦃⇓slice => ⌜slice.start = start ∧ 
               slice.stop = stop ∧ 
               slice.step = step ∧
               (slice.step.isSome → slice.step.get! > 0) ∧
               ((slice.start.isSome ∧ slice.stop.isSome) → slice.start.get! ≤ slice.stop.get!)⌝⦄ := by
  simp [s_]
  intro h_pre
  simp
  exact h_pre
-- </vc-theorems>
