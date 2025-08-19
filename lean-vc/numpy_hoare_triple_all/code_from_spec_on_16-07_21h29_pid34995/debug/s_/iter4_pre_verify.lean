import Std.Do.Triple
import Std.Tactic.Do

Use one of the two predefined instances `index_exp` or `s_` rather than directly using IndexExpression.

For any index combination, including slicing and axis insertion, ``a[indices]`` is the same as ``a[np.index_exp[indices]]`` for any array `a`. However, ``np.index_exp[indices]`` can be used anywhere in Python code and returns a tuple of slice objects that can be used in the construction of complex index expressions.
-/

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

/-- Index expression builder that creates slice objects for array indexing.
    This is a simplified version of numpy.s_ that creates slice objects
    for use in array indexing operations. -/
def s_ (start : Option Nat) (stop : Option Nat) (step : Option Nat := none) : Id Slice :=
  pure { start := start, stop := stop, step := step }

/-- Specification: s_ creates a well-formed slice object
    This comprehensive specification captures:
    1. The slice object contains the provided start, stop, and step values
    2. If step is provided, it must be positive (non-zero)
    3. If start and stop are both provided, start should be less than or equal to stop
    4. The resulting slice is valid for array indexing operations
    5. The slice preserves the ordering constraints (start ≤ stop when both present)
    6. The step value, if present, is positive for forward slicing
-/
theorem s_spec (start : Option Nat) (stop : Option Nat) (step : Option Nat := none) :
    ⦃⌜(step.isSome → step.get! > 0) ∧ 
     ((start.isSome ∧ stop.isSome) → start.get! ≤ stop.get!)⌝⦄
    s_ start stop step
    ⦃⇓slice => ⌜slice.start = start ∧ 
               slice.stop = stop ∧ 
               slice.step = step ∧
               (slice.step.isSome → slice.step.get! > 0) ∧
               ((slice.start.isSome ∧ slice.stop.isSome) → slice.start.get! ≤ slice.stop.get!)⌝⦄ := by
  intro h
  simp [s_]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact h.1
  · exact h.2