import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Check if Array is Positive

This module ports the Dafny specification for checking if all elements 
in an array/sequence are non-negative (≥ 0).

The specification includes multiple method variants:
- `mpositive`: Basic check for positive array
- `mpositive3`: Alternative implementation
- `mpositive4`: Another alternative implementation
- `mpositivertl`: Right-to-left implementation
-/

namespace NumpySpec.DafnyBenchmarks.ExercisePositive

/-- Predicate: all elements in the list are non-negative -/
def positive (s : List Int) : Prop :=
  ∀ i : Fin s.length, s[i] ≥ 0

/-- Convert array to list for specification purposes -/
def arrayToList (v : Array Int) : List Int :=
  v.toList

/-- Implementation placeholder for mpositive -/
def mpositive (v : Array Int) : Id Bool := sorry

/-- Hoare triple for mpositive -/
theorem mpositive_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mpositive v
    ⦃⇓b => ⌜b = positive (arrayToList v)⌝⦄ := by
  sorry

/-- Implementation placeholder for mpositive3 -/
def mpositive3 (v : Array Int) : Id Bool := sorry

/-- Hoare triple for mpositive3 -/
theorem mpositive3_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mpositive3 v
    ⦃⇓b => ⌜b = positive (arrayToList v)⌝⦄ := by
  sorry

/-- Implementation placeholder for mpositive4 -/
def mpositive4 (v : Array Int) : Id Bool := sorry

/-- Hoare triple for mpositive4 -/
theorem mpositive4_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mpositive4 v
    ⦃⇓b => ⌜b = positive (arrayToList v)⌝⦄ := by
  sorry

/-- Implementation placeholder for mpositivertl -/
def mpositivertl (v : Array Int) : Id Bool := sorry

/-- Hoare triple for mpositivertl (right-to-left) -/
theorem mpositivertl_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mpositivertl v
    ⦃⇓b => ⌜b = positive (arrayToList v)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExercisePositive