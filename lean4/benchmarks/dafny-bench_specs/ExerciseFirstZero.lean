import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Find First Zero

This module ports the Dafny specification for finding the first zero
element in an array.

The specification includes:
- A method `mfirstCero` (mfirstZero) that finds the index of the first zero
- Returns an index i where:
  - 0 ≤ i ≤ array.length
  - All elements before index i are non-zero
  - If i < array.length, then array[i] = 0
  - If i = array.length, then no zero exists in the array
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseFirstZero

/-- Implementation placeholder for mfirstCero -/
def mfirstCero (v : Array Int) : Id Nat := sorry

/-- Hoare triple for mfirstCero (find first zero) -/
theorem mfirstCero_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mfirstCero v
    ⦃⇓i => ⌜0 ≤ i ∧ i ≤ v.size ∧
           (∀ j : Nat, j < i → v[j]! ≠ 0) ∧
           (i ≠ v.size → v[i]! = 0)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseFirstZero