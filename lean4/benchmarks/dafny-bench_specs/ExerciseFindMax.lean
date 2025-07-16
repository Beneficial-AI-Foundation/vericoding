import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Find Maximum

This module ports the Dafny specification for finding the maximum value and its
position in an array of non-negative integers.

The specification includes:
- A method `findMax` that returns both the position and value of the maximum element
- Requires all elements to be non-negative
- Ensures the returned value is the maximum
- Ensures the returned position contains the maximum value
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseFindMax

/-- Implementation placeholder for findMax -/
def findMax (a : Array Int) : Id (Nat × Int) := sorry

/-- Hoare triple for findMax -/
theorem findMax_spec (a : Array Int) 
    (h1 : a.size > 0) 
    (h2 : ∀ i : Nat, i < a.size → a[i]! ≥ 0) :
    ⦃⌜a.size > 0 ∧ (∀ i : Nat, i < a.size → a[i]! ≥ 0)⌝⦄ 
    findMax a
    ⦃⇓(pos, maxVal) => ⌜(∀ i : Nat, i < a.size → a[i]! ≤ maxVal) ∧
                        (∃ i : Nat, i < a.size ∧ a[i]! = maxVal) ∧
                        0 ≤ pos ∧ pos < a.size ∧
                        a[pos]! = maxVal⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseFindMax