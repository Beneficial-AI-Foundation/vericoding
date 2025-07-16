import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Find First Negative Element

This module ports the Dafny specification for finding the first negative
element in an array.

The specification includes:
- A predicate `positive` that checks if all elements in a sequence are non-negative
- Two method variants (`mfirstNegative` and `mfirstNegative2`) that:
  - Return a boolean indicating if a negative element exists
  - Return the index of the first negative element if it exists
  - Ensure all elements before the first negative are non-negative
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseFirstNegative

/-- Predicate: all elements in the list are non-negative -/
def positive (s : List Int) : Prop :=
  ∀ u : Nat, u < s.length → s[u]! ≥ 0

/-- Get sublist from index 0 to i (exclusive) -/
def sublistTo (v : Array Int) (i : Nat) : List Int :=
  (v.toList).take i

/-- Implementation placeholder for mfirstNegative -/
def mfirstNegative (v : Array Int) : Id (Bool × Nat) := sorry

/-- Hoare triple for mfirstNegative -/
theorem mfirstNegative_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mfirstNegative v
    ⦃⇓(b, i) => ⌜(b ↔ ∃ k : Nat, k < v.size ∧ v[k]! < 0) ∧
                (b → 0 ≤ i ∧ i < v.size ∧ v[i]! < 0 ∧ positive (sublistTo v i))⌝⦄ := by
  sorry

/-- Implementation placeholder for mfirstNegative2 -/
def mfirstNegative2 (v : Array Int) : Id (Bool × Nat) := sorry

/-- Hoare triple for mfirstNegative2 -/
theorem mfirstNegative2_spec (v : Array Int) :
    ⦃⌜True⌝⦄ 
    mfirstNegative2 v
    ⦃⇓(b, i) => ⌜(b ↔ ∃ k : Nat, k < v.size ∧ v[k]! < 0) ∧
                (b → 0 ≤ i ∧ i < v.size ∧ v[i]! < 0 ∧ positive (sublistTo v i))⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseFirstNegative