import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Exercise: Check Array Containment

This module ports the Dafny specification for checking if elements from one
strictly sorted array are contained in another strictly sorted array.

The specification includes:
- A predicate `strictSorted` for strictly increasing sequences
- A method `mcontained` that checks if the first n elements of array v
  are contained in the first m elements of array w
- The algorithm should run in O(m+n) time
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseContained

/-- Predicate: sequence is strictly sorted (increasing) -/
def strictSorted (s : List Int) : Prop :=
  ∀ u w : Nat, u < w → w < s.length → s[u]! < s[w]!

/-- Check if element is in the first m elements of a list -/
def inFirstM (elem : Int) (w : List Int) (m : Nat) : Prop :=
  ∃ j : Nat, j < m ∧ j < w.length ∧ w[j]? = some elem

/-- Implementation placeholder for mcontained -/
def mcontained (v w : Array Int) (n m : Nat) : Id Bool := sorry

/-- Hoare triple for mcontained -/
theorem mcontained_spec (v w : Array Int) (n m : Nat) 
    (h1 : n ≤ m) (h2 : n ≥ 0)
    (h3 : strictSorted v.toList) 
    (h4 : strictSorted w.toList)
    (h5 : v.size ≥ n) (h6 : w.size ≥ m) :
    ⦃⌜n ≤ m ∧ n ≥ 0 ∧ 
      strictSorted v.toList ∧ strictSorted w.toList ∧
      v.size ≥ n ∧ w.size ≥ m⌝⦄ 
    mcontained v w n m
    ⦃⇓b => ⌜b = (∀ k : Nat, k < n → inFirstM v[k]! w.toList m)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseContained