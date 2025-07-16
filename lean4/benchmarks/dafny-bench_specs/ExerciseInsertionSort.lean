import Std.Do.Triple
import Std.Tactic.Do
import NumpySpec.DafnyBenchmarks.Multiset

open Std.Do

/-!
# Exercise: Insertion Sort

This module ports the Dafny specification for insertion sort algorithm.

The specification includes:
- A predicate `sorted_seg` for checking if a segment is sorted (inclusive on both ends)
- A method `InsertionSort` that sorts an entire array using insertion sort
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseInsertionSort

/-- Predicate: segment [i, j] is sorted (inclusive) -/
def sorted_seg (a : Array Int) (i j : Nat) : Prop :=
  ∀ l k : Nat, i ≤ l → l ≤ k → k ≤ j → a[l]! ≤ a[k]!

/-- Implementation placeholder for InsertionSort -/
def InsertionSort (a : Array Int) : StateM (Array Int) Unit := sorry

/-- Hoare triple for InsertionSort -/
theorem InsertionSort_spec (a : Array Int) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄ 
    StateT.run (InsertionSort a) a
    ⦃⇓(_, a') => ⌜sorted_seg a' 0 (a'.size - 1) ∧ 
                  Multiset.ofList a'.toList = Multiset.ofList a.toList⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseInsertionSort