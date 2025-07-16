import Std.Do.Triple
import Std.Tactic.Do
import NumpySpec.DafnyBenchmarks.Multiset

open Std.Do

/-!
# Exercise: Selection Sort

This module ports the Dafny specification for selection sort algorithm.

The specification includes:
- A predicate `sorted_seg` for checking if a segment is sorted
- A method `selSort` that sorts a segment of an array using selection sort
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseSelSort

/-- Predicate: segment [i, j) is sorted -/
def sorted_seg (a : Array Int) (i j : Nat) : Prop :=
  ∀ l k : Nat, i ≤ l → l ≤ k → k < j → a[l]! ≤ a[k]!

/-- Implementation placeholder for selSort -/
def selSort (a : Array Int) (c f : Nat) : StateM (Array Int) Unit := sorry

/-- Hoare triple for selSort -/
theorem selSort_spec (a : Array Int) (c f : Nat) 
    (h : 0 ≤ c ∧ c ≤ f ∧ f ≤ a.size) :
    ⦃⌜0 ≤ c ∧ c ≤ f ∧ f ≤ a.size⌝⦄ 
    StateT.run (selSort a c f) a
    ⦃⇓(_, a') => ⌜sorted_seg a' c f ∧ 
                  Multiset.ofList (a'.toList.drop c |>.take (f - c)) = 
                  Multiset.ofList (a.toList.drop c |>.take (f - c)) ∧
                  a'.toList.take c = a.toList.take c ∧
                  a'.toList.drop f = a.toList.drop f⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseSelSort