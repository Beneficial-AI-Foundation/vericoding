import Std.Do.Triple
import Std.Tactic.Do
import NumpySpec.DafnyBenchmarks.Multiset

open Std.Do

/-!
# Exercise: Bubble Sort

This module ports the Dafny specification for bubble sort algorithm.

The specification includes:
- A predicate `sorted_seg` for checking if a segment is sorted
- Two bubble sort methods `bubbleSorta` and `bubbleSort` that sort a segment of an array
-/

namespace NumpySpec.DafnyBenchmarks.ExerciseBubbleSort

/-- Predicate: segment [i, j) is sorted -/
def sorted_seg (a : Array Int) (i j : Nat) : Prop :=
  ∀ l k : Nat, i ≤ l → l ≤ k → k < j → a[l]! ≤ a[k]!

/-- Implementation placeholder for bubbleSorta -/
def bubbleSorta (a : Array Int) (c f : Nat) : StateM (Array Int) Unit := sorry

/-- Hoare triple for bubbleSorta -/
theorem bubbleSorta_spec (a : Array Int) (c f : Nat) 
    (h : 0 ≤ c ∧ c ≤ f ∧ f ≤ a.size) :
    ⦃⌜0 ≤ c ∧ c ≤ f ∧ f ≤ a.size⌝⦄ 
    StateT.run (bubbleSorta a c f) a
    ⦃⇓(_, a') => ⌜sorted_seg a' c f ∧ 
                  Multiset.ofList (a'.toList.drop c |>.take (f - c)) = 
                  Multiset.ofList (a.toList.drop c |>.take (f - c)) ∧
                  a'.toList.take c = a.toList.take c ∧
                  a'.toList.drop f = a.toList.drop f⌝⦄ := by
  sorry

/-- Implementation placeholder for bubbleSort -/
def bubbleSort (a : Array Int) (c f : Nat) : StateM (Array Int) Unit := sorry

/-- Hoare triple for bubbleSort -/
theorem bubbleSort_spec (a : Array Int) (c f : Nat) 
    (h : 0 ≤ c ∧ c ≤ f ∧ f ≤ a.size) :
    ⦃⌜0 ≤ c ∧ c ≤ f ∧ f ≤ a.size⌝⦄ 
    StateT.run (bubbleSort a c f) a
    ⦃⇓(_, a') => ⌜sorted_seg a' c f ∧ 
                  Multiset.ofList (a'.toList.drop c |>.take (f - c)) = 
                  Multiset.ofList (a.toList.drop c |>.take (f - c)) ∧
                  a'.toList.take c = a.toList.take c ∧
                  a'.toList.drop f = a.toList.drop f⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.ExerciseBubbleSort