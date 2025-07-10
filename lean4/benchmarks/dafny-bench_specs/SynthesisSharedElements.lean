import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Shared Elements

This module ports the Dafny synthesis task for finding shared elements between two arrays.

The specification includes:
- A predicate `InArray` to check if an element exists in an array
- A method `sharedElements` that returns elements present in both arrays
- Ensures all returned elements are in both arrays
- Ensures all returned elements are distinct
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisSharedElements

/-- Predicate: element x is in array a -/
def InArray (a : Array Int) (x : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = x

/-- Implementation placeholder for sharedElements -/
def sharedElements (a b : Array Int) : Id (List Int) := sorry

/-- Hoare triple for sharedElements -/
theorem sharedElements_spec (a b : Array Int) :
    ⦃⌜True⌝⦄ 
    sharedElements a b
    ⦃⇓result => ⌜(∀ x ∈ result, InArray a x ∧ InArray b x) ∧
                 (∀ i j : Nat, i < j → j < result.length → result[i]! ≠ result[j]!)⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisSharedElements