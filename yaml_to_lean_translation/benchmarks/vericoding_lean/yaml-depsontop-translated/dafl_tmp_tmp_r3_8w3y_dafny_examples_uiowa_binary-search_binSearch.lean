```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_binary-search_binSearch",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_binary-search_binSearch",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["binSearch"]
}
-/

namespace DafnyBenchmarks

/--
Predicate indicating whether an array is sorted in ascending order.
Translated from Dafny's isSorted predicate.
-/
def isSorted (a : Array Int) : Bool :=
  ∀ i j : Nat, i ≤ j ∧ j < a.size → a.get i ≤ a.get j

/--
Binary search implementation translated from Dafny.
Returns true if element K exists in sorted array a.

@param a The sorted input array
@param K The key to search for
@return Whether K exists in array a
-/
def binSearch (a : Array Int) (K : Int) : Bool := sorry

/--
Specification for binary search correctness.
-/
theorem binSearch_spec (a : Array Int) (K : Int) :
  isSorted a →
  binSearch a K = (∃ i : Nat, i < a.size ∧ a.get i = K) := sorry

end DafnyBenchmarks
```