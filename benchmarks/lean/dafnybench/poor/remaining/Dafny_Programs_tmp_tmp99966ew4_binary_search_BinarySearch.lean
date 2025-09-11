import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny_Programs_tmp_tmp99966ew4_binary_search_BinarySearch",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Dafny_Programs_tmp_tmp99966ew4_binary_search_BinarySearch",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Predicate indicating whether an array is sorted in ascending order.
Translated from Dafny's sorted predicate.
-/
def sorted (a : Array Int) : Bool :=
  ∀ j k, 0 ≤ j → j < k → k < a.size → a.get ⟨j⟩ ≤ a.get ⟨k⟩

/--
Binary search implementation specification.
Translated from Dafny's BinarySearch method.

@param a The sorted array to search in
@param value The value to search for
@return index The index where value was found, or -1 if not found
-/
def BinarySearch (a : Array Int) (value : Int) : Int := sorry

/--
Main specification theorem for BinarySearch.
Captures the key properties:
1. If index ≥ 0, then value is found at that index
2. If index < 0, then value is not present in the array
-/
theorem BinarySearch_spec (a : Array Int) (value : Int) :
  sorted a →
  let index := BinarySearch a value
  (0 ≤ index → index < a.size ∧ a.get ⟨index⟩ = value) ∧
  (index < 0 → ∀ k, 0 ≤ k → k < a.size → a.get ⟨k⟩ ≠ value) := sorry

end DafnyBenchmarks