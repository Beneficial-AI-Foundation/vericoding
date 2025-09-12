import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "Clover_selectionsort_SelectionSort",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Clover_selectionsort_SelectionSort",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
SelectionSort method translated from Dafny.
Takes an array of integers and sorts it in ascending order.

Original Dafny ensures clauses:
- Elements are sorted in ascending order
- Output array is a permutation of input array
-/
def SelectionSort (a : Array Int) : Array Int := sorry

/--
Specification for SelectionSort method.
Ensures:
1. Array is sorted in ascending order
2. Output array contains same elements as input (is a permutation)
-/
theorem SelectionSort_spec (a : Array Int) :
  let result := SelectionSort a
  -- Array is sorted in ascending order
  (∀ i j, 0 ≤ i → i < j → j < result.size → result.get i ≤ result.get j) ∧
  -- Output is a permutation of input
  (result.toList.toMultiset = a.toList.toMultiset) := sorry

end DafnyBenchmarks