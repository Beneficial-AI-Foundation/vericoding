```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_793_LastPosition",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_793_LastPosition",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["LastPosition"]
}
-/

namespace DafnyBenchmarks

/--
Finds the last position of an element in a sorted array.
Input:
  - arr: Array of integers
  - elem: Integer to search for
Returns:
  - Position of the last occurrence of elem, or -1 if not found
Requires:
  - Array is non-empty
  - Array is sorted in non-decreasing order
Ensures:
  - Result is -1 or a valid index with the element
  - If result is valid, it's the last occurrence
  - Array contents remain unchanged
-/
def LastPosition (arr : Array Int) (elem : Int) : Int := sorry

/--
Specification for LastPosition function
-/
theorem LastPosition_spec (arr : Array Int) (elem : Int) :
  arr.size > 0 ∧ 
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr.get i ≤ arr.get j) →
  let pos := LastPosition arr elem
  (pos = -1 ∨ 
   (0 ≤ pos ∧ pos < arr.size ∧ 
    arr.get pos = elem ∧
    (pos ≤ arr.size - 1 ∨ arr.get (pos + 1) > elem))) ∧
  (∀ i, 0 ≤ i ∧ i < arr.size → arr.get i = arr.get i) := sorry

end DafnyBenchmarks
```