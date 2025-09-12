```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_610_RemoveElement",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_610_RemoveElement",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["RemoveElement"]
}
-/

namespace DafnyBenchmarks

/--
RemoveElement removes an element at index k from array s and returns the resulting array.

@param s The input array
@param k The index to remove
@return The array with element at index k removed

Requirements:
- k must be a valid index in s (0 ≤ k < s.size)

Ensures:
- Output array is one element shorter than input
- Elements before k are preserved
- Elements after k are shifted down by one
-/
def RemoveElement (s : Array Int) (k : Int) : Array Int := sorry

/--
Specification for RemoveElement method
-/
theorem RemoveElement_spec (s : Array Int) (k : Int) :
  0 ≤ k ∧ k < s.size →
  let v := RemoveElement s k
  v.size = s.size - 1 ∧
  (∀ i, 0 ≤ i ∧ i < k → v.get i = s.get i) ∧
  (∀ i, k ≤ i ∧ i < v.size → v.get i = s.get (i + 1)) := sorry

end DafnyBenchmarks
```