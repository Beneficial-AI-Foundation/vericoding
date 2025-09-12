import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_751_IsMinHeap",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_751_IsMinHeap",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Checks if an array represents a valid min heap.
Translated from Dafny method IsMinHeap.

@param a The input array to check
@return Whether the array is a valid min heap
-/
def IsMinHeap (a : Array Int) : Bool := sorry

/--
Specification for IsMinHeap method.
Ensures that:
1. If result is true, then for all valid indices i, a is less than or equal to its children
2. If result is false, then there exists an index i where a is greater than one of its children
-/
theorem IsMinHeap_spec (a : Array Int) (result : Bool) :
  result → (∀ i, 0 ≤ i ∧ i < a.size / 2 → 
    a.get i ≤ a.get (2*i + 1) ∧ 
    (2*i + 2 = a.size ∨ a.get i ≤ a.get (2*i + 2))) ∧
  (¬result → ∃ i, 0 ≤ i ∧ i < a.size / 2 ∧ 
    (a.get i > a.get (2*i + 1) ∨ 
     (2*i + 2 ≠ a.size ∧ a.get i > a.get (2*i + 2)))) := sorry

end DafnyBenchmarks