import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_625_SwapFirstAndLast",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_625_SwapFirstAndLast",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
SwapFirstAndLast swaps the first and last elements of an array.

@param a The input array to modify
-/
def SwapFirstAndLast (a : Array Int) : Array Int := sorry

/--
Specification for SwapFirstAndLast:
- Requires array length > 0
- Ensures first element becomes last element from original array
- Ensures last element becomes first element from original array 
- Ensures all other elements remain unchanged
-/
theorem SwapFirstAndLast_spec (a : Array Int) (old_a : Array Int) :
  a.size > 0 →
  (SwapFirstAndLast a).get 0 = old_a.get (old_a.size - 1) ∧
  (SwapFirstAndLast a).get (a.size - 1) = old_a.get ⟨0⟩ ∧
  (∀ k, 1 ≤ k ∧ k < a.size - 1 → (SwapFirstAndLast a).get k = old_a.get ⟨k⟩) := sorry

end DafnyBenchmarks