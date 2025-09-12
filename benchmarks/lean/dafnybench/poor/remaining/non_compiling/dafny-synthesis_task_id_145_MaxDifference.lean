import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_145_MaxDifference",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_145_MaxDifference",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
MaxDifference takes an array of integers and returns the maximum difference between any two elements.
Requires the array to have length > 1.
Ensures the returned difference is greater than or equal to any difference between two array elements.
-/
def MaxDifference (a : Array Int) : Int := sorry

/--
Specification for MaxDifference:
- Requires array length > 1
- Ensures returned difference is ≥ any difference between array elements
-/
theorem MaxDifference_spec (a : Array Int) (diff : Int) :
  a.size > 1 →
  (∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size → 
    (a.get ⟨i⟩) - (a.get ⟨j⟩) ≤ diff) := sorry

end DafnyBenchmarks