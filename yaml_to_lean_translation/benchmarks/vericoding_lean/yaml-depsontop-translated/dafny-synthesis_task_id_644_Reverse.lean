```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_644_Reverse",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_644_Reverse",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Reverse"]
}
-/

namespace DafnyBenchmarks

/--
Reverses the elements of an array in place.

@param a The array to reverse
-/
def Reverse (a : Array Int) : Array Int := sorry

/--
Specification for the Reverse method:
- The resulting array has each element equal to the corresponding element 
  from the original array in reverse order
-/
theorem Reverse_spec (a : Array Int) :
  ∀ k, 0 ≤ k ∧ k < (Reverse a).size → 
    (Reverse a).get k = a.get ((a.size - 1) - k) := sorry

end DafnyBenchmarks
```