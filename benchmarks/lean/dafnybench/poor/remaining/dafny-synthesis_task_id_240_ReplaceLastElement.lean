import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_240_ReplaceLastElement",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_240_ReplaceLastElement",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Replaces the last element of the first array with all elements of the second array.

@param first The first input array
@param second The second input array
@return The resulting array with last element replaced
-/
def ReplaceLastElement (first : Array Int) (second : Array Int) : Array Int := sorry

/--
Specification for ReplaceLastElement:
- Requires first array to be non-empty
- Ensures result size is size of first array minus 1 plus size of second array
- Ensures all elements before last of first array are preserved
- Ensures elements after first array are from second array
-/
theorem ReplaceLastElement_spec (first second : Array Int) :
  first.size > 0 →
  let result := ReplaceLastElement first second
  result.size = first.size - 1 + second.size ∧
  (∀ i, 0 ≤ i ∧ i < first.size - 1 → result.get ⟨i⟩ = first.get ⟨i⟩) ∧
  (∀ i, first.size - 1 ≤ i ∧ i < result.size → result.get ⟨i⟩ = second.get (i - first.size + 1)) := sorry

end DafnyBenchmarks