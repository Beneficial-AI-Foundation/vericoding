import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_760_HasOnlyOneDistinctElement",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_760_HasOnlyOneDistinctElement",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Checks if an array has only one distinct element.
Translated from Dafny specification.

@param a The input array to check
@return True if all elements are equal, false otherwise
-/
def HasOnlyOneDistinctElement (a : Array Int) : Bool := sorry

/--
Specification for HasOnlyOneDistinctElement.
- If result is true, all elements in the array are equal
- If result is false, there exist two different elements
-/
theorem HasOnlyOneDistinctElement_spec (a : Array Int) :
  (HasOnlyOneDistinctElement a = true → 
    ∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size → a.get ⟨i⟩ = a.get ⟨j⟩) ∧
  (HasOnlyOneDistinctElement a = false →
    ∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size ∧ a.get ⟨i⟩ ≠ a.get ⟨j⟩) := sorry

end DafnyBenchmarks