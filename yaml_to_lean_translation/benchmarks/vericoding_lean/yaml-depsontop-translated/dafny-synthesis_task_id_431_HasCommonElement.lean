```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_431_HasCommonElement",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_431_HasCommonElement",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["HasCommonElement"]
}
-/

namespace DafnyBenchmarks

/--
Checks if two arrays have any common elements.
Translated from Dafny method HasCommonElement.

@param a First array to check
@param b Second array to check
@return True if arrays have a common element, false otherwise
-/
def HasCommonElement (a b : Array Int) : Bool := sorry

/--
Specification for HasCommonElement method.
Ensures:
- If result is true, there exist indices i,j where a[i] equals b[j]
- If result is false, no such indices exist where elements are equal
-/
theorem HasCommonElement_spec (a b : Array Int) :
  (HasCommonElement a b = true → 
    ∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧ a.get i = b.get j) ∧
  (HasCommonElement a b = false →
    ∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size → a.get i ≠ b.get j) := sorry

end DafnyBenchmarks
```