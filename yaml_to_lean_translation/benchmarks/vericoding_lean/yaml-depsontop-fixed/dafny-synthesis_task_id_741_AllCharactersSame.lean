import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_741_AllCharactersSame",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_741_AllCharactersSame",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Checks if all characters in a string are the same.
Returns true if all characters match, false if there are any differences.

@param s The input string to check
@return True if all characters are the same, false otherwise
-/
def AllCharactersSame (s : String) : Bool := sorry

/--
Specification for AllCharactersSame:
- If result is true, then all characters in the string are equal
- If result is false, then string length > 1 and there exist two different characters
-/
theorem AllCharactersSame_spec (s : String) :
  let result := AllCharactersSame s
  (result → ∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length → s.get i = s.get j) ∧
  (!result → s.length > 1 ∧ ∃ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ i ≠ j ∧ s.get i ≠ s.get j) := sorry

end DafnyBenchmarks