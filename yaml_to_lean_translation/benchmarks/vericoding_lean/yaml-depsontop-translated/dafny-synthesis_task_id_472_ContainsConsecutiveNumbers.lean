```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_472_ContainsConsecutiveNumbers",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_472_ContainsConsecutiveNumbers",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["ContainsConsecutiveNumbers"]
}
-/

namespace DafnyBenchmarks

/--
Checks if an array contains consecutive numbers.
Translated from Dafny method ContainsConsecutiveNumbers.

@param a The input array to check
@return True if array contains consecutive numbers, false otherwise
-/
def ContainsConsecutiveNumbers (a : Array Int) : Bool := sorry

/--
Specification for ContainsConsecutiveNumbers.
The array must be non-empty and the result is true if and only if
there exist consecutive elements that differ by 1.
-/
theorem ContainsConsecutiveNumbers_spec (a : Array Int) :
  a.size > 0 →
  ContainsConsecutiveNumbers a = true ↔ 
    (∃ i, 0 ≤ i ∧ i < a.size - 1 ∧ a.get i + 1 = a.get (i + 1)) := sorry

end DafnyBenchmarks
```