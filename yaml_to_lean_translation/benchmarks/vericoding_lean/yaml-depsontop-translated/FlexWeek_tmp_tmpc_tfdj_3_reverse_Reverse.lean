```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "FlexWeek_tmp_tmpc_tfdj_3_reverse_Reverse",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: FlexWeek_tmp_tmpc_tfdj_3_reverse_Reverse",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Reverse"]
}
-/

namespace DafnyBenchmarks

/--
Reverses an array of characters.
Input array must not be empty.
Returns a new array with elements in reverse order.
Original array is not modified.
-/
def Reverse (a : Array Char) : Array Char := sorry

/--
Specification for Reverse method:
- Input array must not be empty
- Output array has same length as input
- Each element in output is from reversed position in input
-/
theorem reverse_spec (a : Array Char) :
  a.size > 0 →
  let b := Reverse a
  (b.size = a.size) ∧
  (∀ k, 0 ≤ k ∧ k < a.size → b.get k = a.get ((a.size - 1) - k)) := sorry

end DafnyBenchmarks
```