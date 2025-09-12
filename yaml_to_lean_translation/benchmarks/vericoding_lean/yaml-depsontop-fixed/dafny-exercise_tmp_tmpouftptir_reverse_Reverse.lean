import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "dafny-exercise_tmp_tmpouftptir_reverse_Reverse",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_reverse_Reverse",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Reverses an array of characters.

@param a The input array to reverse
@return b The reversed array

Specification:
- Requires input array length > 0
- Ensures input array is unchanged
- Ensures output array has same length as input
- Ensures output array contains reversed elements of input
-/
def Reverse (a : Array Char) : Array Char := sorry

/--
Specification theorem for Reverse function stating its key properties:
1. Input array must be non-empty
2. Input array remains unchanged
3. Output array has same length as input
4. Output array contains reversed elements of input
-/
theorem reverse_spec (a : Array Char) (b : Array Char) :
  a.size > 0 →
  b = Reverse a →
  (b.size = a.size ∧
   ∀ i, 0 ≤ i ∧ i < a.size → b.get i = a.get (a.size - i - 1)) := sorry

end DafnyBenchmarks