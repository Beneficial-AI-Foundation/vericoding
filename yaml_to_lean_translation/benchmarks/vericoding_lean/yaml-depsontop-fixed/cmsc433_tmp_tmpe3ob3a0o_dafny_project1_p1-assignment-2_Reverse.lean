import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_Reverse",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_Reverse", 
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Reverses an array of integers.
Returns a new array containing the elements in reverse order.

@param a The input array to reverse
@return The reversed array
-/
def Reverse (a : Array Int) : Array Int := sorry

/--
Specification for the Reverse function.
Ensures:
1. The output array has the same length as input
2. Elements are reversed
3. The output array is newly created
-/
theorem reverse_spec (a : Array Int) (aRev : Array Int) :
  aRev = Reverse a →
  (aRev.size = a.size) ∧ 
  (∀ i, 0 ≤ i ∧ i < a.size → a.get i = aRev.get (aRev.size - i - 1)) := sorry

end DafnyBenchmarks