```lean
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Int.Basic
import Mathlib.Data.Array.Basic

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_412_RemoveOddNumbers",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_412_RemoveOddNumbers",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": []
}
-/

namespace DafnyBenchmarks

/--
Predicate indicating if a number is even
-/
def IsEven (n : Int) : Bool :=
  n % 2 = 0

/--
Removes odd numbers from an array of integers.
Returns an array containing only the even numbers from the input array.

@param arr The input array of integers
@return Array of even integers from the input
-/
def RemoveOddNumbers (arr : Array Int) : Array Int :=
  sorry

/--
Specification for RemoveOddNumbers:
1. All numbers in the output are even and exist in the input
2. All even numbers in the input are in the output
-/
theorem RemoveOddNumbers_spec (arr : Array Int) :
  let result := RemoveOddNumbers arr
  (∀ i, 0 ≤ i ∧ i < result.size → IsEven result[i]! ∧ result[i]! ∈ arr.toList) ∧
  (∀ i, 0 ≤ i ∧ i < arr.size ∧ IsEven arr[i]! → arr[i]! ∈ result.toList) :=
  sorry

end DafnyBenchmarks
```