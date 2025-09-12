```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_426_FilterOddNumbers",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_426_FilterOddNumbers",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["IsOdd"],
  "methods": ["FilterOddNumbers"]
}
-/

namespace DafnyBenchmarks

/-- Predicate indicating if a number is odd -/
def IsOdd (n : Int) : Bool :=
  n % 2 ≠ 0

/-- 
Filter odd numbers from an array of numbers.
Returns a new array containing only the odd numbers from the input array.
-/
def FilterOddNumbers (arr : Array Int) : Array Int :=
  sorry

/--
Specification for FilterOddNumbers:
1. All numbers in the output are odd and exist in the input
2. All odd numbers in the input are in the output
-/
theorem FilterOddNumbers_spec (arr : Array Int) :
  let result := FilterOddNumbers arr
  (∀ i, 0 ≤ i ∧ i < result.size → IsOdd (result.get i) ∧ (result.get i) ∈ arr.toList) ∧
  (∀ i, 0 ≤ i ∧ i < arr.size ∧ IsOdd (arr.get i) → (arr.get i) ∈ result.toList) :=
  sorry

end DafnyBenchmarks
```