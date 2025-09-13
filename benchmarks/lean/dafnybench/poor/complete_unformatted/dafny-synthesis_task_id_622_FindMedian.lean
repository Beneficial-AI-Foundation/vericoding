import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_622_FindMedian",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_622_FindMedian",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Finds the median of two sorted arrays.
Translated from Dafny method FindMedian.

@param a First sorted array
@param b Second sorted array
@return The median value according to specified rules
-/
def FindMedian (a b : Array Int) : Int := sorry

/--
Specification for FindMedian method.
Requires:
- Arrays are non-null and have same length > 0
- Arrays are sorted in ascending order
Ensures:
- Returns median according to array length parity
-/
theorem FindMedian_spec (a b : Array Int) :
  a.size = b.size ∧
  a.size > 0 ∧
  (∀ i, 0 ≤ i ∧ i < a.size - 1 → a[i]! ≤ a[i + 1]!) ∧
  (∀ i, 0 ≤ i ∧ i < b.size - 1 → b[i]! ≤ b[i + 1]!) →
  FindMedian a b =
    if a.size % 2 = 0
    then (a[a.size / 2 - 1]! + b[0]!) / 2
    else a[a.size / 2]! := sorry

end DafnyBenchmarks
