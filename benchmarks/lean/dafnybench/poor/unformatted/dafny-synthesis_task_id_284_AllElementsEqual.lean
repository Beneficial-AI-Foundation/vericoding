import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_284_AllElementsEqual",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_284_AllElementsEqual",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Checks if all elements in an array are equal to a given value n.

@param a The input array to check
@param n The value to compare against
@return True if all elements equal n, false otherwise
-/
def AllElementsEqual (a : Array Int) (n : Int) : Bool := sorry

/--
Specification for AllElementsEqual:
- If result is true, then all elements in array equal n
- If result is false, then there exists an element not equal to n
-/
theorem AllElementsEqual_spec (a : Array Int) (n : Int) :
  (AllElementsEqual a n = true → ∀ i, 0 ≤ i ∧ i < a.size → a[i]! = n) ∧
  (AllElementsEqual a n = false → ∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! ≠ n) := sorry

end DafnyBenchmarks
