import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_433_IsGreater",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_433_IsGreater",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Checks if a number is greater than all elements in an array.

@param n The number to compare
@param a The array to check against
@return True if n is greater than all elements in a, false otherwise
-/
def IsGreater (n : Int) (a : Array Int) : Bool := sorry

/--
Specification for IsGreater:
- If result is true, n is greater than all elements in the array
- If result is false, there exists an element in the array that is >= n
-/
theorem IsGreater_spec (n : Int) (a : Array Int) :
  (IsGreater n a = true → ∀ i, 0 ≤ i ∧ i < a.size → n > a[i]!) ∧
  (IsGreater n a = false → ∃ i, 0 ≤ i ∧ i < a.size ∧ n ≤ a[i]!) := sorry

end DafnyBenchmarks
