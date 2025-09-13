import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_629_FindEvenNumbers",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_629_FindEvenNumbers",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Predicate that checks if a number is even
-/
def IsEven (n : Int) : Bool :=
  n % 2 = 0

/--
Function that finds all even numbers in an array.
Returns a sequence containing all even numbers from the input array.

Ensures:
- All numbers in output are even and exist in input
- All even numbers from input exist in output
-/
def FindEvenNumbers (arr : Array Int) : Array Int := sorry

/--
Specification for FindEvenNumbers:
1. All numbers in output are even and exist in input
2. All even numbers from input exist in output
-/
theorem FindEvenNumbers_spec (arr : Array Int) :
  let result := FindEvenNumbers arr
  (∀ i, 0 ≤ i ∧ i < result.size → IsEven (result[i]!) ∧ (result[i]!) ∈ arr.toList) ∧
  (∀ i, 0 ≤ i ∧ i < arr.size ∧ IsEven (arr[i]!) → (arr[i]!) ∈ result.toList) := sorry

end DafnyBenchmarks
