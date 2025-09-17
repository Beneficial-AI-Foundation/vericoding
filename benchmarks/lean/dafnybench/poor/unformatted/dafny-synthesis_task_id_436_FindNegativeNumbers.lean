

/-!
{
"name": "dafny-synthesis_task_id_436_FindNegativeNumbers",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_436_FindNegativeNumbers",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate indicating if a number is negative
-/
def IsNegative (n : Int) : Bool :=
n < 0

/--
Find negative numbers from an array of numbers.
Returns a sequence containing all negative numbers from the input array.

@param arr Input array of integers
@return Array of negative integers from the input
-/
def FindNegativeNumbers (arr : Array Int) : Array Int :=
sorry

/--
Specification for FindNegativeNumbers:
1. All numbers in output are negative and exist in input
2. All negative numbers in input are in output
-/
theorem FindNegativeNumbers_spec (arr : Array Int) :
let result := FindNegativeNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsNegative (result[i]!) ∧ (∃ j, 0 ≤ j ∧ j < arr.size ∧ result[i]! = arr[j]!)) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsNegative (arr[i]!) → (∃ j, 0 ≤ j ∧ j < result.size ∧ arr[i]! = result[j]!)) :=
sorry
