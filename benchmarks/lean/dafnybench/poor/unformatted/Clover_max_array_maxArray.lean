


/-!
{
"name": "Clover_max_array_maxArray",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_max_array_maxArray",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translation of Dafny maxArray method.
Takes an array of integers and returns the maximum value.

Preconditions:
- Array must have length >= 1

Postconditions:
- Result is greater than or equal to all array elements
- Result equals some element in the array
-/
def maxArray (a : Array Int) : Int := sorry

/--
Specification for maxArray method.
-/
theorem maxArray_spec (a : Array Int) :
a.size ≥ 1 →
let m := maxArray a
(∀ k, 0 ≤ k ∧ k < a.size → m ≥ a[k]!) ∧
(∃ k, 0 ≤ k ∧ k < a.size ∧ m = a[k]!) := sorry