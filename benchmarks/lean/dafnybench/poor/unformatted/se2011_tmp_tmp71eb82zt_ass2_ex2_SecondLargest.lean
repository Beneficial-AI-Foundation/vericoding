

/-!
{
"name": "se2011_tmp_tmp71eb82zt_ass2_ex2_SecondLargest",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: se2011_tmp_tmp71eb82zt_ass2_ex2_SecondLargest",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the second largest element in an array.

@param a The input array of integers
@return The second largest element in the array

Requirements:
- The array must not be empty
-/
def SecondLargest (a : Array Int) : Int :=
sorry

/--
Specification for SecondLargest method.
Ensures that:
- The returned value is less than or equal to the maximum element
- The returned value is greater than or equal to all non-maximum elements
-/
theorem SecondLargest_spec (a : Array Int) :
a.size > 0 →
∃ i, 0 ≤ i ∧ i < a.size ∧
(∀ j, 0 ≤ j ∧ j < a.size ∧ j ≠ i →
(a[i]! ≥ a[j]!) ∧
(SecondLargest a ≤ a[i]!) ∧
(if a[j]! ≠ a[i]! then SecondLargest a ≥ a[j]! else SecondLargest a ≤ a[j]!)) :=
sorry
