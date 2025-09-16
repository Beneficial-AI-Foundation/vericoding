

/-!
{
"name": "dafny-synthesis_task_id_567_IsSorted",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_567_IsSorted",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if an array is sorted in non-decreasing order.

@param a The array to check
@return sorted True if the array is sorted, false otherwise

Requires:
- Array must be non-empty

Ensures:
- sorted is true iff for all valid indices i,j where i < j, a ≤ a
- If not sorted, there exist indices i,j where i < j and a > a
-/
def IsSorted (a : Array Int) : Bool := sorry

/-- Specification for IsSorted -/
theorem IsSorted_spec (a : Array Int) :
a.size > 0 →
(IsSorted a ↔ (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!)) ∧
(¬IsSorted a → ∃ i j, 0 ≤ i ∧ i < j ∧ j < a.size ∧ a[i]! > a[j]!) := sorry
