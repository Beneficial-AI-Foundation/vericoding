

/-!
{
"name": "dafny-synthesis_task_id_733_FindFirstOccurrence",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_733_FindFirstOccurrence",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the first occurrence of a target value in a sorted array.

@param arr The input array to search
@param target The value to find
@return The index of the first occurrence of target, or -1 if not found

Requirements:
- Array must be non-null
- Array must be sorted in non-decreasing order

Ensures:
- If index is valid, arr equals target
- If index is -1, target is not in array
- Array contents are unchanged
-/
def FindFirstOccurrence (arr : Array Int) (target : Int) : Int := sorry

/-- Specification for FindFirstOccurrence -/
theorem FindFirstOccurrence_spec
(arr : Array Int) (target : Int) :
(∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!) →
let result := FindFirstOccurrence arr target
(0 ≤ result ∧ result < arr.size → arr[result.toNat]! = target) ∧
(result = -1 → ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! ≠ target) := sorry
