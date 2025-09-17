

/-!
{
"name": "dafny-synthesis_task_id_627_SmallestMissingNumber",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_627_SmallestMissingNumber",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the smallest non-negative integer that is not present in a sorted array.

@param s The input sorted array of non-negative integers
@return The smallest non-negative integer not in the array
-/
def SmallestMissingNumber (s : Array Int) : Int := sorry

/--
Specification for SmallestMissingNumber:
- Input array must be sorted in ascending order
- All elements must be non-negative
- Output must be non-negative
- Output must not be in the input array
- All numbers less than output must be in the input array
-/
theorem SmallestMissingNumber_spec (s : Array Int) :
(∀ i j, 0 ≤ i → i < j → j < s.size → s[i]! ≤ s[j]!) →
(∀ i, 0 ≤ i → i < s.size → s[i]! ≥ 0) →
let v := SmallestMissingNumber s
0 ≤ v ∧
(∀ i, 0 ≤ i → i < s.size → s[i]! ≠ v) ∧
(∀ k, 0 ≤ k → k < v → ∃ i, 0 ≤ i ∧ i < s.size ∧ s[i]! = k) := sorry
