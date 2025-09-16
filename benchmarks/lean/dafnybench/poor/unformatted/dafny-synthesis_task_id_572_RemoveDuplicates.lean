

/-!
{
"name": "dafny-synthesis_task_id_572_RemoveDuplicates",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_572_RemoveDuplicates",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
RemoveDuplicates takes an array of integers and returns a sequence with duplicates removed.
The output sequence contains exactly the elements that appear in the input array,
and no element appears more than once in the output.
-/
def RemoveDuplicates (a : Array Int) : Array Int := sorry

/--
Specification for RemoveDuplicates:
1. For any element x in the result, it must exist in the input array
2. For any element x in the input array, it must exist in the result
3. No duplicates in the result array
-/
theorem RemoveDuplicates_spec (a : Array Int) :
let result := RemoveDuplicates a
(∀ x, (result.contains x ↔ ∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x)) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≠ result[j]!) := sorry
