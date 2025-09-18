

/-!
{
"name": "dafny-synthesis_task_id_262_SplitArray",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_262_SplitArray",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Splits an array into two parts at index L.
Input:
- arr: The input array to split
- L: The split point
Returns:
- A pair of arrays representing the first and second parts
-/
def SplitArray (arr : Array Int) (L : Int) : Array Int × Array Int := sorry

/--
Specification for SplitArray:
- Requires L to be between 0 and array length
- Ensures first part has length L
- Ensures second part has length arr.size - L
- Ensures concatenating parts gives original array
-/
theorem SplitArray_spec (arr : Array Int) (L : Int) :
(0 ≤ L ∧ L ≤ arr.size) →
let (firstPart, secondPart) := SplitArray arr L
firstPart.size = L ∧
secondPart.size = arr.size - L ∧
(firstPart.append secondPart) = arr := sorry
