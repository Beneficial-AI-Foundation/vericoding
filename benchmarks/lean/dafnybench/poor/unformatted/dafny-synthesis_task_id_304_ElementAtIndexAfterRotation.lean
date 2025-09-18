

/-!
{
"name": "dafny-synthesis_task_id_304_ElementAtIndexAfterRotation",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_304_ElementAtIndexAfterRotation",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the element at a given index after rotating an array by n positions.

@param l The input array
@param n The number of positions to rotate
@param index The index to find the element at
@return The element at the rotated position
-/
def ElementAtIndexAfterRotation (l : Array Int) (n : Nat) (index : Nat) : Int :=
sorry

/--
Specification for ElementAtIndexAfterRotation:
- Requires n ≥ 0
- Requires index is within bounds of array
- Ensures returned element is at correct rotated position
-/
theorem ElementAtIndexAfterRotation_spec
(l : Array Int) (n : Nat) (index : Nat) :
n ≥ 0 →
0 ≤ index →
index < l.size →
ElementAtIndexAfterRotation l n index = l[((index - n + l.size) % l.size)]! := sorry
