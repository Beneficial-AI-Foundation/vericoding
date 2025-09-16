

/-!
{
"name": "dafny-synthesis_task_id_591_SwapFirstAndLast",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_591_SwapFirstAndLast",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
SwapFirstAndLast swaps the first and last elements of an array.

@param a The input array to modify
-/
def SwapFirstAndLast (a : Array Int) : Array Int := sorry

/--
Specification for SwapFirstAndLast:
- Requires array is non-null and non-empty
- Ensures first and last elements are swapped
- Ensures all other elements remain unchanged
-/
theorem SwapFirstAndLast_spec (a : Array Int) :
a.size > 0 →
let result := SwapFirstAndLast a
result.size = a.size ∧
result[0]! = a[a.size - 1]! ∧
result[result.size - 1]! = a[0]! ∧
(∀ k, 1 ≤ k ∧ k < a.size - 1 → result[k]! = a[k]!) := sorry
