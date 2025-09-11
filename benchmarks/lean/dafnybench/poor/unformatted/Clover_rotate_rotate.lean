

/-!
{
"name": "Clover_rotate_rotate",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_rotate_rotate",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Rotates an array by a given offset.
Translated from Dafny method rotate.

@param a The input array to rotate
@param offset The rotation offset (must be non-negative)
@return The rotated array
-/
def rotate (a : Array Int) (offset : Int) : Array Int := sorry

/--
Specification for the rotate method.
Ensures:
1. Output array has same length as input
2. Each element is correctly rotated by the offset
-/
theorem rotate_spec (a : Array Int) (offset : Int) :
offset ≥ 0 →
let b := rotate a offset
(b.size = a.size) ∧
(∀ i, 0 ≤ i ∧ i < a.size → b[i]! = a[((i + offset) % a.size).toNat]!) := sorry