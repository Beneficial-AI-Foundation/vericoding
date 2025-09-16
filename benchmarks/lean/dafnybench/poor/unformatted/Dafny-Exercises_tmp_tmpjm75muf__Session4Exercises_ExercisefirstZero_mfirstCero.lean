

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExercisefirstZero_mfirstCero",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session4Exercises_ExercisefirstZero_mfirstCero",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the first occurrence of zero in an array.
Returns the index of the first zero, or the array length if no zero is found.

@param v The input array to search
@return The index of the first zero, or array length if none found
-/
def mfirstCero (v : Array Int) : Int := sorry

/--
Specification for mfirstCero:
1. The returned index is within bounds (0 ≤ i ≤ array size)
2. All elements before index i are non-zero
3. If i is not the array length, then v is zero
-/
theorem mfirstCero_spec (v : Array Int) :
let i := mfirstCero v
0 ≤ i ∧ i ≤ v.size ∧
(∀ j, 0 ≤ j ∧ j < i → v[j.toNat]! ≠ 0) ∧
(i ≠ v.size → v[i.toNat]! = 0) := sorry
