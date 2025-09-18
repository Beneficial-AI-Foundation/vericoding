

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mmaximum1",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mmaximum1",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translation of Dafny method mmaximum1 which finds the first maximum element in an array.
Original requires array length > 0.
Original ensures output index is valid and element at that index is maximum.
-/
def mmaximum1 (v : Array Int) : Int := sorry

/--
Specification for mmaximum1 method:
- Requires array length > 0
- Ensures output index is valid (0 ≤ i < v.size)
- Ensures element at index i is ≥ all other elements
-/
theorem mmaximum1_spec (v : Array Int) :
v.size > 0 →
let i := mmaximum1 v
0 ≤ i ∧ i < v.size ∧
∀ k, 0 ≤ k ∧ k < v.size → v[i.toNat]! ≥ v[k]! := sorry
