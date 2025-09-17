

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExercisePeekSum_mPeekSum",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExercisePeekSum_mPeekSum",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate that checks if element at index i is greater than or equal to all previous elements -/
def isPeek (v : Array Int) (i : Nat) : Bool := sorry

/-- Function that computes sum of all peak elements up to index i -/
partial def peekSum (v : Array Int) (i : Nat) : Int :=
if i = 0 then 0
else if isPeek v (i-1) then v[i-1]! + peekSum v (i-1)
else peekSum v (i-1)

/-- Method that computes sum of all peak elements in array -/
def mPeekSum (v : Array Int) : Int := sorry

/-- Specification for mPeekSum -/
theorem mPeekSum_spec (v : Array Int) :
v.size > 0 → mPeekSum v = peekSum v v.size := sorry
