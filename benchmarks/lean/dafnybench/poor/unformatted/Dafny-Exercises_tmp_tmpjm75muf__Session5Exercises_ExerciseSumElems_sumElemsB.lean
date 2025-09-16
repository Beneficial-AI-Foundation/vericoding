

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElemsB",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElemsB",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Recursive sum of array elements from right to left -/
partial def SumR (s : Array Int) : Int :=
if s.size = 0 then 0
else SumR (s.extract 0 (s.size - 1)) + s[s.size - 1]!
decreasing_by all_goals simp_wf; omega

/-- Recursive sum of array elements from left to right -/
partial def SumL (s : Array Int) : Int :=
if s.size = 0 then 0
else s[0]! + SumL (s.extract 1 s.size)
decreasing_by all_goals simp_wf; omega

/-- Sum of array elements in range [c,f) -/
def SumV (v : Array Int) (c : Nat) (f : Nat) : Int :=
SumR (v.extract c f)

/-- Method to sum all elements in an array -/
def sumElemsB (v : Array Int) : Int := sorry

/-- Specification for sumElemsB -/
theorem sumElemsB_spec (v : Array Int) :
sumElemsB v = SumR (v.extract 0 v.size) := sorry
