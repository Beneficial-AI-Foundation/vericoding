

/-!
{
"name": "MFES_2021_tmp_tmpuljn8zd9_Exams_Special_Exam_03_2020_4_CatalanNumbers_calcC",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: MFES_2021_tmp_tmpuljn8zd9_Exams_Special_Exam_03_2020_4_CatalanNumbers_calcC",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Recursive function to calculate the nth Catalan number.
Translated from Dafny function C(n).
-/
def C (n : Nat) : Nat :=
if n = 0 then
1
else
(4 * n - 2) * C (n-1) / (n + 1)
decreasing_by all_goals simp_wf; omega

/--
Method to calculate the nth Catalan number.
Ensures the result equals C(n).
-/
def calcC (n : Nat) : Nat := sorry

/--
Specification for calcC method ensuring it returns the correct Catalan number.
-/
theorem calcC_spec (n : Nat) : calcC n = C n := sorry
