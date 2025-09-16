

/-!
{
"name": "Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_maxArrayReverse",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_maxArrayReverse",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/



/-- maxArrayReverse method translated from Dafny -/
def maxArrayReverse (arr : Array Int) : Int := sorry

/-- Specification for maxArrayReverse -/
theorem maxArrayReverse_spec (arr : Array Int) :
arr.size > 0 →
(∀ i : Nat, 0 ≤ i ∧ i < arr.size → arr[i]! ≤ maxArrayReverse arr) ∧
(∃ x : Nat, 0 ≤ x ∧ x < arr.size ∧ arr[x]! = maxArrayReverse arr) := sorry
