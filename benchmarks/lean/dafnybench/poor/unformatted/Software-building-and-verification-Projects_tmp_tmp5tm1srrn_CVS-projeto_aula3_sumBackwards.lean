

/-!
{
"name": "Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_sumBackwards",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_sumBackwards",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/




/-- Sum function translated from Dafny -/
partial def sum (n : Nat) : Nat :=
if n == 0 then 0
else n + sum (n-1)

/-- sumBackwards method translated from Dafny -/
def sumBackwards (n : Nat) : Nat := sorry

/-- Specification for sumBackwards -/
theorem sumBackwards_spec (n : Nat) :
sumBackwards n = sum n := sorry
