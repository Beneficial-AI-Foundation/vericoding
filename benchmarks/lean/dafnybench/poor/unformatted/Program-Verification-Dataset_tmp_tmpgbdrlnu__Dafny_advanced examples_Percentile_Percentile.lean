

/-!
{
"name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_Percentile",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_Percentile",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Sum_ of elements of array A from indices 0 to end (inclusive) -/
partial def SumUpto (A : Array Float) (end_ : Int) : Float :=
if end_ == -1 then
0.0
else
A[end_.toNat]! + SumUpto A (end_ - 1)

/-- Sum_ of all elements in array A -/
def Sum_ (A : Array Float) : Float :=
SumUpto A (A.size - 1)

/-- Percentile function specification -/
theorem percentile_spec (p : Float) (A : Array Float) (total : Float) (i : Int) :
(∀ i, 0 ≤ i ∧ i < A.size → A[i]! > 0.0) →
0.0 ≤ p ∧ p ≤ 100.0 →
total == Sum_ A →
total > 0.0 →
-1 ≤ i ∧ i < A.size ∧
SumUpto A i.toNat ≤ (p/100.0) * total ∧
(i.toNat + 1 < A.size → SumUpto A (i.toNat + 1) > (p/100.0) * total) := sorry

/-- Percentile function implementation -/
def Percentile (p : Float) (A : Array Float) (total : Float) : Int := sorry
