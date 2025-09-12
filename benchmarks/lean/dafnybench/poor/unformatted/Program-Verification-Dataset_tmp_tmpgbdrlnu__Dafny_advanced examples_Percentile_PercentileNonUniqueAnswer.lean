import Std

open Std.Do

/-!
{
  "name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_PercentileNonUniqueAnswer",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_PercentileNonUniqueAnswer",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Sum of elements of array A from indices 0 to end (inclusive) -/
def SumUpto (A : Array Float) (end : Int) : Float :=
  if end == -1 then
    0.0
  else
    A.get ⟨end⟩ + SumUpto A (end - 1)

/-- Sum of all elements in array A -/
def Sum (A : Array Float) : Float :=
  SumUpto A (A.size - 1)

/-- Specification for PercentileNonUniqueAnswer method -/
theorem percentile_non_unique_answer_spec 
  (p : Float) (A : Array Float) (total : Float) (i1 i2 : Int) :
  (∀ i, 0 ≤ i ∧ i < A.size → A.get ⟨i⟩ > 0.0) ∧
  0.0 ≤ p ∧ p ≤ 100.0 ∧
  total == Sum A ∧
  total > 0.0 ∧
  -1 ≤ i1 ∧ i1 < A.size ∧
  SumUpto A i1 ≤ (p/100.0) * total ∧
  (i1 + 1 < A.size → SumUpto A (i1 + 1) ≥ (p/100.0) * total) ∧
  -1 ≤ i2 ∧ i2 < A.size ∧
  SumUpto A i2 ≤ (p/100.0) * total ∧
  (i2 + 1 < A.size → SumUpto A (i2 + 1) ≥ (p/100.0) * total) ∧
  i1 ≠ i2 := sorry

/-- Implementation of PercentileNonUniqueAnswer method -/
def PercentileNonUniqueAnswer : Float × Array Float × Float × Int × Int := sorry

end DafnyBenchmarks