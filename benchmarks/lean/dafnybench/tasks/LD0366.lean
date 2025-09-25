-- <vc-preamble>
partial def SumUpto (A : Array Float) (end_ : Int) : Float :=
if end_ == -1 then
0.0
else
A[end_.toNat]! + SumUpto A (end_ - 1)

def Sum_ (A : Array Float) : Float :=
SumUpto A (A.size - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PercentileNonUniqueAnswer : Float × Array Float × Float × Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem percentile_non_unique_answer_spec
(p : Float) (A : Array Float) (total : Float) (i1 i2 : Int) :
(∀ i, 0 ≤ i ∧ i < A.size → A[i]! > 0.0) ∧
0.0 ≤ p ∧ p ≤ 100.0 ∧
total == Sum_ A ∧
total > 0.0 ∧
-1 ≤ i1 ∧ i1 < A.size ∧
SumUpto A i1 ≤ (p/100.0) * total ∧
(i1 + 1 < A.size → SumUpto A (i1 + 1) ≥ (p/100.0) * total) ∧
-1 ≤ i2 ∧ i2 < A.size ∧
SumUpto A i2 ≤ (p/100.0) * total ∧
(i2 + 1 < A.size → SumUpto A (i2 + 1) ≥ (p/100.0) * total) ∧
i1 ≠ i2 :=
sorry
-- </vc-theorems>