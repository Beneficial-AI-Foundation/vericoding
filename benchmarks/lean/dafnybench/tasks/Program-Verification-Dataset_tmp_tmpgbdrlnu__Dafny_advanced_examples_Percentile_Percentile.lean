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
def Percentile (p : Float) (A : Array Float) (total : Float) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem percentile_spec (p : Float) (A : Array Float) (total : Float) (i : Int) :
(∀ i, 0 ≤ i ∧ i < A.size → A[i]! > 0.0) →
0.0 ≤ p ∧ p ≤ 100.0 →
total == Sum_ A →
total > 0.0 →
-1 ≤ i ∧ i < A.size ∧
SumUpto A i.toNat ≤ (p/100.0) * total ∧
(i.toNat + 1 < A.size → SumUpto A (i.toNat + 1) > (p/100.0) * total) :=
sorry
-- </vc-theorems>