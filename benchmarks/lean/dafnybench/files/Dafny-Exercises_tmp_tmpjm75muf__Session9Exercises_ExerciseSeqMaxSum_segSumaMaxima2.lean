-- <vc-preamble>
partial def Sum_ (v : Array Int) (i j : Int) : Int :=
if i = j then 0
else Sum_ v i (j-1) + v[(j-1).toNat]!

def SumMaxToRight (v : Array Int) (i s : Int) : Prop :=
∀ l ss, 0 ≤ l ∧ l ≤ i ∧ ss = i + 1 → Sum_ v l ss ≤ s

partial def Sum2 (v : Array Int) (i j : Int) : Int :=
if i = j then 0
else v[i.toNat]! + Sum2 v (i+1) j

def SumMaxToRight2 (v : Array Int) (j i s : Int) : Prop :=
∀ l ss, j ≤ l ∧ l ≤ i ∧ ss = i + 1 → Sum2 v l ss ≤ s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def segSumaMaxima2 (v : Array Int) (i : Int) : (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem segSumaMaxima2_spec (v : Array Int) (i : Int) (s k : Int) :
v.size > 0 ∧ 0 ≤ i ∧ i < v.size →
0 ≤ k ∧ k ≤ i ∧ s = Sum2 v k (i+1) ∧ SumMaxToRight2 v 0 i s :=
sorry
-- </vc-theorems>