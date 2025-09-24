-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindMax (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindMax_spec (a : Array Int) :
a.size > 0 →
let i := FindMax a
0 ≤ i ∧ i < a.size ∧
∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≤ a[i.toNat]! :=
sorry
-- </vc-theorems>