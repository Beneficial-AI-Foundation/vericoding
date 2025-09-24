-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mmaximum1 (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mmaximum1_spec (v : Array Int) :
v.size > 0 →
let i := mmaximum1 v
0 ≤ i ∧ i < v.size ∧
∀ k, 0 ≤ k ∧ k < v.size → v[i.toNat]! ≥ v[k]! :=
sorry
-- </vc-theorems>