-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mlastMaximum (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mlastMaximum_spec (v : Array Int) :
v.size > 0 →
let i := mlastMaximum v
(0 ≤ i ∧ i < v.size) ∧
(∀ k, 0 ≤ k ∧ k < v.size → v[i.toNat]! ≥ v[k]!) ∧
(∀ l, i < l ∧ l < v.size → v[i.toNat]! > v[l.toNat]!) :=
sorry
-- </vc-theorems>