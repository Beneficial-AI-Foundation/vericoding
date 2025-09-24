-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mfirstMaximum (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mfirstMaximum_spec (v : Array Int) :
v.size > 0 →
let i := mfirstMaximum v
(0 ≤ i ∧ i < v.size) ∧
(∀ k, 0 ≤ k ∧ k < v.size → v[i.toNat]! ≥ v[k]!) ∧
(∀ l, 0 ≤ l ∧ l < i → v[i.toNat]! > v[l.toNat]!) :=
sorry
-- </vc-theorems>