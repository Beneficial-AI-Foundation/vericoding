-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mfirstCero (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mfirstCero_spec (v : Array Int) :
let i := mfirstCero v
0 ≤ i ∧ i ≤ v.size ∧
(∀ j, 0 ≤ j ∧ j < i → v[j.toNat]! ≠ 0) ∧
(i ≠ v.size → v[i.toNat]! = 0) :=
sorry
-- </vc-theorems>