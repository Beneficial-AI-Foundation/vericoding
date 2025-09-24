-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def barrier (v : Array Int) (p : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem barrier_spec (v : Array Int) (p : Int) :
v.size > 0 ∧
0 ≤ p ∧ p < v.size →
barrier v p = (∀ k l, 0 ≤ k ∧ k ≤ p ∧ p < l ∧ l < v.size → v[k.toNat]! < v[l.toNat]!) :=
sorry
-- </vc-theorems>