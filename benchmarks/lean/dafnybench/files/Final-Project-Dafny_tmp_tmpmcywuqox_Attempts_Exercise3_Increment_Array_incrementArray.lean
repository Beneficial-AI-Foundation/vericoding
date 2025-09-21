-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def incrementArray (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem incrementArray_spec (a : Array Int) :
a.size > 0 →
∀ i, 0 ≤ i ∧ i < a.size →
(incrementArray a)[i]! = a[i]!+1:=
sorry
-- </vc-theorems>