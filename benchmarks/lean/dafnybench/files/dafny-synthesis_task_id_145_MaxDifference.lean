-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MaxDifference (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MaxDifference_spec (a : Array Int) (diff : Int) :
a.size > 1 →
(∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size →
(a[i]!) - (a[j]!) ≤ diff) :=
sorry
-- </vc-theorems>