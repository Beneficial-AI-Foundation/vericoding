-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minArray (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minArray_spec (a : Array Int) :
a.size > 0 →
(∀ i, 0 ≤ i ∧ i < a.size → minArray a ≤ a[i]!) ∧
(∃ i, 0 ≤ i ∧ i < a.size ∧ minArray a = a[i]!) :=
sorry
-- </vc-theorems>