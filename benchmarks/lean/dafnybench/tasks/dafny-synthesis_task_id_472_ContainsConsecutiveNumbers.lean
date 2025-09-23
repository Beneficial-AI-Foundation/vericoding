-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ContainsConsecutiveNumbers (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ContainsConsecutiveNumbers_spec (a : Array Int) :
a.size > 0 →
ContainsConsecutiveNumbers a = true ↔
(∃ i, 0 ≤ i ∧ i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) :=
sorry
-- </vc-theorems>