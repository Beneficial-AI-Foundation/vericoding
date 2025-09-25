-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SecondLargest (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SecondLargest_spec (a : Array Int) :
a.size > 0 →
∃ i, 0 ≤ i ∧ i < a.size ∧
(∀ j, 0 ≤ j ∧ j < a.size ∧ j ≠ i →
(a[i]! ≥ a[j]!) ∧
(SecondLargest a ≤ a[i]!) ∧
(if a[j]! ≠ a[i]! then SecondLargest a ≥ a[j]! else SecondLargest a ≤ a[j]!)) :=
sorry
-- </vc-theorems>