-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_spec (a : Array Int) :
∀ i, 0 ≤ i ∧ i < a.size →
(reverse a)[i]! = a[a.size - 1 - i]! :=
sorry
-- </vc-theorems>