-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SwapFirstAndLast (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SwapFirstAndLast_spec (a : Array Int) :
a.size > 0 →
let result := SwapFirstAndLast a
result.size = a.size ∧
result[0]! = a[a.size - 1]! ∧
result[result.size - 1]! = a[0]! ∧
(∀ k, 1 ≤ k ∧ k < a.size - 1 → result[k]! = a[k]!) :=
sorry
-- </vc-theorems>