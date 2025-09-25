-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SwapFirstAndLast (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SwapFirstAndLast_spec (a : Array Int) (old_a : Array Int) :
a.size > 0 →
(SwapFirstAndLast a)[0]! = old_a[old_a.size - 1]! ∧
(SwapFirstAndLast a)[a.size - 1]! = old_a[0]! ∧
(∀ k, 1 ≤ k ∧ k < a.size - 1 → (SwapFirstAndLast a)[k]! = old_a[k]!) :=
sorry
-- </vc-theorems>