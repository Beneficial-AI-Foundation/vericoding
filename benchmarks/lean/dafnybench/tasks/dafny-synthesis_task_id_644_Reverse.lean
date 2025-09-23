-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Reverse (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Reverse_spec (a : Array Int) :
∀ k, 0 ≤ k ∧ k < (Reverse a).size →
(Reverse a)[k]! = a[(a.size - 1) - k]! :=
sorry
-- </vc-theorems>