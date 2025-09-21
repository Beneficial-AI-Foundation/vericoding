-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TestArrayElements (a : Array Int) (j : Nat) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem TestArrayElements_spec (a : Array Int) (j : Nat) :
(j < a.size) →
let result := TestArrayElements a j
(result[j]! = 60) ∧
(∀ k, 0 ≤ k ∧ k < a.size ∧ k ≠ j → result[k]! = a[k]!) :=
sorry
-- </vc-theorems>