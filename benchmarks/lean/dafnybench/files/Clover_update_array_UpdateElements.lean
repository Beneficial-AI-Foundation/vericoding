-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def UpdateElements (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem UpdateElements_spec (a : Array Int) :
a.size ≥ 8 →
let a' := UpdateElements a
(a'[4]! = a[4]! + 3) ∧
(a'[7]! = 516) ∧
(∀ i, 0 ≤ i ∧ i < a.size → i ≠ 7 ∧ i ≠ 4 → a'[i]! = a[i]!) :=
sorry
-- </vc-theorems>