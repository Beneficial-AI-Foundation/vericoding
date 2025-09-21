-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountEqualNumbers (a b c : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountEqualNumbers_spec (a b c : Int) :
let count := CountEqualNumbers a b c
count ≥ 0 ∧ count ≤ 3 ∧
(count = 3 ↔ (a = b ∧ b = c)) ∧
(count = 2 ↔ ((a = b ∧ b ≠ c) ∨ (a ≠ b ∧ b = c) ∨ (a = c ∧ b ≠ c))) ∧
(count = 1 ↔ (a ≠ b ∧ b ≠ c ∧ a ≠ c)) :=
sorry
-- </vc-theorems>