-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dice_sum_outcomes (n s k : Nat) : Nat := sorry

theorem dice_sum_outcomes_invalid_inputs₁ (s k : Nat) :
  dice_sum_outcomes 0 s k = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dice_sum_outcomes_invalid_inputs₂ (n k : Nat) :
  dice_sum_outcomes n 0 k = 0 := sorry
-- </vc-theorems>