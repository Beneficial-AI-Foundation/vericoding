-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_most_common_divisor (l r : Nat) : Nat := sorry

theorem single_number_returns_itself (x : Nat)
  (h : x > 0) : find_most_common_divisor x x = x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_output_is_positive (l r : Nat)
  (h₁ : l > 0) (h₂ : r > 0) : find_most_common_divisor l r > 0 := sorry

theorem range_output_less_than_max_input (l r : Nat)  
  (h₁ : l > 0) (h₂ : r > 0) : find_most_common_divisor l r ≤ max l r := sorry
-- </vc-theorems>