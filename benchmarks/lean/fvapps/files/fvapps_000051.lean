-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_have_no_winner (n k d1 d2 : Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_winner_properties (n k d1 d2 : Nat) :
  (n % 3 ≠ 0 → ¬(can_have_no_winner n k d1 d2 = true)) ∧ 
  (k > n ∨ d1 > n ∨ d2 > n → ¬(can_have_no_winner n k d1 d2 = true)) ∧
  (d1 = 0 ∧ d2 = 0 ∧ k % 3 = 0 ∧ k ≤ n → can_have_no_winner n k d1 d2 = true) :=
  sorry

theorem no_winner_trivial_case (n : Nat) :
  can_have_no_winner n 0 0 0 = true :=
  sorry

theorem no_winner_board_size_multiple_three (n k d1 d2 : Nat) :
  n % 3 ≠ 0 → can_have_no_winner n k d1 d2 = false :=
  sorry

theorem no_winner_values_bounds (n k d1 d2 : Nat) :
  k > n ∨ d1 > n ∨ d2 > n → can_have_no_winner n k d1 d2 = false :=
  sorry

theorem no_winner_zero_differences (n k : Nat) :
  k % 3 = 0 → k ≤ n → can_have_no_winner n k 0 0 = true :=
  sorry
-- </vc-theorems>