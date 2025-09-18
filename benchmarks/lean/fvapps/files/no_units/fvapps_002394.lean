-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_win_nim (n : Nat) : Bool := sorry

theorem can_win_nim_returns_bool (n : Nat) :
  can_win_nim n = true ∨ can_win_nim n = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_win_nim_period_four (n : Nat) :
  can_win_nim n = can_win_nim (n + 4) := sorry

theorem can_win_nim_losing_position (n : Nat) :
  n % 4 = 0 → can_win_nim n = false := sorry

theorem can_win_nim_winning_position (n : Nat) :
  n % 4 ≠ 0 → can_win_nim n = true := sorry
-- </vc-theorems>