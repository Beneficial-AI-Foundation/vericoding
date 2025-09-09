-- <vc-helpers>
-- </vc-helpers>

def can_win_nim (n : Nat) : Bool := sorry

theorem can_win_nim_returns_bool (n : Nat) :
  can_win_nim n = true ∨ can_win_nim n = false := sorry

theorem can_win_nim_period_four (n : Nat) :
  can_win_nim n = can_win_nim (n + 4) := sorry

theorem can_win_nim_losing_position (n : Nat) :
  n % 4 = 0 → can_win_nim n = false := sorry

theorem can_win_nim_winning_position (n : Nat) :
  n % 4 ≠ 0 → can_win_nim n = true := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval can_win_nim 4

/-
info: True
-/
-- #guard_msgs in
-- #eval can_win_nim 1

/-
info: True
-/
-- #guard_msgs in
-- #eval can_win_nim 2

-- Apps difficulty: introductory
-- Assurance level: unguarded