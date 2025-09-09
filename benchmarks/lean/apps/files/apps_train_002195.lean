-- <vc-helpers>
-- </vc-helpers>

def solve_palindrome_swaps (s : String) : Int :=
  sorry

theorem makeable_palindrome_valid (s : String) :
  solve_palindrome_swaps s ≥ 0 ∧ solve_palindrome_swaps s ≠ -1 :=
sorry

theorem unmakeable_palindrome_invalid (s : String) :
  solve_palindrome_swaps s = -1 :=
sorry

theorem solve_palindrome_swaps_bounds (s : String)
  (h : solve_palindrome_swaps s ≠ -1) :
  0 ≤ solve_palindrome_swaps s ∧ 
  solve_palindrome_swaps s ≤ (s.length * (s.length - 1)) / 2 :=
sorry

theorem empty_string_zero : 
  solve_palindrome_swaps "" = 0 :=
sorry

theorem single_char_zero (c : Char) :
  solve_palindrome_swaps (String.mk [c]) = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_palindrome_swaps "eel"

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_palindrome_swaps "ataatmma"

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_palindrome_swaps "snuke"

-- Apps difficulty: competition
-- Assurance level: unguarded