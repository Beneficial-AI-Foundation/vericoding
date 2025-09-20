-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_palindrome_swaps (s : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>