-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_phone_keypad (digits: String) : Nat := sorry

theorem solve_phone_keypad_bounds (digits: String) :
  solve_phone_keypad digits < 1000000007 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_phone_keypad_single_seven_or_nine (d: Char) :
  d = '7' ∨ d = '9' →
  solve_phone_keypad (String.mk [d]) = 4 := sorry

theorem solve_phone_keypad_single_one (d: Char) :
  d = '1' →
  solve_phone_keypad (String.mk [d]) = 0 := sorry

theorem solve_phone_keypad_single_other (d: Char) :
  d ≠ '0' ∧ d ≠ '1' ∧ d ≠ '7' ∧ d ≠ '9' →
  solve_phone_keypad (String.mk [d]) = 3 := sorry

theorem solve_phone_keypad_all_zeros (n: Nat) :
  solve_phone_keypad (String.mk (List.replicate n '0')) = 0 := sorry

theorem solve_phone_keypad_commutative (a b: Char) :
  solve_phone_keypad (String.mk [a, b]) = 
  solve_phone_keypad (String.mk [b, a]) := sorry

theorem solve_phone_keypad_regression_72 :
  solve_phone_keypad "72" = 12 := sorry

theorem solve_phone_keypad_regression_234 :
  solve_phone_keypad "234" = 27 := sorry
-- </vc-theorems>