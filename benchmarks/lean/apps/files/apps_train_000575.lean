-- <vc-helpers>
-- </vc-helpers>

def sumDigits (n : Nat) : Nat := sorry

def find_jojo_aadhar (n : Nat) : Nat := sorry

theorem digit_sum_div_ten (n : Nat) : 
  (sumDigits (find_jojo_aadhar n)) % 10 = 0 := sorry

theorem matches_input_except_last (n : Nat) :
  find_jojo_aadhar n / 10 = n := sorry

theorem last_digit_in_range (n : Nat) :
  0 ≤ find_jojo_aadhar n % 10 ∧ find_jojo_aadhar n % 10 ≤ 9 := sorry

/-
info: 37
-/
-- #guard_msgs in
-- #eval find_jojo_aadhar 3

/-
info: 109
-/
-- #guard_msgs in
-- #eval find_jojo_aadhar 10

/-
info: 424
-/
-- #guard_msgs in
-- #eval find_jojo_aadhar 42

-- Apps difficulty: interview
-- Assurance level: unguarded