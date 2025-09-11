-- <vc-preamble>
def is_very_even_number (n : Nat) : Bool := sorry

def digitSum (n : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def singleDigitSum (n : Nat) : Nat := sorry

theorem very_even_single_digit (n : Nat) :
  n < 10 → is_very_even_number n = (n % 2 = 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem very_even_digit_sum (n : Nat) :
  is_very_even_number n = (singleDigitSum n % 2 = 0) := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_very_even_number 88

/-
info: True
-/
-- #guard_msgs in
-- #eval is_very_even_number 222

/-
info: True
-/
-- #guard_msgs in
-- #eval is_very_even_number 841
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded