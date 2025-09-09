-- <vc-helpers>
-- </vc-helpers>

def jumping_number (n : Nat) : String := sorry

theorem single_digit_jumping (n : Nat) (h : n ≤ 9) : 
  jumping_number n = "Jumping!!" := sorry

theorem result_is_valid (n : Nat) :
  jumping_number n = "Jumping!!" ∨ jumping_number n = "Not!!" := sorry

theorem consecutive_ascending_jumping :
  jumping_number 1234 = "Jumping!!" := sorry

theorem consecutive_descending_jumping :
  jumping_number 4321 = "Jumping!!" := sorry

theorem two_digit_consecutive_jumping :
  jumping_number 12 = "Jumping!!" := sorry

/-
info: 'Jumping!!'
-/
-- #guard_msgs in
-- #eval jumping_number 9

/-
info: 'Jumping!!'
-/
-- #guard_msgs in
-- #eval jumping_number 23

/-
info: 'Not!!'
-/
-- #guard_msgs in
-- #eval jumping_number 79

-- Apps difficulty: introductory
-- Assurance level: unguarded